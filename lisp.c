// vim: set tabstop=2 shiftwidth=2 textwidth=79 expandtab:
// gcc -O2 -g -Wall -Wextra -pedantic -fno-strict-aliasing

#define _GNU_SOURCE
#include <assert.h>   // for assert
#include <stdbool.h>  // for bool
#include <stddef.h>   // for NULL
#include <stdint.h>   // for int32_t, etc
#include <stdio.h>    // for getline, fprintf
#include <string.h>   // for memcpy
#include <sys/mman.h> // for mmap
#undef _GNU_SOURCE

#include "greatest.h"

#define WARN_UNUSED __attribute__((warn_unused_result))

/*
  We use tagged pointers. Tag values and interpretations as shown here:

    High                                                         Low
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX00  Integer
    0000000000000000000000000000000000000000000000000XXXXXXX00001111  Character
    00000000000000000000000000000000000000000000000000000000X0011111  Boolean
    0000000000000000000000000000000000000000000000000000000000101111  Nil
    0000000000000000000000000000000000000000000000000000000000111111  Error
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX001  Pair
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX010  Vector
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX011  String
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX101  Symbol
    XXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXXX110  Closure
*/

// Objects

typedef int64_t word;
typedef uint64_t uword;

const int kBitsPerByte = 8;                        // bits
const int kWordSize = sizeof(word);                // bytes
const int kBitsPerWord = kWordSize * kBitsPerByte; // bits

const unsigned int kIntegerTag = 0x0;
const unsigned int kIntegerTagMask = 0x3;
const unsigned int kIntegerShift = 2;
const unsigned int kIntegerBits = kBitsPerWord - kIntegerShift;
const word kIntegerMax = (1LL << (kIntegerBits - 1)) - 1;
const word kIntegerMin = -(1LL << (kIntegerBits - 1));

word Object_encode_integer(word value) {
  assert(value < kIntegerMax && "too big");
  assert(value > kIntegerMin && "too small");
  return value << kIntegerShift;
}

word Object_decode_integer(uword value) { return (word)value >> kIntegerShift; }

bool Object_is_integer(uword value) {
  return (value & kIntegerTagMask) == kIntegerTag;
}

const unsigned int kImmediateTagMask = 0x3f;

const unsigned int kCharTag = 0xf;
const unsigned int kCharMask = 0xff;
const unsigned int kCharShift = 8;

word Object_encode_char(char value) {
  return ((word)value << kCharShift) | kCharTag;
}

char Object_decode_char(word value) {
  return (value >> kCharShift) & kCharMask;
}

bool Object_is_char(uword value) { return (value & kCharTag) == kCharTag; }

const unsigned int kBoolTag = 0x1f;
const unsigned int kBoolMask = 0x80;
const unsigned int kBoolShift = 7;

word Object_encode_bool(bool value) {
  return ((word)value << kBoolShift) | kBoolTag;
}

bool Object_decode_bool(word value) { return value & kBoolMask; }

word Object_true() { return Object_encode_bool(true); }

word Object_false() { return Object_encode_bool(false); }

word Object_nil() { return 0x2f; }

const unsigned int kErrorTag = 0x3f; // 0b111111
uword Object_error() { return kErrorTag; }

const unsigned int kPairTag = 0x1;
const uword kHeapTagMask = ((uword)0x7);
const uword kHeapPtrMask = ~kHeapTagMask;

const unsigned int kCarIndex = 0;
const unsigned int kCarOffset = kCarIndex * kWordSize;
const unsigned int kCdrIndex = kCarIndex + 1;
const unsigned int kCdrOffset = kCdrIndex * kWordSize;
const unsigned int kPairSize = kCdrOffset + kWordSize;

uword Object_address(void *obj) { return (uword)obj & kHeapPtrMask; }

bool Object_is_pair(uword value) { return (value & kHeapTagMask) == kPairTag; }

uword Object_pair_car(uword value) {
  assert(Object_is_pair(value));
  return ((uword *)Object_address((void *)value))[kCarIndex];
}

uword Object_pair_cdr(uword value) {
  assert(Object_is_pair(value));
  return ((uword *)Object_address((void *)value))[kCdrIndex];
}

const unsigned int kSymbolTag = 0x5;

typedef struct {
  word length;
  char cstr[];
} Symbol;

// Environment (as alist)

typedef struct Env {
  const char *name;
  word value;
  struct Env *prev;
} Env;

Env Env_bind(const char *name, word value, Env *prev) {
  return (Env){.name = name, .value = value, .prev = prev};
}

bool Env_find(Env *env, const char *key, word *result) {
  if (env == NULL) {
    return false;
  }
  if (strcmp(env->name, key) == 0) {
    *result = env->value;
    return true;
  }
  return Env_find(env->prev, key, result);
}

// AST

struct ASTNode;
typedef struct ASTNode ASTNode;

typedef struct {
  ASTNode *car;
  ASTNode *cdr;
} Pair;

ASTNode *AST_new_integer(word value) {
  return (ASTNode *)Object_encode_integer(value);
}

bool AST_is_integer(ASTNode *node) {
  return ((word)node & kIntegerTagMask) == kIntegerTag;
}

word AST_get_integer(ASTNode *node) { return (word)node >> kIntegerShift; }

ASTNode *AST_new_char(char value) {
  return (ASTNode *)Object_encode_char(value);
}

bool AST_is_char(ASTNode *node) {
  return ((word)node & kImmediateTagMask) == kCharTag;
}

char AST_get_char(ASTNode *node) { return Object_decode_char((word)node); }

ASTNode *AST_new_bool(bool value) {
  return (ASTNode *)Object_encode_bool(value);
}

bool AST_is_bool(ASTNode *node) {
  return ((word)node & kImmediateTagMask) == kBoolTag;
}

bool AST_get_bool(ASTNode *node) { return Object_decode_bool((word)node); }

ASTNode *AST_new_nil() { return (ASTNode *)Object_nil(); }

bool AST_is_nil(ASTNode *node) { return (word)node == Object_nil(); }

ASTNode *AST_nil() { return (ASTNode *)Object_nil(); }

bool AST_is_error(ASTNode *node) { return (uword)node == Object_error(); }
ASTNode *AST_error() { return (ASTNode *)Object_error(); }

ASTNode *AST_heap_alloc(unsigned char tag, uword size) {
  uword address = (uword)calloc(size, 1);
  return (ASTNode *)(address | tag);
}

bool AST_is_heap_object(ASTNode *node) {
  unsigned char tag = (uword)node & kHeapTagMask;
  return (tag & kIntegerTagMask) > 0 && (tag & kImmediateTagMask) != 0x07;
}

bool AST_is_pair(ASTNode *node);
ASTNode *AST_pair_car(ASTNode *node);
ASTNode *AST_pair_cdr(ASTNode *node);

void AST_heap_free(ASTNode *node) {
  if (!AST_is_heap_object(node)) {
    return;
  }
  if (AST_is_pair(node)) {
    AST_heap_free(AST_pair_car(node));
    AST_heap_free(AST_pair_cdr(node));
  }
  free((void *)Object_address(node));
}

void AST_pair_set_car(ASTNode *node, ASTNode *car);
void AST_pair_set_cdr(ASTNode *node, ASTNode *cdr);

ASTNode *AST_new_pair(ASTNode *car, ASTNode *cdr) {
  ASTNode *node = AST_heap_alloc(kPairTag, sizeof(Pair));
  AST_pair_set_car(node, car);
  AST_pair_set_cdr(node, cdr);
  return node;
}

bool AST_is_pair(ASTNode *node) {
  return ((uword)node & kHeapTagMask) == kPairTag;
}

Pair *AST_as_pair(ASTNode *node) {
  assert(AST_is_pair(node));
  return (Pair *)Object_address(node);
}

ASTNode *AST_pair_car(ASTNode *node) { return AST_as_pair(node)->car; }

void AST_pair_set_car(ASTNode *node, ASTNode *car) {
  AST_as_pair(node)->car = car;
}

ASTNode *AST_pair_cdr(ASTNode *node) { return AST_as_pair(node)->cdr; }

void AST_pair_set_cdr(ASTNode *node, ASTNode *cdr) {
  AST_as_pair(node)->cdr = cdr;
}

Symbol *AST_as_symbol(ASTNode *node);

ASTNode *AST_new_symbol(const char *str) {
  word data_length = strlen(str) + 1;
  ASTNode *node = AST_heap_alloc(kSymbolTag, sizeof(Symbol) + data_length);
  Symbol *s = AST_as_symbol(node);
  s->length = data_length;
  memcpy(s->cstr, str, data_length);
  return node;
}

bool AST_is_symbol(ASTNode *node) {
  return ((uword)node & kHeapTagMask) == kSymbolTag;
}

Symbol *AST_as_symbol(ASTNode *node) {
  assert(AST_is_symbol(node));
  return (Symbol *)Object_address(node);
}

const char *AST_symbol_cstr(ASTNode *node) {
  return (const char *)AST_as_symbol(node)->cstr;
}

bool AST_symbol_matches(ASTNode *node, const char *cstr) {
  return strcmp(AST_symbol_cstr(node), cstr) == 0;
}

// Buffer
typedef unsigned char byte;

typedef enum {
  kWritable,
  kExecutable,
} BufferState;

typedef struct {
  byte *address;
  BufferState state;
  size_t len;
  size_t capacity;
} Buffer;

byte *Buffer_alloc_writable(size_t capacity) {
  byte *result = mmap(NULL, capacity, PROT_READ | PROT_WRITE,
                      MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
  assert(result != MAP_FAILED);
  return result;
}

void Buffer_init(Buffer *result, size_t capacity) {
  result->address = Buffer_alloc_writable(capacity);
  assert(result->address != MAP_FAILED);
  result->state = kWritable;
  result->len = 0;
  result->capacity = capacity;
}

void Buffer_deinit(Buffer *buf) {
  munmap(buf->address, buf->capacity);
  buf->address = NULL;
  buf->len = 0;
  buf->capacity = 0;
}

int Buffer_make_executable(Buffer *buf) {
  int result = mprotect(buf->address, buf->len, PROT_EXEC);
  buf->state = kExecutable;
  return result;
}

word Buffer_len(Buffer *buf) { return buf->len; }
byte Buffer_at8(Buffer *buf, size_t pos) { return buf->address[pos]; }

void Buffer_at_put8(Buffer *buf, size_t pos, byte b) { buf->address[pos] = b; }

void Buffer_at_put32(Buffer *buf, size_t offset, uint32_t value) {
  for (uword i = 0; i < sizeof(value); i++) {
    Buffer_at_put8(buf, offset + i, (value >> (i * kBitsPerByte)) & 0xff);
  }
}

word max(word left, word right) { return left > right ? left : right; }

void Buffer_ensure_capacity(Buffer *buf, word additional_capacity) {
  if (buf->len + additional_capacity <= buf->capacity) {
    return;
  }
  word new_capacity =
      max(buf->capacity * 2, buf->capacity + additional_capacity);
  byte *address = Buffer_alloc_writable(new_capacity);
  memcpy(address, buf->address, buf->len);
  int result = munmap(buf->address, buf->capacity);
  assert(result == 0 && "munmap failed");
  buf->address = address;
  buf->capacity = new_capacity;
}

void Buffer_write8(Buffer *buf, byte b) {
  Buffer_ensure_capacity(buf, sizeof b);
  Buffer_at_put8(buf, buf->len++, b);
}

void Buffer_write32(Buffer *buf, int32_t value) {
  for (size_t i = 0; i < sizeof value; i++) {
    Buffer_write8(buf, (value >> (i * kBitsPerByte)) & 0xff);
  }
}

void Buffer_write_arr(Buffer *buf, const byte *arr, size_t len) {
  for (size_t i = 0; i < len; i++) {
    Buffer_write8(buf, arr[i]);
  }
}

// Emit

// The order here is determined by the x86 ISA encoding
typedef enum {
  kRax = 0,
  kRcx,
  kRdx,
  kRbx,
  kRsp,
  kRbp,
  kRsi,
  kRdi,
} Register;

// The order here is determined by the x86 ISA encoding
typedef enum {
  kAl = 0,
  kCl,
  kDl,
  kBl,
  kAh,
  kCh,
  kDh,
  kBh,
} PartialRegister;

// Condition codes
typedef enum {
  kOverflow = 0,
  kNotOverflow,
  kBelow,
  kCarry = kBelow,
  kNotAboveOrEqual = kBelow,
  kAboveOrEqual,
  kNotBelow = kAboveOrEqual,
  kNotCarry = kAboveOrEqual,
  kEqual,
  kZero = kEqual,
  kLess = 0xc,
  kNotGreaterOrEqual = kLess,
} Condition;

typedef struct Indirect {
  Register reg;
  int8_t disp;
} Indirect;

Indirect Ind(Register reg, int8_t disp) {
  return (Indirect){.reg = reg, .disp = disp};
}

static const byte kRexPrefix = 0x48;

typedef enum { Scale1 = 0, Scale2, Scale4, Scale8 } Scale;

typedef enum {
  kIndexRax = 0,
  kIndexRcx,
  kIndexRdx,
  kIndexRbx,
  kIndexNone,
  kIndexRbp,
  kIndexRsi,
  kIndexRdi
} Index;

byte sib(Register base, Index index, Scale scale) {
  return ((scale & 0x3) << 6) | ((index & 0x7) << 3) | (base & 0x7);
}

byte modrm(byte mod, byte rm, byte reg) {
  return ((mod & 0x3) << 6) | ((reg & 0x7) << 3) | (rm & 0x7);
}

void Emit_mov_reg_imm32(Buffer *buf, Register dst, int32_t src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0xc7);
  Buffer_write8(buf, modrm(3, dst, 0));
  Buffer_write32(buf, src);
}

void Emit_ret(Buffer *buf) { Buffer_write8(buf, 0xc3); }

void Emit_add_reg_imm32(Buffer *buf, Register dst, int32_t src) {
  Buffer_write8(buf, kRexPrefix);
  if (dst == kRax) {
    // Optimization: add eax, {imm32} can either be encoded as 05 {imm32} or 81
    // c0 {imm32}.
    Buffer_write8(buf, 0x05);
  } else {
    Buffer_write8(buf, 0x81);
    Buffer_write8(buf, modrm(3, dst, 0));
  }
  Buffer_write32(buf, src);
}

void Emit_sub_reg_imm32(Buffer *buf, Register dst, int32_t src) {
  Buffer_write8(buf, kRexPrefix);
  if (dst == kRax) {
    // Optimization: sub eax, {imm32} can either be encoded as 2d {imm32} or 81
    // e8 {imm32}.
    Buffer_write8(buf, 0x2d);
  } else {
    Buffer_write8(buf, 0x81);
    Buffer_write8(buf, modrm(3, dst, 5));
  }
  Buffer_write32(buf, src);
}

void Emit_shl_reg_imm8(Buffer *buf, Register dst, int8_t bits) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0xc1);
  Buffer_write8(buf, modrm(3, dst, 4));
  Buffer_write8(buf, bits);
}

void Emit_shr_reg_imm8(Buffer *buf, Register dst, int8_t bits) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0xc1);
  Buffer_write8(buf, modrm(3, dst, 5));
  Buffer_write8(buf, bits);
}

void Emit_or_reg_imm8(Buffer *buf, Register dst, uint8_t tag) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x83);
  Buffer_write8(buf, modrm(3, dst, 1));
  Buffer_write8(buf, tag);
}

void Emit_and_reg_imm8(Buffer *buf, Register dst, uint8_t tag) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x83);
  Buffer_write8(buf, modrm(3, dst, 4));
  Buffer_write8(buf, tag);
}

void Emit_cmp_reg_imm32(Buffer *buf, Register left, int32_t right) {
  Buffer_write8(buf, kRexPrefix);
  if (left == kRax) {
    // Optimization: cmp rax, {imm32} can be encoded as 0x3d {imm32}
    Buffer_write8(buf, 0x3d);
  } else {
    Buffer_write8(buf, 0x81);
    Buffer_write8(buf, modrm(3, left, 7));
  }
  Buffer_write32(buf, right);
}

void Emit_setcc_imm8(Buffer *buf, Condition cond, PartialRegister dst) {
  Buffer_write8(buf, 0x0f);
  Buffer_write8(buf, 0x90 + cond);
  Buffer_write8(buf, 0xc0 + (dst & 0x7));
}

uint8_t disp8(int8_t disp) { return disp >= 0 ? disp : 0x100 + disp; }

static uint32_t disp32(int32_t disp) {
  return disp >= 0 ? disp : 0x100000000 + disp;
}

void Emit_address_disp8(Buffer *buf, Register direct, Indirect indirect) {
  if (indirect.reg == kRsp) {
    Buffer_write8(buf, modrm(1, kIndexNone, direct));
    Buffer_write8(buf, sib(kRsp, kIndexNone, Scale1));
  } else {
    Buffer_write8(buf, modrm(1, indirect.reg, direct));
  }
  Buffer_write8(buf, disp8(indirect.disp));
}

// mov [dst+disp], src
void Emit_store_reg_indirect(Buffer *buf, Indirect dst, Register src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x89);
  Emit_address_disp8(buf, src, dst);
}

// add dst, [src+disp]
void Emit_add_reg_indirect(Buffer *buf, Register dst, Indirect src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x03);
  Emit_address_disp8(buf, dst, src);
}

// sub dst, [src+disp]
void Emit_sub_reg_indirect(Buffer *buf, Register dst, Indirect src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x2b);
  Emit_address_disp8(buf, dst, src);
}

// mul rax, [src+disp]
void Emit_mul_reg_indirect(Buffer *buf, Indirect src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0xf7);
  Emit_address_disp8(buf, 4, src);
}

// cmp left, [right+disp]
void Emit_cmp_reg_indirect(Buffer *buf, Register left, Indirect right) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x3b);
  Emit_address_disp8(buf, left, right);
}

// mov dst, [src+disp]
void Emit_load_reg_indirect(Buffer *buf, Register dst, Indirect src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x8b);
  Emit_address_disp8(buf, dst, src);
}

word Emit_jcc(Buffer *buf, Condition cond, int32_t offset) {
  Buffer_write8(buf, 0x0f);
  Buffer_write8(buf, 0x80 + cond);
  word pos = Buffer_len(buf);
  Buffer_write32(buf, disp32(offset));
  return pos;
}

word Emit_jmp(Buffer *buf, int32_t offset) {
  Buffer_write8(buf, 0xe9);
  word pos = Buffer_len(buf);
  Buffer_write32(buf, disp32(offset));
  return pos;
}

void Emit_backpatch_imm32(Buffer *buf, int32_t target_pos) {
  word current_pos = Buffer_len(buf);
  word relative_pos = current_pos - target_pos - sizeof(int32_t);
  Buffer_at_put32(buf, target_pos, disp32(relative_pos));
}

void Emit_mov_reg_reg(Buffer *buf, Register dst, Register src) {
  Buffer_write8(buf, kRexPrefix);
  Buffer_write8(buf, 0x89);
  Buffer_write8(buf, modrm(3, dst, src));
}

void Emit_rsp_adjust(Buffer *buf, word adjust) {
  if (adjust < 0) {
    Emit_sub_reg_imm32(buf, kRsp, -adjust);
  } else if (adjust > 0) {
    Emit_add_reg_imm32(buf, kRsp, adjust);
  }
}

void Emit_call_imm32(Buffer *buf, word absolute_address) {
  word relative_address = absolute_address - (Buffer_len(buf) + 5);
  Buffer_write8(buf, 0xe8);
  Buffer_write32(buf, relative_address);
}

// Compile

int Compile_call(Buffer *buf, ASTNode *callable, ASTNode *args,
                 word stack_index, Env *varenv, Env *labels);
int Compile_let(Buffer *buf, ASTNode *bindings, ASTNode *body, word stack_index,
                Env *binding_env, Env *body_env, Env *labels);
void Compile_compare_imm32(Buffer *buf, int32_t value);

ASTNode *operand1(ASTNode *args) { return AST_pair_car(args); }

ASTNode *operand2(ASTNode *args) { return AST_pair_car(AST_pair_cdr(args)); }

ASTNode *operand3(ASTNode *args) {
  return AST_pair_car(AST_pair_cdr(AST_pair_cdr(args)));
}

#define _(exp)                                                                 \
  do {                                                                         \
    int result = exp;                                                          \
    if (result != 0)                                                           \
      return result;                                                           \
  } while (0)

int Compile_expr(Buffer *buf, ASTNode *node, word stack_index, Env *varenv,
                 Env *labels) {
  if (AST_is_integer(node)) {
    word value = AST_get_integer(node);
    Emit_mov_reg_imm32(buf, kRax, Object_encode_integer(value));
    return 0;
  }
  if (AST_is_char(node)) {
    char value = AST_get_char(node);
    Emit_mov_reg_imm32(buf, kRax, Object_encode_char(value));
    return 0;
  }
  if (AST_is_bool(node)) {
    bool value = AST_get_bool(node);
    Emit_mov_reg_imm32(buf, kRax, Object_encode_bool(value));
    return 0;
  }
  if (AST_is_nil(node)) {
    Emit_mov_reg_imm32(buf, kRax, Object_nil());
    return 0;
  }
  if (AST_is_pair(node)) {
    return Compile_call(buf, AST_pair_car(node), AST_pair_cdr(node),
                        stack_index, varenv, labels);
  }
  if (AST_is_symbol(node)) {
    const char *symbol = AST_symbol_cstr(node);
    word value;
    if (Env_find(varenv, symbol, &value)) {
      Emit_load_reg_indirect(buf, kRax, Ind(kRsp, value));
      return 0;
    }
    return -1;
  }
  assert(0 && "unexpected node type");
}

const int32_t kLabelPlaceholder = 0xdeadbeef;

int Compile_if(Buffer *buf, ASTNode *cond, ASTNode *consequent,
               ASTNode *alternate, word stack_index, Env *varenv, Env *labels) {
  _(Compile_expr(buf, cond, stack_index, varenv, labels));
  Emit_cmp_reg_imm32(buf, kRax, Object_false());
  word alternate_pos = Emit_jcc(buf, kEqual, kLabelPlaceholder);
  _(Compile_expr(buf, consequent, stack_index, varenv, labels));
  word end_pos = Emit_jmp(buf, kLabelPlaceholder);
  Emit_backpatch_imm32(buf, alternate_pos);
  _(Compile_expr(buf, alternate, stack_index, varenv, labels));
  Emit_backpatch_imm32(buf, end_pos);
  return 0;
}

const Register kHeapPointer = kRsi;

int Compile_cons(Buffer *buf, ASTNode *car, ASTNode *cdr, int stack_index,
                 Env *varenv, Env *labels) {
  // Compile and store car on the stack
  _(Compile_expr(buf, car, stack_index, varenv, labels));
  Emit_store_reg_indirect(buf, Ind(kRbp, stack_index), kRax);
  // Compile and store cdr
  _(Compile_expr(buf, cdr, stack_index - kWordSize, varenv, labels));
  Emit_store_reg_indirect(buf, Ind(kHeapPointer, kCdrOffset), kRax);
  // Fetch car and store in heap
  Emit_load_reg_indirect(buf, kRax, Ind(kRbp, stack_index));
  Emit_store_reg_indirect(buf, Ind(kHeapPointer, kCarOffset), kRax);

  // Store tagged pointer in tax
  Emit_mov_reg_reg(buf, kRax, kHeapPointer);
  Emit_or_reg_imm8(buf, kRax, kPairTag);
  // Bump the heap pointer
  Emit_add_reg_imm32(buf, kHeapPointer, kPairSize);
  return 0;
}

word list_length(ASTNode *node) {
  if (AST_is_nil(node)) {
    return 0;
  }
  assert(AST_is_pair(node));
  return 1 + list_length(AST_pair_cdr(node));
}

int Compile_labelcall(Buffer *buf, ASTNode *callable, ASTNode *args,
                      word stack_index, Env *varenv, Env *labels, word nargs,
                      word rsp_adjust) {
  if (AST_is_nil(args)) {
    const char *symbol = AST_symbol_cstr(callable);
    word code_address;
    if (!Env_find(labels, symbol, &code_address)) {
      return -1;
    }
    Emit_rsp_adjust(buf, rsp_adjust);
    Emit_call_imm32(buf, code_address);
    Emit_rsp_adjust(buf, -rsp_adjust);
    return 0;
  }

  assert(AST_is_pair(args));
  ASTNode *arg = AST_pair_car(args);
  _(Compile_expr(buf, arg, stack_index, varenv, labels));
  Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
  return Compile_labelcall(buf, callable, AST_pair_cdr(args),
                           stack_index - kWordSize, varenv, labels, nargs,
                           rsp_adjust);
}

int Compile_call(Buffer *buf, ASTNode *callable, ASTNode *args,
                 word stack_index, Env *varenv, Env *labels) {
  if (AST_is_symbol(callable)) {
    if (AST_symbol_matches(callable, "labelcall")) {
      ASTNode *label = operand1(args);
      assert(AST_is_symbol(label));
      ASTNode *call_args = AST_pair_cdr(args);
      word nargs = list_length(call_args);

      return Compile_labelcall(buf, label, call_args, stack_index - kWordSize,
                               varenv, labels, nargs, stack_index + kWordSize);
    }
    if (AST_symbol_matches(callable, "let")) {
      return Compile_let(buf, operand1(args), operand2(args), stack_index,
                         varenv, varenv, labels);
    }
    if (AST_symbol_matches(callable, "if")) {
      return Compile_if(buf, operand1(args), operand2(args), operand3(args),
                        stack_index, varenv, labels);
    }
    if (AST_symbol_matches(callable, "cons")) {
      return Compile_cons(buf, operand1(args), operand2(args), stack_index,
                          varenv, labels);
    }
    if (AST_symbol_matches(callable, "car")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_load_reg_indirect(buf, kRax, Ind(kRax, kCarOffset - kPairTag));
      return 0;
    }
    if (AST_symbol_matches(callable, "cdr")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_load_reg_indirect(buf, kRax, Ind(kRax, kCdrOffset - kPairTag));
      return 0;
    }
    if (AST_symbol_matches(callable, "add1")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_add_reg_imm32(buf, kRax, Object_encode_integer(1));
      return 0;
    }
    if (AST_symbol_matches(callable, "sub1")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_sub_reg_imm32(buf, kRax, Object_encode_integer(1));
      return 0;
    }
    if (AST_symbol_matches(callable, "integer->char")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_shl_reg_imm8(buf, kRax, kCharShift - kIntegerShift);
      Emit_or_reg_imm8(buf, kRax, kCharTag);
      return 0;
    }
    if (AST_symbol_matches(callable, "char->integer")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_shr_reg_imm8(buf, kRax, kCharShift - kIntegerShift);
      return 0;
    }
    if (AST_symbol_matches(callable, "nil?")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_cmp_reg_imm32(buf, kRax, Object_nil());
      Emit_mov_reg_imm32(buf, kRax, 0);
      Emit_setcc_imm8(buf, kEqual, kAl);
      Emit_shl_reg_imm8(buf, kRax, kBoolShift);
      Emit_or_reg_imm8(buf, kRax, kBoolTag);
      return 0;
    }
    if (AST_symbol_matches(callable, "zero?")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Compile_compare_imm32(buf, Object_encode_integer(0));
      return 0;
    }
    if (AST_symbol_matches(callable, "not")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Compile_compare_imm32(buf, Object_false());
      return 0;
    }
    if (AST_symbol_matches(callable, "integer?")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_and_reg_imm8(buf, kRax, kIntegerTagMask);
      Compile_compare_imm32(buf, kIntegerTag);
      return 0;
    }
    if (AST_symbol_matches(callable, "boolean?")) {
      _(Compile_expr(buf, operand1(args), stack_index, varenv, labels));
      Emit_and_reg_imm8(buf, kRax, kImmediateTagMask);
      Compile_compare_imm32(buf, kBoolTag);
      return 0;
    }
    if (AST_symbol_matches(callable, "+")) {
      _(Compile_expr(buf, operand2(args), stack_index, varenv, labels));
      Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
      _(Compile_expr(buf, operand1(args), stack_index - kWordSize, varenv,
                     labels));
      Emit_add_reg_indirect(buf, kRax, Ind(kRsp, stack_index));
      return 0;
    }
    if (AST_symbol_matches(callable, "-")) {
      _(Compile_expr(buf, operand2(args), stack_index, varenv, labels));
      Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
      _(Compile_expr(buf, operand1(args), stack_index - kWordSize, varenv,
                     labels));
      Emit_sub_reg_indirect(buf, kRax, Ind(kRsp, stack_index));
      return 0;
    }
    if (AST_symbol_matches(callable, "*")) {
      _(Compile_expr(buf, operand2(args), stack_index, varenv, labels));
      // Remove the tag so that the result is still only tagged with 0b00
      // instead of 0b0000
      Emit_shr_reg_imm8(buf, kRax, kIntegerShift);
      Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
      _(Compile_expr(buf, operand1(args), stack_index - kWordSize, varenv,
                     labels));
      Emit_mul_reg_indirect(buf, Ind(kRsp, stack_index));
      return 0;
    }
    if (AST_symbol_matches(callable, "=")) {
      _(Compile_expr(buf, operand2(args), stack_index, varenv, labels));
      Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
      _(Compile_expr(buf, operand1(args), stack_index - kWordSize, varenv,
                     labels));
      Emit_cmp_reg_indirect(buf, kRax, Ind(kRsp, stack_index));
      Emit_mov_reg_imm32(buf, kRax, 0);
      Emit_setcc_imm8(buf, kEqual, kAl);
      Emit_shl_reg_imm8(buf, kRax, kBoolShift);
      Emit_or_reg_imm8(buf, kRax, kBoolTag);
      return 0;
    }
    if (AST_symbol_matches(callable, "<")) {
      _(Compile_expr(buf, operand2(args), stack_index, varenv, labels));
      Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
      _(Compile_expr(buf, operand1(args), stack_index - kWordSize, varenv,
                     labels));
      Emit_cmp_reg_indirect(buf, kRax, Ind(kRsp, stack_index));
      Emit_mov_reg_imm32(buf, kRax, 0);
      Emit_setcc_imm8(buf, kLess, kAl);
      Emit_shl_reg_imm8(buf, kRax, kBoolShift);
      Emit_or_reg_imm8(buf, kRax, kBoolTag);
      return 0;
    }
  }
  assert(0 && "unexpected call type");
}

int Compile_let(Buffer *buf, ASTNode *bindings, ASTNode *body, word stack_index,
                Env *binding_env, Env *body_env, Env *labels) {
  if (AST_is_nil(bindings)) {
    // Base case: no bindings (or none left)
    _(Compile_expr(buf, body, stack_index, body_env, labels));
    return 0;
  }
  assert(AST_is_pair(bindings));
  // Unpack the binding
  ASTNode *binding = AST_pair_car(bindings);
  ASTNode *name = AST_pair_car(binding);
  assert(AST_is_symbol(name));
  ASTNode *binding_expr = AST_pair_car(AST_pair_cdr(binding));
  // Evaluate the RHS, store result on stack
  _(Compile_expr(buf, binding_expr, stack_index, binding_env, labels));
  Emit_store_reg_indirect(buf, Ind(kRsp, stack_index), kRax);
  // Bind the name to a stack offset
  Env entry = Env_bind(AST_symbol_cstr(name), stack_index, body_env);
  _(Compile_let(buf, AST_pair_cdr(bindings), body, stack_index - kWordSize,
                binding_env, &entry, labels));
  return 0;
}

static const byte kEntryPrologue[] = {
    // Save the heap in rsi, our global heap pointer
    // mov rsi, rdi
    kRexPrefix,
    0x89,
    0xfe,
};

static const byte kFunctionEpilogue[] = {
    // ret
    0xc3,
};

int Compile_code_impl(Buffer *buf, ASTNode *formals, ASTNode *body,
                      word stack_index, Env *varenv) {
  if (AST_is_nil(formals)) {
    _(Compile_expr(buf, body, stack_index, varenv, NULL));
    Buffer_write_arr(buf, kFunctionEpilogue, sizeof kFunctionEpilogue);
    return 0;
  }

  assert(AST_is_pair(formals));
  ASTNode *name = AST_pair_car(formals);
  assert(AST_is_symbol(name));
  Env entry = Env_bind(AST_symbol_cstr(name), stack_index, varenv);
  return Compile_code_impl(buf, AST_pair_cdr(formals), body,
                           stack_index - kWordSize, &entry);
}

int Compile_code(Buffer *buf, ASTNode *code) {
  assert(AST_is_pair(code));
  ASTNode *code_sym = AST_pair_car(code);
  assert(AST_is_symbol(code_sym));
  assert(AST_symbol_matches(code_sym, "code"));
  ASTNode *formals = AST_pair_car(AST_pair_cdr(code));
  ASTNode *code_body = AST_pair_car(AST_pair_cdr(AST_pair_cdr(code)));
  return Compile_code_impl(buf, formals, code_body, -kWordSize, NULL);
}

int Compile_labels(Buffer *buf, ASTNode *bindings, ASTNode *body, Env *labels,
                   word body_pos) {
  if (AST_is_nil(bindings)) {
    Emit_backpatch_imm32(buf, body_pos);
    // Base case: no bindings; compile the body
    _(Compile_expr(buf, body, -kWordSize, NULL, labels));
    Buffer_write_arr(buf, kFunctionEpilogue, sizeof kFunctionEpilogue);
    return 0;
  }

  assert(AST_is_pair(bindings));
  // Get the next binding
  ASTNode *binding = AST_pair_car(bindings);
  ASTNode *name = AST_pair_car(binding);
  assert(AST_is_symbol(name));
  ASTNode *binding_code = AST_pair_car(AST_pair_cdr(binding));
  word function_location = Buffer_len(buf);
  // Compile the binding function
  _(Compile_code(buf, binding_code));
  // Bind the name to the location in the instruction strema
  Env entry = Env_bind(AST_symbol_cstr(name), function_location, labels);
  _(Compile_labels(buf, AST_pair_cdr(bindings), body, &entry, body_pos));
  return 0;
}

WARN_UNUSED int Compile_entry(Buffer *buf, ASTNode *node) {
  Buffer_write_arr(buf, kEntryPrologue, sizeof kEntryPrologue);
  if (AST_is_pair(node)) {
    // Assume it's (labels ...)
    ASTNode *labels_sym = AST_pair_car(node);
    if (AST_is_symbol(labels_sym) && AST_symbol_matches(labels_sym, "labels")) {
      // Jump to body
      word body_pos = Emit_jmp(buf, kLabelPlaceholder);
      ASTNode *bindings = AST_pair_car(AST_pair_cdr(node));
      assert(AST_is_pair(bindings) || AST_is_nil(bindings));
      ASTNode *body = AST_pair_car(AST_pair_cdr(AST_pair_cdr(node)));
      _(Compile_labels(buf, bindings, body, /*labels=*/NULL, body_pos));
      return 0;
    }
  }
  _(Compile_expr(buf, node, /*stack_index=*/-kWordSize, /*varenv=*/NULL,
                 /*labels=*/NULL));
  Buffer_write_arr(buf, kFunctionEpilogue, sizeof kFunctionEpilogue);
  return 0;
}

void Compile_compare_imm32(Buffer *buf, int32_t value) {
  Emit_cmp_reg_imm32(buf, kRax, value);
  Emit_mov_reg_imm32(buf, kRax, 0);
  Emit_setcc_imm8(buf, kEqual, kAl);
  Emit_shl_reg_imm8(buf, kRax, kBoolShift);
  Emit_or_reg_imm8(buf, kRax, kBoolTag);
}

typedef int (*JitFunction)(uword *heap);

// Reader

ASTNode *read_rec(char *input, word *pos);

void advance(word *pos) { ++*pos; }

char next(char *input, word *pos) {
  advance(pos);
  return input[*pos];
}

char skip_whitespace(char *input, word *pos) {
  char c = '\0';
  for (c = input[*pos]; isspace(c); c = next(input, pos)) {
    ;
  }
  return c;
}

bool starts_symbol(char c) {
  switch (c) {
  case '+':
  case '-':
  case '*':
  case '<':
  case '>':
  case '=':
  case '?':
    return true;
  default:
    return isalpha(c);
  }
}

ASTNode *read_integer(char *input, word *pos, int sign) {
  char c = '\0';
  word result = 0;
  for (char c = input[*pos]; isdigit(c); c = next(input, pos)) {
    result *= 10;
    result += c - '0';
  }
  return AST_new_integer(result * sign);
}

const word ATOM_MAX = 32;
bool is_symbol_char(char c) { return starts_symbol(c) || isdigit(c); }

ASTNode *read_symbol(char *input, word *pos) {
  char buf[ATOM_MAX + 1];
  word length = 0;
  for (length = 0; length < ATOM_MAX && is_symbol_char(input[*pos]); length++) {
    buf[length] = input[*pos];
    advance(pos);
  }
  buf[length] = '\0';
  return AST_new_symbol(buf);
}
ASTNode *read_char(char *input, word *pos) {
  char c = input[*pos];
  if (c == '\'') {
    return AST_error();
  }
  advance(pos);
  if (input[*pos] != '\'') {
    return AST_error();
  }
  advance(pos);
  return AST_new_char(c);
}

ASTNode *read_list(char *input, word *pos) {
  char c = skip_whitespace(input, pos);
  if (c == ')') {
    advance(pos);
    return AST_nil();
  }
  ASTNode *car = read_rec(input, pos);
  assert(car != AST_error());
  ASTNode *cdr = read_list(input, pos);
  assert(cdr != AST_error());
  return AST_new_pair(car, cdr);
}

ASTNode *read_rec(char *input, word *pos) {
  char c = skip_whitespace(input, pos);
  if (isdigit(c)) {
    return read_integer(input, pos, 1);
  }
  if (c == '+' && isdigit(input[*pos + 1])) {
    advance(pos);
    return read_integer(input, pos, 1);
  }
  if (c == '-' && isdigit(input[*pos + 1])) {
    advance(pos);
    return read_integer(input, pos, -1);
  }
  if (starts_symbol(c)) {
    return read_symbol(input, pos);
  }
  if (c == '\'') {
    advance(pos);
    return read_char(input, pos);
  }
  if (c == '#' && input[*pos + 1] == 't') {
    advance(pos);
    advance(pos);
    return AST_new_bool(true);
  }
  if (c == '#' && input[*pos + 1] == 'f') {
    advance(pos);
    advance(pos);
    return AST_new_bool(false);
  }
  if (c == '(') {
    advance(pos);
    return read_list(input, pos);
  }
  return AST_error();
}

ASTNode *Reader_read(char *input) {
  word pos = 0;
  return read_rec(input, &pos);
}

// Testing
uword Testing_execute_entry(Buffer *buf, uword *heap) {
  assert(buf != NULL);
  assert(buf->address != NULL);
  assert(buf->state == kExecutable);
  // The pointer-pointer cast is allowed but the underlying
  // data-to-function-pointer back-and-forth is only guaranteed to work on
  // POSIX systems (because of eg dlsym).
  JitFunction function = *(JitFunction *)(&buf->address);
  return function(heap);
}

uword Testing_execute_expr(Buffer *buf) {
  return Testing_execute_entry(buf, NULL);
}

TEST Testing_expect_entry_has_contents(Buffer *buf, byte *arr,
                                       size_t arr_size) {
  size_t total_size =
      sizeof kEntryPrologue + arr_size + sizeof kFunctionEpilogue;
  ASSERT_EQ_FMT(total_size, Buffer_len(buf), "%ld");

  byte *ptr = buf->address;
  ASSERT_MEM_EQ(kEntryPrologue, ptr, sizeof kEntryPrologue);
  ptr += sizeof kEntryPrologue;
  ASSERT_MEM_EQ(arr, ptr, arr_size);
  ptr += arr_size;
  ASSERT_MEM_EQ(kFunctionEpilogue, ptr, sizeof kFunctionEpilogue);
  ptr += sizeof kFunctionEpilogue;
  PASS();
}

#define EXPECT_EQUALS_BYTES(buf, arr)                                          \
  ASSERT_MEM_EQ(arr, (buf)->address, sizeof arr)

#define EXPECT_ENTRY_CONTAINS_CODE(buf, arr)                                   \
  CHECK_CALL(Testing_expect_entry_has_contents(buf, arr, sizeof arr))

#define RUN_BUFFER_TEST(test_name)                                             \
  do {                                                                         \
    Buffer buf;                                                                \
    Buffer_init(&buf, 1);                                                      \
    GREATEST_RUN_TEST1(test_name, &buf);                                       \
    Buffer_deinit(&buf);                                                       \
  } while (0)

#define RUN_HEAP_TEST(test_name)                                               \
  do {                                                                         \
    Buffer buf;                                                                \
    Buffer_init(&buf, 1);                                                      \
    uword *heap = malloc(1000 * kWordSize);                                    \
    GREATEST_RUN_TESTp(test_name, &buf, heap);                                 \
    free(heap);                                                                \
    Buffer_deinit(&buf);                                                       \
  } while (0)

ASTNode *list1(ASTNode *item0) { return AST_new_pair(item0, AST_nil()); }

ASTNode *list2(ASTNode *item0, ASTNode *item1) {
  return AST_new_pair(item0, list1(item1));
}

ASTNode *list3(ASTNode *item0, ASTNode *item1, ASTNode *item2) {
  return AST_new_pair(item0, list2(item1, item2));
}

ASTNode *new_unary_call(const char *name, ASTNode *arg) {
  return list2(AST_new_symbol(name), arg);
}

ASTNode *new_binary_call(const char *name, ASTNode *arg0, ASTNode *arg1) {
  return list3(AST_new_symbol(name), arg0, arg1);
}

// End testing

// Tests
TEST encode_positive_integer(void) {
  ASSERT_EQ(Object_encode_integer(0), 0x0);
  ASSERT_EQ(Object_encode_integer(1), 0x4);
  ASSERT_EQ(Object_encode_integer(10), 0x28);
  PASS();
}

TEST encode_negative_integer(void) {
  ASSERT_EQ(Object_encode_integer(0), 0x0);
  ASSERT_EQ(Object_encode_integer(-1), 0xfffffffffffffffc);
  ASSERT_EQ(Object_encode_integer(-10), 0xffffffffffffffd8);
  PASS();
}

TEST encode_char(void) {
  ASSERT_EQ(Object_encode_char('\0'), 0xf);
  ASSERT_EQ(Object_encode_char('a'), 0x610f);
  PASS();
}

TEST decode_char(void) {
  ASSERT_EQ(Object_decode_char(0xf), '\0');
  ASSERT_EQ(Object_decode_char(0x610f), 'a');
  PASS();
}

TEST encode_bool(void) {
  ASSERT_EQ(Object_encode_bool(true), 0x9f);
  ASSERT_EQ(Object_encode_bool(false), 0x1f);
  ASSERT_EQ(Object_true(), 0x9f);
  ASSERT_EQ(Object_false(), 0x1f);
  PASS();
}

TEST decode_bool(void) {
  ASSERT_EQ(Object_decode_bool(0x9f), true);
  ASSERT_EQ(Object_decode_bool(0x1f), false);
  PASS();
}

TEST address(void) {
  ASSERT_EQ(Object_address((void *)0xFF01), 0xFF00);
  PASS();
}

TEST ast_new_pair(void) {
  ASTNode *node = AST_new_pair(NULL, NULL);
  ASSERT(AST_is_pair(node));
  AST_heap_free(node);
  PASS();
}

TEST ast_pair_car_returns_car(void) {
  ASTNode *node = AST_new_pair(AST_new_integer(123), NULL);
  ASTNode *car = AST_pair_car(node);
  ASSERT(AST_is_integer(car));
  ASSERT_EQ(Object_decode_integer((uword)car), 123);
  AST_heap_free(node);
  PASS();
}

TEST ast_pair_cdr_returns_cdr(void) {
  ASTNode *node = AST_new_pair(NULL, AST_new_integer(123));
  ASTNode *cdr = AST_pair_cdr(node);
  ASSERT(AST_is_integer(cdr));
  ASSERT_EQ(Object_decode_integer((uword)cdr), 123);
  AST_heap_free(node);
  PASS();
}

TEST ast_new_symbol(void) {
  const char *value = "my symbol";
  ASTNode *node = AST_new_symbol(value);
  ASSERT(AST_is_symbol(node));
  ASSERT_STR_EQ(AST_symbol_cstr(node), value);
  AST_heap_free(node);
  PASS();
}

#define ASSERT_IS_CHAR_EQ(node, c)                                             \
  do {                                                                         \
    ASTNode *__tmp = node;                                                     \
    if (AST_is_error(__tmp)) {                                                 \
      fprintf(stderr, "Expected a char but got an error.\n");                  \
    }                                                                          \
    ASSERT(AST_is_char(__tmp));                                                \
    ASSERT_EQ(AST_get_char(__tmp), c);                                         \
  } while (0);

#define ASSERT_IS_INT_EQ(node, val)                                            \
  do {                                                                         \
    ASTNode *__tmp = node;                                                     \
    if (AST_is_error(__tmp)) {                                                 \
      fprintf(stderr, "Expected an int but got an error.\n");                  \
    }                                                                          \
    ASSERT(AST_is_integer(__tmp));                                             \
    ASSERT_EQ(AST_get_integer(__tmp), val);                                    \
  } while (0);

#define ASSERT_IS_SYM_EQ(node, cstr)                                           \
  do {                                                                         \
    ASTNode *__tmp = node;                                                     \
    if (AST_is_error(__tmp)) {                                                 \
      fprintf(stderr, "Expected a symbol but got an error.\n");                \
    }                                                                          \
    ASSERT(AST_is_symbol(__tmp));                                              \
    ASSERT_STR_EQ(AST_symbol_cstr(__tmp), cstr);                               \
  } while (0);

TEST read_with_integer_returns_integer(void) {
  char *input = "1234";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_INT_EQ(node, 1234);
  AST_heap_free(node);
  PASS();
}

TEST read_with_negative_integer_returns_integer(void) {
  char *input = "-1234";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_INT_EQ(node, -1234);
  AST_heap_free(node);
  PASS();
}

TEST read_with_positive_integer_returns_integer(void) {
  char *input = "+1234";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_INT_EQ(node, 1234);
  AST_heap_free(node);
  PASS();
}

TEST read_with_leading_whitespace_ignores_whitespace(void) {
  char *input = "   \t   \n  1234";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_INT_EQ(node, 1234);
  AST_heap_free(node);
  PASS();
}

TEST read_with_symbol_returns_symbol(void) {
  char *input = "hello?+-*=>";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_SYM_EQ(node, "hello?+-*=>");
  AST_heap_free(node);
  PASS();
}

TEST read_with_symbol_with_trailing_digits(void) {
  char *input = "add1 1";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_SYM_EQ(node, "add1");
  AST_heap_free(node);
  PASS();
}

TEST read_with_char_returns_char(void) {
  char *input = "'a'";
  ASTNode *node = Reader_read(input);
  ASSERT_IS_CHAR_EQ(node, 'a');
  ASSERT(AST_is_error(Reader_read("''")));
  ASSERT(AST_is_error(Reader_read("'aa'")));
  ASSERT(AST_is_error(Reader_read("'aa")));
  AST_heap_free(node);
  PASS();
}

TEST read_with_bool_returns_bool(void) {
  ASSERT_EQ(Reader_read("#t"), AST_new_bool(true));
  ASSERT_EQ(Reader_read("#f"), AST_new_bool(false));
  ASSERT(AST_is_error(Reader_read("#")));
  ASSERT(AST_is_error(Reader_read("#x")));
  ASSERT(AST_is_error(Reader_read("##")));
  PASS();
}

TEST read_with_nil_returns_nil(void) {
  char *input = "()";
  ASTNode *node = Reader_read(input);
  ASSERT(AST_is_nil(node));
  AST_heap_free(node);
  PASS();
}

TEST read_with_list_returns_list(void) {
  char *input = "( 1 2 0 )";
  ASTNode *node = Reader_read(input);
  ASSERT(AST_is_pair(node));
  ASSERT_IS_INT_EQ(AST_pair_car(node), 1);
  ASSERT_IS_INT_EQ(AST_pair_car(AST_pair_cdr(node)), 2);
  ASSERT_IS_INT_EQ(AST_pair_car(AST_pair_cdr(AST_pair_cdr(node))), 0);
  ASSERT(AST_is_nil(AST_pair_cdr(AST_pair_cdr(AST_pair_cdr(node)))));
  AST_heap_free(node);
  PASS();
}

TEST read_with_nested_list_returns_list(void) {
  char *input = "((hello world) (foo bar))";
  ASTNode *node = Reader_read(input);
  ASSERT(AST_is_pair(node));
  ASTNode *first = AST_pair_car(node);
  ASSERT(AST_is_pair(first));
  ASSERT_IS_SYM_EQ(AST_pair_car(first), "hello");
  ASSERT_IS_SYM_EQ(AST_pair_car(AST_pair_cdr(first)), "world");
  ASSERT(AST_is_nil(AST_pair_cdr(AST_pair_cdr(first))));
  ASTNode *second = AST_pair_car(AST_pair_cdr(node));
  ASSERT(AST_is_pair(second));
  ASSERT_IS_SYM_EQ(AST_pair_car(second), "foo");
  ASSERT_IS_SYM_EQ(AST_pair_car(AST_pair_cdr(second)), "bar");
  ASSERT(AST_is_nil(AST_pair_cdr(AST_pair_cdr(second))));
  AST_heap_free(node);
  PASS();
}

TEST buffer_write8_increases_length(Buffer *buf) {
  ASSERT_EQ(buf->len, 0);
  Buffer_write8(buf, 0xdb);
  ASSERT_EQ(Buffer_at8(buf, 0), 0xdb);
  ASSERT_EQ(buf->len, 1);
  PASS();
}

TEST buffer_write8_expands_buffer(void) {
  Buffer buf;
  Buffer_init(&buf, 1);
  ASSERT_EQ(buf.capacity, 1);
  ASSERT_EQ(buf.len, 0);
  Buffer_write8(&buf, 0xdb);
  Buffer_write8(&buf, 0xef);
  ASSERT(buf.capacity > 1);
  ASSERT_EQ(buf.len, 2);
  Buffer_deinit(&buf);
  PASS();
}

TEST buffer_write32_expands_buffer(void) {
  Buffer buf;
  Buffer_init(&buf, 1);
  ASSERT_EQ(buf.capacity, 1);
  ASSERT_EQ(buf.len, 0);
  Buffer_write32(&buf, 0xdeadbeef);
  ASSERT(buf.capacity > 1);
  ASSERT_EQ(buf.len, 4);
  Buffer_deinit(&buf);
  PASS();
}

TEST buffer_write32_writes_little_endian(Buffer *buf) {
  Buffer_write32(buf, 0xdeadbeef);
  ASSERT_EQ(Buffer_at8(buf, 0), 0xef);
  ASSERT_EQ(Buffer_at8(buf, 1), 0xbe);
  ASSERT_EQ(Buffer_at8(buf, 2), 0xad);
  ASSERT_EQ(Buffer_at8(buf, 3), 0xde);
  PASS();
}

TEST compile_positive_integer(Buffer *buf) {
  word value = 123;
  ASTNode *node = AST_new_integer(value);
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov eax, imm(123)
  byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(value));
  PASS();
}

TEST compile_negative_integer(Buffer *buf) {
  word value = -123;
  ASTNode *node = AST_new_integer(value);
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov eax, imm(-123)
  byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0xfe, 0xff, 0xff};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(value));
  PASS();
}

TEST compile_char(Buffer *buf) {
  char value = 'a';
  ASTNode *node = AST_new_char(value);
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov eax, imm('a')
  byte expected[] = {0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_char(value));
  PASS();
}

TEST compile_true(Buffer *buf) {
  ASTNode *node = AST_new_bool(true);
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov eax, imm(true)
  byte expected[] = {0x48, 0xc7, 0xc0, 0x9f, 0x0, 0x0, 0x0};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_true());
  PASS();
}

TEST compile_false(Buffer *buf) {
  ASTNode *node = AST_new_bool(false);
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov eax, imm(false)
  byte expected[] = {0x48, 0xc7, 0xc0, 0x1f, 0x00, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_false());
  PASS();
}

TEST compile_nil(Buffer *buf) {
  ASTNode *node = AST_nil();
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov eax, imm(nil)
  byte expected[] = {0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_nil());
  PASS();
}

TEST compile_unary_add1(Buffer *buf) {
  ASTNode *node = new_unary_call("add1", AST_new_integer(123));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov rax, imm(123); add rax, imm(1)
  byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00,
                     0x48, 0x05, 0x04, 0x00, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(124));
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_add1_nested(Buffer *buf) {
  ASTNode *node =
      new_unary_call("add1", new_unary_call("add1", AST_new_integer(123)));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov rax, imm(123); add rax, imm(1); add rax, imm(1)
  byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0x48, 0x05, 0x04,
                     0x00, 0x00, 0x00, 0x48, 0x05, 0x04, 0x00, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(125));
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_sub1(Buffer *buf) {
  ASTNode *node = new_unary_call("sub1", AST_new_integer(123));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov rax, imm(123); sub rax, imm(1)
  byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00,
                     0x48, 0x2d, 0x04, 0x00, 0x00, 0x00};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(122));
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_integer_to_char(Buffer *buf) {
  ASTNode *node = new_unary_call("integer->char", AST_new_integer(97));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov rax, imm(97); shl rax, 6; or rax, 0xf
  byte expected[] = {0x48, 0xc7, 0xc0, 0x84, 0x01, 0x00, 0x00, 0x48,
                     0xc1, 0xe0, 0x06, 0x48, 0x83, 0xc8, 0x0f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_char('a'));
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_char_to_integer(Buffer *buf) {
  ASTNode *node = new_unary_call("char->integer", AST_new_char('a'));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // mov rax, imm('a'); shr rax, 6
  byte expected[] = {0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00,
                     0x00, 0x48, 0xc1, 0xe8, 0x06};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(97));
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_nilp_with_nil_returns_true(Buffer *buf) {
  ASTNode *node = new_unary_call("nil?", AST_nil());
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 2f 00 00 00    mov    rax,0x2f
  // 7:  48 3d 2f 00 00 00       cmp    rax,0x0000002f
  // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 14: 0f 94 c0                sete   al
  // 17: 48 c1 e0 07             shl    rax,0x7
  // 1b: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00, 0x48,
                     0x3d, 0x2f, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0,
                     0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
                     0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_true());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_nilp_with_non_nil_returns_false(Buffer *buf) {
  ASTNode *node = new_unary_call("nil?", AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
  // 7:  48 3d 2f 00 00 00       cmp    rax,0x0000002f
  // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 14: 0f 94 c0                sete   al
  // 17: 48 c1 e0 07             shl    rax,0x7
  // 1b: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48,
                     0x3d, 0x2f, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0,
                     0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
                     0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_false());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_zerop_with_zero_returns_true(Buffer *buf) {
  ASTNode *node = new_unary_call("zero?", AST_new_integer(0));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 7:  48 3d 00 00 00 00       cmp    rax,0x00000000
  // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 14: 0f 94 c0                sete   al
  // 17: 48 c1 e0 07             shl    rax,0x7
  // 1b: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x48,
                     0x3d, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0,
                     0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
                     0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_true());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_zerop_with_non_zero_returns_false(Buffer *buf) {
  ASTNode *node = new_unary_call("zero?", AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
  // 7:  48 3d 00 00 00 00       cmp    rax,0x00000000
  // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 14: 0f 94 c0                sete   al
  // 17: 48 c1 e0 07             shl    rax,0x7
  // 1b: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48,
                     0x3d, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0,
                     0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
                     0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_false());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_not_with_false_returns_true(Buffer *buf) {
  ASTNode *node = new_unary_call("not", AST_new_bool(false));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 1f 00 00 00    mov    rax,0x1f
  // 7:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
  // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 14: 0f 94 c0                sete   al
  // 17: 48 c1 e0 07             shl    rax,0x7
  // 1b: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x1f, 0x00, 0x00, 0x00, 0x48,
                     0x3d, 0x1f, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0,
                     0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
                     0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_true());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_not_with_non_false_returns_false(Buffer *buf) {
  ASTNode *node = new_unary_call("not", AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
  // 7:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
  // d:  48 c7 c0 00 00 00 00    mov    rax,0x0
  // 14: 0f 94 c0                sete   al
  // 17: 48 c1 e0 07             shl    rax,0x7
  // 1b: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48,
                     0x3d, 0x1f, 0x00, 0x00, 0x00, 0x48, 0xc7, 0xc0,
                     0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0, 0x48,
                     0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_false());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_integerp_with_integer_returns_true(Buffer *buf) {
  ASTNode *node = new_unary_call("integer?", AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
  // 7:  48 83 e0 03             and    rax,0x3
  // b:  48 3d 00 00 00 00       cmp    rax,0x00000000
  // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
  // 18: 0f 94 c0                sete   al
  // 1b: 48 c1 e0 07             shl    rax,0x7
  // 1f: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x83,
                     0xe0, 0x03, 0x48, 0x3d, 0x00, 0x00, 0x00, 0x00, 0x48,
                     0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0,
                     0x48, 0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_true());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_integerp_with_non_integer_returns_false(Buffer *buf) {
  ASTNode *node = new_unary_call("integer?", AST_nil());
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 2f 00 00 00    mov    rax,0x2f
  // 7:  48 83 e0 03             and    rax,0x3
  // b:  48 3d 00 00 00 00       cmp    rax,0x00000000
  // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
  // 18: 0f 94 c0                sete   al
  // 1b: 48 c1 e0 07             shl    rax,0x7
  // 1f: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00, 0x48, 0x83,
                     0xe0, 0x03, 0x48, 0x3d, 0x00, 0x00, 0x00, 0x00, 0x48,
                     0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0,
                     0x48, 0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_false());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_booleanp_with_boolean_returns_true(Buffer *buf) {
  ASTNode *node = new_unary_call("boolean?", AST_new_bool(true));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 9f 00 00 00    mov    rax,0x9f
  // 7:  48 83 e0 3f             and    rax,0x3f
  // b:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
  // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
  // 18: 0f 94 c0                sete   al
  // 1b: 48 c1 e0 07             shl    rax,0x7
  // 1f: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x9f, 0x00, 0x00, 0x00, 0x48, 0x83,
                     0xe0, 0x3f, 0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00, 0x48,
                     0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0,
                     0x48, 0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_true());
  AST_heap_free(node);
  PASS();
}

TEST compile_unary_booleanp_with_non_boolean_returns_false(Buffer *buf) {
  ASTNode *node = new_unary_call("boolean?", AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // 0:  48 c7 c0 14 00 00 00    mov    rax,0x14
  // 7:  48 83 e0 3f             and    rax,0x3f
  // b:  48 3d 1f 00 00 00       cmp    rax,0x0000001f
  // 11: 48 c7 c0 00 00 00 00    mov    rax,0x0
  // 18: 0f 94 c0                sete   al
  // 1b: 48 c1 e0 07             shl    rax,0x7
  // 1f: 48 83 c8 1f             or     rax,0x1f
  byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00, 0x48, 0x83,
                     0xe0, 0x3f, 0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00, 0x48,
                     0xc7, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x0f, 0x94, 0xc0,
                     0x48, 0xc1, 0xe0, 0x07, 0x48, 0x83, 0xc8, 0x1f};
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_false());
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_plus(Buffer *buf) {
  ASTNode *node = new_binary_call("+", AST_new_integer(5), AST_new_integer(8));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov    rax,0x20
      0x48, 0xc7, 0xc0, 0x20, 0x00, 0x00, 0x00,
      // mov    QWORD PTR [rsp-0x8],rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov    rax,0x14
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // add    rax,QWORD PTR [rbp-0x8]
      0x48, 0x03, 0x44, 0x24, 0xf8};
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(13));
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_plus_nested(Buffer *buf) {
  ASTNode *node = new_binary_call(
      "+", new_binary_call("+", AST_new_integer(1), AST_new_integer(2)),
      new_binary_call("+", AST_new_integer(3), AST_new_integer(4)));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov    rax,0x10
      0x48, 0xc7, 0xc0, 0x10, 0x00, 0x00, 0x00,
      // mov    QWORD PTR [rsp-0x8],rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov    rax,0xc
      0x48, 0xc7, 0xc0, 0x0c, 0x00, 0x00, 0x00,
      // add    rax,QWORD PTR [rsp-0x8]
      0x48, 0x03, 0x44, 0x24, 0xf8,
      // mov    QWORD PTR [rsp-0x8],rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov    rax,0x8
      0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
      // mov    QWORD PTR [rsp-0x10],rax
      0x48, 0x89, 0x44, 0x24, 0xf0,
      // mov    rax,0x4
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // add    rax,QWORD PTR [rsp-0x10]
      0x48, 0x03, 0x44, 0x24, 0xf0,
      // add    rax,QWORD PTR [rsp-0x8]
      0x48, 0x03, 0x44, 0x24, 0xf8};
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(10));
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_minus(Buffer *buf) {
  ASTNode *node = new_binary_call("-", AST_new_integer(5), AST_new_integer(8));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov    rax,0x20
      0x48, 0xc7, 0xc0, 0x20, 0x00, 0x00, 0x00,
      // mov    QWORD PTR [rsp-0x8],rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov    rax,0x14
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // add    rax,QWORD PTR [rsp-0x8]
      0x48, 0x2b, 0x44, 0x24, 0xf8};
  // clang-format on 
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(-3));
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_minus_nested(Buffer *buf) {
  ASTNode *node = new_binary_call(
      "-", new_binary_call("-", AST_new_integer(5), AST_new_integer(1)),
      new_binary_call("-", AST_new_integer(4), AST_new_integer(3)));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov    rax,0xc
      0x48, 0xc7, 0xc0, 0x0c, 0x00, 0x00, 0x00,
      // mov    QWORD PTR [rsp-0x8],rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov    rax,0x10
      0x48, 0xc7, 0xc0, 0x10, 0x00, 0x00, 0x00,
      // add    rax,QWORD PTR [rsp-0x8]
      0x48, 0x2b, 0x44, 0x24, 0xf8,
      //  mov    QWORD PTR [rsp-0x8],rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov    rax,0x4
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // mov    QWORD PTR [rsp-0x10],rax
      0x48, 0x89, 0x44, 0x24, 0xf0,
      // mov    rax,0x14
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // add    rax,QWORD PTR [rsp-0x10]
      0x48, 0x2b, 0x44, 0x24, 0xf0,
      // add    rax,QWORD PTR [rsp-0x8]
      0x48, 0x2b, 0x44, 0x24, 0xf8};
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ(result, Object_encode_integer(3));
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_mul(Buffer *buf) {
  ASTNode *node = new_binary_call("*", AST_new_integer(5), AST_new_integer(8));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(40), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_mul_nested(Buffer *buf) {
  ASTNode *node = new_binary_call(
      "*", new_binary_call("*", AST_new_integer(1), AST_new_integer(2)),
      new_binary_call("*", AST_new_integer(3), AST_new_integer(4)));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(24), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_eq_with_same_address_returns_true(Buffer *buf) {
  ASTNode *node = new_binary_call("=", AST_new_integer(5), AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_true(), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_eq_with_different_address_returns_false(Buffer *buf) {
  ASTNode *node = new_binary_call("=", AST_new_integer(5), AST_new_integer(4));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_false(), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_lt_with_left_less_than_right_returns_true(Buffer *buf) {
  ASTNode *node = new_binary_call("<", AST_new_integer(-5), AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_true(), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_lt_with_left_equal_to_right_returns_false(Buffer *buf) {
  ASTNode *node = new_binary_call("<", AST_new_integer(5), AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_false(), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_binary_lt_with_left_greater_than_right_returns_false(Buffer *buf) {
  ASTNode *node = new_binary_call("<", AST_new_integer(6), AST_new_integer(5));
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_false(), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_symbol_in_env_returns_value(Buffer *buf) {
  ASTNode *node = AST_new_symbol("hello");
  Env env0 = Env_bind("hello", 33, /*prev=*/NULL);
  Env env1 = Env_bind("world", 66, &env0);
  int compile_result = Compile_expr(buf, node, -kWordSize, &env1, NULL);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
    // mov rax, [rbp+33]
    0x48, 0x8b, 0x44, 0x24, 33};
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  AST_heap_free(node);
  PASS();
}

TEST compile_symbol_in_env_returns_first_value(Buffer *buf) {
  ASTNode *node = AST_new_symbol("hello");
  Env env0 = Env_bind("hello", 55, /*prev=*/NULL);
  Env env1 = Env_bind("hello", 66, &env0);
  int compile_result = Compile_expr(buf, node, -kWordSize, &env1, NULL);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
    // mov rax, [rbp+66]
    0x48, 0x8b, 0x44, 0x24, 66};
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  AST_heap_free(node);
  PASS();
}

TEST compile_symbol_not_in_env_raises_compile_error(Buffer *buf) {
  ASTNode *node = AST_new_symbol("hello");
  int compile_result = Compile_expr(buf, node, -kWordSize, NULL, NULL);
  ASSERT_EQ(compile_result, -1);
  AST_heap_free(node);
  PASS();
}

TEST compile_let_with_no_bindings(Buffer *buf) {
  ASTNode *node = Reader_read("(let () (+ 1 2))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(3), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_let_with_one_binding(Buffer *buf) {
  ASTNode *node = Reader_read("(let ((a 1)) (+ a 2))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(3), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_let_with_multiple_bindings(Buffer *buf) {
  ASTNode *node = Reader_read("(let ((a 1) (b 2)) (+ a b))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(3), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_nested_let(Buffer *buf) {
  ASTNode *node = Reader_read("(let ((a 1)) (let ((b 2)) (+ a b)))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(3), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_let_is_not_let_star(Buffer *buf) {
  ASTNode *node = Reader_read("(let ((a 1) (b a)) a)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, -1);
  AST_heap_free(node);
  PASS();
}

TEST compile_if_with_true_cond(Buffer *buf) {
  ASTNode *node = Reader_read("(if #t 1 2)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
    // mov rax, 0x9f
    0x48, 0xc7, 0xc0, 0x9f, 0x00, 0x00, 0x00,
    // cmp rax, 0x1f
    0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00,
    // je alternate
    0x0f, 0x84, 0x0c, 0x00, 0x00, 0x00,
    // mov rax, compile (1)
    0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
    // jmp end
    0xe9, 0x07, 0x00, 0x00, 0x00,
    // alternate:
    // mov rax, compile (2)
    0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00};
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(1), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_if_with_false_cond(Buffer *buf) {
  ASTNode *node = Reader_read("(if #f 1 2)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
    // mov rax, 0x1f
    0x48, 0xc7, 0xc0, 0x1f, 0x00, 0x00, 0x00,
    // cmp rax, 0x1f
    0x48, 0x3d, 0x1f, 0x00, 0x00, 0x00,
    // je alternate
    0x0f, 0x84, 0x0c, 0x00, 0x00, 0x00,
    // mov rax, compile(1)
    0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
    // jmp end
    0xe9, 0x07, 0x00, 0x00, 0x00,
    // alternate:
    // mov rax, compile(2)
    0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00
    // end:
  };
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(2), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_nested_if(Buffer *buf) {
  ASTNode *node = Reader_read("(if (< 1 2) (if #f 3 4) 5)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(4), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_cons(Buffer *buf, uword *heap) {
  ASTNode *node = Reader_read("(cons 1 2)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rax, 0x2
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // mov [rbp-8], rax
      0x48, 0x89, 0x45, 0xf8,
      // mov rax, 0x4
      0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
      // mov [rsi+Cdr], rax
      0x48, 0x89, 0x46, 0x08,
      // mov rax, [rbp-8]
      0x48, 0x8b, 0x45, 0xf8,
      // mov [rsi+Car], rax
      0x48, 0x89, 0x46, 0x00,
      // mov rax, rsi
      0x48, 0x89, 0xf0,
      // or rax, kPairTag
      0x48, 0x83, 0xc8, 0x01,
      // add rsi, 2*kWordSize
      0x48, 0x81, 0xc6, 0x10, 0x00, 0x00, 0x00,
  };
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, heap);
  ASSERT(Object_is_pair(result));
  ASSERT_EQ_FMT(Object_encode_integer(1), Object_pair_car(result), "0x%lx");
  ASSERT_EQ_FMT(Object_encode_integer(2), Object_pair_cdr(result), "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_two_cons(Buffer *buf, uword *heap) {
  ASTNode *node = Reader_read(
      "(let ((a (cons 1 2)) (b (cons 3 4))) (cons (cdr a) (cdr b)))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, heap);
  ASSERT(Object_is_pair(result));
  ASSERT_EQ_FMT(Object_encode_integer(2), Object_pair_car(result), "0x%lx");
  ASSERT_EQ_FMT(Object_encode_integer(4), Object_pair_cdr(result), "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_nested_cons(Buffer *buf, uword *heap) {
  ASTNode *node = Reader_read("(cons (cons 1 2) (cons 3 4))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, heap);
  ASSERT(Object_is_pair(result));
  ASSERT(Object_is_pair(Object_pair_car(result)));
  ASSERT_EQ_FMT(Object_encode_integer(1),
                Object_pair_car(Object_pair_car(result)), "0x%lx");
  ASSERT_EQ_FMT(Object_encode_integer(2),
                Object_pair_cdr(Object_pair_car(result)), "0x%lx");
  ASSERT(Object_is_pair(Object_pair_cdr(result)));
  ASSERT_EQ_FMT(Object_encode_integer(3),
                Object_pair_car(Object_pair_cdr(result)), "0x%lx");
  ASSERT_EQ_FMT(Object_encode_integer(4),
                Object_pair_cdr(Object_pair_cdr(result)), "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_car(Buffer *buf, uword *heap) {
  ASTNode *node = Reader_read("(car (cons 1 2))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rax, 0x2
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // mov [rbp-8], rax
      0x48, 0x89, 0x45, 0xf8,
      // mov rax, 0x4
      0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
      // mov [rsi+Cdr], rax
      0x48, 0x89, 0x46, 0x08,
      // mov rax, [rbp-8]
      0x48, 0x8b, 0x45, 0xf8,
      // mov [rsi+Car], rax
      0x48, 0x89, 0x46, 0x00,
      // mov rax, rsi
      0x48, 0x89, 0xf0,
      // or rax, kPairTag
      0x48, 0x83, 0xc8, 0x01,
      // add rsi, 2*kWordSize
      0x48, 0x81, 0xc6, 0x10, 0x00, 0x00, 0x00,
      // mov rax, [rax-1]
      0x48, 0x8b, 0x40, 0xff,
  };
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, heap);
  ASSERT_EQ_FMT(Object_encode_integer(1), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_cdr(Buffer *buf, uword *heap) {
  ASTNode *node = Reader_read("(cdr (cons 1 2))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rax, 0x2
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // mov [rbp-8], rax
      0x48, 0x89, 0x45, 0xf8,
      // mov rax, 0x4
      0x48, 0xc7, 0xc0, 0x08, 0x00, 0x00, 0x00,
      // mov [rsi+Cdr], rax
      0x48, 0x89, 0x46, 0x08,
      // mov rax, [rbp-8]
      0x48, 0x8b, 0x45, 0xf8,
      // mov [rsi+Car], rax
      0x48, 0x89, 0x46, 0x00,
      // mov rax, rsi
      0x48, 0x89, 0xf0,
      // or rax, kPairTag
      0x48, 0x83, 0xc8, 0x01,
      // add rsi, 2*kWordSize
      0x48, 0x81, 0xc6, 0x10, 0x00, 0x00, 0x00,
      // mov rax, [rax+7]
      0x48, 0x8b, 0x40, 0x07,
  };
  // clang-format on
  EXPECT_ENTRY_CONTAINS_CODE(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, heap);
  ASSERT_EQ_FMT(Object_encode_integer(2), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_code_with_no_params(Buffer *buf) {
  ASTNode *node = Reader_read("(code () 1)");
  int compile_result = Compile_code(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rax, 0x2
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_expr(buf);
  ASSERT_EQ_FMT(Object_encode_integer(1), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_code_with_one_param(Buffer *buf) {
  ASTNode *node = Reader_read("(code (x) x)");
  int compile_result = Compile_code(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rax, [rsp-8]
      0x48, 0x8b, 0x44, 0x24, 0xf8,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  AST_heap_free(node);
  PASS();
}

TEST compile_code_with_two_params(Buffer *buf) {
  ASTNode *node = Reader_read("(code (x y) (+ x y))");
  int compile_result = Compile_code(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rax, [rsp-16]
      0x48, 0x8b, 0x44, 0x24, 0xf0,
      // mov [rsp-24], rax
      0x48, 0x89, 0x44, 0x24, 0xe8,
      // mov rax, [rsp-8]
      0x48, 0x8b, 0x44, 0x24, 0xf8,
      // add rax, [rsp-24]
      0x48, 0x03, 0x44, 0x24, 0xe8,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  AST_heap_free(node);
  PASS();
}

TEST compile_labels_with_no_labels(Buffer *buf) {
  ASTNode *node = Reader_read("(labels () 1)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rsi, rdi
      0x48, 0x89, 0xfe,
      // jmp 0x00
      0xe9, 0x00, 0x00, 0x00, 0x00,
      // mov rax, 0x2
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, /*heap=*/NULL);
  ASSERT_EQ_FMT(Object_encode_integer(1), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_labels_with_one_label(Buffer *buf) {
  ASTNode *node = Reader_read("(labels ((const (code () 5))) 1)");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rsi, rdi
      0x48, 0x89, 0xfe,
      // jmp 0x08
      0xe9, 0x08, 0x00, 0x00, 0x00,
      // mov rax, compile(5)
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // ret
      0xc3,
      // mov rax, 0x2
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, /*heap=*/NULL);
  ASSERT_EQ_FMT(Object_encode_integer(1), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_labelcall_with_no_params(Buffer *buf) {
  ASTNode *node =
      Reader_read("(labels ((const (code () 5))) (labelcall const))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rsi, rdi
      0x48, 0x89, 0xfe,
      // jmp 0x08
      0xe9, 0x08, 0x00, 0x00, 0x00,
      // mov rax, compile(5)
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // ret
      0xc3,
      // call `const`
      0xe8, 0xf3, 0xff, 0xff, 0xff,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, /*heap=*/NULL);
  ASSERT_EQ_FMT(Object_encode_integer(5), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_labelcall_with_no_params_and_locals(Buffer *buf) {
  ASTNode *node = Reader_read(
      "(labels ((const (code () 5))) (let ((a 1)) (labelcall const)))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rsi, rdi
      0x48, 0x89, 0xfe,
      // jmp 0x08
      0xe9, 0x08, 0x00, 0x00, 0x00,
      // mov rax, compile(5)
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // ret
      0xc3,
      // mov rax, compile(1)
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // mov [rsp-8], rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // sub rsp, 8
      0x48, 0x81, 0xec, 0x08, 0x00, 0x00, 0x00,
      // call `const`
      0xe8, 0xe0, 0xff, 0xff, 0xff,
      // add rsp, 8
      0x48, 0x81, 0xc4, 0x08, 0x00, 0x00, 0x00,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, /*heap=*/NULL);
  ASSERT_EQ_FMT(Object_encode_integer(5), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_labelcall_with_one_param(Buffer *buf) {
  ASTNode *node = Reader_read("(labels ((id (code (x) x))) (labelcall id 5))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rsi, rdi
      0x48, 0x89, 0xfe,
      // jmp 0x06
      0xe9, 0x06, 0x00, 0x00, 0x00,
      // mov rax, [rsp-8]
      0x48, 0x8b, 0x44, 0x24, 0xf8,
      // ret
      0xc3,
      // mov rax, compile(5)
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // mov [rsp-16], rax
      0x48, 0x89, 0x44, 0x24, 0xf0,
      // call `id`
      0xe8, 0xe9, 0xff, 0xff, 0xff,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, /*heap=*/NULL);
  ASSERT_EQ_FMT(Object_encode_integer(5), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

TEST compile_labelcall_with_one_param_and_locals(Buffer *buf) {
  ASTNode *node = Reader_read(
      "(labels ((id (code (x) x))) (let ((a 1)) (labelcall id 5)))");
  int compile_result = Compile_entry(buf, node);
  ASSERT_EQ(compile_result, 0);
  // clang-format off
  byte expected[] = {
      // mov rsi, rdi
      0x48, 0x89, 0xfe,
      // jmp 0x06
      0xe9, 0x06, 0x00, 0x00, 0x00,
      // mov rax, [rsp-8]
      0x48, 0x8b, 0x44, 0x24, 0xf8,
      // ret
      0xc3,
      // mov rax, compile(1)
      0x48, 0xc7, 0xc0, 0x04, 0x00, 0x00, 0x00,
      // mov [rsp-8], rax
      0x48, 0x89, 0x44, 0x24, 0xf8,
      // mov rax, compile(5)
      0x48, 0xc7, 0xc0, 0x14, 0x00, 0x00, 0x00,
      // mov [rsp-24], rax
      0x48, 0x89, 0x44, 0x24, 0xe8,
      // sub rsp, 8
      0x48, 0x81, 0xec, 0x08, 0x00, 0x00, 0x00,
      // call `id`
      0xe8, 0xd6, 0xff, 0xff, 0xff,
      // add rsp, 8
      0x48, 0x81, 0xc4, 0x08, 0x00, 0x00, 0x00,
      // ret
      0xc3,
  };
  // clang-format on
  EXPECT_EQUALS_BYTES(buf, expected);
  Buffer_make_executable(buf);
  uword result = Testing_execute_entry(buf, /*heap=*/NULL);
  ASSERT_EQ_FMT(Object_encode_integer(5), result, "0x%lx");
  AST_heap_free(node);
  PASS();
}

SUITE(object_tests) {
  RUN_TEST(encode_positive_integer);
  RUN_TEST(encode_negative_integer);
  RUN_TEST(encode_char);
  RUN_TEST(decode_char);
  RUN_TEST(encode_bool);
  RUN_TEST(decode_bool);
  RUN_TEST(address);
}

SUITE(ast_tests) {
  RUN_TEST(ast_new_pair);
  RUN_TEST(ast_pair_car_returns_car);
  RUN_TEST(ast_pair_cdr_returns_cdr);
  RUN_TEST(ast_new_symbol);
}

SUITE(reader_tests) {
  RUN_TEST(read_with_integer_returns_integer);
  RUN_TEST(read_with_negative_integer_returns_integer);
  RUN_TEST(read_with_positive_integer_returns_integer);
  RUN_TEST(read_with_leading_whitespace_ignores_whitespace);
  RUN_TEST(read_with_symbol_returns_symbol);
  RUN_TEST(read_with_symbol_with_trailing_digits);
  RUN_TEST(read_with_nil_returns_nil);
  RUN_TEST(read_with_list_returns_list);
  RUN_TEST(read_with_nested_list_returns_list);
  RUN_TEST(read_with_char_returns_char);
  RUN_TEST(read_with_bool_returns_bool);
}

SUITE(buffer_tests) {
  RUN_BUFFER_TEST(buffer_write8_increases_length);
  RUN_TEST(buffer_write8_expands_buffer);
  RUN_TEST(buffer_write32_expands_buffer);
  RUN_BUFFER_TEST(buffer_write32_writes_little_endian);
}

SUITE(compiler_tests) {
  RUN_BUFFER_TEST(compile_positive_integer);
  RUN_BUFFER_TEST(compile_negative_integer);
  RUN_BUFFER_TEST(compile_char);
  RUN_BUFFER_TEST(compile_true);
  RUN_BUFFER_TEST(compile_false);
  RUN_BUFFER_TEST(compile_nil);
  RUN_BUFFER_TEST(compile_unary_add1);
  RUN_BUFFER_TEST(compile_unary_add1_nested);
  RUN_BUFFER_TEST(compile_unary_sub1);
  RUN_BUFFER_TEST(compile_unary_integer_to_char);
  RUN_BUFFER_TEST(compile_unary_char_to_integer);
  RUN_BUFFER_TEST(compile_unary_nilp_with_nil_returns_true);
  RUN_BUFFER_TEST(compile_unary_nilp_with_non_nil_returns_false);
  RUN_BUFFER_TEST(compile_unary_zerop_with_zero_returns_true);
  RUN_BUFFER_TEST(compile_unary_zerop_with_non_zero_returns_false);
  RUN_BUFFER_TEST(compile_unary_not_with_false_returns_true);
  RUN_BUFFER_TEST(compile_unary_not_with_non_false_returns_false);
  RUN_BUFFER_TEST(compile_unary_integerp_with_integer_returns_true);
  RUN_BUFFER_TEST(compile_unary_integerp_with_non_integer_returns_false);
  RUN_BUFFER_TEST(compile_unary_booleanp_with_boolean_returns_true);
  RUN_BUFFER_TEST(compile_unary_booleanp_with_non_boolean_returns_false);
  RUN_BUFFER_TEST(compile_binary_plus);
  RUN_BUFFER_TEST(compile_binary_plus_nested);
  RUN_BUFFER_TEST(compile_binary_minus);
  RUN_BUFFER_TEST(compile_binary_minus_nested);
  RUN_BUFFER_TEST(compile_binary_mul);
  RUN_BUFFER_TEST(compile_binary_mul_nested);
  RUN_BUFFER_TEST(compile_binary_eq_with_same_address_returns_true);
  RUN_BUFFER_TEST(compile_binary_eq_with_different_address_returns_false);
  RUN_BUFFER_TEST(compile_binary_lt_with_left_less_than_right_returns_true);
  RUN_BUFFER_TEST(compile_binary_lt_with_left_equal_to_right_returns_false);
  RUN_BUFFER_TEST(compile_binary_lt_with_left_greater_than_right_returns_false);
  RUN_BUFFER_TEST(compile_symbol_in_env_returns_value);
  RUN_BUFFER_TEST(compile_symbol_in_env_returns_first_value);
  RUN_BUFFER_TEST(compile_symbol_not_in_env_raises_compile_error);
  RUN_BUFFER_TEST(compile_let_with_no_bindings);
  RUN_BUFFER_TEST(compile_let_with_one_binding);
  RUN_BUFFER_TEST(compile_let_with_multiple_bindings);
  RUN_BUFFER_TEST(compile_nested_let);
  RUN_BUFFER_TEST(compile_let_is_not_let_star);
  RUN_BUFFER_TEST(compile_if_with_true_cond);
  RUN_BUFFER_TEST(compile_if_with_false_cond);
  RUN_BUFFER_TEST(compile_nested_if);
  RUN_HEAP_TEST(compile_cons);
  RUN_HEAP_TEST(compile_two_cons);
  RUN_HEAP_TEST(compile_nested_cons);
  RUN_HEAP_TEST(compile_car);
  RUN_HEAP_TEST(compile_cdr);
  RUN_BUFFER_TEST(compile_code_with_no_params);
  RUN_BUFFER_TEST(compile_code_with_one_param);
  RUN_BUFFER_TEST(compile_code_with_two_params);
  RUN_BUFFER_TEST(compile_labels_with_no_labels);
  RUN_BUFFER_TEST(compile_labels_with_one_label);
  RUN_BUFFER_TEST(compile_labelcall_with_no_params);
  RUN_BUFFER_TEST(compile_labelcall_with_no_params_and_locals);
  RUN_BUFFER_TEST(compile_labelcall_with_one_param);
  RUN_BUFFER_TEST(compile_labelcall_with_one_param_and_locals);
}
// End Tests

typedef void (*REPL_Callback)(char *);

void print_value(uword object) {
  if (Object_is_integer(object)) {
    fprintf(stderr, "%ld", Object_decode_integer(object));
    return;
  }
  if (object == Object_false()) {
    fprintf(stderr, "#f");
    return;
  }
  if (object == Object_true()) {
    fprintf(stderr, "#t");
    return;
  }
  if (object == Object_nil()) {
    fprintf(stderr, "nil");
    return;
  }
  if (Object_is_char(object)) {
    fprintf(stderr, "%c", Object_decode_char(object));
    return;
  }
  if (AST_is_heap_object((ASTNode *)object) && AST_is_pair((ASTNode *)object)) {
    fprintf(stderr, "(");
    print_value((uword)AST_pair_car((ASTNode *)object));
    fprintf(stderr, " ");
    print_value((uword)AST_pair_cdr((ASTNode *)object));
    fprintf(stderr, ")");
    return;
  }
  fprintf(stderr, "Unprintable value");
}

void print_assembly(char *line) {
  // Parse the line
  ASTNode *node = Reader_read(line);
  free(line);
  if (AST_is_error(node)) {
    fprintf(stderr, "Parse error.\n");
    return;
  }

  // Compile the line
  Buffer buf;
  Buffer_init(&buf, 1);
  int result = Compile_expr(&buf, node, /*stack_index=*/-kWordSize, NULL, NULL);
  AST_heap_free(node);
  if (result < 0) {
    fprintf(stderr, "Compile error.\n");
    Buffer_deinit(&buf);
    return;
  }

  // Print the assembled code
  for (size_t i = 0; i < buf.len; i++) {
    fprintf(stderr, "%.02x ", buf.address[i]);
  }
  fprintf(stderr, "\n");

  Buffer_deinit(&buf);
}

uword *heap = NULL;

void evaluate_expr(char *line) {
  if (!heap) {
    heap = malloc(1000 * kWordSize);
  }

  // Parse the line
  ASTNode *node = Reader_read(line);
  if (AST_is_error(node)) {
    fprintf(stderr, "Parse error.\n");
    return;
  }

  // Compile the line
  Buffer buf;
  Buffer_init(&buf, 1);
  int compile_result = Compile_entry(&buf, node);
  AST_heap_free(node);
  if (compile_result < 0) {
    fprintf(stderr, "Compile error.\n");
    Buffer_deinit(&buf);
    return;
  }

  // Execute the code
  Buffer_make_executable(&buf);
  uword result = Testing_execute_entry(&buf, heap);

  // Print the result
  print_value(result);
  fprintf(stderr, "\n");

  // Clean up
  Buffer_deinit(&buf);
}

int repl(REPL_Callback callback) {
  do {
    // Read a line
    fprintf(stdout, "lisp> ");
    char *line = NULL;
    size_t size = 0;
    ssize_t nchars = getline(&line, &size, stdin);
    if (nchars < 0) {
      fprintf(stderr, "Goodbye.\n");
      free(line);
      free(heap);
      break;
    }

    callback(line);
    free(line);
  } while (true);
  return 0;
}

GREATEST_MAIN_DEFS();

int run_tests(int argc, char **argv) {
  GREATEST_MAIN_BEGIN();
  RUN_SUITE(object_tests);
  RUN_SUITE(ast_tests);
  RUN_SUITE(buffer_tests);
  RUN_SUITE(compiler_tests);
  RUN_SUITE(reader_tests);
  GREATEST_MAIN_END();
}

int main(int argc, char **argv) {
  if (argc == 2) {
    if (strcmp(argv[1], "--repl-assembly") == 0) {
      return repl(print_assembly);
    }
    if (strcmp(argv[1], "--repl-eval") == 0) {
      return repl(evaluate_expr);
    }
  }
  return run_tests(argc, argv);
}