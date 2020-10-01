#include <assert.h>   // for assert
#include <stdbool.h>  // for bool
#include <stddef.h>   // for NULL
#include <stdint.h>   // for int32_t, etc
#include <string.h>   // for memcpy
#include <sys/mman.h> // for mmap

#include "greatest.h"

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

word Object_encode_integer(word value)
{
    assert(value < kIntegerMax && "too big");
    assert(value > kIntegerMin && "too small");
    return value << kIntegerShift;
}

const unsigned int kImmediateTagMask = 0x3f;

const unsigned int kCharTag = 0xf;
const unsigned int kCharMask = 0xff;
const unsigned int kCharShift = 8;

word Object_encode_char(char value)
{
    return ((word)value << kCharShift) | kCharTag;
}

char Object_decode_char(word value)
{
    return (value >> kCharShift) & kCharMask;
}

const unsigned int kBoolTag = 0x1f;
const unsigned int kBoolMask = 0x80;
const unsigned int kBoolShift = 7;

word Object_encode_bool(bool value)
{
    return ((word)value << kBoolShift) | kBoolTag;
}

bool Object_decode_bool(word value)
{
    return value & kBoolMask;
}

word Object_true()
{
    return Object_encode_bool(true);
}

word Object_false()
{
    return Object_encode_bool(false);
}

word Object_nil()
{
    return 0x2f;
}

const unsigned int kPairTag = 0x1;
const uword kHeapTagMask = ((uword)0x7);
const uword kHeapPtrMask = ~kHeapTagMask;

uword Object_address(void *obj)
{
    return (uword)obj & kHeapPtrMask;
}

const unsigned int kSymbolTag = 0x5;

typedef struct
{
    word length;
    char cstr[];
} Symbol;

// AST

struct ASTNode;
typedef struct ASTNode ASTNode;

typedef struct
{
    ASTNode *car;
    ASTNode *cdr;
} Pair;

ASTNode *AST_new_integer(word value)
{
    return (ASTNode *)Object_encode_integer(value);
}

bool AST_is_integer(ASTNode *node)
{
    return ((word)node & kIntegerTagMask) == kIntegerTag;
}

word AST_get_integer(ASTNode *node)
{
    return (word)node >> kIntegerShift;
}

ASTNode *AST_new_char(char value)
{
    return (ASTNode *)Object_encode_char(value);
}

bool AST_is_char(ASTNode *node)
{
    return ((word)node & kImmediateTagMask) == kCharTag;
}

char AST_get_char(ASTNode *node)
{
    return Object_decode_char((word)node);
}

ASTNode *AST_new_bool(bool value)
{
    return (ASTNode *)Object_encode_bool(value);
}

bool AST_is_bool(ASTNode *node)
{
    return ((word)node & kImmediateTagMask) == kBoolTag;
}

bool AST_get_bool(ASTNode *node)
{
    return Object_decode_bool((word)node);
}

ASTNode *AST_new_nil()
{
    return (ASTNode *)Object_nil();
}

bool AST_is_nil(ASTNode *node)
{
    return (word)node == Object_nil();
}

ASTNode *AST_nil()
{
    return (ASTNode *)Object_nil();
}

ASTNode *AST_heap_alloc(unsigned char tag, uword size)
{
    uword address = (uword)calloc(size, 1);
    return (ASTNode *)(address | tag);
}

bool AST_is_heap_object(ASTNode *node)
{
    unsigned char tag = (uword)node & kHeapTagMask;
    return (tag & kIntegerTagMask) > 0 && (tag & kImmediateTagMask) != 0x07;
}

bool AST_is_pair(ASTNode *node);
ASTNode *AST_pair_car(ASTNode *node);
ASTNode *AST_pair_cdr(ASTNode *node);

void AST_heap_free(ASTNode *node)
{
    if (!AST_is_heap_object(node))
    {
        return;
    }
    if (AST_is_pair(node))
    {
        AST_heap_free(AST_pair_car(node));
        AST_heap_free(AST_pair_cdr(node));
    }
    free((void *)Object_address(node));
}

void AST_pair_set_car(ASTNode *node, ASTNode *car);
void AST_pair_set_cdr(ASTNode *node, ASTNode *cdr);

ASTNode *AST_new_pair(ASTNode *car, ASTNode *cdr)
{
    ASTNode *node = AST_heap_alloc(kPairTag, sizeof(Pair));
    AST_pair_set_car(node, car);
    AST_pair_set_cdr(node, cdr);
    return node;
}

bool AST_is_pair(ASTNode *node)
{
    return ((uword)node & kHeapTagMask) == kPairTag;
}

Pair *AST_as_pair(ASTNode *node)
{
    assert(AST_is_pair(node));
    return (Pair *)Object_address(node);
}

ASTNode *AST_pair_car(ASTNode *node)
{
    return AST_as_pair(node)->car;
}

void AST_pair_set_car(ASTNode *node, ASTNode *car)
{
    AST_as_pair(node)->car = car;
}

ASTNode *AST_pair_cdr(ASTNode *node)
{
    return AST_as_pair(node)->cdr;
}

void AST_pair_set_cdr(ASTNode *node, ASTNode *cdr)
{
    AST_as_pair(node)->cdr = cdr;
}

Symbol *AST_as_symbol(ASTNode *node);

ASTNode *AST_new_symbol(const char *str)
{
    word data_length = strlen(str) + 1;
    ASTNode *node = AST_heap_alloc(kSymbolTag, sizeof(Symbol) + data_length);
    Symbol *s = AST_as_symbol(node);
    s->length = data_length;
    memcpy(s->cstr, str, data_length);
    return node;
}

bool AST_is_symbol(ASTNode *node)
{
    return ((uword)node & kHeapTagMask) == kSymbolTag;
}

Symbol *AST_as_symbol(ASTNode *node)
{
    assert(AST_is_symbol(node));
    return (Symbol *)Object_address(node);
}

const char *AST_symbol_cstr(ASTNode *node)
{
    return (const char *)AST_as_symbol(node)->cstr;
}

bool AST_symbol_matches(ASTNode *node, const char *cstr)
{
    return strcmp(AST_symbol_cstr(node), cstr) == 0;
}

ASTNode *list1(ASTNode *item0)
{
    return AST_new_pair(item0, AST_nil());
}

ASTNode *list2(ASTNode *item0, ASTNode *item1)
{
    return AST_new_pair(item0, list1(item1));
}

ASTNode *new_unary_call(const char *name, ASTNode *arg)
{
    return list2(AST_new_symbol(name), arg);
}

// Buffer
typedef unsigned char byte;

typedef enum
{
    kWritable,
    kExecutable,
} BufferState;

typedef struct
{
    byte *address;
    BufferState state;
    size_t len;
    size_t capacity;
} Buffer;

byte *Buffer_alloc_writable(size_t capacity)
{
    byte *result = mmap(NULL, capacity, PROT_READ | PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
    assert(result != MAP_FAILED);
    return result;
}

void Buffer_init(Buffer *result, size_t capacity)
{
    result->address = Buffer_alloc_writable(capacity);
    assert(result->address != MAP_FAILED);
    result->state = kWritable;
    result->len = 0;
    result->capacity = capacity;
}

void Buffer_deinit(Buffer *buf)
{
    munmap(buf->address, buf->capacity);
    buf->address = NULL;
    buf->len = 0;
    buf->capacity = 0;
}

int Buffer_make_executable(Buffer *buf)
{
    int result = mprotect(buf->address, buf->len, PROT_EXEC);
    buf->state = kExecutable;
    return result;
}

byte Buffer_at8(Buffer *buf, size_t pos)
{
    return buf->address[pos];
}

void Buffer_at_put8(Buffer *buf, size_t pos, byte b)
{
    buf->address[pos] = b;
}

word max(word left, word right)
{
    return left > right ? left : right;
}

void Buffer_ensure_capacity(Buffer *buf, word additional_capacity)
{
    if (buf->len + additional_capacity <= buf->capacity)
    {
        return;
    }
    word new_capacity = max(buf->capacity * 2, buf->capacity + additional_capacity);
    byte *address = Buffer_alloc_writable(new_capacity);
    memcpy(address, buf->address, buf->len);
    int result = munmap(buf->address, buf->capacity);
    assert(result == 0 && "munmap failed");
    buf->address = address;
    buf->capacity = new_capacity;
}

void Buffer_write8(Buffer *buf, byte b)
{
    Buffer_ensure_capacity(buf, sizeof b);
    Buffer_at_put8(buf, buf->len++, b);
}

void Buffer_write32(Buffer *buf, int32_t value)
{
    for (size_t i = 0; i < sizeof value; i++)
    {
        Buffer_write8(buf, (value >> (i * kBitsPerByte)) & 0xff);
    }
}

// Emit

// The order here is determined by the x86 ISA encoding
typedef enum
{
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
typedef enum
{
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
typedef enum
{
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
} Condition;

static const byte kRexPrefix = 0x48;

void Emit_mov_reg_imm32(Buffer *buf, Register dst, int32_t src)
{
    Buffer_write8(buf, kRexPrefix);
    Buffer_write8(buf, 0xc7);
    Buffer_write8(buf, 0xc0 + dst);
    Buffer_write32(buf, src);
}

void Emit_ret(Buffer *buf)
{
    Buffer_write8(buf, 0xc3);
}

void Emit_add_reg_imm32(Buffer *buf, Register dst, int32_t src)
{
    Buffer_write8(buf, kRexPrefix);
    if (dst == kRax)
    {
        // Optimization: add eax, {imm32} can either be encoded as 05 {imm32} or 81
        // c0 {imm32}.
        Buffer_write8(buf, 0x05);
    }
    else
    {
        Buffer_write8(buf, 0x81);
        Buffer_write8(buf, 0xc0 + dst);
    }
    Buffer_write32(buf, src);
}

void Emit_sub_reg_imm32(Buffer *buf, Register dst, int32_t src)
{
    Buffer_write8(buf, kRexPrefix);
    if (dst == kRax)
    {
        // Optimization: sub eax, {imm32} can either be encoded as 2d {imm32} or 81
        // e8 {imm32}.
        Buffer_write8(buf, 0x2d);
    }
    else
    {
        Buffer_write8(buf, 0x81);
        Buffer_write8(buf, 0xe8 + dst);
    }
    Buffer_write32(buf, src);
}

void Emit_shl_reg_imm8(Buffer *buf, Register dst, int8_t bits)
{
    Buffer_write8(buf, kRexPrefix);
    Buffer_write8(buf, 0xc1);
    Buffer_write8(buf, 0xe0 + dst);
    Buffer_write8(buf, bits);
}

void Emit_shr_reg_imm8(Buffer *buf, Register dst, int8_t bits)
{
    Buffer_write8(buf, kRexPrefix);
    Buffer_write8(buf, 0xc1);
    Buffer_write8(buf, 0xe8 + dst);
    Buffer_write8(buf, bits);
}

void Emit_or_reg_imm8(Buffer *buf, Register dst, uint8_t tag)
{
    Buffer_write8(buf, kRexPrefix);
    Buffer_write8(buf, 0x83);
    Buffer_write8(buf, 0xc8 + dst);
    Buffer_write8(buf, tag);
}

void Emit_and_reg_imm8(Buffer *buf, Register dst, uint8_t tag)
{
    Buffer_write8(buf, kRexPrefix);
    Buffer_write8(buf, 0x83);
    Buffer_write8(buf, 0xe0 + dst);
    Buffer_write8(buf, tag);
}

void Emit_cmp_reg_imm32(Buffer *buf, Register left, int32_t right)
{
    Buffer_write8(buf, kRexPrefix);
    if (left == kRax)
    {
        // Optimization: cmp rax, {imm32} can be encoded as 0x3d {imm32}
        Buffer_write8(buf, 0x3d);
    }
    else
    {
        Buffer_write8(buf, 0x81);
        Buffer_write8(buf, 0xf8 + left);
    }
    Buffer_write32(buf, right);
}

void Emit_setcc_imm8(Buffer *buf, Condition cond, PartialRegister dst)
{
    Buffer_write8(buf, 0x0f);
    Buffer_write8(buf, 0x90 + cond);
    Buffer_write8(buf, 0xc0 + dst);
}

// Compile

int Compile_call(Buffer *buf, ASTNode *callable, ASTNode *args);
void Compile_compare_imm32(Buffer *buf, int32_t value);

ASTNode *operand1(ASTNode *args)
{
    return AST_pair_car(args);
}

#define _(exp)             \
    do                     \
    {                      \
        int result = exp;  \
        if (result != 0)   \
            return result; \
    } while (0)

int Compile_expr(Buffer *buf, ASTNode *node)
{
    if (AST_is_integer(node))
    {
        word value = AST_get_integer(node);
        Emit_mov_reg_imm32(buf, kRax, Object_encode_integer(value));
        return 0;
    }
    if (AST_is_char(node))
    {
        char value = AST_get_char(node);
        Emit_mov_reg_imm32(buf, kRax, Object_encode_char(value));
        return 0;
    }
    if (AST_is_bool(node))
    {
        bool value = AST_get_bool(node);
        Emit_mov_reg_imm32(buf, kRax, Object_encode_bool(value));
        return 0;
    }
    if (AST_is_nil(node))
    {
        Emit_mov_reg_imm32(buf, kRax, Object_nil());
        return 0;
    }
    if (AST_is_pair(node))
    {
        return Compile_call(buf, AST_pair_car(node), AST_pair_cdr(node));
    }
    assert(0 && "unexpected node type");
}

int Compile_call(Buffer *buf, ASTNode *callable, ASTNode *args)
{
    assert(AST_pair_cdr(args) == AST_nil() &&
           "only unary function calls supported");

    if (AST_is_symbol(callable))
    {
        if (AST_symbol_matches(callable, "add1"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_add_reg_imm32(buf, kRax, Object_encode_integer(1));
            return 0;
        }
        if (AST_symbol_matches(callable, "sub1"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_sub_reg_imm32(buf, kRax, Object_encode_integer(1));
            return 0;
        }
        if (AST_symbol_matches(callable, "integer->char"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_shl_reg_imm8(buf, kRax, kCharShift - kIntegerShift);
            Emit_or_reg_imm8(buf, kRax, kCharTag);
            return 0;
        }
        if (AST_symbol_matches(callable, "char->integer"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_shr_reg_imm8(buf, kRax, kCharShift - kIntegerShift);
            return 0;
        }
        if (AST_symbol_matches(callable, "nil?"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_cmp_reg_imm32(buf, kRax, Object_nil());
            Emit_mov_reg_imm32(buf, kRax, 0);
            Emit_setcc_imm8(buf, kEqual, kAl);
            Emit_shl_reg_imm8(buf, kRax, kBoolShift);
            Emit_or_reg_imm8(buf, kRax, kBoolTag);
            return 0;
        }
        if (AST_symbol_matches(callable, "zero?"))
        {
            _(Compile_expr(buf, operand1(args)));
            Compile_compare_imm32(buf, Object_encode_integer(0));
            return 0;
        }
        if (AST_symbol_matches(callable, "not"))
        {
            _(Compile_expr(buf, operand1(args)));
            Compile_compare_imm32(buf, Object_false());
            return 0;
        }
        if (AST_symbol_matches(callable, "integer?"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_and_reg_imm8(buf, kRax, kIntegerTagMask);
            Compile_compare_imm32(buf, kIntegerTag);
            return 0;
        }
        if (AST_symbol_matches(callable, "bool?"))
        {
            _(Compile_expr(buf, operand1(args)));
            Emit_and_reg_imm8(buf, kRax, kImmediateTagMask);
            Compile_compare_imm32(buf, kBoolTag);
            return 0;
        }
    }
    assert(0 && "unexpected call type");
}

int Compile_function(Buffer *buf, ASTNode *node)
{
    int result = Compile_expr(buf, node);
    if (result != 0)
    {
        return result;
    }
    Emit_ret(buf);
    return 0;
}

void Compile_compare_imm32(Buffer *buf, int32_t value)
{
    Emit_cmp_reg_imm32(buf, kRax, value);
    Emit_mov_reg_imm32(buf, kRax, 0);
    Emit_setcc_imm8(buf, kEqual, kAl);
    Emit_shl_reg_imm8(buf, kRax, kBoolShift);
    Emit_or_reg_imm8(buf, kRax, kBoolTag);
}

typedef int (*JitFunction)();

// Testing

#define EXPECT_EQUALS_BYTES(buf, arr) ASSERT_MEM_EQ(arr, (buf)->address, sizeof(arr))

word Testing_execute_expr(Buffer *buf)
{
    assert(buf != NULL);
    assert(buf->address != NULL);
    assert(buf->state == kExecutable);

    JitFunction function = *(JitFunction *)(&buf->address);
    return function();
}

void Testing_print_hex_array(FILE *fp, byte *arr, size_t arr_size)
{
    for (size_t i = 0; i < arr_size; i++)
    {
        fprintf(fp, "%.2x ", arr[i]);
    }
}

#define RUN_BUFFER_TEST(test_name)           \
    do                                       \
    {                                        \
        Buffer buf;                          \
        Buffer_init(&buf, 1);                \
        GREATEST_RUN_TEST1(test_name, &buf); \
        Buffer_deinit(&buf);                 \
    } while (0)

// Tests

TEST encode_positive_integer(void)
{
    ASSERT_EQ(0x0, Object_encode_integer(0));
    ASSERT_EQ(0x4, Object_encode_integer(1));
    ASSERT_EQ(0x28, Object_encode_integer(10));
    PASS();
}

TEST encode_negative_integer(void)
{
    ASSERT_EQ(0x0, Object_encode_integer(0));
    ASSERT_EQ((word)0xfffffffffffffffc, Object_encode_integer(-1));
    ASSERT_EQ((word)0xffffffffffffffd8, Object_encode_integer(-10));
    PASS();
}

TEST encode_char(void)
{
    ASSERT_EQ(Object_encode_char('\0'), 0xf);
    ASSERT_EQ(Object_encode_char('a'), 0x610f);
    PASS();
}

TEST decode_char(void)
{
    ASSERT_EQ(Object_decode_char(0xf), '\0');
    ASSERT_EQ(Object_decode_char(0x610f), 'a');
    PASS();
}

TEST encode_bool(void)
{
    ASSERT_EQ(Object_encode_bool(true), 0x9f);
    ASSERT_EQ(Object_encode_bool(false), 0x1f);
    ASSERT_EQ(Object_true(), 0x9f);
    ASSERT_EQ(Object_false(), 0x1f);
    PASS();
}

TEST decode_bool(void)
{
    ASSERT_EQ(Object_decode_bool(0x9f), true);
    ASSERT_EQ(Object_decode_bool(0x1f), false);
    PASS();
}

TEST buffer_write8_increases_length(Buffer *buf)
{
    ASSERT_EQ(buf->len, 0);
    Buffer_write8(buf, 0xdb);
    ASSERT_EQ(Buffer_at8(buf, 0), 0xdb);
    ASSERT_EQ(buf->len, 1);
    PASS();
}

TEST buffer_write8_expands_buffer(void)
{
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

TEST buffer_write32_expands_buffer(void)
{
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

TEST buffer_write32_writes_little_endian(Buffer *buf)
{
    Buffer_write32(buf, 0xdeadbeef);
    ASSERT_EQ(Buffer_at8(buf, 0), 0xef);
    ASSERT_EQ(Buffer_at8(buf, 1), 0xbe);
    ASSERT_EQ(Buffer_at8(buf, 2), 0xad);
    ASSERT_EQ(Buffer_at8(buf, 3), 0xde);
    PASS();
}

TEST compile_positive_integer(Buffer *buf)
{
    word value = 123;
    ASTNode *node = AST_new_integer(value);
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    // mov eax, imm(123); ret
    byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    word result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_encode_integer(value));
    PASS();
}

TEST compile_negative_integer(Buffer *buf)
{
    word value = -123;
    ASTNode *node = AST_new_integer(value);
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    // mov eax, imm(-123); ret
    byte expected[] = {0x48, 0xc7, 0xc0, 0x14, 0xfe, 0xff, 0xff, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    word result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_encode_integer(value));
    PASS();
}

TEST compile_char(Buffer *buf)
{
    char value = 'a';
    ASTNode *node = AST_new_char(value);
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    byte expected[] = {0x48, 0xc7, 0xc0, 0x0f, 0x61, 0x00, 0x00, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    word result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_encode_char(value));
    PASS();
}

TEST compile_true(Buffer *buf)
{
    ASTNode *node = AST_new_bool(true);
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    // mov eax, imm(true); ret
    byte expected[] = {0x48, 0xc7, 0xc0, 0x9f, 0x0, 0x0, 0x0, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    word result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_true());
    PASS();
}

TEST compile_false(Buffer *buf)
{
    ASTNode *node = AST_new_bool(false);
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    // mov eax, imm(false); ret
    byte expected[] = {0x48, 0xc7, 0xc0, 0x1f, 0x00, 0x00, 0x00, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    word result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_false());
    PASS();
}

TEST compile_nil(Buffer *buf)
{
    ASTNode *node = AST_new_nil();
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    // mov eax, imm(nil); ret
    byte expected[] = {0x48, 0xc7, 0xc0, 0x2f, 0x00, 0x00, 0x00, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    word result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_nil());
    PASS();
}

TEST compile_unary_add1(Buffer *buf)
{
    ASTNode *node = new_unary_call("add1", AST_new_integer(123));
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00,
                       0x48, 0x05, 0x04, 0x00, 0x00, 0x00, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    uword result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_encode_integer(124));
    AST_heap_free(node);
    PASS();
}

TEST compile_unary_add1_nested(Buffer *buf)
{
    ASTNode *node = new_unary_call("add1",
                                   new_unary_call("add1", AST_new_integer(123)));
    int compile_result = Compile_function(buf, node);
    ASSERT_EQ(compile_result, 0);
    byte expected[] = {0x48, 0xc7, 0xc0, 0xec, 0x01, 0x00, 0x00,
                       0x48, 0x05, 0x04, 0x00, 0x00, 0x00, 0x48,
                       0x05, 0x04, 0x00, 0x00, 0x00, 0xc3};
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    uword result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_encode_integer(125));
    AST_heap_free(node);
    PASS();
}

TEST compile_unary_booleanp_with_non_boolean_returns_false(Buffer *buf)
{
    ASTNode *node = new_unary_call("bool?", AST_new_integer(5));
    int compile_result = Compile_function(buf, node);
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
    EXPECT_EQUALS_BYTES(buf, expected);
    Buffer_make_executable(buf);
    uword result = Testing_execute_expr(buf);
    ASSERT_EQ(result, Object_false());
    AST_heap_free(node);
    PASS();
}

SUITE(object_tests)
{
    RUN_TEST(encode_positive_integer);
    RUN_TEST(encode_negative_integer);
    RUN_TEST(encode_char);
    RUN_TEST(decode_char);
    RUN_TEST(encode_bool);
    RUN_TEST(decode_bool);
}

SUITE(buffer_tests)
{
    RUN_BUFFER_TEST(buffer_write8_increases_length);
    RUN_TEST(buffer_write8_expands_buffer);
    RUN_TEST(buffer_write32_expands_buffer);
    RUN_BUFFER_TEST(buffer_write32_writes_little_endian);
}

SUITE(compiler_tests)
{
    RUN_BUFFER_TEST(compile_positive_integer);
    RUN_BUFFER_TEST(compile_negative_integer);
    RUN_BUFFER_TEST(compile_char);
    RUN_BUFFER_TEST(compile_true);
    RUN_BUFFER_TEST(compile_false);
    RUN_BUFFER_TEST(compile_nil);
    RUN_BUFFER_TEST(compile_unary_add1);
    RUN_BUFFER_TEST(compile_unary_add1_nested);
    RUN_BUFFER_TEST(compile_unary_booleanp_with_non_boolean_returns_false);
}

// End Tests

GREATEST_MAIN_DEFS();

int main(int argc, char **argv)
{
    GREATEST_MAIN_BEGIN();
    RUN_SUITE(object_tests);
    RUN_SUITE(buffer_tests);
    RUN_SUITE(compiler_tests);
    GREATEST_MAIN_END();
}
