default Order dec

$include <prelude.sail>
$include <arith.sail>

type u8_range = range(0, 255)
type u16_range = range(0, 65535)
type u32_range = range(0, 4294967295)
type u64_range = range(0, 18446744073709551615)

type i8_range = range(-128, 127)
type i16_range = range(-32768, 32767)
type i32_range = range(-2147483648, 2147483647)
type i64_range = range(-9223372036854775808, 9223372036854775807)

type tiny = range(0, 8)
type tiny_product = range(0, 64)
type u8_product = range(0, 65025)
type u16_product = range(0, 4294836225)
type u32_product = range(0, 18446744065119617025)
type u32_sum = range(0, 8589934590)
type u8_modulus : Int = 256
type u16_modulus : Int = 65536
type u32_modulus : Int = 4294967296

function keep_u8(value : u8_range) -> u8_range = value
function keep_u16(value : u16_range) -> u16_range = value
function keep_u32(value : u32_range) -> u32_range = value
function keep_u64(value : u64_range) -> u64_range = value

function keep_i8(value : i8_range) -> i8_range = value
function keep_i16(value : i16_range) -> i16_range = value
function keep_i32(value : i32_range) -> i32_range = value
function keep_i64(value : i64_range) -> i64_range = value

function multiply_tiny(left : tiny, right : tiny) -> tiny_product = left * right
function multiply_u8_exact(left : u8_range, right : u8_range) -> u8_product = left * right
function multiply_u16_exact(left : u16_range, right : u16_range) -> u16_product = left * right
function multiply_u32_exact(left : u32_range, right : u32_range) -> u32_product = left * right
function add_u32_exact(left : u32_range, right : u32_range) -> u32_sum = left + right

function add_u8_wrapping(left : u8_range, right : u8_range) -> u8_range =
  tmod_nat(left + right, sizeof(u8_modulus))

function add_u16_wrapping(left : u16_range, right : u16_range) -> u16_range =
  tmod_nat(left + right, sizeof(u16_modulus))

function add_u32_wrapping(left : u32_range, right : u32_range) -> u32_range =
  tmod_nat(left + right, sizeof(u32_modulus))

function multiply_u8_wrapping(left : u8_range, right : u8_range) -> u8_range =
  tmod_nat(left * right, sizeof(u8_modulus))

function multiply_u16_wrapping(left : u16_range, right : u16_range) -> u16_range =
  tmod_nat(left * right, sizeof(u16_modulus))

function multiply_u32_wrapping(left : u32_range, right : u32_range) -> u32_range =
  tmod_nat(left * right, sizeof(u32_modulus))

$[c_repr uint8]
newtype annotated_u8 = AnnotatedU8 : nat

$[c_repr uint16]
newtype annotated_u16 = AnnotatedU16 : nat

$[c_repr uint32]
newtype annotated_u32 = AnnotatedU32 : nat

$[c_repr uint64]
newtype annotated_u64 = AnnotatedU64 : nat

$[c_repr int8]
newtype annotated_i8 = AnnotatedI8 : int

$[c_repr int16]
newtype annotated_i16 = AnnotatedI16 : int

$[c_repr int32]
newtype annotated_i32 = AnnotatedI32 : int

$[c_repr int64]
newtype annotated_i64 = AnnotatedI64 : int

function keep_annotated_u8(value : annotated_u8) -> annotated_u8 = value
function keep_annotated_u16(value : annotated_u16) -> annotated_u16 = value
function keep_annotated_u32(value : annotated_u32) -> annotated_u32 = value
function keep_annotated_u64(value : annotated_u64) -> annotated_u64 = value

function keep_annotated_i8(value : annotated_i8) -> annotated_i8 = value
function keep_annotated_i16(value : annotated_i16) -> annotated_i16 = value
function keep_annotated_i32(value : annotated_i32) -> annotated_i32 = value
function keep_annotated_i64(value : annotated_i64) -> annotated_i64 = value

function main() -> unit = ()
