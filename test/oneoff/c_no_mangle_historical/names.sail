default Order dec

$include <prelude.sail>

type byte_pair = (bits(8), bits(8))

val add_pair : byte_pair -> bits(8)

function add_pair((left, right)) = left + right

val increment_twice : bits(8) -> bits(8)

function increment_twice(result) = {
  let tmp = result + 0x01;
  tmp + 0x01
}

// `restrict` is a C keyword, while `zrestrict` collides with its historical
// zencoded fallback. Together they exercise fallback and collision suffixing.
val restrict : bits(8) -> bits(8)

function restrict(value) = value

val zrestrict : bits(8) -> bits(8)

function zrestrict(value) = value

val keep_if : forall 'a. (bool, 'a) -> option('a)

function keep_if(condition, value) =
  if condition then Some(value) else None()

val main : unit -> unit

function main() = {
  let account : byte_pair = (0x01, 0x02);
  assert(add_pair(account) == 0x03);
  assert(increment_twice(0x01) == 0x03);
  assert(restrict(0x04) == 0x04);
  assert(zrestrict(0x05) == 0x05);
  let selected : option(bits(8)) = keep_if(true, 0x2A);
  assert(match selected { Some(value) => value == 0x2A, None() => false })
}
