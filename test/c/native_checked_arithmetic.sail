default Order dec

$include <prelude.sail>
$include <smt.sail>

$[c_repr uint64]
newtype checked_u64 = Checked_u64 : nat

$[c_repr int64]
newtype checked_i64 = Checked_i64 : int

type u64_with_add_headroom = range(0, 2 ^ 64 - 33)
type u64_at_least_95 = range(95, 2 ^ 64 - 1)
type bounded_u64 = range(0, 2 ^ 64 - 1)
type small_u64 = range(0, 100)
type small_u64_product = range(0, 10000)
type small_i64 = range(-100, 100)
type small_i64_sum = range(-200, 200)
type small_i64_product = range(-10000, 10000)
type thirteen_u64 = range(13, 13)
type five_u64 = range(5, 5)
type eight_u64 = range(8, 8)
type minus_thirteen_i64 = range(-13, -13)
type minus_five_i64 = range(-5, -5)
type small_i128 = range(-(2 ^ 65), 2 ^ 65)
type small_i128_sum = range(-(2 ^ 66), 2 ^ 66)
type multiplicand_i128 = range(-(2 ^ 63), 2 ^ 63)
type small_i128_product = range(-(2 ^ 126), 2 ^ 126)
type thirteen_i128 = range(2 ^ 64 + 13, 2 ^ 64 + 13)
type divisor_i128 = range(2 ^ 64 + 5, 2 ^ 64 + 5)

val proven_u64_add_32 : u64_with_add_headroom -> bounded_u64

function proven_u64_add_32(value) = value + 32

val proven_u64_sub_95 : u64_at_least_95 -> bounded_u64

function proven_u64_sub_95(value) = value - 95

val proven_u64_mul : (small_u64, small_u64) -> small_u64_product

function proven_u64_mul(left, right) = left * right

val proven_u64_div : (thirteen_u64, five_u64) -> int

function proven_u64_div(left, right) = tdiv_int(left, right)

val proven_u64_mod : (thirteen_u64, five_u64) -> int

function proven_u64_mod(left, right) = tmod_int(left, right)

val proven_i64_add : (small_i64, small_i64) -> small_i64_sum

function proven_i64_add(left, right) = left + right

val proven_i64_sub : (small_i64, small_i64) -> small_i64_sum

function proven_i64_sub(left, right) = left - right

val proven_i64_mul : (small_i64, small_i64) -> small_i64_product

function proven_i64_mul(left, right) = left * right

val proven_i64_div : (minus_thirteen_i64, minus_five_i64) -> int

function proven_i64_div(left, right) = tdiv_int(left, right)

val proven_i64_mod : (minus_thirteen_i64, minus_five_i64) -> int

function proven_i64_mod(left, right) = tmod_int(left, right)

val proven_i128_add : (small_i128, small_i128) -> small_i128_sum

function proven_i128_add(left, right) = left + right

val proven_i128_sub : (small_i128, small_i128) -> small_i128_sum

function proven_i128_sub(left, right) = left - right

val proven_i128_mul : (multiplicand_i128, multiplicand_i128) -> small_i128_product

function proven_i128_mul(left, right) = left * right

val proven_i128_div : (thirteen_i128, divisor_i128) -> small_i128

function proven_i128_div(left, right) = tdiv_nat(left, right)

val proven_i128_mod : (thirteen_i128, divisor_i128) -> small_i128

function proven_i128_mod(left, right) = tmod_nat(left, right)

val mixed_i128_u64_lte : (small_i128, bounded_u64) -> bool

function mixed_i128_u64_lte(left, right) = left <= right

val mixed_u64_i128_lte : (bounded_u64, small_i128) -> bool

function mixed_u64_i128_lte(left, right) = left <= right

val checked_u64_add : (checked_u64, checked_u64) -> checked_u64

function checked_u64_add(Checked_u64(left), Checked_u64(right)) -> checked_u64 =
    Checked_u64(left + right)

val checked_u64_sub : (checked_u64, checked_u64) -> checked_u64

function checked_u64_sub(Checked_u64(left), Checked_u64(right)) -> checked_u64 =
    if right <= left then Checked_u64(left - right) else Checked_u64(0)

val checked_u64_mul : (checked_u64, checked_u64) -> checked_u64

function checked_u64_mul(Checked_u64(left), Checked_u64(right)) -> checked_u64 =
    Checked_u64(left * right)

val checked_u64_div : (checked_u64, checked_u64) -> checked_u64

function checked_u64_div(Checked_u64(left), Checked_u64(right)) -> checked_u64 =
    if right == 0 then {
        Checked_u64(0)
    } else {
        let quotient = tdiv_int(left, right);
        assert(0 <= quotient);
        Checked_u64(quotient)
    }

val checked_u64_mod : (checked_u64, checked_u64) -> checked_u64

function checked_u64_mod(Checked_u64(left), Checked_u64(right)) -> checked_u64 =
    if right == 0 then Checked_u64(0) else Checked_u64(tmod_int(left, right))

val power_two_tdiv : (checked_u64, eight_u64) -> checked_u64

function power_two_tdiv(Checked_u64(value), divisor) -> checked_u64 = {
    let quotient = tdiv_int(value, divisor);
    assert(0 <= quotient);
    Checked_u64(quotient)
}

val power_two_tmod : (checked_u64, eight_u64) -> checked_u64

function power_two_tmod(Checked_u64(value), divisor) -> checked_u64 =
    Checked_u64(tmod_int(value, divisor))

val power_two_ediv : (checked_u64, eight_u64) -> checked_u64

function power_two_ediv(Checked_u64(value), divisor) -> checked_u64 = {
    let quotient = ediv_int(value, divisor);
    assert(0 <= quotient);
    Checked_u64(quotient)
}

val power_two_emod : (checked_u64, eight_u64) -> checked_u64

function power_two_emod(Checked_u64(value), divisor) -> checked_u64 =
    Checked_u64(emod_int(value, divisor))

/* Represented operands do not determine the representation of a wider
   mathematical result.  In particular, this subtraction may be negative. */
val signed_u64_difference : (checked_u64, checked_u64) -> int

function signed_u64_difference(Checked_u64(left), Checked_u64(right)) -> int =
    left - right

val checked_i64_add : (checked_i64, checked_i64) -> checked_i64

function checked_i64_add(Checked_i64(left), Checked_i64(right)) -> checked_i64 =
    Checked_i64(left + right)

val checked_i64_sub : (checked_i64, checked_i64) -> checked_i64

function checked_i64_sub(Checked_i64(left), Checked_i64(right)) -> checked_i64 =
    Checked_i64(left - right)

val checked_i64_mul : (checked_i64, checked_i64) -> checked_i64

function checked_i64_mul(Checked_i64(left), Checked_i64(right)) -> checked_i64 =
    Checked_i64(left * right)

val checked_i64_div : (checked_i64, checked_i64) -> checked_i64

function checked_i64_div(Checked_i64(left), Checked_i64(right)) -> checked_i64 =
    Checked_i64(tdiv_int(left, right))

val checked_i64_mod : (checked_i64, checked_i64) -> checked_i64

function checked_i64_mod(Checked_i64(left), Checked_i64(right)) -> checked_i64 =
    Checked_i64(tmod_int(left, right))

val signed_tdiv_by_eight : (checked_i64, eight_u64) -> checked_i64

function signed_tdiv_by_eight(Checked_i64(value), divisor) -> checked_i64 =
    Checked_i64(tdiv_int(value, divisor))

val signed_tmod_by_eight : (checked_i64, eight_u64) -> checked_i64

function signed_tmod_by_eight(Checked_i64(value), divisor) -> checked_i64 =
    Checked_i64(tmod_int(value, divisor))

val signed_ediv_by_eight : (checked_i64, eight_u64) -> checked_i64

function signed_ediv_by_eight(Checked_i64(value), divisor) -> checked_i64 =
    Checked_i64(ediv_int(value, divisor))

val signed_emod_by_eight : (checked_i64, eight_u64) -> checked_i64

function signed_emod_by_eight(Checked_i64(value), divisor) -> checked_i64 =
    Checked_i64(emod_int(value, divisor))

function main() -> unit = {
    let Checked_u64(uadd) = checked_u64_add(Checked_u64(2), Checked_u64(3));
    let Checked_u64(usub) = checked_u64_sub(Checked_u64(5), Checked_u64(3));
    let Checked_u64(umul) = checked_u64_mul(Checked_u64(6), Checked_u64(7));
    let Checked_u64(udiv) = checked_u64_div(Checked_u64(13), Checked_u64(5));
    let Checked_u64(umod) = checked_u64_mod(Checked_u64(13), Checked_u64(5));
    let Checked_i64(iadd) = checked_i64_add(Checked_i64(-7), Checked_i64(4));
    let Checked_i64(isub) = checked_i64_sub(Checked_i64(-7), Checked_i64(4));
    let Checked_i64(imul) = checked_i64_mul(Checked_i64(-6), Checked_i64(7));
    let Checked_i64(idiv) = checked_i64_div(Checked_i64(-13), Checked_i64(5));
    let Checked_i64(imod) = checked_i64_mod(Checked_i64(-13), Checked_i64(5));
    assert(uadd == 5 & usub == 2 & umul == 42 & udiv == 2 & umod == 3);
    assert(iadd == -3 & isub == -11 & imul == -42 & idiv == -2 & imod == -3)
}
