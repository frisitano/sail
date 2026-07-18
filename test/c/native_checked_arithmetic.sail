default Order dec

$include <prelude.sail>

$[c_repr uint64]
newtype checked_u64 = Checked_u64 : nat

$[c_repr int64]
newtype checked_i64 = Checked_i64 : int

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
