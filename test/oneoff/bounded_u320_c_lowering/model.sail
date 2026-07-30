default Order dec

$include <prelude.sail>
$include <arith.sail>

type u64_quantity = range(0, 18446744073709551615)
type nonzero_u64_quantity = range(1, 18446744073709551615)
type u160_quantity = range(0, 1461501637330902918203684832716283019655932542975)
type u255_quantity = range(0, 57896044618658097711785492504343953926634992332820282019728792003956564819967)
type u319_quantity = range(0, 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468287)
type nonzero_u319_quantity = range(1, 1067993517960455041197510853084776057301352261178326384973520803911109862890320275011481043468287)
type u320_quantity = range(0, 2135987035920910082395021706169552114602704522356652769947041607822219725780640550022962086936575)

struct U64Holder = {
    value : u64_quantity,
}

/* Specialization narrows this immutable singleton, while the deliberately
 * generic identity below exercises the native-to-managed copy boundary. */
let max_u64_as_int : int = 18446744073709551615

val top_level_int_identity : unit -> int
function top_level_int_identity() = max_u64_as_int

val max_u64_holder : unit -> U64Holder
function max_u64_holder() = struct {
    value = 18446744073709551615,
}

val add_u320 : (u319_quantity, u319_quantity) -> u320_quantity
function add_u320(left, right) = left + right

val sub_u320 : (u319_quantity, u319_quantity) -> u319_quantity
function sub_u320(left, right) = if right <= left then left - right else 0

val mul_u320 : (u160_quantity, u160_quantity) -> u320_quantity
function mul_u320(left, right) = left * right

val add_u320_u64 : (u319_quantity, u64_quantity) -> u320_quantity
function add_u320_u64(left, right) = left + right

val sub_u320_u64 : (u319_quantity, u64_quantity) -> u319_quantity
function sub_u320_u64(left, right) = if right <= left then left - right else 0

val mul_u320_u64 : (u255_quantity, u64_quantity) -> u319_quantity
function mul_u320_u64(left, right) = left * right

val div_u320_u64 : (u319_quantity, nonzero_u64_quantity) -> u319_quantity
function div_u320_u64(left, right) = tdiv_nat(left, right)

val mod_u320_u64 : (u319_quantity, nonzero_u64_quantity) -> u64_quantity
function mod_u320_u64(left, right) = tmod_nat(left, right)

val div_u320 : (u319_quantity, nonzero_u319_quantity) -> u319_quantity
function div_u320(left, right) = tdiv_nat(left, right)

val mod_u320 : (u319_quantity, nonzero_u319_quantity) -> u319_quantity
function mod_u320(left, right) = tmod_nat(left, right)

val lt_u320 : (u319_quantity, u319_quantity) -> bool
function lt_u320(left, right) = left < right

val lteq_u320 : (u319_quantity, u319_quantity) -> bool
function lteq_u320(left, right) = left <= right

val gt_u320 : (u319_quantity, u319_quantity) -> bool
function gt_u320(left, right) = left > right

val gteq_u320 : (u319_quantity, u319_quantity) -> bool
function gteq_u320(left, right) = left >= right

val eq_u320 : (u319_quantity, u319_quantity) -> bool
function eq_u320(left, right) = left == right

val neq_u320 : (u319_quantity, u319_quantity) -> bool
function neq_u320(left, right) = left != right

val lt_u320_u64 : (u319_quantity, u64_quantity) -> bool
function lt_u320_u64(left, right) = left < right

val eq_u320_u64 : (u319_quantity, u64_quantity) -> bool
function eq_u320_u64(left, right) = left == right

val widen_u320_to_nat : (bool, u319_quantity, u319_quantity) -> nat
function widen_u320_to_nat(use_zero, left, right) =
    if use_zero then 0 else add_u320(left, right)

function main() -> unit = ()
