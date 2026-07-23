default Order dec

$include <prelude.sail>
$include <arith.sail>

type u65_quantity = range(0, 36893488147419103231)
type u127_quantity = range(0, 170141183460469231731687303715884105727)
type u128_quantity = range(0, 340282366920938463463374607431768211455)
type u191_quantity = range(0, 3138550867693340381917894711603833208051177722232017256447)
type u255_quantity = range(0, 57896044618658097711785492504343953926634992332820282019728792003956564819967)
type u256_quantity = range(0, 115792089237316195423570985008687907853269984665640564039457584007913129639935)
type u256_high_quantity = range(340282366920938463463374607431768211456, 115792089237316195423570985008687907853269984665640564039457584007913129639935)
type u257_quantity = range(0, 231584178474632390847141970017375815706539969331281128078915168015826259279870)

val add_widen_128 : (u128_quantity, u128_quantity) -> range(0, 680564733841876926926749214863536422910)
function add_widen_128(left, right) = left + right

val mul_widen_128 : (u128_quantity, u128_quantity) -> u256_quantity
function mul_widen_128(left, right) = left * right

val add_widen_256 : (u256_quantity, u256_quantity) -> u257_quantity
function add_widen_256(left, right) = left + right

val add_256_128 : (u255_quantity, u127_quantity) -> u256_quantity
function add_256_128(left, right) = left + right

val mul_256_128 : (u191_quantity, u65_quantity) -> u256_quantity
function mul_256_128(left, right) = left * right

val sub_256_128 : (u256_high_quantity, u128_quantity) -> u256_quantity
function sub_256_128(left, right) = left - right

val div_256_128 : (u256_quantity, range(1, 340282366920938463463374607431768211455)) -> u256_quantity
function div_256_128(left, right) = tdiv_nat(left, right)

val mod_256_128 : (u256_quantity, range(1, 340282366920938463463374607431768211455)) -> u128_quantity
function mod_256_128(left, right) = tmod_nat(left, right)

val lt_256_128 : (u256_quantity, u128_quantity) -> bool
function lt_256_128(left, right) = left < right

val eq_256_128 : (u256_quantity, u128_quantity) -> bool
function eq_256_128(left, right) = left == right

val neq_128_256 : (u128_quantity, u256_quantity) -> bool
function neq_128_256(left, right) = left != right

val lt_128_256 : (u128_quantity, u256_quantity) -> bool
function lt_128_256(left, right) = left < right

val sub_128_256 : (u128_quantity, u256_quantity) -> u128_quantity
function sub_128_256(left, right) = if right <= left then left - right else 0

val div_128_256 : (u128_quantity, range(1, 115792089237316195423570985008687907853269984665640564039457584007913129639935)) -> u128_quantity
function div_128_256(left, right) = tdiv_nat(left, right)

val mod_128_256 : (u128_quantity, range(1, 115792089237316195423570985008687907853269984665640564039457584007913129639935)) -> u128_quantity
function mod_128_256(left, right) = tmod_nat(left, right)

function main() -> unit = ()
