default Order dec

$include <prelude.sail>

type bounded_byte = range(0, 255)

val bounded_byte : forall 'value, 0 <= 'value & 'value < 256.
  int('value) -> bounded_byte
function bounded_byte(value) = value

val divide_bounded_byte : forall 'dividend 'divisor,
  0 <= 'dividend & 'dividend < 256 &
  0 <= 'divisor & 'divisor < 256.
  (int('dividend), int('divisor)) -> bounded_byte
function divide_bounded_byte(dividend, divisor) = {
  if divisor == 0 then 0
  else {
    let quotient = tdiv_nat(dividend, divisor);
    bounded_byte(quotient)
  }
}

function main() -> unit = ()
