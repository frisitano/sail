default Order dec

$include <prelude.sail>

type bounded_count = range(0, 64)

function leading_zero_count(value : bits(64)) -> bounded_count = {
  let count : bounded_count = count_leading_zeros(value);
  count
}

function trailing_zero_count(value : bits(64)) -> bounded_count = {
  let count : bounded_count = count_trailing_zeros(value);
  count
}

function main() -> unit = ()
