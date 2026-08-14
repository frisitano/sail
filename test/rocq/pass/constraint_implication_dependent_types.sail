default Order dec

$include <prelude.sail>

struct Nonnegative('n : Int), 0 <= 'n = {
  value : int('n),
}

val make_nonnegative : forall 'n, 0 <= 'n. int('n) -> Nonnegative('n)
function make_nonnegative(n) = struct { value = n }

val pack_positive : int -> option({
  'n, 0 < 'n. Nonnegative('n)
})
function pack_positive(n) =
  if 0 < n then {
    let value = make_nonnegative(n);
    Some(value)
  }
  else
    None()

function main() -> unit = ()
