default Order dec

$include <prelude.sail>

val dependent_existential_tuple : forall 'n. int('n) -> {'m. (int('m), int('n - 'm))}
function dependent_existential_tuple(n) = {
  let (m as 'm) = n;
  (m, n - m)
}
