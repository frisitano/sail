default Order dec

$include <prelude.sail>

type bounded = {'n, 0 <= 'n. int('n)}
type bounded_vector = vector(2, dec, bounded)

val dependent_vector_init : bounded -> bounded_vector
function dependent_vector_init(first) = {
  var values : bounded_vector = vector_init(2, first);
  values[0] = first;
  values
}
