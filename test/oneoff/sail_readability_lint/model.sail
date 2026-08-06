val observe = impure {c: "observe"} : unit -> bool

function not_bool(value : bool) -> bool = if value then false else true

function eq_bool(lhs : bool, rhs : bool) -> bool = if lhs then rhs else not_bool(rhs)

function double_not(value : bool) -> bool = not_bool(not_bool(value))

function compare_true(value : bool) -> bool = eq_bool(value, true)

function identity_conditional(value : bool) -> bool = if value then true else false

function trivial_alias(value : bool) -> bool = let returned = value in returned

/* This named binding deliberately evaluates an effect once and is used twice.
   It must not be diagnosed as a trivial or inlineable source alias. */
function meaningful_effectful_binding() -> bool = {
  let observed = observe();
  if observed then observed else false
}
