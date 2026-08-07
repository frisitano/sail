infix 4 ==
val eq_int = pure { _: "eq_int" } : (int, int) -> bool
val not_bool = pure { _: "not_bool" } : bool -> bool
val identity_bool = pure { _: "identity_bool" } : bool -> bool
overload operator == = {eq_int}

function named_intermediates(value : bool) -> bool = {
    let negated = not_bool(value);
    let restored = not_bool(negated);
    if restored then { value } else { false }
}

/* Boolean negation is operator-like and may directly wrap an already-bound
   condition without requiring an artificial second binding. */
function direct_boolean_negation(value : bool) -> bool =
    if not_bool(value) then { false } else { true }

function direct_else_if(first : bool, second : bool, fallback : bool) -> bool =
    if first then {
        first
    } else if second then {
        second
    } else {
        fallback
    }

function operator_condition(lhs : int, rhs : int, equal : bool, unequal : bool) -> bool =
    if lhs == rhs then { equal } else { unequal }

/* An authored infix expression is not a nested named call even when it is
   passed directly to a function. */
function operator_argument(lhs : int, rhs : int) -> bool = identity_bool(lhs == rhs)
