val observe = impure { c: "observe" } : unit -> bool

function not_bool(value : bool) -> bool = if value then { false } else { true }

function eq_bool(lhs : bool, rhs : bool) -> bool = if lhs then {
    rhs
} else {
    not_bool(rhs)
}

function neq_bool(lhs : bool, rhs : bool) -> bool = not_bool(eq_bool(lhs, rhs))

function double_not(value : bool) -> bool = not_bool(not_bool(value))

function compare_true(value : bool) -> bool = eq_bool(value, true)

function compare_false_not_equal(value : bool) -> bool = neq_bool(value, false)

function negate_literal() -> bool = not_bool(true)

function identity_conditional(value : bool) -> bool = if value then { true } else { false }

function constant_conditional(value : bool) -> bool = if true then { value } else { false }

function duplicate_branches(value : bool) -> bool =
    if value then {
        not_bool(value)
    } else {
        not_bool(value)
    }

/* Removing this conditional would also remove an observable call, so equal
   branches alone are not sufficient for the duplicate-branch rule. */
function effectful_duplicate_branches() -> bool =
    if observe() then { true } else { true }

/* Ignoring the operator-like outer negation must not hide the real call
   nested inside the condition. */
function negated_call_condition() -> bool =
    if not_bool(observe()) then { false } else { true }

function empty_conditional(value : bool) -> unit =
    if value then {
        ()
    }

function conditional_assignment(flag : bool, left : bool, right : bool) -> bool = {
    var selected : bool = false;
    if flag then {
        selected = left
    } else {
        selected = right
    };
    selected
}

function else_after_terminal(value : bool) -> bool = if value then {
    exit(())
} else {
    observe()
}

function nested_else_if(first : bool, second : bool, fallback : bool) -> bool =
    if first then {
        first
    } else {
        if second then { second } else { fallback }
    }

/* A guard followed by the continuation is already the desired source form.
   Jib may represent the continuation as an else branch, but the source linter
   must not attribute that backend structure to this conditional. */
function terminal_guard(value : bool) -> bool = {
    if value then {
        exit(())
    };
    observe()
}

function tail_unit_guard(value : bool) -> unit =
    if value then {
        ()
    } else {
        let _ = observe();
        ()
    }

/* Returning from the empty branch would incorrectly skip the final
   expression, so only tail conditionals are guard-clause candidates. */
function non_tail_unit_branch(value : bool) -> bool = {
    if value then {
        ()
    } else {
        let _ = observe();
        ()
    };
    value
}

function trivial_alias(value : bool) -> bool = let returned = value in
returned

function single_use_temporary(value : bool) -> bool = {
    let tmp = not_bool(value);
    if tmp then { false } else { value }
}

function dead_pure_binding(value : bool) -> bool = {
    let _ = not_bool(value);
    value
}

/* A semantic source name is useful documentation even when the pure binding
   has one use, so it must not be diagnosed as a temporary. */
function meaningful_pure_binding(value : bool) -> bool = {
    let parsed = not_bool(value);
    if parsed then { false } else { value }
}

/* A generically named binding must also be retained when its initializer is
   effectful. */
function effectful_temporary() -> bool = {
    let tmp = observe();
    if tmp then { false } else { true }
}

/* This named binding deliberately evaluates an effect once and is used twice.
   It must not be diagnosed as a trivial or inlineable source alias. */
function meaningful_effectful_binding() -> bool = {
    let observed = observe();
    if observed then { observed } else { false }
}

function nested_function_call(value : bool) -> bool =
    eq_bool(not_bool(value), value)

function function_call_condition(value : bool) -> bool =
    if not_bool(value) then { value } else { false }

function function_call_assertion(value : bool) -> bool = {
    assert(not_bool(value), "predicate");
    value
}
