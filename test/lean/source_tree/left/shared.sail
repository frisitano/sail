struct LeanKeywordFields = {
  block : int,
  prefix : int,
}

struct NestedFields = {
  prefix : int,
  block : LeanKeywordFields,
}

register source_tree_register : int = 3

function effectful_value() -> int = source_tree_register

function left_value() -> int = {
  let have : LeanKeywordFields = struct { block = 1, prefix = 2 };
  have.block
}

function effectful_list() -> list(int) = [|effectful_value()|]

function effectful_cons(xs : list(int)) -> list(int) = effectful_value() :: xs

function effectful_record() -> NestedFields = struct {
  prefix = effectful_value(),
  block = struct { block = 1, prefix = 2 },
}
