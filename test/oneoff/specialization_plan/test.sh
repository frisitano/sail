#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$TEST_DIR/../../.." && pwd)
SAIL=${SAIL:-sail}
LEAN=${LEAN:-lean}
TMP_ROOT=${AGENT_TMPDIR:-"$ROOT/.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/specialization_plan.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT
mkdir -p "$TMP_DIR/with" "$TMP_DIR/repeated" "$TMP_DIR/readable" "$TMP_DIR/without"

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

cd "$ROOT"
MODEL="test/oneoff/c_function_representation_specialization/model.sail"
COMMON_ARGS="--no-color --no-memo-z3 -O --Oconstant-fold -c --c-specialize --c-no-main"

compile_core() {
  output=$1
  shift
  "$SAIL" "$@" $COMMON_ARGS \
    --c-preserve bounded_recursive_once \
    --c-preserve aggregate_encoded_length \
    "$MODEL" -o "$output"
}

# Machine and human emission; the two products deliberately have different
# backend-name policies.
compile_core "$TMP_DIR/with/model" "$@" \
  --c-specialization-plan "$TMP_DIR/plan-a.json" \
  --c-specialization-plan-human "$TMP_DIR/plan-a.md"

# Repeated compilation must be byte-identical.
compile_core "$TMP_DIR/repeated/model" "$@" \
  --c-specialization-plan "$TMP_DIR/plan-b.json"
cmp "$TMP_DIR/plan-a.json" "$TMP_DIR/plan-b.json"

# C naming is descriptive only and may not perturb the machine plan.
compile_core "$TMP_DIR/readable/model" "$@" --c-no-mangle \
  --c-specialization-plan "$TMP_DIR/plan-readable.json" \
  --c-specialization-plan-human "$TMP_DIR/plan-readable.md"
cmp "$TMP_DIR/plan-a.json" "$TMP_DIR/plan-readable.json"
grep -Fq 'Sail source name:' "$TMP_DIR/plan-readable.md"
grep -Fq 'Generated clone name:' "$TMP_DIR/plan-readable.md"
grep -Fq 'Emitted backend symbol:' "$TMP_DIR/plan-readable.md"

# With emission disabled, generated C and headers are unchanged.
compile_core "$TMP_DIR/without/model" "$@"
cmp "$TMP_DIR/with/model.c" "$TMP_DIR/without/model.c"
cmp "$TMP_DIR/with/model.h" "$TMP_DIR/without/model.h"

# Independent structural validation and a compact golden summary cover
# bounded clones, conversions, recursive calls, and all obligation classes.
python3 "$ROOT/tools/specialization_plan_checker.py" "$TMP_DIR/plan-a.json" \
  --emit-lean "$TMP_DIR/ProofFixture.lean"
jq '{
  schema_version,
  clone_sources: [.clones[].source_name] | sort,
  recursive_clone_count: [.clones[] | select(.recursive)] | length,
  conversion_count: [.clones[].conversions[]] | length,
  inferred_bounds: [.clones[].representation_choices[].inferred_bound | select(. != null)] | unique | sort,
  obligation_count: [.clones[].obligations[]] | length,
  required_obligation_kinds: [.clones[].obligations[].kind] | unique | sort,
  unresolved_count: .unresolved_obligations | length
}' "$TMP_DIR/plan-a.json" > "$TMP_DIR/summary.json"
cmp "$TEST_DIR/expected-summary.json" "$TMP_DIR/summary.json"
cmp "$TEST_DIR/ProofFixture.lean" "$TMP_DIR/ProofFixture.lean"
"$LEAN" "$TMP_DIR/ProofFixture.lean"

# Extern calls are explicit contracts and remain unresolved until independent
# evidence is supplied.
"$SAIL" "$@" --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-preserve bounded_foreign_bridge \
  --c-specialization-plan "$TMP_DIR/extern.json" \
  "$TEST_DIR/extern_model.sail" -o "$TMP_DIR/extern"
python3 "$ROOT/tools/specialization_plan_checker.py" "$TMP_DIR/extern.json"
test "$(jq '.unresolved_obligations | length' "$TMP_DIR/extern.json")" -eq 1
test "$(jq '[.clones[].extern_contracts[]] | length' "$TMP_DIR/extern.json")" -eq 1

# Comparison is stable-ID based and reports no semantic change for an
# identical plan.
python3 "$ROOT/tools/specialization_plan_checker.py" "$TMP_DIR/plan-b.json" \
  --compare "$TMP_DIR/plan-a.json" \
  --comparison-output "$TMP_DIR/comparison.md"
grep -Fq -- '- Added clones: 0' "$TMP_DIR/comparison.md"
grep -Fq -- '- Removed clones: 0' "$TMP_DIR/comparison.md"
grep -Fq -- '- Changed clones: 0' "$TMP_DIR/comparison.md"

# The checker must reject duplicate IDs, non-canonical order, dangling
# references, and missing required obligations.
python3 - "$TMP_DIR/plan-a.json" "$TMP_DIR" <<'PY'
import copy
import json
import pathlib
import sys

source = json.loads(pathlib.Path(sys.argv[1]).read_text())
target = pathlib.Path(sys.argv[2])

variants = {}

duplicate = copy.deepcopy(source)
duplicate["clones"].insert(1, copy.deepcopy(duplicate["clones"][0]))
variants["duplicate"] = duplicate

unordered = copy.deepcopy(source)
unordered["clones"].reverse()
variants["unordered"] = unordered

dangling = copy.deepcopy(source)
dangling["clones"][0]["location"]["input"] = "md5:00000000000000000000000000000000"
variants["dangling"] = dangling

missing = copy.deepcopy(source)
missing["clones"][0]["obligations"] = [
    obligation
    for obligation in missing["clones"][0]["obligations"]
    if obligation["kind"] != "conversion_correctness"
]
variants["missing"] = missing

for name, value in variants.items():
    (target / f"invalid-{name}.json").write_text(json.dumps(value) + "\n")
PY

for invalid in duplicate unordered dangling missing; do
  if python3 "$ROOT/tools/specialization_plan_checker.py" "$TMP_DIR/invalid-$invalid.json"; then
    echo "checker accepted invalid $invalid plan" >&2
    exit 1
  fi
done

# Output flags are intentionally unavailable without specialization.
if "$SAIL" "$@" --no-color -c --c-no-main \
  --c-specialization-plan "$TMP_DIR/disabled.json" \
  "$TEST_DIR/extern_model.sail" -o "$TMP_DIR/disabled" \
  2>"$TMP_DIR/disabled.err"
then
  echo 'specialization plan was emitted without --c-specialize' >&2
  exit 1
fi
grep -Fq 'specialization-plan output requires --c-specialize' "$TMP_DIR/disabled.err"
