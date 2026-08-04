#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$TEST_DIR/../../.." && pwd)
SAIL=${SAIL:-sail}
LEAN=${LEAN:-lean}
COQC=${COQC:-coqc}
TMP_ROOT=${AGENT_TMPDIR:-"$ROOT/.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/specialization_plan.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT
mkdir -p "$TMP_DIR/with" "$TMP_DIR/repeated" "$TMP_DIR/readable" "$TMP_DIR/configured" \
  "$TMP_DIR/policy-checked" "$TMP_DIR/policy-all" "$TMP_DIR/policy-assumed" "$TMP_DIR/without"

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

cd "$ROOT"
MODEL="$TEST_DIR/model.sail"
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
  --c-specialization-plan-human "$TMP_DIR/plan-a.md" \
  --c-specialization-obligations-lean "$TMP_DIR/SpecializationObligationsA.lean" \
  --c-specialization-obligations-coq "$TMP_DIR/SpecializationObligationsA.v"

# Repeated compilation must be byte-identical.
compile_core "$TMP_DIR/repeated/model" "$@" \
  --c-specialization-plan "$TMP_DIR/plan-b.json" \
  --c-specialization-obligations-lean "$TMP_DIR/SpecializationObligationsB.lean" \
  --c-specialization-obligations-coq "$TMP_DIR/SpecializationObligationsB.v"
cmp "$TMP_DIR/plan-a.json" "$TMP_DIR/plan-b.json"
cmp "$TMP_DIR/SpecializationObligationsA.lean" "$TMP_DIR/SpecializationObligationsB.lean"
cmp "$TMP_DIR/SpecializationObligationsA.v" "$TMP_DIR/SpecializationObligationsB.v"

# Native outputs contain definitions and a completeness record, but never
# compiler-supplied proof shortcuts. Both files compile independently.
if grep -Eiq '(^|[^[:alnum:]_])(sorry|axiom|admitted)([^[:alnum:]_]|$)' \
  "$TMP_DIR/SpecializationObligationsA.lean" "$TMP_DIR/SpecializationObligationsA.v"
then
  echo 'native specialization obligations contain a forbidden proof shortcut' >&2
  exit 1
fi
grep -Fq 'structure Complete' "$TMP_DIR/SpecializationObligationsA.lean"
grep -Fq 'Record Complete' "$TMP_DIR/SpecializationObligationsA.v"
"$LEAN" -o "$TMP_DIR/SpecializationObligationsA.olean" "$TMP_DIR/SpecializationObligationsA.lean"
cp "$TEST_DIR/SemanticStrength.lean" "$TMP_DIR/SemanticStrength.lean"
LEAN_PATH="$TMP_DIR" "$LEAN" "$TMP_DIR/SemanticStrength.lean"
"$COQC" -Q "$TMP_DIR" "" "$TMP_DIR/SpecializationObligationsA.v"
cp "$TEST_DIR/SemanticStrength.v" "$TMP_DIR/SemanticStrength.v"
"$COQC" -Q "$TMP_DIR" "" "$TMP_DIR/SemanticStrength.v"

python3 - \
  "$TMP_DIR/SpecializationObligationsA.lean" \
  "$TMP_DIR/SpecializationObligationsA.v" \
  > "$TMP_DIR/native-obligation-digests.txt" <<'PY'
import hashlib
import pathlib
import sys

for name, path in zip(("lean", "coq"), sys.argv[1:]):
    print(name, hashlib.sha256(pathlib.Path(path).read_bytes()).hexdigest())
PY
cmp "$TEST_DIR/expected-native-obligation-digests.txt" "$TMP_DIR/native-obligation-digests.txt"

test "$(jq -r '.configuration.narrowing_policy' "$TMP_DIR/plan-a.json")" = proven
test "$(jq '[.clones[].conversions[] | select(.validation == "proven" or .validation == "checked")] | length' "$TMP_DIR/plan-a.json")" -gt 0

# The strict normative schema must evolve with the emitted plan. Validate it
# when the optional Python package is available, without making it a compiler
# test dependency.
python3 - "$ROOT/doc/specialization-plan/schema-v1.json" "$TMP_DIR/plan-a.json" <<'PY'
import json
import pathlib
import sys

try:
    import jsonschema
except ModuleNotFoundError:
    raise SystemExit(0)

schema = json.loads(pathlib.Path(sys.argv[1]).read_text())
plan = json.loads(pathlib.Path(sys.argv[2]).read_text())
jsonschema.Draft202012Validator(schema).validate(plan)
PY

# C naming is descriptive only and may not perturb the machine plan.
compile_core "$TMP_DIR/readable/model" "$@" --c-no-mangle \
  --c-specialization-plan "$TMP_DIR/plan-readable.json" \
  --c-specialization-plan-human "$TMP_DIR/plan-readable.md"
cmp "$TMP_DIR/plan-a.json" "$TMP_DIR/plan-readable.json"
grep -Fq 'Sail source name:' "$TMP_DIR/plan-readable.md"
grep -Fq 'Generated clone name:' "$TMP_DIR/plan-readable.md"
grep -Fq 'Emitted backend symbol:' "$TMP_DIR/plan-readable.md"

# Effective representation-specialization settings contribute to configuration
# identity even when they happen not to change this model's clone set.
compile_core "$TMP_DIR/configured/model" "$@" --c-require-bounded-int \
  --c-specialization-plan "$TMP_DIR/plan-configured.json"
test \
  "$(jq -r '.configuration.id' "$TMP_DIR/plan-a.json")" != \
  "$(jq -r '.configuration.id' "$TMP_DIR/plan-configured.json")"

# Narrowing policy is part of the effective configuration and every recorded
# conversion states whether it is checked, proven, or assumed.
compile_core "$TMP_DIR/policy-checked/model" "$@" --c-narrowing=checked \
  --c-specialization-plan "$TMP_DIR/plan-checked.json" \
  --c-specialization-obligations-lean "$TMP_DIR/CheckedObligations.lean" \
  --c-specialization-obligations-coq "$TMP_DIR/CheckedObligations.v"
compile_core "$TMP_DIR/policy-all/model" "$@" --c-narrowing=all \
  --c-specialization-plan "$TMP_DIR/plan-all.json"
test "$(jq -r '.configuration.narrowing_policy' "$TMP_DIR/plan-checked.json")" = checked
test "$(jq -r '.configuration.narrowing_policy' "$TMP_DIR/plan-all.json")" = all
test \
  "$(jq -r '.configuration.id' "$TMP_DIR/plan-checked.json")" != \
  "$(jq -r '.configuration.id' "$TMP_DIR/plan-all.json")"
grep -Fq '"checked" semanticValue representedValue' "$TMP_DIR/CheckedObligations.lean"
grep -Fq '"checked" semanticValue representedValue' "$TMP_DIR/CheckedObligations.v"
grep -Fq '"proven" semanticValue representedValue' "$TMP_DIR/SpecializationObligationsA.lean"
grep -Fq '"proven" semanticValue representedValue' "$TMP_DIR/SpecializationObligationsA.v"
"$LEAN" -o "$TMP_DIR/CheckedObligations.olean" "$TMP_DIR/CheckedObligations.lean"
"$COQC" -Q "$TMP_DIR" "" "$TMP_DIR/CheckedObligations.v"

# An explicitly narrow representation with no range proof is recorded as an
# assumption only in all mode; proof-backed conversions remain proven.
"$SAIL" "$@" --no-color --no-memo-z3 -O -c --c-specialize --c-no-main \
  --c-narrowing=all \
  --c-preserve compact_word_boundary \
  --c-specialization-plan "$TMP_DIR/plan-assumed.json" \
  --c-specialization-obligations-lean "$TMP_DIR/AssumedObligations.lean" \
  --c-specialization-obligations-coq "$TMP_DIR/AssumedObligations.v" \
  "$TEST_DIR/assumed_model.sail" -o "$TMP_DIR/policy-assumed/model"
test "$(jq '[.clones[].conversions[] | select(.validation == "assumed")] | length' "$TMP_DIR/plan-assumed.json")" -gt 0
test "$(jq '[.assumptions[] | select(.kind == "unchecked_narrowing")] | length' "$TMP_DIR/plan-assumed.json")" -eq 1
grep -Fq '"assumed" semanticValue representedValue' "$TMP_DIR/AssumedObligations.lean"
grep -Fq '"assumed" semanticValue representedValue' "$TMP_DIR/AssumedObligations.v"
"$LEAN" -o "$TMP_DIR/AssumedObligations.olean" "$TMP_DIR/AssumedObligations.lean"
"$COQC" -Q "$TMP_DIR" "" "$TMP_DIR/AssumedObligations.v"

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
  --c-specialization-obligations-lean "$TMP_DIR/ExternObligations.lean" \
  --c-specialization-obligations-coq "$TMP_DIR/ExternObligations.v" \
  "$TEST_DIR/extern_model.sail" -o "$TMP_DIR/extern"
python3 "$ROOT/tools/specialization_plan_checker.py" "$TMP_DIR/extern.json"
test "$(jq '.unresolved_obligations | length' "$TMP_DIR/extern.json")" -eq 1
test "$(jq '[.clones[].extern_contracts[]] | length' "$TMP_DIR/extern.json")" -eq 1
grep -Fq 'S.externEval' "$TMP_DIR/ExternObligations.lean"
grep -Fq 'sem_extern_eval S' "$TMP_DIR/ExternObligations.v"
"$LEAN" -o "$TMP_DIR/ExternObligations.olean" "$TMP_DIR/ExternObligations.lean"
cp "$TEST_DIR/ExternSemanticStrength.lean" "$TMP_DIR/ExternSemanticStrength.lean"
LEAN_PATH="$TMP_DIR" "$LEAN" "$TMP_DIR/ExternSemanticStrength.lean"
"$COQC" -Q "$TMP_DIR" "" "$TMP_DIR/ExternObligations.v"
cp "$TEST_DIR/ExternSemanticStrength.v" "$TMP_DIR/ExternSemanticStrength.v"
"$COQC" -Q "$TMP_DIR" "" "$TMP_DIR/ExternSemanticStrength.v"

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
  --c-specialization-obligations-lean "$TMP_DIR/disabled.lean" \
  "$TEST_DIR/extern_model.sail" -o "$TMP_DIR/disabled" \
  2>"$TMP_DIR/disabled.err"
then
  echo 'specialization obligations were emitted without --c-specialize' >&2
  exit 1
fi
grep -Fq 'specialization output requires --c-specialize' "$TMP_DIR/disabled.err"
