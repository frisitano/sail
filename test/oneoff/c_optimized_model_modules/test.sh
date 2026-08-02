#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_optimized_model_modules.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

HOST_INCLUDE="$TMP_DIR/ffi/optimized/include/evmsail/host"
mkdir -p "$HOST_INCLUDE"
cp "$TEST_DIR/host-sentinel.txt" "$HOST_INCLUDE/sentinel.txt"

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail --c-output-dir "$TMP_DIR/ffi/optimized" \
  --c-preserve-type pair --c-preserve-type four_bytes --c-preserve-type fixed_ids \
  --c-preserve run --c-preserve step --c-preserve pick_fixed_id --c-preserve pick_initialized_id \
  --c-preserve pick_guarded_id \
  --c-preserve machine_pick_zero \
  --c-preserve catch_byte \
  "$TEST_DIR/model.sail_project"

SPEC_INCLUDE="$TMP_DIR/ffi/optimized/include"
SPEC_SOURCE="$TMP_DIR/ffi/optimized/src/spec"

for module in base host_contracts machine entry; do
  test -f "$SPEC_INCLUDE/evmsail/spec/$module.h"
  test -f "$SPEC_SOURCE/$module.c"
done
test -f "$SPEC_INCLUDE/evmsail/spec.h"
cmp "$TEST_DIR/host-sentinel.txt" "$HOST_INCLUDE/sentinel.txt"

grep -Fq '#include "evmsail/spec/base.h"' "$SPEC_INCLUDE/evmsail/spec.h"
grep -Fq 'uint8_t' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'struct pair' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t data[4]' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t catch_byte(uint8_t);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint32_t host_mix_exact(uint32_t, uint8_t);' "$SPEC_INCLUDE/evmsail/spec/host_contracts.h"
grep -Fq 'extern uint32_t public_counter;' "$SPEC_INCLUDE/evmsail/spec/machine.h"
grep -Fq 'uint32_t public_counter' "$SPEC_SOURCE/machine.c"
grep -Fq 'void evmsail_model_init(void);' "$SPEC_INCLUDE/evmsail/spec/entry.h"
grep -Fq '__builtin_trap()' "$SPEC_SOURCE/entry.c"
if grep -Fq 'run requires a nonzero byte' "$SPEC_SOURCE/entry.c"; then
  echo 'strict optimized model retained a managed Sail assertion string' >&2
  exit 1
fi

if grep -REq 'sail_int|mpz_|sail_new|sail_free|CREATE\(|COPY\(|RECREATE\(|KILL\(' \
    "$SPEC_INCLUDE/evmsail" "$SPEC_SOURCE"; then
  echo 'strict optimized model contains a managed Sail representation or ownership helper' >&2
  exit 1
fi

# The fixed_index source type proves every access lies inside the 17-element
# POD array.  Preserve that proof through JIB and emit the C member access
# directly instead of routing through a generated vector helper.
awk '
  /^(uint16_t )?pick_(fixed|initialized|guarded)_id\(/ { printing = 1 }
  printing { print }
  printing && /^}/ { printing = 0 }
' "$SPEC_SOURCE/base.c" > "$TMP_DIR/proved_fixed_vector_accesses.c"
test "$(grep -Fc '.data[(size_t)(index)]' "$TMP_DIR/proved_fixed_vector_accesses.c")" -eq 3
if grep -Eq '(fast_)?(unsigned_)?vector_access_' "$TMP_DIR/proved_fixed_vector_accesses.c"; then
  echo 'proved fixed-vector access retained an out-of-line helper call' >&2
  exit 1
fi

# Helper demand is recorded while lowering each module's typed JIB calls.  The
# vector-17 construction helpers are needed by base.c and vector-4 helpers by
# machine.c. Definitions follow the module that selects them, not the source
# module that happened to declare the carrier type.
grep -Fq 'internal_vector_init_vector_17_uint_16' "$SPEC_SOURCE/base.c"
grep -Fq 'internal_vector_update_vector_17_uint_16' "$SPEC_SOURCE/base.c"
test "$(grep -Ec '^static .*vector_' "$SPEC_SOURCE/base.c")" -eq 2
grep -Fq 'internal_vector_init_vector_4_uint_8' "$SPEC_SOURCE/machine.c"
grep -Fq 'internal_vector_update_vector_4_uint_8' "$SPEC_SOURCE/machine.c"
test "$(grep -Ec '^static .*vector_' "$SPEC_SOURCE/machine.c")" -eq 2
for module in host_contracts entry; do
  if grep -Eq '^static .*vector_|^static bool EQUAL\(vector_' "$SPEC_SOURCE/$module.c"; then
    echo "unrelated module $module contains a fixed-vector helper definition" >&2
    exit 1
  fi
done

for source in "$SPEC_SOURCE"/*.c; do
  "$CC" ${CFLAGS:-} -std=c11 -Wall -I "$SPEC_INCLUDE" -c "$source" -o "$TMP_DIR/$(basename "$source" .c).o"
done

"$CC" ${CFLAGS:-} -std=c11 -Wall -I "$SPEC_INCLUDE" \
  "$TEST_DIR/host_stub.c" "$TEST_DIR/harness.c" "$TMP_DIR"/*.o \
  -o "$TMP_DIR/optimized-model-test"
"$TMP_DIR/optimized-model-test"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/negative/ffi/optimized" \
    --c-preserve bad "$TEST_DIR/negative.sail_project" \
    >"$TMP_DIR/negative.stdout" 2>"$TMP_DIR/negative.stderr"; then
  echo 'strict optimized model unexpectedly accepted an unbounded integer' >&2
  exit 1
fi

grep -Eqi 'bounded|unbounded|fixed representation|optimized model' "$TMP_DIR/negative.stderr"
