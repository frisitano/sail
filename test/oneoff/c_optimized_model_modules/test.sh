#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_optimized_model_modules.XXXXXX")
cleanup() {
  if [ "${KEEP_TEST_TMP:-0}" = 1 ]; then
    printf 'preserved test output: %s\n' "$TMP_DIR" >&2
  else
    rm -rf "$TMP_DIR"
  fi
}
trap cleanup EXIT

if [ -n "${SAIL_PLUGIN:-}" ]; then
  set -- -plugin "$SAIL_PLUGIN"
else
  set --
fi

HOST_INCLUDE="$TMP_DIR/ffi/optimized/include/evmsail/host"
mkdir -p "$HOST_INCLUDE"
cp "$TEST_DIR/host-sentinel.txt" "$HOST_INCLUDE/sentinel.txt"
cp "$TEST_DIR/external_types.h" "$HOST_INCLUDE/types.h"

"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail --c-output-dir "$TMP_DIR/ffi/optimized" \
  --c-optimized-include-dir "$TMP_DIR/ffi/optimized/include" \
  --c-optimized-external-type pair=evmsail/host/types.h \
  --c-optimized-external-type byte_slice=evmsail/host/types.h \
  --c-optimized-external-type byte_slice_small=evmsail/host/types.h \
  --c-optimized-byte-pointer-field byte_slice.bytes=test_bytes_at \
  --c-optimized-byte-pointer-field byte_slice_small.bytes=test_bytes_at \
  --c-optimized-byte-pointer-field analyzed_code.bytes=test_bytes_at \
  --c-optimized-byte-pointer-type jump_table_index=test_jumpdests_at \
  --c-preserve-type pair --c-preserve-type byte_slice --c-preserve-type byte_slice_small \
  --c-preserve-type analyzed_code \
  --c-preserve-type four_bytes --c-preserve-type fixed_ids \
  --c-preserve-type fixed_ids_box \
  --c-preserve pair_sum \
  --c-preserve byte_slice_at --c-preserve byte_slice_small_at --c-preserve byte_slice_same_start \
  --c-preserve byte_slice_next --c-preserve byte_slice_advance --c-preserve byte_slice_distance \
  --c-preserve jumpdest_from_offset --c-preserve empty_jumpdest --c-preserve empty_direct_jumpdest \
  --c-preserve allocated_jumpdest \
  --c-preserve analyzed_code_at --c-preserve analyzed_code_copy \
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
printf '%s\n' base.c host_contracts.c machine.c entry.c > "$TMP_DIR/expected-sources.list"
cmp "$TMP_DIR/expected-sources.list" "$SPEC_SOURCE/sources.list"
cmp "$TEST_DIR/host-sentinel.txt" "$HOST_INCLUDE/sentinel.txt"

grep -Fq '#include "evmsail/spec/base.h"' "$SPEC_INCLUDE/evmsail/spec.h"
grep -Fq '#include "evmsail/host/types.h"' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint8_t' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'uint16_t pair_sum(struct pair);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'struct byte_slice byte_slice_at(uint8_t, uint8_t);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Fq 'test_bytes_at((uint64_t)(off))' "$SPEC_SOURCE/base.c"
grep -Fq 'struct analyzed_code {' "$SPEC_INCLUDE/evmsail/spec/base.h"
test "$(grep -Fc 'uint8_t *' "$SPEC_INCLUDE/evmsail/spec/base.h")" -ge 2
grep -Fq 'test_jumpdests_at((uint64_t)(off))' "$SPEC_SOURCE/base.c"
grep -Eq 'uint8_t \* *jumpdest_from_offset\(uint8_t\);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Eq 'extern uint8_t \* *EMPTY_DIRECT_JUMP_TABLE;' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Eq 'uint8_t \* *empty_direct_jumpdest\(unit\);' "$SPEC_INCLUDE/evmsail/spec/base.h"
grep -Eq '= NULL;' "$SPEC_SOURCE/base.c"
grep -Eq 'EMPTY_DIRECT_JUMP_TABLE = z[[:alnum:]]+;' "$SPEC_SOURCE/base.c"
if grep -Eq '__direct\)|__direct\(' "$SPEC_SOURCE/base.c"; then
  echo 'adapter-free byte pointer emitted a synthetic offset adapter call' >&2
  exit 1
fi
grep -Eq 'uint8_t \* *allocated_jumpdest\(uint8_t\);' "$SPEC_INCLUDE/evmsail/spec/host_contracts.h"
grep -Fq 'test_jumpdest_alloc(off)' "$SPEC_SOURCE/host_contracts.c"
grep -Fq '= (off +' "$SPEC_SOURCE/base.c"
grep -Eq 'z[[:alnum:]]+ - z[[:alnum:]]+\)' "$SPEC_SOURCE/base.c"
if grep -Fq 'CONVERT_OF(mach_uint, byte_pointer_test_bytes_at)' "$SPEC_SOURCE/base.c"; then
  echo 'optimized extraction converted a byte pointer back to its semantic integer offset' >&2
  exit 1
fi
if grep -REq 'struct pair[[:space:]]*\{' "$SPEC_INCLUDE/evmsail/spec"; then
  echo 'optimized extraction redefined an externally owned struct' >&2
  exit 1
fi
if grep -REq 'struct byte_slice[[:space:]]*\{' "$SPEC_INCLUDE/evmsail/spec"; then
  echo 'optimized extraction redefined the externally owned byte-pointer struct' >&2
  exit 1
fi
if grep -REq 'struct byte_slice_small[[:space:]]*\{' "$SPEC_INCLUDE/evmsail/spec"; then
  echo 'optimized extraction redefined the second externally owned byte-pointer struct' >&2
  exit 1
fi
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
test "$(grep -Ec '^static .*vector_.*\{$' "$SPEC_SOURCE/base.c")" -eq 3
grep -Fq 'internal_vector_init_vector_4_uint_8' "$SPEC_SOURCE/machine.c"
grep -Fq 'internal_vector_update_vector_4_uint_8' "$SPEC_SOURCE/machine.c"
test "$(grep -Ec '^static .*vector_.*\{$' "$SPEC_SOURCE/machine.c")" -eq 3
for module in host_contracts entry; do
  if test "$(grep -Ec '^static .*vector_.*\{$' "$SPEC_SOURCE/$module.c")" -ne 1 \
      || ! grep -Fq 'EQUAL(vector_17_uint_16)' "$SPEC_SOURCE/$module.c"; then
    echo "module $module does not contain exactly the globally required fixed-vector equality helper" >&2
    exit 1
  fi
done

for source in "$SPEC_SOURCE"/*.c; do
  "$CC" ${CFLAGS:-} -std=c11 -Wall -Werror=implicit-function-declaration \
    -I "$SPEC_INCLUDE" -c "$source" -o "$TMP_DIR/$(basename "$source" .c).o"
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

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/missing-header/ffi/optimized" \
    --c-optimized-include-dir "$TMP_DIR/ffi/optimized/include" \
    --c-optimized-external-type pair=evmsail/host/missing.h \
    --c-preserve-type pair "$TEST_DIR/model.sail_project" \
    >"$TMP_DIR/missing-header.stdout" 2>"$TMP_DIR/missing-header.stderr"; then
  echo 'optimized extraction unexpectedly accepted a missing external type header' >&2
  exit 1
fi

grep -Fqi 'does not exist' "$TMP_DIR/missing-header.stderr"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/missing-type/ffi/optimized" \
    --c-optimized-include-dir "$TMP_DIR/ffi/optimized/include" \
    --c-optimized-external-type missing_type=evmsail/host/types.h \
    "$TEST_DIR/model.sail_project" \
    >"$TMP_DIR/missing-type.stdout" 2>"$TMP_DIR/missing-type.stderr"; then
  echo 'optimized extraction unexpectedly accepted an unknown external type' >&2
  exit 1
fi

grep -Fqi 'does not name a concrete type' "$TMP_DIR/missing-type.stderr"

# Output stems follow Sail module names, not source basenames.  Both source
# basenames deliberately differ from their project module names.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail \
  --c-output-dir "$TMP_DIR/filename/ffi/optimized" \
  --c-preserve from_first_filename --c-preserve from_second_filename \
  "$TEST_DIR/filename.sail_project"

FILENAME_INCLUDE="$TMP_DIR/filename/ffi/optimized/include/evmsail"
FILENAME_SOURCE="$TMP_DIR/filename/ffi/optimized/src/spec"

for module in first_filename_output second_filename_output; do
  test -f "$FILENAME_INCLUDE/spec/$module.h"
  test -f "$FILENAME_SOURCE/$module.c"
  test "$(grep -Fc "#include \"evmsail/spec/$module.h\"" "$FILENAME_INCLUDE/spec.h")" -eq 1
done
test ! -e "$FILENAME_INCLUDE/spec/first_source.h"
test ! -e "$FILENAME_SOURCE/first_source.c"
test ! -e "$FILENAME_INCLUDE/spec/second_source.h"
test ! -e "$FILENAME_SOURCE/second_source.c"
grep -Fq 'from_first_filename' "$FILENAME_INCLUDE/spec/first_filename_output.h"
grep -Fq 'from_first_filename' "$FILENAME_SOURCE/first_filename_output.c"
grep -Fq 'from_second_filename' "$FILENAME_INCLUDE/spec/second_filename_output.h"
grep -Fq 'from_second_filename' "$FILENAME_SOURCE/second_filename_output.c"
if grep -Fq 'from_second_filename' "$FILENAME_INCLUDE/spec/first_filename_output.h" \
    || grep -Fq 'from_second_filename' "$FILENAME_SOURCE/first_filename_output.c" \
    || grep -Fq 'from_first_filename' "$FILENAME_INCLUDE/spec/second_filename_output.h" \
    || grep -Fq 'from_first_filename' "$FILENAME_SOURCE/second_filename_output.c"; then
  echo 'optimized extraction assigned a definition to the wrong project module' >&2
  exit 1
fi

# Source-tree output preserves the source layout without changing the
# project's semantic module structure. The manifest is the authoritative,
# ordered compilation input for nested generated translation units.
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail \
  --c-output-dir "$TMP_DIR/source-tree/ffi/optimized" \
  --c-optimized-source-root "$TEST_DIR" \
  --c-preserve from_first_filename --c-preserve from_second_filename \
  "$TEST_DIR/source_tree.sail_project"

SOURCE_TREE_INCLUDE="$TMP_DIR/source-tree/ffi/optimized/include/evmsail"
SOURCE_TREE_SOURCE="$TMP_DIR/source-tree/ffi/optimized/src/spec"

for source in filename_first/first_source filename_second/second_source; do
  test -f "$SOURCE_TREE_INCLUDE/spec/$source.h"
  test -f "$SOURCE_TREE_SOURCE/$source.c"
  test "$(grep -Fc "#include \"evmsail/spec/$source.h\"" "$SOURCE_TREE_INCLUDE/spec.h")" -eq 1
done
test ! -e "$SOURCE_TREE_INCLUDE/spec/source_tree.h"
test ! -e "$SOURCE_TREE_SOURCE/source_tree.c"
grep -Fq '#include "evmsail/spec/filename_first/first_source.h"' \
  "$SOURCE_TREE_INCLUDE/spec/filename_second/second_source.h"
grep -Fq 'from_first_filename' "$SOURCE_TREE_SOURCE/filename_first/first_source.c"
grep -Fq 'from_second_filename' "$SOURCE_TREE_SOURCE/filename_second/second_source.c"
printf '%s\n' filename_first/first_source.c filename_second/second_source.c \
  > "$TMP_DIR/source-tree-expected.list"
cmp "$TMP_DIR/source-tree-expected.list" "$SOURCE_TREE_SOURCE/sources.list"

# Regeneration replaces the previous manifest-owned output set. This keeps a
# switch from module output to source-tree output from leaving an obsolete
# monolithic translation unit visible beside the new package.
touch "$SOURCE_TREE_SOURCE/obsolete.c" "$SOURCE_TREE_INCLUDE/spec/obsolete.h"
"$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
  --all-modules \
  --c-optimized-model --c-package evmsail \
  --c-output-dir "$TMP_DIR/source-tree/ffi/optimized" \
  --c-optimized-source-root "$TEST_DIR" \
  --c-preserve from_first_filename --c-preserve from_second_filename \
  "$TEST_DIR/source_tree.sail_project"
test ! -e "$SOURCE_TREE_SOURCE/obsolete.c"
test ! -e "$SOURCE_TREE_INCLUDE/spec/obsolete.h"
cmp "$TMP_DIR/source-tree-expected.list" "$SOURCE_TREE_SOURCE/sources.list"

while IFS= read -r source; do
  object=$(printf '%s' "$source" | tr '/' '_')
  "$CC" ${CFLAGS:-} -std=c11 -Wall -I "$TMP_DIR/source-tree/ffi/optimized/include" \
    -c "$SOURCE_TREE_SOURCE/$source" -o "$TMP_DIR/$object.o"
done < "$SOURCE_TREE_SOURCE/sources.list"

if "$SAIL" "$@" --no-color --no-memo-z3 -O --Oconstant-fold -c \
    --all-modules \
    --c-optimized-model --c-package evmsail \
    --c-output-dir "$TMP_DIR/collision/ffi/optimized" \
    "$TEST_DIR/collision.sail_project" \
    >"$TMP_DIR/collision.stdout" 2>"$TMP_DIR/collision.stderr"; then
  echo 'optimized extraction unexpectedly accepted colliding module file stems' >&2
  exit 1
fi

grep -Fq 'FooBar' "$TMP_DIR/collision.stderr"
grep -Fq 'Foo_bar' "$TMP_DIR/collision.stderr"
grep -Fq "file stem 'foo_bar'" "$TMP_DIR/collision.stderr"
test ! -e "$TMP_DIR/collision/ffi/optimized/include/evmsail/spec.h"
test ! -e "$TMP_DIR/collision/ffi/optimized/include/evmsail/spec/foo_bar.h"
test ! -e "$TMP_DIR/collision/ffi/optimized/src/spec/foo_bar.c"
