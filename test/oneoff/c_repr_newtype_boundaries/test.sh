#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)

SAIL=${SAIL:-sail}
SAIL_DIR=${SAIL_DIR:-$("$SAIL" --dir)}
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_repr_newtype_boundaries.XXXXXX")

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

trap 'rm -rf "$TMP_DIR"' EXIT

run_sail() {
  if [ -n "${SAIL_PLUGIN:-}" ]; then
    "$SAIL" -plugin "$SAIL_PLUGIN" "$@"
  else
    "$SAIL" "$@"
  fi
}

expect_boundary_failure_with_policy() {
  name=$1
  expected=$2
  policy=$3
  output="$TMP_DIR/$name.$policy"

  run_sail --no-color -O -c --c-specialize --c-narrowing="$policy" "$TEST_DIR/$name.sail" -o "$output"
  # Word splitting is intentional for user/compiler and pkg-config flags.
  # shellcheck disable=SC2086
  "$CC" ${CFLAGS:-} $GMP_CFLAGS "$output.c" "$SAIL_DIR"/lib/*.c -I "$SAIL_DIR/lib" $GMP_LIBS -o "$output.bin"

  if "$output.bin" > "$output.result" 2> "$output.err"; then
    echo "$name unexpectedly crossed its native integer representation boundary" >&2
    exit 1
  fi

  test ! -s "$output.result"
  grep -Fq "$expected" "$output.err"
}

expect_boundary_failure() {
  expect_boundary_failure_with_policy "$1" "$2" checked
}

expect_boundary_failure negative 'Sail C backend: negative integer cannot be represented as uint64_t'
grep -Eq 'INT(8|16|32|64)_C\(-1\)' "$TMP_DIR/negative.checked.c"
if grep -Fq 'neg_int(' "$TMP_DIR/negative.checked.c"; then
  echo 'bounded negative literal detoured through the Sail integer runtime' >&2
  exit 1
fi
expect_boundary_failure overflow 'Sail C backend: integer value is outside the uint64_t domain'
expect_boundary_failure nat_overflow 'Sail C backend: integer value is outside the uint64_t domain'
expect_boundary_failure negative_u8 'Sail C backend: negative integer cannot be represented as uint8_t'
expect_boundary_failure overflow_u8 'Sail C backend: integer value is outside the uint8_t domain'
expect_boundary_failure record_negative_u8 'Sail C backend: negative integer cannot be represented as uint8_t'
expect_boundary_failure tuple_overflow_u8 'Sail C backend: integer value is outside the uint8_t domain'
expect_boundary_failure_with_policy record_negative_u8 \
  'Sail C backend: negative integer cannot be represented as uint8_t' proven
expect_boundary_failure_with_policy tuple_overflow_u8 \
  'Sail C backend: integer value is outside the uint8_t domain' proven

# Aggregate folding may retain conversions that are total at the target C
# carrier. Exercise both signed extrema and unsigned extrema through record
# and tuple construction under the checked policy.
SAFE_OUTPUT="$TMP_DIR/aggregate_safe_boundaries"
run_sail --no-color -O -c --c-specialize --c-narrowing=checked \
  "$TEST_DIR/aggregate_safe_boundaries.sail" -o "$SAFE_OUTPUT"
# Word splitting is intentional for user/compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS "$SAFE_OUTPUT.c" "$SAIL_DIR"/lib/*.c \
  -I "$SAIL_DIR/lib" $GMP_LIBS -o "$SAFE_OUTPUT.bin"
"$SAFE_OUTPUT.bin" > "$SAFE_OUTPUT.result" 2> "$SAFE_OUTPUT.err"
test ! -s "$SAFE_OUTPUT.result"
test ! -s "$SAFE_OUTPUT.err"

# A uint16_t record field is path-refined to one byte before conversion.
# Specialization records each field-to-byte conversion as Proven_narrow.
# Under the defensive checked policy, optimizer paths that fold records,
# converted tuples, returns, copies, or initializers must leave the marker at
# a standalone assignment where C emission restores the guard.
build_aggregate_proven_narrow() {
  policy=$1
  policy_dir="$TMP_DIR/aggregate_proven_narrow_$policy"
  output="$policy_dir/aggregate_proven_narrow"

  mkdir -p "$policy_dir"
  run_sail --no-color -O -c --c-specialize --c-specialize-log --c-no-main \
    --c-narrowing="$policy" \
    --c-preserve record_fold --c-preserve converted_tuple_fold \
    --c-preserve terminal_sink --c-preserve propagated_aggregate \
    --c-preserve initialized_local \
    "$TEST_DIR/aggregate_proven_narrow.sail" -o "$output" \
    2> "$policy_dir/specialize.log"
  # Word splitting is intentional for user/compiler and pkg-config flags.
  # shellcheck disable=SC2086
  "$CC" ${CFLAGS:-} $GMP_CFLAGS "$output.c" \
    "$TEST_DIR/aggregate_proven_narrow_runner.c" "$SAIL_DIR"/lib/*.c \
    -I "$policy_dir" -I "$TEST_DIR" -I "$SAIL_DIR/lib" $GMP_LIBS \
    -o "$policy_dir/runner"
}

build_aggregate_proven_narrow checked
checked_dir="$TMP_DIR/aggregate_proven_narrow_checked"
test "$(grep -Fc \
  'conversion source=%u16 destination=%u8 interval=0..255 proof=true' \
  "$checked_dir/specialize.log")" -eq 5
test "$(grep -Fc \
  'sail_native_conversion_failure("integer value is outside the uint8_t domain")' \
  "$checked_dir/aggregate_proven_narrow.c")" -eq 5
for case_name in record tuple terminal propagation initialization; do
  "$checked_dir/runner" "$case_name" > "$checked_dir/$case_name.result" \
    2> "$checked_dir/$case_name.err"
  test ! -s "$checked_dir/$case_name.result"
  test ! -s "$checked_dir/$case_name.err"
done

build_aggregate_proven_narrow all
all_dir="$TMP_DIR/aggregate_proven_narrow_all"
test "$(grep -Fc \
  'conversion source=%u16 destination=%u8 interval=0..255 proof=true' \
  "$all_dir/specialize.log")" -eq 5
if grep -Fq \
    'sail_native_conversion_failure("integer value is outside the uint8_t domain")' \
    "$all_dir/aggregate_proven_narrow.c"; then
  echo 'narrowing=all unexpectedly retained a checked Proven_narrow guard' >&2
  exit 1
fi
for case_name in record tuple terminal propagation initialization; do
  "$all_dir/runner" "$case_name" > "$all_dir/$case_name.result" \
    2> "$all_dir/$case_name.err"
  test ! -s "$all_dir/$case_name.result"
  test ! -s "$all_dir/$case_name.err"
done

# `all` is the explicit extraction escape hatch: every narrowing is a
# low-limb projection, including boundaries without reconstructed evidence.
ALL_OUTPUT="$TMP_DIR/overflow_all"
run_sail --no-color -O -c --c-specialize --c-narrowing=all \
  "$TEST_DIR/overflow.sail" -o "$ALL_OUTPUT"
# Word splitting is intentional for user/compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS "$ALL_OUTPUT.c" "$SAIL_DIR"/lib/*.c -I "$SAIL_DIR/lib" $GMP_LIBS -o "$ALL_OUTPUT.bin"
"$ALL_OUTPUT.bin" > "$ALL_OUTPUT.result" 2> "$ALL_OUTPUT.err"
grep -Fq 'unreachable = 0' "$ALL_OUTPUT.result"
test ! -s "$ALL_OUTPUT.err"
grep -Fq 'u128_to_u64_unchecked' "$ALL_OUTPUT.c"
