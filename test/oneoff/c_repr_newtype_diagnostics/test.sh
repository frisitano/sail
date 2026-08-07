#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
SAIL=${SAIL:-sail}
TMP_ROOT=${AGENT_TMPDIR:-"$TEST_DIR/../../../.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/c_repr_newtype_diagnostics.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

run_sail() {
  if [ -n "${SAIL_PLUGIN:-}" ]; then
    "$SAIL" -plugin "$SAIL_PLUGIN" "$@"
  else
    "$SAIL" "$@"
  fi
}

expect_error() {
  input=$1
  expected=$2
  output="$TMP_DIR/${input%.sail}"

  if run_sail --no-color -c "$TEST_DIR/$input" -o "$output" 2> "$output.result"; then
    echo "$input unexpectedly compiled" >&2
    exit 1
  fi
  grep -Fq "$expected" "$output.result"
}

expect_error unsupported.sail 'C backend: unsupported representation "u32" in $[c_repr]; supported representations are uint8, uint16, uint32, uint64, int8, int16, int32, int64, u256, byte_pointer, fixed_bytes, fixed_bytes_u64_lanes'
expect_error wrong_target.sail 'C backend: $[c_repr] is only valid on a newtype'
expect_error wrong_payload.sail 'C backend: $[c_repr] uint64 requires a mathematical int or nat payload'
expect_error missing_argument.sail 'C backend: $[c_repr] requires a representation name'
expect_error wrong_u256_payload.sail 'C backend: $[c_repr] u256 requires an exact bits(256) or range(0, 2^256 - 1) payload'
expect_error wrong_fixed_bytes_element.sail 'C backend: $[c_repr] fixed_bytes requires a vector of byte (bits(8)) elements'
expect_error wrong_fixed_bytes_length.sail 'C backend: $[c_repr] fixed_bytes requires a statically sized, positive vector payload'

run_sail --no-color -c --c-specialize --c-preserve keep "$TEST_DIR/u256_range.sail" -o "$TMP_DIR/u256_range"
grep -Eq 'u256 zkeep\(u256( [[:alnum:]_]+)?\);' "$TMP_DIR/u256_range.h"

if run_sail --no-color -c --c-specialize --c-require-bounded-int --c-preserve keep \
    "$TEST_DIR/unbounded_int.sail" -o "$TMP_DIR/unbounded_int" 2> "$TMP_DIR/unbounded_int.result"; then
  echo 'unbounded_int.sail unexpectedly compiled with --c-require-bounded-int' >&2
  exit 1
fi
grep -Fq 'cannot select a native integer representation for definition keep; add a finite semantic bound' \
  "$TMP_DIR/unbounded_int.result"

if run_sail --no-color -c --c-specialize --c-require-bounded-int --c-preserve keep \
    "$TEST_DIR/self_dependent_int.sail" -o "$TMP_DIR/self_dependent_int" \
    2> "$TMP_DIR/self_dependent_int.result"; then
  echo 'self_dependent_int.sail unexpectedly compiled with --c-require-bounded-int' >&2
  exit 1
fi
grep -Fq 'self-dependent accumulator update' "$TMP_DIR/self_dependent_int.result"
grep -Fq 'use a finite signed range and narrow the sum at the semantic update boundary' \
  "$TMP_DIR/self_dependent_int.result"

run_sail --no-color -c --c-specialize --c-require-bounded-int --c-preserve main \
  "$TEST_DIR/bounded_accumulator.sail" -o "$TMP_DIR/bounded_accumulator"
grep -Fq '__int128 ztotal;' "$TMP_DIR/bounded_accumulator.h"
grep -Eq '^unit zkeep\(__int128( [[:alnum:]_]+)?\);$' "$TMP_DIR/bounded_accumulator.h"
grep -Eq '^unit zkeep_int16_t_to_unit\(int16_t( [[:alnum:]_]+)?\);$' "$TMP_DIR/bounded_accumulator.h"
if grep -Eq 'sail_int|CREATE\(sail_int\)|add_int' "$TMP_DIR/bounded_accumulator.c"; then
  echo 'range-bounded accumulator retained arbitrary-precision arithmetic' >&2
  exit 1
fi
grep -Fq 'ztotal + zdelta' "$TMP_DIR/bounded_accumulator.c"

# Generic library containers such as option('a) have no concrete integer
# representation at their declaration site.  Their bounded instantiations must
# not trip the strict diagnostic.
run_sail --no-color -c --c-specialize --c-require-bounded-int --c-preserve keep \
  "$TEST_DIR/generic_container.sail" -o "$TMP_DIR/generic_container"
