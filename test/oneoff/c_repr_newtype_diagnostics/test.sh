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

expect_error unsupported.sail 'C backend: unsupported representation "u32" in $[c_repr]; supported representations are uint64, int64, u256, fixed_bytes'
expect_error wrong_target.sail 'C backend: $[c_repr] is only valid on a newtype'
expect_error wrong_payload.sail 'C backend: $[c_repr] uint64 requires a mathematical int or nat payload'
expect_error missing_argument.sail 'C backend: $[c_repr] requires a representation name'
expect_error wrong_u256_payload.sail 'C backend: $[c_repr] u256 requires an exact bits(256) payload'
expect_error wrong_fixed_bytes_element.sail 'C backend: $[c_repr] fixed_bytes requires a vector of byte (bits(8)) elements'
expect_error wrong_fixed_bytes_length.sail 'C backend: $[c_repr] fixed_bytes requires a statically sized, positive vector payload'
