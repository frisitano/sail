#!/bin/sh

set -eu

TEST_DIR=$(CDPATH= cd -- "$(dirname "$0")" && pwd)
ROOT=$(CDPATH= cd -- "$TEST_DIR/../../.." && pwd)
CC=${CC:-cc}
TMP_ROOT=${AGENT_TMPDIR:-"$ROOT/.agent-tmp"}

mkdir -p "$TMP_ROOT"
TMP_DIR=$(mktemp -d "$TMP_ROOT/signed_runtime_conversion.XXXXXX")
trap 'rm -rf "$TMP_DIR"' EXIT

if command -v pkg-config >/dev/null 2>&1; then
  GMP_CFLAGS=$(pkg-config --cflags gmp)
  GMP_LIBS=$(pkg-config --libs gmp)
else
  GMP_CFLAGS=
  GMP_LIBS=-lgmp
fi

# Word splitting is intentional for user/compiler and pkg-config flags.
# shellcheck disable=SC2086
"$CC" ${CFLAGS:-} $GMP_CFLAGS -std=gnu11 -I "$ROOT/lib" \
  "$TEST_DIR/runner_gmp.c" "$ROOT/lib/sail.c" "$ROOT/lib/sail_failure.c" \
  $GMP_LIBS -o "$TMP_DIR/runner_gmp"

"$TMP_DIR/runner_gmp"

RUNNERS=runner_gmp
case $(uname -m) in
  x86_64|amd64)
    # The legacy int128 runtime currently uses x86 intrinsics. Exercise its
    # identical checked-conversion contract on the architectures it supports.
    # shellcheck disable=SC2086
    "$CC" ${CFLAGS:-} $GMP_CFLAGS -std=gnu11 -I "$ROOT/lib/int128" \
      "$TEST_DIR/runner_int128.c" "$ROOT/lib/int128/sail.c" "$ROOT/lib/sail_failure.c" \
      $GMP_LIBS -o "$TMP_DIR/runner_int128"
    "$TMP_DIR/runner_int128"
    RUNNERS="$RUNNERS runner_int128"
    ;;
esac

for runner in $RUNNERS; do
  for direction in high low; do
    if "$TMP_DIR/$runner" "$direction" >/dev/null 2>&1; then
      echo "$runner accepted an out-of-range signed conversion ($direction)" >&2
      exit 1
    fi
  done
done
