#!/usr/bin/env bash

SAIL_SOURCE="${BASH_SOURCE[0]}"
while [[ -L "$SAIL_SOURCE" ]]; do
    SAIL_LINK_DIR="$( cd -P "$( dirname "$SAIL_SOURCE" )" && pwd )"
    SAIL_SOURCE="$(readlink "$SAIL_SOURCE")"
    [[ "$SAIL_SOURCE" != /* ]] && SAIL_SOURCE="$SAIL_LINK_DIR/$SAIL_SOURCE"
done

SAIL_DIR="$( cd -P "$( dirname "$SAIL_SOURCE" )" && pwd )"
export SAIL_DIR
# This would be nice, but concurrent tests are failing due to dune's global lock
#exec dune exec --root="$SAIL_DIR" --no-build --display=quiet --no-print-directory -- sail $*

# Where to find plugins
export DUNE_DIR_LOCATIONS="libsail:share:$SAIL_DIR/_build/install/default/share/libsail"
exec "$SAIL_DIR/_build/install/default/bin/sail" "$@"
