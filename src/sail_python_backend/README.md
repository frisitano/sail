# Sail Python backend

The Python backend is an optional Sail target that emits an executable,
typed Python module. It lowers Sail's checked typed AST directly to ordinary
Python declarations and functions. It does **not** pass through JIB or embed a
JIB interpreter, so the source model's records, unions, enums, aliases,
function signatures, and nominal boundaries remain visible in the output.

The backend and runtime are generic: neither contains architecture- or
application-specific code.

## Build and run

Build the compiler, plugin, and standalone runtime from the Sail repository
root:

```sh
opam exec -- dune build --root . \
  src/bin/sail.exe \
  src/sail_python_backend/sail_plugin_python.cmxs
```

Build the plugin against the same `libsail` source revision as the compiler
that loads it. Native OCaml plugin compatibility is revision-sensitive; a
matching package version alone is not an ABI guarantee.

An installed plugin is discovered through Sail's plugin site. For an in-tree
build, load it explicitly:

```sh
_build/default/src/bin/sail.exe \
  -plugin _build/default/src/sail_python_backend/sail_plugin_python.cmxs \
  --python -o model.py model.sail
```

The default output is `out.py`. If `-o` has no `.py` suffix, the backend adds
one. Generated modules require Python 3.10 or newer because pattern matching
is emitted directly.

By default, the runtime is embedded and the generated module is
self-contained. To share the separately installed `sail_runtime.py`, pass a
dotted Python import name:

```sh
sail --python --python-runtime-module sail_runtime -o model.py model.sail
```

Add the installed package's `lib/sail_python_backend` directory to
`PYTHONPATH`, or otherwise make `sail_runtime.py` importable. The option only
accepts Python identifier components separated by dots; it cannot inject an
arbitrary import statement.

Generated modules require
[`ethereum-types`](https://pypi.org/project/ethereum-types/). This is the
backend's only numeric profile: `nat` uses `Uint`; exact unsigned ranges use
`U8`, `U16`, `U32`, `U64`, or `U256`; and other constant non-negative ranges
use a cached `Unsigned` subclass produced by `BoundedUint[lo, hi]`. Signed and
unbounded Sail `int` values remain ordinary Python `int` values.

Arithmetic is evaluated with Python integer intermediates, then reconstructed
at a Sail result boundary when the checked result type is nominal or bounded.
This avoids accidentally importing the checked-overflow behavior of a
particular `ethereum-types` class into the semantics of a Sail arithmetic
expression. It does not add general-purpose coercion at function, record, or
extern boundaries: range-changing and modular conversions remain explicit in
the Sail program.

Sail's width-aware `Bits` class remains in the runtime because
`ethereum-types` does not provide Sail bitvector semantics.

Byte-oriented types can be mapped to the corresponding `ethereum-types`
classes:

```sh
sail --python --python-ethereum-fixed-bytes address=Bytes20 \
  --python-ethereum-fixed-bytes hash=Bytes32 \
  -o model.py model.sail
```

`--python-ethereum-fixed-bytes` is repeatable and maps a named Sail type
abbreviation to a class exported by `ethereum_types.bytes`. The backend
requires the abbreviation to expand to `vector(N, _, bits(8))` and rejects a
mapping whose `BytesN` width disagrees. Sail type abbreviations are
transparent, so checked signatures containing the same expanded byte-vector
type use the selected representation too. Generated boundaries accept the
selected representation directly. Conversions to that representation are
emitted only where the Sail program explicitly invokes the corresponding
constructor.

The backend never infers semantic meanings from vector width alone. The
`ethereum-types` dependency is isolated to the generated runtime layer. In
split-package output, only `_runtime.py` imports `ethereum_types`;
source-aligned modules import numeric and selected fixed-byte classes from
their relative `_runtime`.

For review-oriented output that follows the Sail declaration and expression
shape more closely, opt in explicitly:

```sh
sail --python --python-preserve-structure -o model.py model.sail
```

This mode emits declarations in rewritten Sail AST order and prefers direct
Python returns, branches, matches, and loop statements over generated result
temporaries. It is a presentation choice, not a different semantic pipeline:
both modes lower the checked typed AST directly. By itself, this option retains
metadata and runtime behavior. The default remains the conservative lowering,
which is useful when a normalized single-result form is preferred.

By default, the backend treats Sail's successful type checking as
authoritative. It does not insert Python coercions or validators at generated
function, return, register, constant, or host-extern boundaries. If a
representation conversion is required, it must be explicit in Sail and is
emitted as the corresponding Python constructor. Host implementations are
likewise responsible for satisfying their declared Sail signatures.

For an executable representation of dependent record validity, opt in to
Pydantic:

```sh
sail --python --python-pydantic -o model.py model.sail
```

In this mode, a record with runtime-relevant numeric or Boolean type
parameters gains a frozen `<Record>Validity` witness and a `validity` field.
The witness records those parameters and checks their Sail constraints.
Constrained record fields are checked by an `after` model validator, including
integer bounds, singleton values, and dependent vector lengths. Construction,
record replacement, and direct field assignment therefore enforce the
executable invariant. Generated field validators preflight assignments so a
rejected field or validity-witness replacement leaves the existing record
unchanged. Validation is strict and never coerces a value to make it fit.
Mutation performed inside a mutable field, such as appending directly to a
list, remains ordinary Python and is not intercepted by the containing record.
Records without runtime-relevant constraints remain ordinary dataclasses.
`Bits` and fixed `BytesN` fields retain their own width checks instead of
duplicating them in a record validator.

If a function constructs a dependent record and a required numeric witness
cannot be recovered from its ordinary arguments, the backend exposes a
collision-safe `_sail_implicit_<name>` parameter and supplies the checked Sail
instantiation at generated call sites. This is explicit dictionary passing
for erased Sail type parameters, not a representation conversion. The option
adds a Pydantic 2 runtime dependency; it does not add validators to function,
return, register, constant, or host-extern boundaries.

Large specifications can opt into a source-aligned importable package instead
of a single module:

```sh
sail --python --python-split --python-source-root spec \
  --python-preserve-structure \
  -o model spec/main.sail
```

In split mode, `-o` names a package directory (`model.py` is treated as
`model`). Sail records, unions, enums, aliases, and ordinary functions live in
modules matching their innermost Sail source file beneath
`--python-source-root`; `_types.py` is an imports-only compatibility aggregator
that re-exports those source-local types. Registers and immutable top-level
values live in the same source module as their Sail declarations. For example,
`spec/instructions/arithmetic.sail` becomes
`model/instructions/arithmetic.py`. Included Sail library files outside that
root are placed below `model/_sail/`. Calls within one Sail source file are
direct Python calls. Non-cyclic cross-file references import the exact
functions and immutable values they use from the corresponding source modules.
For example, a dependency on `byte_slice` is emitted as
`from model.primitives.bytes import byte_slice`. When two source modules form a
value-dependency cycle, the cyclic edge instead imports the readable owner
module and uses qualified access such as `helpers.split_increment(...)`.

Mutable registers are not copied through imports. A function in the register's
source module reads and writes its Python global directly, and the backend
infers the required `global` declaration. A function in another source module
imports the owner module and accesses the register through it, for example
`from model.evm import machine` followed by `machine.pc = 0`. Every import is
emitted at the top of its file. The backend analyzes the source-module
dependency graph before rendering, uses module qualification only for cyclic
value edges, and orders package aggregation so imports do not depend on
partially initialized symbols. No `E402` suppression is generated. The package
`__init__.py` re-exports immutable declarations, exposes current register
values dynamically, contains metadata, and provides the compatibility
`reset()`/`finish()` API. Split output does not contain `_model.py` or a
separate lifecycle module.

When a Sail `let`, `var`, or assignment supplies a destination name, the
backend lowers control flow directly into that destination. Thus a named Sail
binding around an `if`, `match`, or `try` retains its readable source name
rather than being routed through `_sail_value_*`. Pure one-expression blocks
and conditionals are emitted inline when Python has an equivalent expression.
The `_sail_value_*` spelling is reserved for genuinely anonymous,
statement-valued expressions for which the checked Sail AST provides no
binding name.

The source-root option only affects split-package paths and generated source
comments. It does not change type checking, name resolution, rewrites, or
runtime semantics. Generate into an empty or previously generated directory;
the backend creates and updates its files but deliberately does not remove
unrelated or stale files.

## Generated Python model

The generated module or package is intended to be readable and usable as
normal Python:

- Sail records become mutable, slotted `@dataclass` declarations. With
  `--python-pydantic`, records that require executable dependent validation
  become strict Pydantic dataclasses and carry a generated validity witness.
  A Sail record update is emitted as a deep-copied `dataclasses.replace`,
  preserving value-style update behavior and revalidating constrained records.
- Sail unions become a nominal base class plus a frozen, slotted dataclass for
  each constructor.
- Sail enums with compiler-generated numeric conversions become
  `ethereum_types.enum.UintEnum` classes. Python's normal
  `EnumType(number)` constructor converts from an integer, while a member's
  `.value` converts back. The generated `Enum_of_num` and `num_of_Enum`
  scaffolding is therefore omitted. Enums without those conversions remain
  ordinary Python `Enum` classes.
- Sail type abbreviations become `TypeAlias` declarations when they alias a
  type, and abstract Sail types become nominal Python classes.
- Sail functions become typed Python `def` declarations. Their annotations
  retain Sail's checked types without inserting dynamic coercions. Explicit
  Sail constructors remain explicit Python constructors.
- Sail matches become Python `match` statements, with explicit guards where
  needed. Control flow is emitted directly as `if`, `for`, `while`, `try`, and
  exception-based early return.

Names are escaped deterministically when they conflict with Python syntax or
runtime names. The original Sail spelling remains available in the source
metadata.

The public module or package exports:

- generated types, constructors, functions, top-level values, and registers;
- immutable top-level Sail `let` bindings, initialized once as annotated module
  assignments;
- `reset()`, which re-evaluates generated register initializers. In split
  packages it coordinates private reset helpers in the source modules that own
  registers; normal import initializes each declaration inline;
- `finish()`, currently a no-op lifecycle hook;
- `register_extern(name, callable)` and `register_externs(mapping)` in the
  default generic-runtime mode; an explicit extern contract replaces this
  registry when `--python-extern-module` is selected;
- runtime values and annotations including `Uint`, `U8`, `U16`, `U32`, `U64`,
  `U256`, `BoundedUint`, `Bits`, `IntegerRange`, `BitWidth`, and
  `VectorLength`;
- `__sail_types__`, mapping source type names to Python types;
- `__sail_functions__`, mapping source function names to Python callables;
- `__sail_signatures__`, containing their Python annotations;
- `__sail_source_signatures__`, preserving Sail's rendered type schemes;
- `__sail_effects__`, classifying specified functions as `pure` or
  `effectful` from Sail's effect analysis; and
- `__sail_externs__`, mapping bodyless or explicitly targeted Sail values to
  the host target names used by the Python module.

A Sail function whose public type is `unit -> T` is exposed as a zero-argument
Python function. A bodyless extern with that type is likewise invoked with no
Python arguments:

```python
import model

model.register_extern("host_read", lambda: 42)
answer = model.read_from_host()
```

An `extern "python" = "host_name"` annotation selects `host_name`. Without
one, a bodyless value uses its Sail identifier. Calling an unregistered,
non-core extern raises `SailUnsupportedError` with the missing name. The
runtime implements generic integer, Boolean, string, list, vector, and
bitvector primitives; model-specific I/O, memory, concurrency, and environment
effects belong in host adapters.

For a split extraction with a statically defined host boundary, provide an
importable contract module and copy its source into the generated package:

```sh
sail --python --python-split \
  --python-extern-module model.HostContract \
  --python-import-file extractions/HostContract.py \
  -o model spec.sail
```

Each generated source module then imports only the contract functions it uses
under readable `_host_<target>` bindings and calls them directly. The generated
runtime contains no extern registry or `call_extern` path in this mode.
`--python-import-file` is repeatable and requires `--python-split`.

## Numeric contract

The public boundary keeps Sail numeric domains distinct:

| Sail type | Python value | Contract |
| --- | --- | --- |
| `int` | `int` | Arbitrary precision and signed; no implicit wrapping |
| `nat` | `Uint` | Arbitrary precision and non-negative |
| constant `range(lo, hi)` with `0 <= lo` | `BoundedUint[lo, hi]` | Cached nominal `Unsigned` subclass; bounds are checked by the value type |
| dependent `range(lo, hi)` with a non-negative lower bound | `Uint` | The value type enforces non-negativity; `--python-pydantic` enforces runtime-dependent record relationships |
| `range(0, 2^N - 1)` for N = 8, 16, 32, 64, 256 | `UN` | Exact `ethereum-types` unsigned width |
| `bits(N)` | annotated `Bits` | Exact width; construction and bitvector operations reduce modulo `2^N` |

The ordinary arithmetic operators on `ethereum-types` values are checked, but
generated Sail arithmetic deliberately uses Python integer intermediates and
constructs the checked result representation at the typed boundary. Range
types do not silently become modular merely because their bounds happen to be
a power of two. Modular behavior must be explicit in the Sail model.

`Bits` is the modular, representation-level domain. It rejects mismatched
widths for binary bitvector operations and supports exact-width access,
slicing, slice update, concatenation, logical shifts, signed interpretation,
and zero/sign extension. Concatenation places the left operand in the high
bits. Fixed vectors are Python lists with length and item checks at generated
boundaries; indexing preserves the Sail order encoded by the typed AST.

## Rewrite and lowering boundary

The target registers independently with `Target.register` and uses Sail's
checked rewrite infrastructure. In order, it instantiates Python outcomes,
realizes mappings, removes vector-subrange patterns, lowers string-append and
mapping patterns, truncates hexadecimal literals, optionally performs Sail's
requested monomorphisation rewrites, applies Sail's `undefined false`
normalization, types pattern literals, normalizes tuple/vector/record
assignments, lifts
assignment expressions, merges function clauses, rechecks the result, and
constant-folds for the Python target.

The backend then consumes that rewritten typed AST directly. It does not use
JIB as an intermediate representation.

Sail's type checker also synthesizes `undefined_<Type>` constructors for
records and enums. The Python backend recognizes those definitions through
their generated `undefined_gen` annotation and omits them from the public
module surface. Any use of a generated undefined constructor lowers directly
to `sail_undefined(...)`, which raises `SailUndefinedError`; a user-authored
function whose name happens to begin with `undefined_` remains an ordinary
function.

The direct lowering currently handles:

- literals, local and top-level values, typed function application, tuples,
  lists, vectors, bitvectors, records, record updates, unions, and enums;
- identifier, literal, tuple, list, vector, cons, constructor, record, `as`,
  wildcard, and alternative patterns after the registered rewrites;
- blocks, local bindings, mutable locals, register reads/writes, assignment,
  conditionals, guarded matches, `foreach`, `while`, `repeat until`, explicit
  return, assertions, exits, throws, and catches; and
- references, configuration lookup, size expressions, constraints, and
  lowered undefined values.

## Deliberate limitations and diagnostics

The backend stops generation with a source-located `Python backend:` error
when a construct that should have been normalized survives, including
bitfield declarations, negative/vector-concatenation/vector-subrange/string-
append patterns, vector-range or vector-concatenation assignments, effectful
vector indices or match guards, and interpreter-only internal values. It also
reports when a required function has no value specification or a bitvector
extension/truncation width cannot be inferred.

Other current boundaries are:

- free numeric indices in a polymorphic type-alias declaration are erased
  from that alias's import-time Python expression; concrete uses still retain
  their width/length/range annotations and checks;
- dependent record constructors recover numeric witnesses from record
  arguments and singleton bindings where possible; otherwise
  `--python-pydantic` emits an explicit implicit-witness parameter and passes
  the checked Sail instantiation at generated internal call sites;
- Sail `real` is emitted through Python `float`, so exact rational semantics
  are not promised;
- deterministic defaults only exist for the runtime's basic scalar,
  bitvector, fixed-unsigned, and list shapes; and
- host effects require registered adapters, while `finish()` does not yet
  lower Sail finish effects.

Undefined values raise `SailUndefinedError`, an unmatched clause raises
`SailMatchFailure`, and an unregistered extern or unavailable default/config
raises `SailUnsupportedError` at execution time.

## Tests

After building the plugin, run:

```sh
python3 test/python/run_tests.py \
  --sail _build/default/src/bin/sail.exe \
  --plugin _build/default/src/sail_python_backend/sail_plugin_python.cmxs
```

The Dune entry point is:

```sh
opam exec -- dune build --root . @python-runtest
```

For generated-artifact linting, run Ruff's complete default Python error
families (the EVM integration pins Ruff 0.15.22):

```sh
uv run --no-project --with ruff==0.15.22 ruff check \
  --select E4,E7,E9,F --ignore E741,F841 path/to/generated.py
```

The backend emits explicit runtime and generated-type imports rather than
wildcard imports. This is semantically equivalent for generated references and
allows Ruff `F821` to report an unresolved executable annotation or expression
name instead of classifying it as possibly supplied by `import *`. The two
ignored rules preserve source-oriented extraction: `E741` rejects valid but
visually ambiguous Sail identifiers such as `l`, while `F841` rejects no-op
Sail `let` bindings that the structural mode deliberately retains.

The suite evaluates the same fixture with the Sail interpreter and compares
its behavioral golden output with generated Python in embedded-runtime,
external-runtime, and source-split package modes. It also:

- parses generated source and compares selected declarations against a
  structural golden, protecting the dataclass/enum/function architecture;
- generates a dependent-record fixture with `--python-pydantic` and checks
  strict validity witnesses, constructor propagation, dependent field bounds,
  and assignment revalidation;
- checks that split types, constants, registers, and functions are placed in
  their Sail source modules, including nested local includes, same-owner
  `global` writes, module-qualified cross-owner writes, cyclic cross-file calls,
  source-name-preserving branch destinations, top-of-file imports, and the
  absence of `_model.py` and `E402` suppressions;
- compiles both generated modules;
- resolves generated annotations, statically audits generated global names,
  and rejects wildcard imports that would make undefined-name lint ambiguous;
- exercises records, unions, enums, patterns, loops, early returns,
  assertions, exceptions, registers, reset, config, and externs; and
- checks exact range boundaries, checked fixed unsigned arithmetic, explicit
  wrapping, bitvector overflow, shifts, signed interpretation,
  concatenation, slicing, slice update, and width/length errors.
