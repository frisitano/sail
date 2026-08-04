# Sail Specialization Plan

The specialization plan is a versioned, backend-neutral record of the
representation choices made while Sail lowers a typed definition to specialized
JIB clones. It exists so an independent checker or proof assistant can
reconstruct refinement obligations without trusting the compiler-generated C
names.

## Contract

- Purpose: record the source identity, semantic and represented signatures,
  inferred bounds, conversions, call edges, extern contracts, assumptions,
  diagnostics, and proof obligations for each representation clone.
- Trust model: the compiler is an untrusted producer. The structural checker is
  also untrusted convenience code. A proof consumer validates references and
  reconstructs semantic obligations from the machine plan.
- Consumers: structural validation, Lean/Coq adapters, regression tests, and
  human review.
- Schema: `1.1.0`, identified by
  `https://sail-lang.org/schemas/specialization-plan/v1`.
- Non-goals: certifying the compiler, making JIB display names or C symbols
  stable, or proving an extern implementation without an independent contract.

The normative machine schema is [schema-v1.json](schema-v1.json). The human
report is deliberately non-normative.

## Stable identity and provenance

Every identity is a domain-separated digest:

- an input identity hashes the bytes of each source file contributing to the
  typed AST (the recorded path is descriptive);
- a source identity hashes the Sail name, semantic signature, input identity,
  and numeric source span (not the invocation path);
- a clone identity hashes the source identity, represented signature, and
  normalized inferred bounds;
- conversion, call-edge, and obligation identities hash their owning clone and
  canonical subject, never an output-list position.

Display order, generated JIB names, C name mangling, and transient compiler
symbols are excluded from these preimages. The machine plan therefore does not
change under `--c-no-mangle`. The human report shows three distinct fields:
Sail source name, generated clone name, and emitted backend symbol. The latter
is descriptive and never a proof reference.

Version 1 uses MD5 because OCaml's standard library makes that digest available
without adding a compiler dependency. It is used for deterministic identity,
not adversarial integrity. The algorithm and domain are explicit in every ID,
so a future schema can migrate to SHA-256 without ambiguous references.

## Emission

Plan emission is optional and has no effect when disabled:

```sh
sail -c --c-specialize \
  --c-narrowing=proven \
  --c-specialization-plan model.specialization.json \
  --c-specialization-plan-human model.specialization.md \
  --c-specialization-obligations-lean SpecializationObligations.lean \
  --c-specialization-obligations-coq SpecializationObligations.v \
  model.sail -o model
```

Requesting any specialization output without `--c-specialize` is an error.
Machine JSON and native Lean/Coq definitions are written after specialization
and final bounded-integer auditing, before C name generation. The human report
is written after backend symbols are assigned.

Canonical output uses UTF-8 JSON, fixed object-field order, and lexicographic
record ordering by stable ID. Identical compiler version, configuration,
inputs, and specialization decisions produce byte-identical JSON.
Lean and Coq definitions are rendered from the same backend-neutral OCaml
proposition tree. Quantifiers, implication, conjunction, existential witnesses,
relation applications, and literals are constructed once; only their concrete
Lean/Coq syntax differs. The generated files are likewise byte-identical across
repeated compilations.

The configuration identity covers the versioned representation-specialization
policy, narrowing policy, bounded-integer enforcement, preserved specialization
roots, and the effective per-type representation settings. Input-local
representation annotations are also covered by the input digests. Backend
naming and output paths are deliberately excluded because they cannot affect
proof identity.

`--c-narrowing` controls conversions into smaller native integer carriers:

- `checked` validates every narrowing at runtime;
- `proven` elides validation only when Sail's interval and path analysis has
  reconstructed a range proof, and checks every other narrowing; and
- `all` projects the low limbs at every narrowing boundary. This is the default
  for `--c-optimized-model`; it is an explicit refinement assumption for any
  boundary without reconstructed evidence.

Plain C generation defaults to `checked`, while `--c-specialize` defaults to
`proven`. An explicit `--c-narrowing` always takes precedence. Each recorded
conversion is classified as `checked`, `proven`, or `assumed`; `assumed`
conversions add an `unchecked_narrowing` assumption and make conversion
correctness unresolved until a downstream refinement proof discharges it.

## Obligations

Each clone contains all required obligation classes:

- representation adequacy;
- operation refinement;
- conversion correctness;
- call compatibility;
- path-condition soundness;
- exception equivalence;
- extern refinement;
- ownership/lifetime compatibility.

`reconstructible` means structural evidence is present in the plan.
`requires_proof` means a proof consumer must discharge the semantic statement.
`unresolved` is indexed at the plan root and must be addressed by independent
evidence. An extern-free clone records `extern_refinement` as `not_applicable`
so completeness remains mechanically checkable.

Operational obligations are forward-simulation statements. Given represented
arguments and a Sail function execution, they require an existential
specialized-JIB outcome together with the refinement relation. Given a Sail call
or extern interaction, the call and extern obligations themselves require
existential represented arguments plus a specialized-JIB or extern outcome;
call-argument representation is not a caller-supplied premise. Exception and
ownership/lifetime obligations are universal safety statements over every
represented Sail/JIB execution pair whose outcomes refine, so both properties
apply to the same execution witnesses established by operation refinement.
Conversion obligations likewise require a represented result for every
well-typed source value. The conversion relation receives the recorded
`checked`, `proven`, or `assumed` validation class, so Lean and Coq consumers
can give each trust path distinct semantics. Consequently, missing representations, empty
downstream execution relations, or incompatible side-condition witnesses cannot
satisfy `Complete` merely by vacuity.

Path-condition soundness is deliberately source-only: source argument
well-typedness and source reachability imply the inferred bounds. It does not
assume that represented arguments already exist or that specialized JIB
execution is reachable; representation adequacy consumes those independently
established bounds.

## Native Lean and Coq definitions

The native files declare:

- an abstract semantic interface for typed Sail evaluation, specialized JIB
  evaluation, representation relations, conversions, calls, reachability,
  exception behavior, and ownership/lifetime behavior;
- one proposition per applicable stable obligation ID;
- metadata for every obligation, including `not_applicable` entries; and
- a `Complete` structure/record collecting every applicable proposition.

The generated files contain definitions only. They contain no proofs, `sorry`,
`Admitted`, axioms, SMT queries, or solver certificates. Keep implementations
of the semantic interface and proofs of `Complete` in separate user-owned
files: regeneration overwrites the definitions file named on the command line.

The trust boundary is explicit. Sail and the generated semantic-interface
declarations are untrusted statement producers. A downstream proof must
instantiate that interface with independently reviewed typed Sail and
specialized JIB/representation semantics, then prove the generated
propositions. Compiling a generated file checks syntax and typing; it does not
establish refinement by itself. Stable IDs connect those propositions to the
JSON audit artifact without relying on JIB display names or C symbols.

The focused regression suite also compiles separate Lean and Rocq consumers
whose source semantics can execute while every specialized execution, call,
conversion, and extern relation is empty. Those consumers prove that the
relevant obligations—and therefore `Complete`—are impossible. A second
consumer makes representation false and source bounds false while retaining
source well-typedness and reachability, ensuring the path-bound obligation
cannot regain a downstream premise.

## Optional independent checking and comparison

`tools/specialization_plan_checker.py` does not link against Sail. It rejects
malformed JSON, unsupported versions, duplicate or non-canonical IDs, dangling
references, incomplete unresolved indexes, invalid statuses, and missing
obligation classes. It remains useful for audits and comparisons, but it is not
part of normal compiler emission of Lean or Coq.

```sh
python3 tools/specialization_plan_checker.py model.specialization.json
python3 tools/specialization_plan_checker.py model.specialization.json \
  --emit-lean ProofFixture.lean
python3 tools/specialization_plan_checker.py new.json \
  --compare old.json --comparison-output comparison.md
```

The comparison report uses stable clone IDs, so renaming a C symbol does not
look like a semantic specialization change. The Lean adapter embeds the plan
digest, representative clone identity, and aggregate counts. It also extracts
an unsigned inferred-bound witness and discharges the corresponding
representation-adequacy inequality, demonstrating proof-level consumption
rather than JSON parsing alone.

## Compiler integration and merge notes

The implementation intentionally has a narrow overlap surface:

- `src/lib/jib_compile.ml` records provenance at the point a demanded clone is
  finalized;
- `src/lib/specialization_plan.ml` owns the shared typed obligation
  representation, identity, ordering, and all JSON/human/Lean/Coq rendering;
- `src/sail_c_backend/c_backend.ml` chooses the safe emission points;
- `src/sail_c_backend/sail_plugin_c.ml` owns the optional CLI flags.

The cleanup task may edit C naming, `--c-no-mangle`, `$target_name`, or the same
backend files. Resolve conflicts by preserving this boundary: never add backend
symbols to machine-plan identities, keep human symbols descriptive, and retain
emission after specialization but before/after naming as documented above.
No compiler behavior should depend on either output path.
