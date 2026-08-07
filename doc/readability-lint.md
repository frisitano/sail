# Sail readability lint

`--lint-readability` enables an opt-in, backend-independent hygiene audit at
three compiler boundaries:

1. the parser AST, before operator and literal elaboration;
2. the typed Sail AST, after transitive effects have been attached; and
3. post-specialization Jib, before an extraction backend consumes the IR.

Every diagnostic has a stable rule ID. Post-Jib diagnostics unwrap generated
locations to the originating Sail range and suppress only instructions with no
recoverable source location. The linter never uses regular expressions over
Sail source text.

## Parser Sail rules

| Rule | Diagnostic | Safety condition |
| --- | --- | --- |
| `sail-nested-function-call` | A function argument contains another explicitly written named function call | Name the inner result before the outer call so evaluation order and source intent remain explicit |
| `sail-function-call-condition` | An `if`, `while`/`until`, match subject/guard, or assertion predicate contains an explicitly written named function call | Name predicate and subject results before control-flow selection; infix operators and compiler-generated helpers are not treated as source calls |
| `sail-identity-conditional` | Authored `if c then true else false` and its inverse | Rewrites preserve evaluation count |
| `sail-constant-conditional` | An authored conditional with a literal condition | The unreachable branch is not evaluated by Sail |
| `sail-else-after-terminal` | An explicit else arm follows an authored return, throw, or exit | The terminal arm cannot fall through; the else body can follow the conditional |
| `sail-prefer-early-return` | A function-tail conditional has one explicit unit arm and one non-empty arm | Returning from the empty arm and continuing with the non-empty arm preserves the function result; non-tail conditionals are excluded |
| `sail-nested-else-if` | An `else` block contains only another conditional | Removing the redundant block preserves the conditional expression and branch order |

## Typed Sail rules

| Rule | Diagnostic | Safety condition |
| --- | --- | --- |
| `sail-redundant-bool` | Literal boolean comparisons, literal negation, and double negation | Rewrites preserve evaluation count |
| `sail-duplicate-branches` | A pure condition selects structurally identical branches | Removing the conditional preserves evaluation because the condition has no effects |
| `sail-empty-conditional` | A pure condition selects two unit literals | Removing the conditional preserves evaluation because the condition has no effects |
| `sail-conditional-assignment` | Both arms assign a value to the same simple local | Assigning one conditional value preserves branch laziness and evaluates the local destination once |
| `sail-trivial-alias` | A let-bound value returned unchanged | The bound expression is still evaluated once |
| `sail-single-use-temporary` | A pure, single-use `tmp`/`temp` binding | Requires an attached empty effect set; semantic names are retained |
| `sail-dead-pure-binding` | An unused wildcard binding of a pure expression | Requires an attached empty effect set |

The single-use rule intentionally does not diagnose semantic source names or
effectful initializers. A name can document a protocol invariant even when it
has one use, and an effectful call cannot be removed or reordered merely
because its result is inconvenient.

## Post-Jib rules

| Rule | Diagnostic | Safety basis |
| --- | --- | --- |
| `jib-declaration-assignment-split` | Adjacent declaration and first assignment | Structural; no transformation is performed by the linter |
| `jib-unit-plumbing` | Unit locals and explicit unit returns | Unit has one value; backend ABI erasure remains backend-owned |
| `jib-single-use-pure-temporary` | Single-use generated temporary initialized from a Jib value | Jib values are pure and the local is not rewritten |
| `jib-dead-pure-temporary` | Unread generated temporary initialized from a Jib value | Jib values are pure and the local is not rewritten |
| `jib-redundant-bool` | Literal boolean operations and double negation | Jib value operations are pure |
| `jib-constant-conditional` | Conditional with a literal condition | Structural |
| `jib-empty-conditional` | Conditional with two empty branches | The Jib condition is a pure value |
| `jib-duplicate-branches` | Conditional with structurally identical branch bodies | Instruction locations are ignored; Jib operations and control flow must match |
| `jib-conditional-assignment` | Two pure branch values assigned to the same destination | Jib values are pure; backend recovery must preserve the single condition evaluation and destination conversion |
| `jib-else-after-terminal` | Else branch retained after a return, throw, or exit | The then branch cannot fall through |
| `jib-partial-branch-initialization` | An immediately consumed local is initialized on only one fallthrough branch | Requires a declaration/conditional/read sequence and accounts for terminal arms |
| `jib-identity-copy` | Copy from a local to itself | Structural |
| `jib-redundant-join` | Jump to the immediately following label | Control-flow preserving |
| `jib-redundant-scope` | Empty or singleton block/try block | Structural; the backend decides whether to flatten it |
| `jib-dead-label` | Label with no incoming jump | Whole-body jump-target analysis |
| `jib-lost-source-name` | Generated local without retained source-name provenance | Reported only with a recoverable source range |

## Branch diagnostics

Branch cleanup is split by the information needed to prove it safe.

| Pattern | Owner | Reason |
| --- | --- | --- |
| Literal condition | Parser Sail and post-Jib lint | The selected branch is known without C semantics |
| Boolean identity/inverse | Parser Sail and post-Jib lint | Evaluation count is preserved |
| Identical branch bodies | Typed Sail and post-Jib lint | Typed Sail requires a pure condition for direct removal; Jib also inventories residual lowered clones |
| Same-local branch assignment | Typed Sail and post-Jib lint | The source rule requires a simple local destination; Jib proves the common lowered destination |
| Else after a terminal then-arm | Parser Sail and post-Jib lint | The parser AST distinguishes an explicit else from Sail's synthesized unit arm; Jib catches structure introduced by lowering |
| Local initialized on only one fallthrough arm | Post-Jib lint | Jib exposes declarations, writes, terminal arms, and the consuming read |
| Redundant forward join or dead label | Post-Jib lint | Requires lowered control-flow targets |
| Exhaustive Sail pattern match | Sail type/pattern checker | The source union or enum, not its C representation, defines exhaustiveness |
| Exhaustive generated C enum switch | Clang `-Wswitch-enum` | Verifies the final C mapping and any backend-introduced cases |
| Covered/default C switch syntax | Clang `-Wcovered-switch-default` | C-only switch policy |
| Prefer positive condition | No blanket warning | Failure-first guard clauses are intentional and often clearer; only the provably tail-position empty-arm case gets `sail-prefer-early-return` |

## Ownership of cleanup findings

The lint is deliberately not a second C parser. The cleanup work that motivated
these rules is divided as follows.

| Cleanup family | Disposition |
| --- | --- |
| Authored call placement, boolean identity conditionals, constant conditions, and terminal else arms | Parser Sail lint; canonical rewriting stays source-owned |
| Boolean operator identities, trivial aliases, and pure source temporaries | Typed Sail lint; canonical rewriting stays compiler-owned |
| Branch clones and asymmetric fallthrough initialization | Post-Jib lint; corresponds to `bugprone-branch-clone` and the backend-independent core of `-Wuninitialized` |
| Terminal else arms | Parser Sail and post-Jib lint; corresponds to `readability-else-after-return` before and after lowering |
| Unit arguments/results/locals and discarded unit call results | Post-Jib lint plus C unit-erasure transformation; non-C backends choose their own unit representation |
| Split declarations, pure generated copies, dead/single-use temporaries, and conversion-copy scaffolding | Post-Jib lint; pure-copy propagation, conversion folding, return sinking, and declaration initialization remain compiler transformations |
| Redundant blocks, forward joins, fallthrough gotos, match joins, and dead labels | Post-Jib lint; scope flattening and control-flow restructuring remain compiler transformations |
| Lost semantic local names and redundant aggregate return copies | Post-Jib provenance lint; named aggregate-return consolidation remains a compiler transformation |
| Aggregate construction/fixed-bitvector web scaffolding | Compiler transformation; there is no stable source-level warning when the aggregate is semantically meaningful |
| Short-circuit diamonds and bounded-integer predicates | Compiler transformation after Jib proof/type information is available; the linter reports only residual safe boolean shapes |
| Code following the optimized model's fatal boundary | Optimized-C compiler transformation; the canonical Sail effect model remains backend-independent |
| Unreferenced top-level letbinds and unused internal parameters/specializations | Compiler whole-program elimination; source unused-binding checks remain the existing Sail linter's responsibility |
| Branch polarity and guard-clause layout | Parser Sail lint only for explicit unit arms in function-tail conditionals; no generic polarity rule |
| C integer conversions, signedness, overflow, ABI/layout, padding, `_Noreturn`, prototypes, include hygiene, allocation APIs, unchecked library results, C standard compatibility, switch syntax, and formatting | Clang diagnostics, clang-tidy, clang-format, or the C backend; these have no backend-independent Sail meaning |

C-only findings remain C-only because other extraction targets do not share C
integer promotion, object representation, library, or ABI rules. Promoting
those checks to Sail would either be meaningless or would impose a C
representation on the specification.
