# Coq backend regression cases

Minimal Sail inputs for Coq-backend defects. Each is small enough to read
and to run by hand:

```sh
sail --coq --coq-output-dir OUT -o m test/coq/<case>.sail
```

- `mutrec_mixed_measure.sail` — a mutually recursive group where only one
  member declares a `termination_measure`. This used to emit Coq that could
  not compile: the measured member carried `(_reclimit, _acc)` and
  `{struct _acc}` while the unmeasured member carried neither, so the
  emitted mutual `Fixpoint` had no decreasing argument in every branch
  (`Cannot guess decreasing argument of fix`); and the unmeasured member
  called the measured member's entry-point wrapper, which is emitted after
  the block and so is not in scope inside it (`The variable f was not found
  in the current environment`). Sail now rejects the mixed group with a
  message naming the members that need a measure.

- `mutrec_all_measured.sail` — the same group with measures on both
  members. Generates, and the generated Coq compiles.

- `constraint_obligations.sail` — a function with a `forall 'n, 0 <= 'n &
  'n < 256` constraint, plus a caller. By default the constraint is emitted
  as a comment, so the Coq type admits values the Sail type forbids and any
  downstream proof re-derives the bound by hand. Under
  `--coq-constraint-obligations` it becomes a hypothesis
  `(_sailConstraint0 : (0 <=? n) && (n <? 256) = true)` and the call site
  supplies it with `ltac:(sail_constraint)`. Generate both ways and compile:

  ```sh
  sail --coq --coq-constraint-obligations --coq-output-dir OUT -o c \
      test/coq/constraint_obligations.sail
  (cd OUT && rocq c c_types.v && rocq c c.v)
  ```
