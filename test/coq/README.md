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
