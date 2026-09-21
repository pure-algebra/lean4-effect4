# FR-08 evidence: the typed-failure escape is source-reachable and is rc.112's behaviour

Companion to `../2026-09-21-foundations-slices-3-4-review-and-fr08-ruling.md`.

`VendorEscapeProbe.ts` runs the pinned rc.112 source end to end with bun 1.4.2. The child
fiber is `Fiber<number, never>`: `catchCause(uninterruptible(await latch >> fail 42), _ =>
succeed 0)`. Row `poison=false` completes the latch with no interrupt and the catch runs
(`Success 0`). Row `poison=true` records an interrupt while the child is masked, then
completes the latch: the fiber exits `Failure Cause([Fail(42)])`. `vendor-escape.json` is
the output; `vendor-sha256.json` pins the six source files the probe loads. Run it from the
repository root:

```sh
bun docs/research/2026-09-21-foundations-fr08-evidence/VendorEscapeProbe.ts
```

The same two runs on the Lean machines are the checked battery
`Test/Counterexamples/Machine/Semantics/InterruptEscape.lean` (`E4-SCHED-CE-008`), whose
`lake env lean` log is `interrupt-escape.log`: the frame machine (`Api.replay`) and the term
evaluator (`replayR`) both exit `Fail 42` from a program the checker types at answer `nat`,
error `never`, with the tape `[evaluate, interruptFrom root, answerAsync root 0 (success unit)]`.
The second program in that file re-masks the walk with `interruptible`'s restoration so the
escaped string failure reaches a `nat`-typed catch: both machines die with the bad-shape
defect from a source program that contains no defect.

`SkipsCleanProbe.lean` (log `skips-clean.log`) elaborates the ruling's replacement contract:
the interpreter-free walk predicate `skipsClean`, the lemma that a `Fail`-free failure fits
every effect type, the guard-miss-only frame contract, the slice 5 `popR_typed` statement
with the walk premise, and two finite controls on the `E4-SCHED-CE-006` state: the amended
contract accepts that stack, and the walk is not clean (`rfl`), while the same walk with an
interrupt-only failure is clean and fits. Run it from the repository root:

```sh
lake env lean -DwarningAsError=true docs/research/2026-09-21-foundations-fr08-evidence/SkipsCleanProbe.lean
```

`DivergenceProbe.lean` (log `divergence.log`) checks the owner's amendment (ruling §4): a copy
of `popR` with only the preempted-skip branch changed to pass on
`Cause.combine (stripFail cause) ic` ends the `E4-SCHED-CE-006` walk with the interrupt-only
failure, which fits the catch's output type; a defect in the original failure is retained;
the sanitized cause is `Fail`-free for every input; the replace-by-interrupt alternative drops
defects. `skipsClean` in `SkipsCleanProbe.lean` is historical after that amendment.

These are exact runs and elaborated statements. No decision-tape family, whole-machine
preservation or replacement runtime is claimed; `popR_typed` itself is slice 5's proof.
