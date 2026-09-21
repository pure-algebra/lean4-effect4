# Brief for Codex: foundations slice 5 (M3b/M4) after the divergence

Repo `lean4-effect4` (Lean 4.33.1). Base: the head of `refactor/phase1-phase3` after the
divergence slice (`2026-09-21-codex-brief-foundations-divergence-slice.md`) is merged; this
slice does not start before that merge. Branch `codex/foundations-slice-5` in the worktree
`/private/tmp/effect4-foundations-slice-5`, fast-forwarded to that base by the coordinator at
dispatch; nothing is pushed. **Retargeted 2026-09-21** after the owner overruled R1 and R2:
the machine strips at a preempted skip, so `popR_typed` is unconditional and the walk premise
machinery of the earlier text (`skipsClean`, `DeliveryClean`, `NoEscape`) is not landed. This brief supersedes §2a.3 and §5 of
[`foundations slices 3–6`](2026-09-21-codex-brief-foundations-slices-3-6.md); everything else
in that brief and in the plan (`2026-09-20-foundations-plan-and-next-two-slices.md`, D1–D14)
stands. Ruling of record:
[`slices 3–4 review and the FR-08 ruling`](2026-09-21-foundations-slices-3-4-review-and-fr08-ruling.md)
with its checked evidence in `2026-09-21-foundations-fr08-evidence/`.

Goal in one sentence: **assemble the typed-state invariant on the reference machine and
prove its first hard cases, with `popR_typed` stated under the walk premise the ruling
names, so that every remaining obligation is a named, ceilinged statement rather than a
guess about interruption.**

## 0. What the ruling changed

The brief's §2a.3 repair (`DeliveryStateOk`, the entry-mask exception) was refuted by
`E4-SCHED-CE-006/007`. The coordinator then established, in
`Test/Counterexamples/Machine/Semantics/InterruptEscape.lean` (`E4-SCHED-CE-008`), that the
state behind those counterexamples is reachable from a checker-typed source program on both
Lean machines, and that the pinned rc.112 source does the same end to end: an interrupt
recorded while a fiber is masked, followed by a failure leaving the masked region, makes
`popR` (and `internal/core.ts:540-545`) skip every interruptible catch, and the fiber exits
with the original typed failure. `Effect<number, never>` completes with `Fail 42`. A re-masked
walk then runs a `nat`-typed handler on a string and dies with the bad-shape defect from
defect-free source.

So no invariant of the form "every reachable delivery fits its declared error column" is
true of the reference machine, and none should be attempted. The ruling:

- **R1 (overruled, ruling §4).** The machine diverges from rc.112 as a signed divergence
  (`U-01`): at a preempted skip of a catch that would have run, both walks pass on
  `Cause.combine (stripFail cause) ic` instead of the original failure. That landed in the
  divergence slice; this slice changes no runtime source.
- **R2 (overruled, ruling §4).** The typed-state theorem is unconditional. The sanitized
  exit at a preempted skip is `Fail`-free, so it fits every effect type
  (`strongExit_of_clean`); no run premise exists.
- **R3.** `FrameAccepts.resume.skip` becomes guard-miss-only, and every frame arrow reads
  `StrongExit`/`TypedProg` instead of `ExitFits`/the parameter. The former all-failures
  disjunct was standing in for the preemption case, which the walk premise now carries.
- **R4.** `InterruptProvenance` stays as the frame premise: the causes `popR` and `deliverR`
  inject on the success paths are recorded interrupts, which fit every effect type.
- **R5.** The interpreter hook contracts landed as `True` in `Residual.lean` are filled, and
  `popR_typed` is generic in the interpreter under a `HookLaws` record; the concrete
  `interpR` instance is a separately named, open M5 obligation.

## 1. Standing constraints

As in the slices 3–6 brief §2: one compiler per checkout; explicit paths; nothing pushed;
`-DwarningAsError=true`; receipts and evidence force-added under `docs/research/`;
statements before proofs with `#proof_wanted` markers under a gate with an exact ceiling in
the same commit; no `first`, `simp_all` or `try` by hand; the registration shapes of the
Phase C receipt; narrow builds, `make check` at the end. Stop the slice and record the
smallest amendment on a checked counterexample to a frozen statement, a relation needing
runtime data the machine does not carry, a reachable case a source row refuses, or an
interface that cannot state a hard case.

The old `E4-SCHED-CE-006/007` files stay as they are: they refute the input audit's
proposal, which is what their `Reviewed…` names say. Do not rename them.

## 2. Files

- `Typed/Contracts.lean`: the R3 amendment only (old and new statements below).
- `Typed/Residual.lean`: `frameProtocols` becomes `frameProtocols (root : NativeEff)` with
  the real hook arrows (§3.3); nothing else moves.
- New `Typed/Stack.lean`: `cleanExit`, `strongExit_of_clean`, `HookLaws`, `popR_typed`,
  `saveAnswerR_typed`, `deliver_active`, `deliver_stale`.
- New `Typed/Assembly.lean`: `preds`, `TypedState`, `RReachable`, `AnswersOk`,
  `typedState_load` (marker), `capture_lookup`.
- New `Typed/Adequacy.lean`: the declared M6 delivery-adequacy obligations (§3.6).
- New `Laws/Machine/Keeps.lean`: the unary `Keeps` ladder (imports `Machine/Fibers` only).
- Controls: new `Test/Program/TypedStack.lean` and `Test/Program/TypedStateContract.lean`,
  both added to `Test/All.lean`. Read `2026-09-21-foundations-fr08-evidence/SkipsCleanProbe.lean`
  and `DivergenceProbe.lean` first: `cleanExit`, `strongExit_of_clean`, the amended frame
  contract and `masked_stack_accepted` are the checked seed of `Typed/Stack.lean`;
  `skipsClean`, `masked_walk_not_clean` and `interrupt_walk_clean` are historical and are
  not landed.

## 3. Statements

### 3.1 The R3 amendment to `FrameAccepts` (record old and new in the receipt)

Old (`Contracts.lean:31-36`):

```lean
| resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
    (run : ∀ ex, ExitFits w tin ex → kind.hasExitArm ex = true → TypedProg w tout (next ex))
    (skip : ∀ ex, ExitFits w tin ex →
      (kind.hasExitArm ex = false ∨ ∃ cause, ex = .failure cause) → ExitFits w tout ex) :
    FrameAccepts w tin tout (.resume kind next)
```

New, with `StrongExit` imported through a parameter `Exits : World → EffTy → ExitV → Prop`
beside `TypedProg` (Contracts must not import Admission; `SavedOk`, `ResumeOk` and the
`Example` namespace take the same parameter):

```lean
| resume {tin tout : EffTy} (kind : GuardKind) (next : ExitV → RProgram)
    (run : ∀ ex, Exits w tin ex → kind.hasExitArm ex = true → TypedProg w tout (next ex))
    (skip : ∀ ex, Exits w tin ex → kind.hasExitArm ex = false → Exits w tout ex) :
    FrameAccepts w tin tout (.resume kind next)
| answer {tin tout : EffTy} (next : ExitV → RProgram)
    (run : ∀ ex, Exits w tin ex → TypedProg w tout (next ex)) :
    FrameAccepts w tin tout (.answer next)
```

The other five arms are unchanged. Reason: the all-failures disjunct rejected every
error-removing catch (`StackProbe.lean:23-33`) while standing in for preemption, and
`E4-SCHED-CE-008` shows preemption is a run-level fact, not a frame-level one. Add the
register row citation to the amendment comment.

### 3.2 The clean-exit lemma (`Typed/Stack.lean`)

Exactly the probe's `cleanExit` and `strongExit_of_clean : cleanExit (.failure c) = true →
StrongExit w ty (.failure c)` (proved at `[propext, Quot.sound]`), plus
`sanitize_clean_exit : cleanExit (.failure (Cause.sanitize cause ic)) = true` for
`InterruptProvenance`-recorded `ic` (from `Cause.sanitize_clean`). These are the only facts
the sanitized branch of `popR` needs. No walk predicate, no per-fiber delivery predicate, no
run-level premise.

### 3.3 Hook contracts and `HookLaws`

`frameProtocols (root : NativeEff) : Contracts.FrameProtocols`:

- `asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, cause.hasInterrupts = true →
  TypedProg root w tout ((interpR root).cancelThenFail name cause)`.
- `iterator w tin tout name := tin.error = tout.error ∧ ∀ v, StrongValue w tin.answer v →
  match ((interpR root).iterNext name v).2 with
  | .done result => StrongExit w tout (.success result)
  | .halt cause => StrongExit w tout (.failure cause)
  | .resume code next => ∃ tin', TypedProg root w tin' code ∧ iterator w tin' tout next`
  (an inductive or a coinductive-free well-founded formulation; state which and why).
- `loop w tin tout name cursor := tin.error = tout.error ∧ ∀ v, StrongValue w tin.answer v →
  match (interpR root).loopResume name cursor v with
  | .continue next body => ∃ tin', TypedProg root w tin' body ∧ loop w tin' tout name next
  | .finish code => TypedProg root w tout code`.

`HookLaws (interp : RInterp) (hooks : FrameProtocols) : Prop` is the record of exactly the
facts `popR`'s `asyncFinalizer`, `iter` and `loop` arms need from `hooks` about `interp`;
`popR_typed` is proved for every `interp` satisfying it. `hookLaws_interpR root :
HookLaws (interpR root) (frameProtocols root)` is declared with its marker in gate
`Typed.M5Hooks` at ceiling 1 and stays open: it needs S1.

### 3.4 The hard proofs, in order (gate `Typed.M4Stack`, ceiling 0 at finish)

1. `popR_typed`: the probe's `PopRTyped` with the landed `FrameAccepts`/`StackAccepts`
   in place of the primed copies, `HookLaws interp hooks` as a premise, and **no walk
   premise**: for all `interp w tin tout ex stack frame`,
   `StackAccepts (TypedProg root) StrongExit hooks w tin tout stack → StrongExit w tin ex →
   InterruptProvenance frame →` match on
   `popR interp ex stack frame`: `(frame', none)` gives `∃ middle, TypedProg root w middle
   frame'.current ∧ StackAccepts … w middle tout frame'.stack ∧ InterruptProvenance frame'`;
   `(_, some ex')` gives `StrongExit w tout ex'`. Prove by the recursion of `popR`. The arms:
   masks inject the recorded cause (`strongExit_of_clean` through `InterruptProvenance`);
   a run arm uses `run`; a guard miss uses `skip`; a preempted skip passes the sanitized
   exit, clean by `sanitize_clean_exit`, so `strongExit_of_clean` types it at every
   `tout'`; `answer` glue uses `run`, `Typed.pure_inv` and
   `typedProg_unguard_inv`; the hook arms use `HookLaws`. The `onExit` push of
   `finalizerMask` is the identity arrow at the handler's output type.
2. `saveAnswerR_typed`: pushing `.answer next` with `run` preserves `SavedOk` at the
   operation's own type.
3. `deliver_active`: a fiber parked at `.withGuard token` receiving `resume target token code`
   installs `current := code`, `parked := .notParked`, and `TypedProg root w tin code` where
   `w.Θ target token = some tin`; the frame's stack is unchanged, so `SavedOk` follows.
4. `deliver_stale`: a mismatched token leaves the fiber unchanged (`f' = f`).
5. `capture_lookup`: an addressed capture's environment is the checker's environment at
   `Node.at_ (.eff root) capture.path`.
6. The `Keeps` ladder in `Laws/Machine/Keeps.lean`.

### 3.5 Assembly (`Typed/Assembly.lean`)

`preds`, `TypedState`, `RReachable`, `AnswersOk` and `typedState_load` exactly as the old
§5 states them (D7, D14, the strong leaves, the active-delivery correlation). There is no
run-level premise: the M7 corollaries (no `badShape`, no halting) are stated over
`RReachable` and `AnswersOk` alone.

### 3.6 Declared delivery adequacy (`Typed/Adequacy.lean`, gate `Typed.M6Adequacy`)

The slices 3–6 brief asked for an actual-delivery adequacy obligation for every answered
`Ψ_F` row; `ef38bf11` landed rows whose `pre`/`post` are `True` for most of categories 1–3
and declared no such obligations. Declare them now, one theorem obligation per row whose
post is `True` or `ans = …` only, of the shape "at a `TypedState` whose fiber performs this
row, the actual `evaluateFiberR` answer satisfies a stated non-trivial post at the
resulting world", with `#proof_wanted` and ceiling equal to their count. Print the
constructor-to-obligation table from `#answer_gate` (extend it to name, per row, whether the
manifest post is non-trivial and which obligation covers it; it still counts 31 + 40). Do not
prove them in this slice; do not leave them unnamed.

## 4. Controls

`Test/Program/TypedStack.lean`: `masked_stack_accepted` and the interrupt-only fit from the
probe; the sanitized skip on the `E4-SCHED-CE-006` state typed at the catch's output
(`diverged_fits` on the landed `popR`); an error-removing catch that runs
(`onFailure`, `Nat → never`, handler typed); a `Nat → never` guard miss on a success; the
`onExit false` arm running under a recorded interrupt with the pushed `finalizerMask`; a
wrong-middle negative (a stack whose frames do not compose, `¬ StackAccepts`); a stale token
that does not deliver (`deliver_stale` observed on `stepDecisionState`). `Test/Program/
TypedStateContract.lean`: elaboration of `TypedState`, `RReachable` and `AnswersOk`; the
`E4-SCHED-CE-008` poisoned root's exit fits its checked type on the landed machine (a
`#guard` on `replayR` plus `strongExit_of_clean`).

## 5. Build, finish, receipt

`lake build Effect4.Laws.Program.Typed.Contracts Effect4.Laws.Program.Typed.Residual
Effect4.Laws.Program.Typed.Stack Effect4.Laws.Program.Typed.Assembly
Effect4.Laws.Program.Typed.Adequacy Effect4.Laws.Machine.Keeps Test.Program.TypedStack
Test.Program.TypedStateContract`, then `make build`, `make check`.

Finish: `popR_typed`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale`,
`capture_lookup` and the ladder at `[propext, Quot.sound]`; `hookLaws_interpR` and
`typedState_load` open at their declared ceilings; `M6Adequacy` fully declared, zero proved;
the receipt in `2026-09-21-foundations-slice5-receipt.md` with base and head, every
statement with its gate and ceiling before and after, the old/new `FrameAccepts` text,
the axioms of every proof, the red-then-green control logs, the commands with exit codes,
and the unique ledger line with every open name. If `popR_typed` needs a premise beyond
`InterruptProvenance` and `HookLaws`, stop, retain the counterexample as `E4-SCHED-CE-009`,
and amend the divergence before any S2 work.
