# A simulation theorem between the frame machine and `interpret`

Status: research, 2026-09-03. Read-only survey; nothing in `Effect4/` was changed.

## Verdict up front

A simulation theorem is provable today, but not the one the question names, and
not against `interpret` alone.

1. The `pure`/`bind`/`perform`/`fail` half is provable against
   `Effects.interpret` **relative to an answer tape**, because
   `PrimInterp` is a record of *pure total functions*
   (`Effect4/Runtime/Runtime.lean:191-219`) and the machine therefore has no
   place to put a handler's monad. The theorem is a control-flow simulation
   modulo an oracle, not "the machine computes `interpret`".
2. The `onExit`/`acquireRelease`/finalizer half is **not statable against
   `Program` at all**: `Program` (`lean4-effects/Effects/Algebra/Program.lean:16-21`)
   has `pure` and `vis` and no bracket former, and `Handler.handle`
   (`.../Algebra/Handler.lean:13-15`) takes an operation, never a
   subcomputation. That half must be stated against
   `Effect4.Flow.runRegions` (`Effect4/Flow/Region.lean:157-161`), which is the
   only Lean face in either repo with `enter`/`leave`/`finalizer` semantics.
3. As stated in the question — "`run` yields the exit `interpret` computes and
   the `ranFinalizer` sequence equals the finalizers the handler ran" — the
   theorem is **false** for one concrete reason before any of the above:
   the machine merges a failing finalizer into a failing body with
   `Cause.combine` (`Effect4/Semantics/Exit.lean:63-68, 172-176`), and the
   region runner keeps only the first failure and discards the release's
   (`Effect4/Flow/Region.lean:65-92`, and its own docstring at `:17-19`). See §5.

## 1. The fragment and the compilation

### 1.1 The type obstruction, and why the lowering fragment dodges it

`Program S A` stores `vis op (next : S.Answer op → Program S A)`: the
continuation is dependently typed in the operation. `PrimInterp.contA : ν → β →
Prim …` (`Runtime.lean:194`) is not. So there is no compilation from a general
signature. Two ways out:

- a retraction `enc op : S.Answer op → β`, `dec op : β → S.Answer op` with
  `dec op (enc op a) = a`, carried as a hypothesis; or
- restrict to a **monomorphic family**, `F = alphabet.toFamily (fun _ => Val)`
  (`lean4-effects/Effects/Family.lean:71-74`), where every request and answer is
  `Effects.Trace.Val`.

The second is free, because it is already the shape every lowering uses:
`FlowService.handle : alphabet.Op → Val → M Val`
(`Effect4/Semantics/Runs.lean:52-55`), `RegionService.handle` returning
`Except Val Val` (`Effect4/Flow/Region.lean:29-32`), and `Script`/`PureTerm` at
the straight-line face (`Effect4/Target/TypeScript/EffectV4.lean:150-278`). Take
`β := Val`, `ε := Val`, `δ ι α := Unit`. All four `DecidableEq` instances that
`armA`, `armE`, `step` and `run` demand (`Runtime.lean:718, 750, 1663, 1724`)
are then available; note they are demanded on the *cause* alphabets, never on
`ν` or `σ`, so the name alphabets are unconstrained.

The goldens are `Program Cell.Sig Nat` (`harness/trace/Generate.lean:98-111`),
so either instantiate `β := Nat` for those or pay the retraction. Say which; do
not leave it implicit.

### 1.2 The compilation

```text
ν := Nat            -- index into a continuation table
σ := Nat            -- index into an answer tape (occurrence number)
compile : Nat → Program S Val → Prim Nat Nat Val Val Unit Unit Unit
compile i (.pure v)      = Prim.success v
compile i (.vis op k)    = Prim.onSuccess (Prim.sync i) (nameOf i op)
  with  interp.syncValue i = tape[i]!
        interp.contA (nameOf i op) a = compile (i+1) (k a)
```

The counter is uniform across branches (every branch of a `vis` is compiled at
`i+1`), so `compile` is a plain structural recursion and the σ-name of the
`n`-th performed operation is `n` on every path. Abort compiles to
`Prim.failure (Cause.fail e)`; a `catch`-shaped handler compiles to
`Prim.onFailure body n`; a region compiles to `Prim.scopedFrame body closeName`
(`Runtime.lean:2156-2159`), which is `Prim.onExit body closeName false`.

**In the fragment:** `success` (`:95`), `failure` (`:97`), `sync` (`:99`),
`onSuccess` (`:109`), `onFailure` (`:111`), `onSuccessAndFailure` (`:113`),
`onExit` (`:118`), and `setInterruptible` (`:120`) **only** as the frame that
`onExit`'s `ensure` pushes (`:558-566`) — never as a compiled body, because a
`SetInterruptible` that is stepped as the current effect is a defect
(`FrameFiber.step_setInterruptible_not_evaluable`, `:1964`).

**Outside:** `suspend` (`:101`) and `withFiber` (`:103`) — thunk names with no
algebra counterpart, the second theorem-refused (`Prim.withFiber_refused`,
`:2179`); `yieldableError` (`:105`), refused (`:2190`); `iterator` (`:107`),
whose inline fold is *supplied data* (`iterator_folds_inline`, `:1091`) and has
no algebraic shadow; `exitFrame` (`:116`), whose `contA` turns an `Exit` into a
value through `PrimInterp.reifyExit` (`:911`, `:203`) — the algebra has no value
that is an exit; `whileLoop` (`:122`), because a `Program` loop is an infinite
tree and `Program` has no loop former. The mask combinators
(`uninterruptible`, `setFiberInterruptible`, `interruptibleRegion`,
`uninterruptibleMask`, `restoreAcquire`, `:2045-2081`) are outside; the
fragment must *prove* they are never entered, not assume it.

### 1.3 The invariant that makes it tractable

Nothing in `Runtime.lean` ever writes `interruptedCause`. `FrameFiber.start`
sets it to `none` and `deferredInterrupt` to `false` (`:293-302`); `ensure`
only reads it (`:558-587`); `getCont` only clears the deferred flag
(`:1181-1191`). So

```lean
theorem step_preserves_uninterrupted :
    self.interruptedCause = none → self.deferredInterrupt = false →
      (step interp self).1 = .running next →
        next.interruptedCause = none ∧ next.deferredInterrupt = false
```

is provable, and under it `FrameFiber.interrupted` (`:316`) is constantly
`false`, so the skip guard in `popFrom` (`:1163`) never fires, `getCont`'s
deferred branch never fires, and `ensure_setInterruptible_no_pending` (`:674`)
makes the pushed mask frame a pure flag write with no replacement. **The entire
interrupt half of the machine is inert in this fragment.** This is what turns
the theorem from a research problem into a packet.

## 2. The theorem

The algebra-side monad that matches `Exit` is `ExceptT (Cause ε δ ι α) M`, not
`ExceptT ε M`: `Exit` is `success β | failure (Cause ε δ ι α)`
(`Effect4/Semantics/Exit.lean:26-31`) and `Cause` is a list of `Reason`s
(`Effect4/Semantics/Cause.lean:579-583`). So

```lean
def exitOf : Except (Cause ε δ ι α) β → Exit β ε δ ι α
  | .ok v => .success v | .error c => .failure c   -- a bijection
```

If the handler's error is the raw user error (as `FCell` uses `String`,
`Generate.lean:80-87`), the map is `Cause.fail`-composed and is *not* a
bijection: a two-reason cause has no algebra-side preimage. State the theorem at
`E := Cause`, and record the `Cause.fail` specialisation as a corollary.

The carrier order is `ExceptT (Cause …) (StateT Log (StateT St Id))`, which is
already the order `Family.Service.tracedExcept` uses (`Generate.lean:109-115`)
and the plan's ruling ("the log survives failure").

```lean
theorem compile_simulates
    {alphabet : Alphabet Ty} (S := (alphabet.toFamily (fun _ => Val)).toSignature)
    (H : Handler S (ExceptT (Cause Val Unit Unit Unit) (StateT St Id)))
    (p : Program S Val) (s0 : St) (tape : List Val)
    (hOracle : answersOf H p s0 = tape)
    (fuel : Nat) (hfuel : bound p ≤ fuel) :
    (FrameFiber.run (tapeInterp tape) fuel (FrameFiber.start (compile 0 p))).1
      = FrameStep.finished (exitOf ((interpret H p).run.run s0).1)
```

`answersOf` is a second structural recursion over `p` that threads the same
state and collects the handler's answers; `hOracle` is what makes the pure
`PrimInterp` legitimate. Be blunt about what this buys: the answers are
*supplied*, not computed, so the content of the theorem is that the machine's
**control flow** — which continuation runs, in which order, with which exit —
equals the algebra's, given agreeing answers. Anyone reading it as "the frame
machine computes `interpret`" is over-reading it. That is still the standard
statement of a simulation modulo an effect oracle, and it is the statement the
census rows need.

### Fuel adequacy

**Provable for the compiled fragment; not provable in general.** For arbitrary
`Prim` plus arbitrary `PrimInterp` there is no measure: `contA n v =
onSuccess (success v) n` diverges, and `weight = size current + Σ size stack`
already fails on `step_onSuccess` (`:1904`), which replaces a term of size
`size body + 1` by `body` with the whole frame pushed. The bound must come from
the *source*: `bound (.pure _) = 1`, `bound (.vis _ k) = 3 + sup over the taken
branch`, discharged along the tape. DB-04 (`docs/DESIGN-BASIS.md:154-172`)
forbids the `∀ fuel` form — exhausted fuel is a live frontier, never a result —
so the statement must be `∀ fuel ≥ bound p`, and that needs a lemma the module
does not have: `run` has only `run_zero`, `run_succ_finished`,
`run_succ_running` (`:2022-2043`), no `run_add` and no monotonicity. Add
`run_add : run interp (m+n) f = ...` first.

### The finalizer half

`FrameEvent.finalizersRun` (`:376`) has no algebra-side counterpart, because
`Program` has no bracket. Against the region runner it does:

```lean
theorem regions_simulate … :
    FrameEvent.traceOf region val err defect
        (FrameFiber.run interp fuel (FrameFiber.start (compileRegion flow))).2
      = Effects.Trace.project finalizerAndOutcomeMask
          (((runRegions fuel flow service nameOf tape input).run []).2)
```

The statement shape already exists: `FrameEvent.toTrace` sends `ranFinalizer` to
`.finalizer` and `yielded` to `.done` and everything else to `none`
(`Effect4/Target/TypeScript/Simulation.lean:44-51`), and `traceOf` filters
(`:58-61`). Today those definitions have no consumer; this theorem is their
consumer. See §5(a) for why the equality is false without a restriction.

## 3. DB-02 and separations 4–5

DB-02 (`docs/DESIGN-BASIS.md:103-126`) closes the pure fragment at the
reification boundary: a raw closure must become a named, registered foreign
boundary. FRAMES-DAG separation 4 says a continuation is a name; separation 5
says the nested body is a subterm and that is *not* a stored closure.

The table compilation respects both, and the reason is mechanical rather than
rhetorical: with `ν := Nat` and `σ := Nat` the emitted `Prim` keeps the derived
`DecidableEq` (`Runtime.lean:123`), stays serialisable, and the Lean functions
live in `PrimInterp`, which deliberately carries no `DecidableEq` and is a
parameter to `armA`/`armE`/`step`/`run` and never a field of `Prim` or
`FrameFiber` (`:191-193`). Bodies are subterms: `onSuccess (compile p) n`
mirrors rc.112's `onSuccess[args] = self`.

**The trap to name in the packet:** the obvious compilation
`ν := Σ op, (S.Answer op → Program S Val)` elaborates fine and is exactly what
separation 4 exists to forbid. Instantiating the name alphabet at a function
type silently drops `DecidableEq` from `Prim ν …` and turns every `frame-arm`
census row from a statement about frames into a statement about Lean functions.
A gate is cheap: require `[DecidableEq ν] [DecidableEq σ]` on the compilation's
output type, or assert `DecidableEq (Prim ν σ β ε δ ι α)` in the battery.

DB-05's no-`HHandler` ruling is conditional on scoped operations storing
first-order references. `Prim.onExit` already does — the finalizer is a name and
only its *outcome exit* is supplied (`PrimInterp.finalizerExit`, `:199-200`;
`FRAME-FB-FINALIZER-EFFECT`). So the machine side owes nothing new. The algebra
side owes everything: it has no scoped operation, which is precisely why the
bracket half goes to `Flow`, where regions are `RegionRow`s with block ids.

## 4. What the theorem makes mechanical

**Census.** The join already happened (commit `5af27c4`).
`Effect4Test/Audit/RuntimeCoverage.lean:2573+` carries **99** rows, not 97:
49 `green`, 25 `partial`, 25 `absent`; `op.Success` already lists five
`FrameFiber` witnesses (`:2574-2579`). So the simulation theorem moves **no row
from partial to green**, and it should not be sold as moving a number.
`docs/RUNTIME-COVERAGE.md:43-49` defines green clause-by-clause against the
census summary; a composite theorem is not a clause of any row's summary line.

What it changes is the kind of evidence:

- `op.Success`, `op.Sync`, `op.OnSuccess`, `op.OnFailure`,
  `op.OnSuccessAndFailure`, `rule.frames-are-primitives`: today each witness is
  a single-transition equation (`step_onSuccess`, `:1904`, etc.). The
  simulation is the first statement in which the *composition* of those
  transitions means something. Record it as an added witness on
  `rule.frames-are-primitives` only, if anywhere.
- `op.Failure` stays `partial`: `FRAME-FB-STACK-ANNOTATION` needs a `Context`
  and a `StackTrace` key, and nothing here supplies either.
- `scope.scoped` and `scope.acquire-release` stay `partial` for the same
  reason (`contextWith`/`provideContext`).
- Every `FRAME-FB-*` loss stays. `FRAME-FB-RAW-FIBER` and
  `FRAME-FB-HOST-ERROR` are outside the fragment by construction.
  `FRAME-FB-ASYNC-FINALIZER` is untouched — the fragment has no
  `AsyncFinalizer`, so the fusion obligation is neither discharged nor
  worsened. `FRAME-FB-NONNULL` becomes *vacuous in the fragment* by
  §1.3 but is not retired; the invariant is a fragment fact, not a model fact.
  `FRAME-FB-MASK-CARRIER` is a cross-package correspondence and unaffected.
  `FRAME-FB-FINALIZER-EFFECT` is the one the theorem sharpens: stated against
  the region runner, whose releases are ordinary operations with their own
  `op`/`answer` rows (`Region.lean:53-77`), the loss becomes "the machine's
  finalizer contributes an exit and no frame activity, and here is the
  projection under which that is exactly the difference". Rewrite the row.

**TRACE-DAG.** `docs/TRACE-DAG.md:39` (`semantics`, `required-open`, "no
simulation theorem in this phase") is precisely the edge this closes, but only
for the Lean-to-Lean pair. It should become `required-closed` with an explicit
scope line: *the Flow runner and the frame machine agree under `m2` on the
compiled fragment* is a theorem; *the host agrees with either* is still
evidence. Do not close it globally.

`docs/TRACE-DAG.md:42` (`bridges`) does **not** close. Its stated open content
is "no theorem relates a host row to a `FrameEvent`", and no Lean theorem can
close that — FRAMES-DAG's `FRAME-L9-HOST-EVIDENCE` and the plan's refusal row
("any statement about the host from a Lean theorem") both say so. What changes
is smaller and real: `FrameEvent.toTrace`/`traceOf` stop being definitions with
no consumer, and the frame stream stops being "recorded and never compared" on
the *Lean* side. Of the plan's "What agreement does not establish" list, exactly
one item moves — "anything about primitives or frames", and only its Lean half.
Interruption, concurrency, types, layer build, host error identity, stack
annotations, defect payloads, termination and byte identity all stay.

## 5. What makes the theorem false, and the honest weaker statement

**(a) Finalizer exit merging — the blocking one.** `armA`/`armE` on `onExit`
(`:941`, `:950`) compose through `Exit.restoreAfterFinalizer`
(`Exit.lean:63-68`), so a failed body with a failed finalizer yields
`failure (Cause.combine bodyCause finalizerCause)` (`Exit.lean:172-176`;
`combine` is a deduped union, `Cause.lean:789-793`). `Flow.Region.closeFrame`
keeps only the *first* release failure and `fail` reports the body's error
unchanged (`Region.lean:65-92`), documented at `Region.lean:17-19` and pinned by
`E4-FLOW-CE-019`. The two models disagree on the failure payload on every run
where a release fails under a failing body. Options, in order of honesty:
restrict the theorem to runs with at most one failure and say so in the
statement; or add the missing `Cause.combine` to the region runner and re-pin
`E4-FLOW-CE-019`; or state agreement only under a mask that erases the payload —
but TRACE-DAG separation 3 fixes the `m1` outcome as
`(tag, reason tags in order, fail payload)`, so the payload is exactly what a
mask cannot erase. **This must be resolved before the packet is written, not
during it.**

**(b) Annotated causes.** `Cause.combine` dedupes `Reason`s that carry
`ReasonAnnotations` (`Cause.lean:28-56, 687`); two reasons equal but for their
annotations do not dedupe. If the algebra's error carrier is an annotated
`Cause`, the machine's merge is not a function of the algebra's error and the
equality fails. Restrict to `α := Unit` with empty annotations and record it as
a hypothesis, not a convention.

**(c) `exitFrame`.** Its `contA` yields `success (interp.reifyExit exit)`
(`:911`): an exit becomes a value. Keep it out of the fragment or the
compilation stops being injective and the induction has no case.

**(d) The oracle.** `PrimInterp.syncValue : σ → β` is pure and total. The
theorem is relative to a tape; anyone quoting it without the `hOracle`
hypothesis is misquoting it.

**(e) Fuel.** `∀ fuel` is false (DB-04 frontier), `∃ fuel` is weak. Use
`∀ fuel ≥ bound p` and prove `run_add` first.

**(f) Proof hygiene.** `popFrom` recomputes `frame.ensure fiber` four times per
frame (`:1158-1175`) and `resumeValue`/`resumeCause` recompute `getCont` up to
five times (`:1595-1657`). Definitionally harmless; `simp` will blow up. Plan on
`generalize`/`set` or private abbreviations from the first lemma.

## Effort and order

| # | Lemma | Lines |
| --- | --- | --- |
| 1 | `exitOf` / `ofExcept` bijection and round trips | ~30 |
| 2 | `step_preserves_uninterrupted` + `popFrom` never skips + `getCont` never defers | ~80 |
| 3 | `run_add`, `run_mono` (missing today) | ~60 |
| 4 | `run_in_context`: a compiled body under an arbitrary stack suffix finishes with its own exit and leaves the suffix untouched | ~150 |
| 5 | `compile`, `tapeInterp`, `bound`, `answersOf` | ~120 |
| 6 | `compile_simulates`, induction on `Program` | ~150 |
| 7 | finalizer half against `runRegions` (`closeFrame` is a `for` in `RunM`; its own list induction) | ~250 |

≈ 700–900 lines plus a battery and an axiom report: one packet, not one
induction. Lemma 4 is the workhorse and the only one with real risk. The plan's
D2 bar ("one induction or none") is met by items 1–6 and **not** by item 7, so
the finalizer half deserves its own fence and its own contract line.

The cheapest useful first step is item 2 alone: `step_preserves_uninterrupted`
is ~80 lines, is true of the model as it stands, is worth having independently
(it is the precise sense in which `FRAME-FB-NONNULL` is harmless), and it is the
gate on whether the rest is a week or a month.
