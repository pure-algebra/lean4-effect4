# Spike S1 — the three parking primitives in `Prim`

Deep plan `docs/research/2026-09-03-deep-plan.md`, ruling 5. This is the record of
what landed, what changed on the frozen surface, and what rc.112 does that this
vocabulary still cannot say.

- **Worktree:** `C:\Users\kokok\Dev\lean4-effect4\.claude\worktrees\agent-a8e6711ea8946c78a`
- **Branch:** `worktree-agent-a8e6711ea8946c78a` (base `main` @ `6d83533`)
- **Nothing committed.** Seven files modified in the worktree.

## 1. What was added

`Effect4/Runtime/Runtime.lean` now carries seventeen `Prim` constructors. The
three new ones are first-order names, as ruling 5 asks:

```lean
| yieldNowWith (priority : Nat)
| async (register : ν) (withSignal : Bool) (cancel : Option ν)
| asyncFinalizer (onInterrupt : ν)
```

Transcribed from `vendor/effect-4.0.0-rc.112/src/internal/effect.ts`:
`yieldNowWith` at `:982-994`, `callbackOptions`/`Async` at `:1102-1143`,
`asyncFinalizer` at `:1145-1160`.

**Arms.** `asyncFinalizer` declares exactly `[contE, contAll]` — census row
`frame-arm.AsyncFinalizer`, "declares contAll and contE and no contA".
`yieldNowWith` and `async` declare nothing and are never frames; they join the
non-frame receipt, which is now eight primitives rather than six.

**`ensure` (the `contAll` hook), `:1149-1154`.** The source reads

```ts
[contAll](fiber) {
  if (fiber.interruptible) {
    fiber.interruptible = false
    fiber._stack.push(setInterruptibleTrue)
  }
}
```

so: **it masks**; it pushes `SetInterruptible(true)` and nothing else; it does
**not** push the frame back; and it returns `undefined`, so there is **no
replacement continuation**. Three theorems freeze exactly that —
`ensure_asyncFinalizer_masks`, `ensure_asyncFinalizer_already_masked`,
`ensure_asyncFinalizer_no_replacement`. Unlike `onExit` there is no "told not to
mask" flag: rc.112 gives `asyncFinalizer` no argument beyond the cancel effect.

**`armE`, `:1155-1159`.** `hasInterrupts(cause) ? flatMap(this[args](), () =>
failCause(cause)) : failCause(cause)`. The closure is defunctionalised into one
new `PrimInterp` field, `cancelThenFail : ν → Cause ε δ ι α → Prim …`,
documented as that closure — the same pattern `finalizerExit` already uses. The
existing `PrimInterp` fields are untouched; the new one is appended last.
`Cause.hasInterrupts` did not exist, so it was added beside `Cause.combine` in
`Effect4/Semantics/Cause.lean`, transcribing `internal/effect.ts:186`
(`self.reasons.some(isInterruptReason)`) over the existing
`ReasonTag.interrupt` alphabet.

**`step`.** `yieldNowWith` and `async` return `(FrameStep.running self, [])`:
a park primitive cannot be resumed by a fiber stepped on its own, so the fixed
point is a live frontier under DB-04, not a failure, a defect or a refusal. The
docstrings say the run loop (`workshop/Deep/Fibers.lean`) intercepts both before
delegating. `asyncFinalizer` reached as `current` is a defect through
`interp.notImplemented`, exactly as `setInterruptible` is — rc.112 gives it no
`evaluate` either.

## 2. The `popFrom` obligation — unfused, not agreed

`docs/FRAMES-DAG.md:200-211` reserved this: *"A frame that pushes during
`contAll` and does not answer the demanded arm would, in rc.112, have its pushed
frame popped next; in the fused loop the push is threaded through the fiber and
restored on top of the frames that are left… The later run-loop and parking
packet that adds it must revisit `popFrom` and either prove the fusion still
agrees or unfuse the loops."*

**The fusion does not still agree. The loop was unfused.**

### The evidence

rc.112's `getCont` (`internal/effect.ts:679-694`) pops from the **live**
`this._stack`:

```ts
while (true) {
  const op = this._stack.pop()
  if (!op) return undefined
  const cont = op[contAll] && op[contAll](this)
  if (cont) { cont[symbol] = cont; return cont }
  if (op[symbol]) return op
}
```

`AsyncFinalizer` is the first frame that both pushes during `contAll` and fails
to answer a demand — under `contA` it has no arm, so it masks, pushes
`SetInterruptible(true)`, and passes. rc.112 then pops that pushed frame on the
very next iteration; `setInterruptible`'s own `contAll`
(`internal/effect.ts:4312-4320`) restores the flag and, with `_interruptedCause`
set, returns `() => failCause(cause)` — a truthy `cont`, so the pop answers with
a **replacement**. Concretely, with stack `[asyncFinalizer, onSuccess]`,
`interruptible = true`, `_interruptedCause = c`, demand `contA`:

| | answer | fiber after |
| --- | --- | --- |
| rc.112 | `replacement (failCause c)` | interruptible restored, `onSuccess` still on the stack |
| old fused `popFrom` | `frame onSuccess` | still masked, a stray `SetInterruptible(true)` left on the stack |

Both the answer and the mask state differ, and this is the mainline path: every
successful async resume pops an `AsyncFinalizer` frame under `contA`. So the
fused reading is wrong once the frame exists, and no side condition rescues it.

### What changed — a two-level loop that is still structural

`FrameFiber.popFrom` keeps its signature **and its structural recursion on the
frame list**. What changed is what happens when a frame is *passed*: before the
loop recurses on `rest`, it drains whatever that frame's hook pushed, in one
non-recursive step.

```lean
def passPushed (demand) (skip) (fiber) : FramePop :=      -- one pop off the scratch stack
  match fiber.stack with
  | [] => FramePop.mk ContAnswer.empty [] [] fiber
  | pushed :: below => …                                  -- pushed.ensure, then answerOf/skip

def joinPushed (demand) (skip) (afterHook) (rest) (tail) : FramePop :=
  match (passPushed demand skip afterHook).answer with
  | ContAnswer.empty => …            -- nothing answered: fall through to tail
  | answer          => …             -- it answered: the pop stops, rest restored under it

def popFrom … | frame :: rest, fiber => …
  -- passed:  passOn frame … (joinPushed demand skip (frame.ensure fiber).fst rest
  --                            (popFrom demand skip rest
  --                               (passPushed demand skip (frame.ensure fiber).fst).fiber))
```

`ContAnswer.empty` is the "nothing here answered" sentinel — no frame ever
answers with it — so `joinPushed` reads it as "keep going". The recursive call
is `popFrom demand skip rest …` on a structurally smaller list, so there is no
`termination_by` and no well-founded machinery.

That is the whole point of the shape. `#print axioms Effect4.FrameFiber.popFrom`
is `[propext]` — the same as before this spike — the definition reduces in the
kernel, `popFrom_nil` and `getCont_empty_stack` are `rfl` again, and
`step_ofExit_finishes` is back to `cases exit <;> rfl`, which is the receipt
that ground `decide`/`rfl` over `step` and `run` still work and that the
coverage module's kernel-reducible ground receipts survive.

**Why one level is exact, and why that is a theorem and not an assumption.**
`FrameFiber.ensure_stack_cases` — proved by cases over all seventeen primitives
— says a hook either leaves the stack alone, or pushes exactly one frame, that
the frame it pushes is `SetInterruptible(true)`, and that it can only push from
an interruptible fiber. `Prim.ensure_setInterruptible_stack` says
`SetInterruptible(true)` pushes nothing. So a second level never arises. The
drain's behaviour on that one shape is stated directly, which is the drain's
correctness statement:

- `passPushed_setInterruptible_substitutes` — a cause is already recorded: the
  drain restores the flag and substitutes `failCause(cause)` for the demanded
  arm, rc.112's `setInterruptible[contAll]` at `internal/effect.ts:4312-4320`.
- `passPushed_setInterruptible_no_pending` — nothing recorded: it restores the
  flag, answers nothing, and pops the frame.

Where a second level *could* arise the definition is still total and loses
nothing: a frame pushed by a pushed frame is left on the scratch stack and
visited by the next step rather than immediately. Nothing is dropped; the order
is simply not exercised, because `ensure_stack_cases` says that state is
unreachable.

The five `induction frames` proofs the old loop admitted stay **structural
inductions on the frame list**. Each gains one `rcases continueFrom_cases …`
step for the new branch — the frame the hook pushed answered, so the pop stops
there — discharged by a `passPushed` companion lemma
(`passPushed_answer_hasArm`, `passPushed_popped_eq_events`,
`passPushed_ranContAll`, `passPushed_skip_eq_of_no_cause`,
`passPushed_skip_all`). No proof was weakened, nothing is `sorry`, and nothing
is owed.

### The two theorems that record the decision

- `FrameFiber.popFrom_pass_no_push` — **the half that still agrees.** A frame
  whose hook pushes nothing, popped from a fiber with an empty scratch stack,
  continues on exactly `popFrom demand skip rest (frame.ensure fiber).fst`,
  which is what the fused loop did. Every frame declared before this packet is
  of that shape (`onExit` pushes but always answers; `setInterruptible` never
  pushes), so the old readings are preserved.
- `FrameFiber.popFrom_asyncFinalizer_pops_its_push` — **the half that does
  not.** For `popFrom contA false [asyncFinalizer c]` on an interruptible fiber
  with a recorded cause, the answer is `replacement (failure cause)` and the
  popped list is `[asyncFinalizer c, setInterruptible true]`: the pushed frame
  is popped inside the same pop.

`docs/FRAMES-DAG.md:200-211` is now stale and must be rewritten at the landing —
`FRAME-FB-ASYNC-FINALIZER` is discharged by unfusing, not by agreement.

## 3. Every public declaration added, changed or removed

This is the input to the frames re-freeze. Nothing was removed.

### `Effect4/Semantics/Cause.lean` — added

| Name | Signature |
| --- | --- |
| `Cause.hasInterrupts` | `{ε δ ι α : Type u} → Cause ε δ ι α → Bool` |
| `Cause.hasInterrupts_iff` | `∀ (self : Cause ε δ ι α), self.hasInterrupts = true ↔ ∃ reason, reason ∈ self.reasons ∧ reason.tag = ReasonTag.interrupt` |
| `Cause.hasInterrupts_empty` | `(empty : Cause ε δ ι α).hasInterrupts = false` |
| `Cause.hasInterrupts_fail` | `∀ (error : ε), (fail error : Cause ε δ ι α).hasInterrupts = false` |
| `Cause.hasInterrupts_die` | `∀ (defect : δ), (die defect : Cause ε δ ι α).hasInterrupts = false` |
| `Cause.hasInterrupts_interrupt` | `∀ (interruptor : Option ι), (interrupt interruptor : Cause ε δ ι α).hasInterrupts = true` |

### `Effect4/Runtime/Runtime.lean` — changed

| Name | Old | New |
| --- | --- | --- |
| `Prim` | fourteen constructors | seventeen: adds `yieldNowWith (priority : Nat)`, `async (register : ν) (withSignal : Bool) (cancel : Option ν)`, `asyncFinalizer (onInterrupt : ν)`, appended after `whileLoop` so existing constructor order is unchanged |
| `Prim.cases_receipt` | fourteen disjuncts, last `∃ loop cursor, self = whileLoop loop cursor` | seventeen disjuncts, adding `(∃ priority, self = yieldNowWith priority) ∨ (∃ register withSignal cancel, self = async register withSignal cancel) ∨ ∃ onInterrupt, self = asyncFinalizer onInterrupt` |
| `PrimInterp` / `PrimInterp.mk` | thirteen fields, last `notImplemented : δ` | fourteen; appends `cancelThenFail : ν → Cause ε δ ι α → Prim ν σ β ε δ ι α`. `PrimInterp.mk` gains a fourteenth argument at the end; every existing field and its accessor is unchanged |
| `Prim.non_frames_have_no_arms` | `(value : β) (cause : Cause ε δ ι α) (thunk : σ) (error : ε)`, six conjuncts | adds binders `(priority : Nat) (register : ν) (withSignal : Bool) (cancel : Option ν)` and two conjuncts, `arms (yieldNowWith priority) = []` and `arms (async register withSignal cancel) = []` |
| `FrameFiber.popFrom` | same type; structural recursion on the frame list, hook pushes threaded through the fiber | same type, **still structural on the frame list**; a passed frame's hook push is drained by one `passPushed` step before the recursion on `rest`. **Behaviour changes** for a frame that pushes and passes. `#print axioms` unchanged at `[propext]` |
| `FrameFiber.popFrom_continue_answer` | `… = (popFrom demand skip rest (frame.ensure fiber).fst).answer` | `… = (continueFrom demand skip frame rest fiber).answer` |
| `FrameFiber.popFrom_continue_popped` | `… = frame :: (popFrom demand skip rest (frame.ensure fiber).fst).popped` | `… = frame :: (continueFrom demand skip frame rest fiber).popped` |
| `FrameFiber.popFrom_continue_events` | `… ++ (popFrom demand skip rest (frame.ensure fiber).fst).events` | `… ++ (continueFrom demand skip frame rest fiber).events` |
| `FrameFiber.popFrom_continue_fiber` | `… = (popFrom demand skip rest (frame.ensure fiber).fst).fiber` | `… = (continueFrom demand skip frame rest fiber).fiber` |

Statements that survive verbatim and matter: `popFrom_nil`, all four
`popFrom_answer_*`, `popFrom_answer_hasArm`, `popFrom_popped_eq_events`,
`popFrom_ranContAll`, every `getCont_*`, `interrupt_skips_every_handler`,
`getCont_mask_stops_skip`, every `resume*` and every pre-existing `step_*`.
Only their proofs moved.

### `Effect4/Runtime/Runtime.lean` — added

| Name | Statement |
| --- | --- |
| `Prim.arms_asyncFinalizer` | `(asyncFinalizer onInterrupt).arms = [Arm.contE, Arm.contAll]` |
| `Prim.hasArm_asyncFinalizer_contA_false` | `(asyncFinalizer onInterrupt).hasArm Arm.contA = false` |
| `Prim.ensure_asyncFinalizer_masks` | `fiber.interruptible = true → (asyncFinalizer onInterrupt).ensure fiber = (FrameFiber.mk fiber.current (setInterruptible true :: fiber.stack) false fiber.interruptedCause fiber.deferredInterrupt, none)` |
| `Prim.ensure_asyncFinalizer_already_masked` | `fiber.interruptible = false → (asyncFinalizer onInterrupt).ensure fiber = (fiber, none)` |
| `Prim.ensure_asyncFinalizer_no_replacement` | `((asyncFinalizer onInterrupt).ensure fiber).snd = none` |
| `Prim.armA_asyncFinalizer_none` | `(asyncFinalizer onInterrupt).armA interp value provided = none` |
| `Prim.armE_asyncFinalizer_interrupt` | `cause.hasInterrupts = true → (asyncFinalizer onInterrupt).armE interp cause provided = some (interp.cancelThenFail onInterrupt cause, [])` |
| `Prim.armE_asyncFinalizer_no_interrupt` | `cause.hasInterrupts = false → (asyncFinalizer onInterrupt).armE interp cause provided = some (failure cause, [])` |
| `Prim.armE_asyncFinalizer_pushes_nothing` | the cause arm ignores the exit the pop supplied and pushes nothing |
| `FrameFiber.passOn` | `Prim … → Option (Prim …) → FramePop … → FramePop …`, the traversal step for a passed frame |
| `FrameFiber.passPushed` | `Arm → Bool → FrameFiber … → FramePop …`, one non-recursive pop off the scratch stack — the frames a hook pushed |
| `FrameFiber.joinPushed` | `Arm → Bool → FrameFiber … → List (Prim …) → FramePop … → FramePop …`, the drain combined with the rest of the traversal |
| `FrameFiber.continueFrom` | `Arm → Bool → Prim … → List (Prim …) → FrameFiber … → FramePop …`, what the traversal continues with once a frame is passed |
| `FrameFiber.passPushed_nil`, `_popped`, `_events`, `_fiber`, `_answer` | the drain read off field by field |
| `FrameFiber.passPushed_answer_hasArm` | a drain that answers with a frame answers with one declaring the demanded arm |
| `FrameFiber.passPushed_setInterruptible_substitutes` | the drain over `SetInterruptible(true)` with a cause recorded: restores the flag, substitutes `failCause(cause)` |
| `FrameFiber.passPushed_setInterruptible_no_pending` | the same with nothing recorded: restores the flag, answers nothing |
| `FrameFiber.passPushed_popped_eq_events`, `FrameFiber.passPushed_ranContAll` | the drain's trace laws |
| `FrameFiber.joinPushed_of_empty`, `FrameFiber.joinPushed_of_answer` | the two branches of the join |
| `FrameFiber.continueFrom_cases` | the two shapes the traversal takes after a frame is passed |
| `FrameFiber.stack_nil_eq` | `fiber.stack = [] → { fiber with stack := [] } = fiber` |
| `FrameFiber.ensure_stack_cases` | a hook leaves the stack alone, or pushes exactly `setInterruptible true` and only from an interruptible fiber, clearing the flag |

| `FrameFiber.popFrom_pass_no_push` | the agreement with the fused reading for a frame that pushes nothing |
| `FrameFiber.popFrom_asyncFinalizer_pops_its_push` | the pushed restoring frame is answered inside the same pop |
| `FrameFiber.step_asyncFinalizer_not_evaluable` | reached as `current`, a defect through `interp.notImplemented` |
| `FrameFiber.step_yieldNowWith_frontier` | `step` is the identity — the DB-04 frontier |
| `FrameFiber.step_async_frontier` | likewise |
| `FrameFiber.step_parking_is_a_fixed_point` | both parking primitives leave the fiber and the trace untouched |

All eight theorems the task named exist and are proved:
`arms_asyncFinalizer`, `armE_asyncFinalizer_interrupt`,
`armE_asyncFinalizer_no_interrupt`, `armA_asyncFinalizer_none`,
`ensure_asyncFinalizer_masks`, `step_yieldNowWith_frontier`,
`step_async_frontier`, `step_asyncFinalizer_not_evaluable`, plus the `popFrom`
pair. Each carries a `census:` tag (`op.Yield`, `op.Async`,
`op.AsyncFinalizer`, `frame-arm.AsyncFinalizer`, `cause.reason-interrupt`,
`rule.frames-are-primitives`).

### Battery-side changes

- `Effect4Test/Runtime/FramesContract.lean` — the six ascriptions above updated
  (`Prim.cases_receipt`, `PrimInterp.mk`, `non_frames_have_no_arms`, the four
  `popFrom_continue_*`), the F1/F6 section prose corrected, and thirty new
  `#check` rows added for the declarations listed above.
- `Effect4Test/Runtime/FramesAxiomReport.lean` — twenty-four new `#print axioms`
  lines.
- `Effect4Test/Semantics/CauseExitContract.lean` — a new §A5b for
  `Cause.hasInterrupts` and its five laws.
- `Effect4Test/Semantics/CauseExitAxiomReport.lean` — five new lines.
- `Effect4Test/Audit/RuntimeCoverage.lean` — the same six ascriptions, and
  **two** pinned axiom receipts re-pinned from `"propext"` to
  `"propext,Quot.sound"` (see §5).
- `Effect4Test/Counterexamples/Runtime/Frames.lean` — **unchanged.** It is
  self-contained (it does not import `Effect4.Runtime.Runtime`; it has its own
  miniature `Prim`), so nothing there needed repair. It still builds.

## 4. Build results

```
$ lake build Effect4
Build completed successfully (104 jobs).

$ lake build <every module under Effect4Test/{Runtime,Semantics,Counterexamples,Audit}>
E4RTCOV	snapshot	Effect4.Prim.withFiber_refused
E4RTCOV	snapshot	Effect4.Prim.yieldableError_host_class_refused
E4RTCOV	coverage	99	79	3	49	25	5
Build completed successfully (129 jobs).
```

The targets `Effect4TestRuntime`, `Effect4TestSemantics` and
`Effect4TestCounterexamples` **do not exist** — `lakefile.toml` declares exactly
two libraries, `Effect4` and `Effect4Test` (`lake build Effect4TestRuntime` →
`unknown target`). The equivalent module set was built instead, plus
`Effect4Test/Audit` because `RuntimeCoverage.lean` also carries frozen
ascriptions and axiom receipts and broke.

`lake build Effect4Test` (the whole battery) still fails, in
`Effect4Test/Protocol/ByteParserContract.lean` (101 errors, `Effect4.Bytes` /
`Effect4.ParseFault` do not exist) and
`Effect4Test/Concurrency/RaceRepresentativeContract.lean` (18 errors,
`raceStep_deterministic` and friends do not exist). Both are **pre-existing red
batteries for other packets** — verified against the untouched main checkout at
`6d83533`, where they fail identically. Neither imports anything I touched.

No `sorry` anywhere under `Effect4/`. The sweep and the trust gate were not run,
as instructed.

## 5. Axiom receipts: two, not forty-eight

The first cut of this spike made `popFrom` well-founded, which put
`[propext, Quot.sound]` on the definition itself and forced forty-eight pinned
receipts in `RuntimeCoverage.lean` from `"propext"` to `"propext,Quot.sound"`.
That was the wrong trade: a well-founded definition does not reduce in the
kernel, so `decide` and `rfl` receipts over `run`/`step` stop working,
`native_decide` is refused by the trust gate, and the coverage module's
kernel-reducible ground receipts would have become `#eval`-only. The two-level
structural shape in §2 was built instead, and the forty-eight are restored.

What remains is two:

| Witness | Was | Is |
| --- | --- | --- |
| `Effect4.FrameFiber.getCont_skip_of_no_pending_cause` | `"propext"` | `"propext,Quot.sound"` |
| `Effect4.FrameFiber.interrupt_skips_every_handler` | `"propext"` | `"propext,Quot.sound"` |

Both are downstream of the two new drain lemmas that the skip proofs need —
`passPushed_skip_eq_of_no_cause` and `passPushed_skip_all` — whose proofs go
through list-membership reasoning (`List.mem_append` and friends). Both are
inside the ceiling `Effect4Test/Runtime/FramesAxiomReport.lean` states ("no
dependency, `propext`, or `propext` with `Quot.sound`; `Classical.choice` and
project-local axioms are not admitted"). Everything else that was re-pinned in
the first cut is back to its original value, verified by comparing every pinned
receipt in `RuntimeCoverage.lean` against `#print axioms`.

Spot receipts after the change:

```
'Effect4.FrameFiber.popFrom'                            depends on axioms: [propext]
'Effect4.FrameFiber.passPushed'                         depends on axioms: [propext]
'Effect4.FrameFiber.joinPushed'                         depends on axioms: [propext]
'Effect4.FrameFiber.popFrom_nil'                        depends on axioms: [propext]
'Effect4.FrameFiber.getCont_empty_stack'                depends on axioms: [propext]
'Effect4.FrameFiber.step_ofExit_finishes'               depends on axioms: [propext]
'Effect4.FrameFiber.popFrom_pass_no_push'               depends on axioms: [propext]
'Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push' depends on axioms: [propext]
'Effect4.FrameFiber.passPushed_setInterruptible_substitutes' depends on axioms: [propext]
'Effect4.FrameFiber.continueFrom_cases'                 depends on axioms: [propext]
'Effect4.Prim.cases_receipt'                            does not depend on any axioms
```

`Prim.cases_receipt` is kept axiom-free by writing its seventeen-way proof as an
explicit `Or.inl`/`Or.inr` term rather than `cases self <;> simp`, because its
pinned receipt is `"none"`.

## 5b. Nothing owed

No `-- OWED:` lines, no `sorry`, no commented-out theorem. Every statement in
§3 is proved over the structural definition. `lake env lean
Effect4/Runtime/Runtime.lean` elaborates clean.

## 6. What I could not prove, and what the vocabulary cannot express

Nothing was left unproved and nothing was dropped for want of a proof.

What rc.112's `AsyncFinalizer` and its `Async` do that this frame vocabulary
cannot say — all of it belongs to the parking state the run-loop packet has to
add, not to the frame machine:

1. **The resume guard.** The pushed closure's first act is `resumed = true`
   (`:1136`), and `Async` also installs `fiber._yielded = () => { resumed = true }`
   (`:1128-1130`). `FrameFiber` has five fields and none is a resume guard, so
   "a `resume(…)` arriving after the finalizer ran is a no-op" is unstatable
   here. `yieldNowWith` has the same guard (`:985-993`) — census row
   `scheduler.yield-now-resume-guard`.
2. **The `AbortController`.** `controller?.abort()` (`:1137`) aborts the
   `AbortSignal` handed to `register`. There is no signal carrier;
   `Prim.async`'s `withSignal : Bool` records only that one was *requested*
   (rc.112's `this[args][1]`), never its identity or its aborted state.
3. **`onCancel ?? exitVoid`** (`:1138`). rc.112 pushes the finalizer when
   *either* a cancel effect was returned *or* a controller exists, and
   substitutes `exitVoid` when there is no cancel effect. `Prim.asyncFinalizer`
   always names one cancel effect, so the "absent ⇒ `exitVoid`" choice is made
   by whoever builds the frame — the run loop — and cannot be read off the
   frame. `Prim.async`'s `cancel : Option ν` is where that information sits
   before the frame exists.
4. **The push decision itself.** `Async`'s `evaluate` decides between three
   outcomes: a synchronous `resume` during `register` short-circuits and returns
   the effect with **no** finalizer pushed (`:1126`); no controller and no
   cancel effect parks with **no** finalizer pushed (`:1131-1133`); otherwise it
   parks *and* pushes (`:1134-1141`). That is a run-loop decision over the
   result of calling a foreign function, so `step` cannot make it — which is
   precisely why `step_async_frontier` is a frontier and not a transition.
5. **The identity of the returned effect.** `flatMap(this[args](), () =>
   failCause(cause))` is defunctionalised to `interp.cancelThenFail`, so the
   model knows *that* the cancel effect runs and then the cause is re-raised,
   but not that the combinator is literally `flatMap`, and not that
   `this[args]()` is a thunk invoked afresh each time. "Invoked at most once"
   holds in rc.112 because the frame is popped, but it is a property of effect
   identity, not of the frame alphabet.
6. **`register.bind(fiber.currentScheduler)`** (`:1113`) and `Yield`'s
   `fiber.currentDispatcher.scheduleTask(…, priority)` (`:986-989`). No
   scheduler or dispatcher carrier exists in this module by construction
   (`Effect4/Concurrency/` is deliberately not imported). `priority` is stored
   as a plain `Nat` and nothing here consumes it.
7. **No `ranFinalizer` event.** `Prim.finalizerEvents (asyncFinalizer _) exit`
   is `[]`, deliberately: `onExit` *runs* its finalizer inside the arm through
   `interp.finalizerExit`, whereas `AsyncFinalizer[contE]` *returns* an effect
   for the machine to step next. Nothing has run at the moment the arm answers,
   so recording a `ranFinalizer` there would be a lie. The cancel effect's
   execution becomes visible one step later, as ordinary `step` events.

## 7. Follow-ups for the landing

- **Re-freeze** `test/contracts/frames.contract.md` from §3.
- **Rewrite `docs/FRAMES-DAG.md:200-211`.** It still says "`AsyncFinalizer` is
  explicitly out of this packet" and offers agreement-or-unfusing as an open
  choice. `FRAME-FB-ASYNC-FINALIZER` is discharged by unfusing; the new prose
  should point at `popFrom_pass_no_push` and
  `popFrom_asyncFinalizer_pops_its_push`.
- **Coverage rows.** `RuntimeCoverage.lean` still carries `op.Yield`,
  `op.Async` (`separateCalculus`, `absent`, no witnesses) and
  `op.AsyncFinalizer`, `frame-arm.AsyncFinalizer` (`excludedInternal`,
  `absent`). This spike deliberately joined **no** witnesses — the clause-by-
  clause rule in `docs/RUNTIME-COVERAGE.md` is a separate step and the sweep was
  not run. The witnesses now available are listed in §3; the two
  `excludedInternal` dispositions in particular look wrong now that the frame is
  modelled rather than excluded.
- Accept or reject the two `"propext,Quot.sound"` re-pins in §5. They come from
  list-membership reasoning in the two new skip lemmas, not from the shape of
  `popFrom`, and could be argued back down to `"propext"` with hand-rolled
  membership proofs if a reviewer wants the receipt untouched.
