import Effect4.Semantics.FrameSimulation
import Effect4.Flow.Region
import Effect4.Target.TypeScript.Simulation

/-!
# Semantics.RegionSimulation

Owner: the finalizer half of packet D4 — the simulation between the region
runner of `Effect4/Flow/Region.lean` and the rc.112 frame machine of
`Effect4/Runtime/Runtime.lean`, under the mask that keeps `finalizer` and
`done`.

`Effect4/Semantics/FrameSimulation.lean` (fence B) proves the *value* half
against `Effects.interpret` and closes with the note that the finalizer half
needs a bracket former the algebra does not have. This module is that half,
stated where it is statable: against `Effect4.Flow.runRegions`, the only Lean
face with `enter`/`leave`/`finalizer` semantics.

## The ruling the fence-B note was waiting for

The note said the two models "disagree on the failure payload on every run
where a release fails under a failing body", because `closeFrame` kept only the
first release failure. Packet D2 changed that: `closeFrame` now returns the
*merged* failure list in close order (`Effect4.Flow.closeFrame_failure_merge`,
against `Exit.asVoidAll`), and `fail` reports `error :: (rest ++ closing)`. So
the machine's `Cause.combine bodyCause finalizerCause` and the runner's list are
related by a projection, not divergent:

* `causeOfFailures` sends a failure list to the cause whose reasons are those
  errors, unannotated, in order — a section;
* `failuresOfCause` sends a cause to its `fail` errors in order — the function
  direction, total, and `failuresOfCause_causeOfFailures` says it retracts.

The direction that is a *function* is `failuresOfCause`. `causeOfFailures` is not
surjective — a cause carrying a `die` or an `interrupt` reason has no failure
list preimage — so the projection only ever goes cause-to-list.

**The empty-annotation hypothesis of
`docs/research/2026-09-03-frame-simulation.md` section 5(b) is not needed for
the theorems below, and the reason is sharper than "we avoided it".**
`Cause.combine self that` is `dedup (self.reasons ++ that.reasons)` when both
are non-empty, and `Cause.dedup` keeps the *first* occurrence
(`Effect4.Cause.dedup_cons`), so the head of a combined cause is the head of the
body's cause whatever the annotations are. `Exit.toOutcome` reads the first
`fail` reason (`Effect4/Target/TypeScript/Simulation.lean`). Hence
`toOutcome_combine` below: the merge is invisible to the wire, on the nose,
with no hypothesis on `ReasonAnnotations`. Section 5(b) stays live only for a
statement that compares whole *causes* rather than their wire projection; no
theorem here does.

## The compilation, and why it is the host's shape

`compileRegion` emits exactly what `Effect4/Target/TypeScript/RegionLower.lean`
lowers to:

* `enter` becomes `Prim.onSuccess body ν` — the `Effect.scoped(Effect.onExit(…))`
  wrapper whose value continues at the region's `continue_` block. It pushes no
  finalizer, because the row it writes is `leave`, and `leave` has **no**
  frame-machine shadow: `FrameEvent.toTrace` sends every event but
  `ranFinalizer` and `yielded` to `none`. Compiling `enter` to `Prim.onExit`
  would manufacture a `finalizer` row the runner never writes.
* `acquire` becomes the `sync` gadget of fence B followed by
  `Prim.onExit rest (RegionName.fin region point) false` — rc.112's
  `Prim.scopedFrame` — so the release is a *named* finalizer, and the frames
  stack in registration order. `leave` compiles to `Prim.success value`, and
  the machine pops the `onExit` frames latest-registered first, each running its
  finalizer against the closing exit. That is the order
  `E4-TARGET-CE-012..014` pin for the host and `Frame.toScope_closeOrder`
  proves for the runner.
* a plain `perform` becomes the fence-B gadget `onSuccess (sync point) (cont point)`.

## Separation 4, restated for this module

Fence B took `ν := Nat`. Here a name has to carry the point of the run it
belongs to, so `ν := RegionName`, an inductive over `Config`, which is
`Nat × BlockId × Env × Tape` — first-order data with a derived `DecidableEq`,
never a Lean function. The `example`s below are the same gate as fence B's:
they fail to elaborate the moment a name alphabet is instantiated at a
function type, which is what `docs/FRAMES-DAG.md` separation 4 exists to
forbid.

`Config.fuel` is a step counter, not a size: the runner spends one unit per
block, so a configuration is reached at most once in a run and a name is
therefore unambiguous without a separate occurrence index.

## What is proved, and what is owed

Proved, in full generality: `unwind_failure` (a failing exit propagating
through an arbitrary fragment stack runs exactly the finalizers that stack
names, in pop order, all against the same exit, and yields that exit) and
`close_success` (a closing value runs the `onExit` frames above the answering
`onSuccess` frame and then answers it). Those two are the finalizer half of the
machine, and they are what `regions_simulate` is assembled from.

Owed, and deliberately not stated as a definition without a proof — the general
theorem, whose exact wording is:

```text
theorem regions_simulate
    (alphabet : FlowAlphabet Ty) (flow : CheckedRegionFlow alphabet)
    (service : RegionService alphabet Id) (nameOf : alphabet.Op -> String)
    (oracle : RegionOracle) (tape input) (fuel' fuel : Nat)
    (hOracle : <the oracle answers what the service answers along this run>)
    (hfuel : regionBound fuel' <= fuel) :
    FrameEvent.traceOf RegionName.regionOf id id (fun _ => Val.unit)
        (FrameFiber.run (regionInterp alphabet flow.flow oracle) fuel
          (FrameFiber.start (compileAt alphabet flow.flow
            ⟨fuel', flow.flow.entry, [input], tape⟩))).2
      = Effects.Trace.project finalizerAndOutcomeMask
          (((Effect4.Flow.runRegions fuel' flow service nameOf tape input).run []).2)
```

What blocks it is not the failure payload — that ruling is settled above — but
the induction: the runner's `leave` continues at `row.continue_` with the fuel
and the decision tape it holds *at the leave*, while the frame `enter` pushes
is named at the *enter*. Closing it needs a `leaveConfig` function that walks
the region body to its close under the oracle and a proof that it agrees with
the runner, which is a second copy of the runner and its own fence. The
instances on `regionNested`, `regionTwoFail` and `regionBothSucceed` are closed
by evaluation in `Effect4Test/Semantics/RegionSimulationContract.lean`, and the
harness prints both sides of the equation for every region program
(`harness/trace/Generate.lean frame-trace`).
-/

namespace Effect4.RegionSimulation

open Effects
open Effects.Trace (Val Outcome)

/-! ## The carriers -/

/-- A point of a region run: the fuel the runner holds, the block it is about
to spend it on, that block's environment, and the decision tape that is left.
The fuel is a step counter, so a point occurs at most once in a run. -/
structure Config where
  /-- The runner's remaining fuel at this point. -/
  fuel : Nat
  /-- The block about to run. -/
  block : BlockId
  /-- The block's positional environment. -/
  env : Effect4.Flow.Env
  /-- The decision tape that is left. -/
  tape : Effect4.Flow.Tape
deriving DecidableEq

/-- A continuation or finalizer name. First-order data: a name is a *name*
(`docs/FRAMES-DAG.md` separation 4), never a stored Lean function. -/
inductive RegionName where
  /-- The continuation of the operation the block at `point` performs. -/
  | cont (point : Config)
  /-- The continuation of the region opened at `point`: its `continue_` block. -/
  | regionCont (region : Nat) (point : Config)
  /-- The release the `acquire` at `point` registered on `region`'s scope. -/
  | fin (region : Nat) (point : Config)
deriving DecidableEq

/-- The region a name belongs to, for `FrameEvent.toTrace`. Only `fin` names
ever reach it: a `ranFinalizer` event carries no other constructor. -/
def RegionName.regionOf : RegionName -> Nat
  | RegionName.cont _ => 0
  | RegionName.regionCont region _ => region
  | RegionName.fin region _ => region

/-- The fragment's cause carrier, as fence B fixes it. -/
abbrev Err := Effect4.Cause Val Unit Unit Unit

/-- The fragment's exit carrier. -/
abbrev Res := Effect4.Exit Val Val Unit Unit Unit

/-- The compiled region program. -/
abbrev Code := Effect4.Prim RegionName Config Val Val Unit Unit Unit

/-- The frame machine at this instantiation. -/
abbrev Machine := Effect4.FrameFiber RegionName Config Val Val Unit Unit Unit

/-- The continuation table. It carries no `DecidableEq` and never enters
`Code` or `Machine`. -/
abbrev Table := Effect4.PrimInterp RegionName Config Val Val Unit Unit Unit

/-- Separation-4 gate: the compiled output keeps decidable equality. This fails
to elaborate if `ν` or `σ` is ever instantiated at a function type. -/
example : DecidableEq Code := inferInstance

/-- Separation-4 gate, for the machine state as well. -/
example : DecidableEq Machine := inferInstance

/-- The projection of a frame trace this module compares: the exit value is a
`Val` already, the error is a `Val` already, and `δ := Unit` has no `Val`-typed
defect carrier, so a defect lands on `Val.unit`. -/
def traceOfRun (events : List (Effect4.FrameEvent RegionName Config Val Val Unit Unit Unit)) :
    Effect4.Trace.Log :=
  Effect4.FrameEvent.traceOf RegionName.regionOf id id (fun _ => Val.unit) events

/-- The mask the theorem compares under: the rows the frame machine can write
at all. `enter`, `leave`, `op`, `answer`, `failed`, `decide` and `frontier`
have no `FrameEvent` shadow (`Effect4/Target/TypeScript/Simulation.lean`), so
keeping them would be comparing a trace with silence. -/
def finalizerAndOutcomeMask : Effects.Trace.Mask :=
  { ops := false, answers := false, decisions := false, regions := false,
    finalizers := true, outcome := true, frontier := false }

/-! ## The oracle

`PrimInterp` is a record of pure total functions, so the machine has nowhere to
put the service's monad; the answers are supplied, exactly as fence B's tape
supplies them. Here the key is the *point* rather than an occurrence index,
because `Config.fuel` already distinguishes occurrences. -/

/-- What the service answers along one run: at each point, the answer of the
operation that point performs, and, for an `acquire`, the answer of the release
it registers when its scope closes. -/
structure RegionOracle where
  /-- The answer of the operation performed at this point. -/
  answer : Config -> Except Val Val
  /-- The answer of the release the `acquire` at this point registered. -/
  release : Config -> Except Val Val

section Shapes

variable {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)

/-- The operation the block at `point` performs, and the request it performs it
on: a plain `perform`, or an `acquire`. -/
def performOp (point : Config) : Option (alphabet.Op × Val) :=
  match flow.block? point.block with
  | none => none
  | some current =>
    match current.term with
    | .plain term =>
      match Effect4.Flow.plan alphabet
          { id := current.id, params := current.params, term := term } point.env point.tape with
      | .perform op request _ _ => some (op, request)
      | _ => none
    | .acquire operation request _ _ _ =>
      match alphabet.lookup operation, point.env[request.index]? with
      | some op, some requestValue => some (op, requestValue)
      | _, _ => none
    | _ => none

/-- Where the operation performed at `point` continues: the target block, the
environment its parameters receive before the answer is appended, and the
region whose scope registers a release (an `acquire`) or `none` (a plain
`perform`). -/
def performCont (point : Config) : Option (BlockId × Effect4.Flow.Env × Option Nat) :=
  match flow.block? point.block with
  | none => none
  | some current =>
    match current.term with
    | .plain term =>
      match Effect4.Flow.plan alphabet
          { id := current.id, params := current.params, term := term } point.env point.tape with
      | .perform _ _ target env' => some (target, env', none)
      | _ => none
    | .acquire operation request release target args =>
      match alphabet.lookup operation, alphabet.lookup release, point.env[request.index]?,
          Effect4.Flow.readArgs point.env args, current.region with
      | some _, some _, some _, some values, some region => some (target, values, some region.value)
      | _, _, _, _, _ => none
    | _ => none

/-- The release operation the `acquire` at `point` registers. -/
def releaseOp (point : Config) : Option alphabet.Op :=
  match flow.block? point.block with
  | none => none
  | some current =>
    match current.term with
    | .acquire _ _ release _ _ => alphabet.lookup release
    | _ => none

end Shapes

/-! ## The compilation -/

/-- The region-aware compilation into the frame machine.

`enter` pushes the region frame (`Effect.scoped(Effect.onExit(…))`, whose value
continues at `continue_`), `acquire` performs its operation and pushes the
`onExit` frame whose finalizer is its release (`Effect.acquireRelease`), and
`leave` yields the closing value, which pops through those frames
latest-registered first. A shape the runner refuses — a missing block, a stuck
plan, an exhausted or mismatched tape, a malformed `acquire` — compiles to the
empty failure, which is unreachable on any run the theorem speaks about,
because such a run does not finish. -/
def compileRegion {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Nat -> BlockId -> Effect4.Flow.Env -> Effect4.Flow.Tape -> Code
  | 0, _, _, _ => Effect4.Prim.failure Effect4.Cause.empty
  | fuel + 1, block, env, tape =>
    match flow.block? block with
    | none => Effect4.Prim.failure Effect4.Cause.empty
    | some current =>
      match current.term with
      | .plain term =>
        match Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | .ret value => Effect4.Prim.success value
        | .jump target env' => compileRegion alphabet flow fuel target env' tape
        | .perform _ _ _ _ =>
          Effect4.Prim.onSuccess (Effect4.Prim.sync ⟨fuel + 1, block, env, tape⟩)
            (RegionName.cont ⟨fuel + 1, block, env, tape⟩)
        | .choose _ _ target env' rest => compileRegion alphabet flow fuel target env' rest
        | .stuck => Effect4.Prim.failure Effect4.Cause.empty
        | .exhausted _ => Effect4.Prim.failure Effect4.Cause.empty
        | .mismatch _ _ => Effect4.Prim.failure Effect4.Cause.empty
      | .enter region body args =>
        match Effect4.Flow.readArgs env args with
        | some values =>
          Effect4.Prim.onSuccess (compileRegion alphabet flow fuel body values tape)
            (RegionName.regionCont region.value ⟨fuel + 1, block, env, tape⟩)
        | none => Effect4.Prim.failure Effect4.Cause.empty
      | .acquire _ _ _ _ _ =>
        match performCont alphabet flow ⟨fuel + 1, block, env, tape⟩ with
        | some _ =>
          Effect4.Prim.onSuccess (Effect4.Prim.sync ⟨fuel + 1, block, env, tape⟩)
            (RegionName.cont ⟨fuel + 1, block, env, tape⟩)
        | none => Effect4.Prim.failure Effect4.Cause.empty
      | .leave value =>
        match env[value.index]? with
        | some v => Effect4.Prim.success v
        | none => Effect4.Prim.failure Effect4.Cause.empty

/-- The compilation at a point. It is `compileRegion` with the point's four
fields spread out; the fuel is the first argument so the recursion is
structural and the compiled program is kernel-reducible, which is what the
receipts on the three region programs evaluate. -/
def compileAt {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (point : Config) : Code :=
  compileRegion alphabet flow point.fuel point.block point.env point.tape

/-- The externally supplied meaning of every name. `contA` is computed from the
flow — a name is a point, and the flow says what happens there — and only the
service's answers come from the oracle. `contE` is the identity on causes: the
fragment has no `onFailure` frame, so no compiled run ever consults it; it is
the inert filler fence B's `tapeInterp` uses. -/
def regionInterp {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) : Table where
  contA := fun name value =>
    match name with
    | RegionName.cont point =>
      match oracle.answer point with
      | .error error => Effect4.Prim.failure (Effect4.Cause.fail error)
      | .ok _ =>
        match performCont alphabet flow point with
        | some (target, env', none) =>
          compileRegion alphabet flow (point.fuel - 1) target (env' ++ [value]) point.tape
        | some (target, env', some region) =>
          Effect4.Prim.onExit
            (compileRegion alphabet flow (point.fuel - 1) target (env' ++ [value]) point.tape)
            (RegionName.fin region point) false
        | none => Effect4.Prim.failure Effect4.Cause.empty
    | RegionName.regionCont region point =>
      match flow.row? ⟨region⟩ with
      | some row =>
        compileRegion alphabet flow (point.fuel - 1) row.continue_ [value] point.tape
      | none => Effect4.Prim.failure Effect4.Cause.empty
    | RegionName.fin _ _ => Effect4.Prim.failure Effect4.Cause.empty
  contE := fun _ cause => Effect4.Prim.failure cause
  syncValue := fun point =>
    match oracle.answer point with
    | .ok value => value
    | .error _ => Val.unit
  finalizerExit := fun name _ =>
    match name with
    | RegionName.fin _ point =>
      match oracle.release point with
      | .ok _ => Effect4.Exit.success ()
      | .error error => Effect4.Exit.failure (Effect4.Cause.fail error)
    | _ => Effect4.Exit.success ()
  suspendBody := fun _ => Effect4.Prim.failure Effect4.Cause.empty
  reifyExit := fun _ => Val.unit
  iterNext := fun _ _ => ([], Effect4.IterStep.done Val.unit)
  loopTest := fun _ _ => false
  loopBody := fun _ _ => Effect4.Prim.failure Effect4.Cause.empty
  loopStep := fun _ value => value
  loopDone := fun _ => Val.unit
  notImplemented := ()

/-- The oracle of a service that does not read or write its own state: the
answer at a point is what the service returns for the operation that point
performs, and a release's answer is what it returns for the release operation
on the resource the `acquire` produced. This is the `stateless` hypothesis of
`Effect4.Flow.closeFrame_failure_closeResult`, in oracle form. -/
def statelessOracle {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (answerOf : alphabet.Op -> Val -> Except Val Val) : RegionOracle where
  answer point :=
    match performOp alphabet flow point with
    | some (op, request) => answerOf op request
    | none => .ok Val.unit
  release point :=
    match performOp alphabet flow point, releaseOp alphabet flow point with
    | some (op, request), some releaser =>
      match answerOf op request with
      | .ok resource => answerOf releaser resource
      | .error error => .error error
    | _, _ => .ok Val.unit

/-- The machine fuel a region run needs. The runner spends one unit per block;
a block costs the machine at most four steps (push the `OnSuccess` frame, run
the `Sync` and pop it, push the `OnExit` frame an `acquire` registers, and one
for the frame a close pops), and one more step yields the exit. -/
def regionBound (runnerFuel : Nat) : Nat := 4 * runnerFuel + 1

/-! ## The projection between `Cause.combine` and the runner's merged list

`Effect4.Flow.Failures` is `List Val`, in close order, first failure first
(`closeFrame_failure_merge`). `Effect4.Cause` is a list of `Reason`s. The two
are related by a section and a retraction, and only the retraction is a
function on all of `Cause`. -/

/-- A failure list as a cause: one unannotated `fail` reason per failure, in
order. A section, not a bijection. -/
def causeOfFailures (failures : Effect4.Flow.Failures) : Err :=
  ⟨failures.map (fun error => Effect4.Reason.fail error Effect4.ReasonAnnotations.empty)⟩

/-- A cause as a failure list: its `fail` errors, in reason order. **This is the
direction that is a function**: it is total on `Cause`, whereas
`causeOfFailures` misses every cause carrying a `die` or an `interrupt`
reason. It is exactly the projection `Effect4.Flow.exitErrors` takes. -/
def failuresOfCause (cause : Err) : Effect4.Flow.Failures :=
  cause.reasons.filterMap Effect4.Reason.error?

/-- The retraction: reading a failure list back off the cause it builds returns
it unchanged. -/
theorem failuresOfCause_causeOfFailures (failures : Effect4.Flow.Failures) :
    failuresOfCause (causeOfFailures failures) = failures := by
  induction failures with
  | nil => rfl
  | cons head rest ih =>
    have hstep : failuresOfCause (causeOfFailures (head :: rest)) =
        head :: failuresOfCause (causeOfFailures rest) := rfl
    rw [hstep, ih]

/-- A non-empty failure list builds a cause whose first `fail` reason carries
its head. -/
theorem find_fail_causeOfFailures (head : Val) (rest : Effect4.Flow.Failures) :
    (causeOfFailures (head :: rest)).reasons.find?
        (fun reason => reason.tag = Effect4.ReasonTag.fail) =
      some (Effect4.Reason.fail head Effect4.ReasonAnnotations.empty) := rfl

/-- A combined cause has the body's first reason as its own first reason:
`Cause.combine` is `Cause.dedup` of the concatenation and `dedup` keeps the
first occurrence. -/
theorem combine_reasons_cons (self that : Err) (reason : Effect4.Reason Val Unit Unit Unit)
    (rest : List (Effect4.Reason Val Unit Unit Unit)) (h : self.reasons = reason :: rest) :
    exists tail, (Effect4.Cause.combine self that).reasons = reason :: tail := by
  by_cases hthat : that.reasons = []
  · refine ⟨rest, ?_⟩
    have hempty : that = Effect4.Cause.empty := Effect4.Cause.ext (by rw [hthat]; rfl)
    rw [hempty, Effect4.Cause.combine_empty_right, h]
  · refine ⟨(Effect4.Cause.dedup (rest ++ that.reasons)).filter
      (fun other => decide (other ≠ reason)), ?_⟩
    rw [Effect4.Cause.combine_reasons self that (by rw [h]; exact List.cons_ne_nil _ _) hthat, h,
      List.cons_append, Effect4.Cause.dedup_cons]

/-- **The lemma that makes the merge invisible to the wire.** `Exit.toOutcome`
reads the *first* `fail` reason, and `combine_reasons_cons` says the merge does
not move it. So the outcome of a merged failure is the outcome of the body's
failure — with no hypothesis on `ReasonAnnotations`, which is why section 5(b)
of the research note is not a hypothesis of this module. -/
theorem toOutcome_combine (self that : Err) (error : Val)
    (annotations : Effect4.ReasonAnnotations Unit)
    (rest : List (Effect4.Reason Val Unit Unit Unit))
    (h : self.reasons = Effect4.Reason.fail error annotations :: rest) :
    Effect4.Exit.toOutcome (β := Val) id id (fun _ => Val.unit)
        (Effect4.Exit.failure (Effect4.Cause.combine self that)) =
      Outcome.failure error := by
  obtain ⟨tail, htail⟩ := combine_reasons_cons self that _ rest h
  simp only [Effect4.Exit.toOutcome, htail]
  rfl

/-! ## The two machine transitions the compiled shape uses at a close

Both hold by `rfl`: an `onExit` frame answers both arms, its `ensure` masks the
fiber and pushes the restoring mask frame, and the mask frame answers neither
arm and is therefore skipped by the next pop. This is fence A's
`step_preserves_uninterrupted` made concrete on the closing path. -/

/-- A failing exit reaching an `onExit` frame runs its finalizer against that
exit and continues with the restored exit; the mask frame `ensure` pushed lands
on top of what is left. -/
theorem step_onExit_failure (interp : Table) (cause : Err) (body : Code) (name : RegionName)
    (rest : List Code) :
    (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
        (Effect4.Prim.onExit body name false :: rest) true none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk
          (Effect4.Prim.ofExit
            (Effect4.Exit.restoreAfterFinalizer (Effect4.Exit.failure cause)
              (interp.finalizerExit name (Effect4.Exit.failure cause))))
          (Effect4.Prim.setInterruptible true :: rest) false none false),
        [Effect4.FrameEvent.popped (Effect4.Prim.onExit body name false),
          Effect4.FrameEvent.ranContAll (Effect4.Prim.onExit body name false),
          Effect4.FrameEvent.ranFinalizer name (Effect4.Exit.failure cause)]) := rfl

/-- A closing value reaching an `onExit` frame runs its finalizer against the
successful exit and continues with the restored exit. -/
theorem step_onExit_success (interp : Table) (value : Val) (body : Code) (name : RegionName)
    (rest : List Code) :
    (Effect4.FrameFiber.mk (Effect4.Prim.success value)
        (Effect4.Prim.onExit body name false :: rest) true none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk
          (Effect4.Prim.ofExit
            (Effect4.Exit.restoreAfterFinalizer (Effect4.Exit.success value)
              (interp.finalizerExit name (Effect4.Exit.success value))))
          (Effect4.Prim.setInterruptible true :: rest) false none false),
        [Effect4.FrameEvent.popped (Effect4.Prim.onExit body name false),
          Effect4.FrameEvent.ranContAll (Effect4.Prim.onExit body name false),
          Effect4.FrameEvent.ranFinalizer name (Effect4.Exit.success value)]) := rfl

/-! ## The closing stacks

Which frames a closing exit runs through, and which finalizers they name. -/

/-- The frames a *failure* runs through: every frame of the fragment answers or
is skipped, so a failure consumes the whole stack. The `onExit` frames name the
finalizers, in pop order; `onSuccess` frames declare no `contE` arm and mask
frames declare neither, so both are skipped and name nothing. -/
def unwindNames : List Code -> List RegionName
  | [] => []
  | Effect4.Prim.onExit _ name _ :: rest => name :: unwindNames rest
  | _ :: rest => unwindNames rest

/-- The stack shapes this module's theorems range over: the four primitives a
compiled region run can leave on the stack. -/
def unwindable : List Code -> Bool
  | [] => true
  | Effect4.Prim.onExit _ _ flag :: rest => !flag && unwindable rest
  | Effect4.Prim.onSuccess _ _ :: rest => unwindable rest
  | Effect4.Prim.setInterruptible flag :: rest => flag && unwindable rest
  | _ :: _ => false

/-- The finalizers a *closing value* runs before the region frame answers: the
`onExit` frames above the first frame that declares a `contA` arm. -/
def closeNames : List Code -> List RegionName
  | Effect4.Prim.onExit _ name _ :: rest => name :: closeNames rest
  | Effect4.Prim.setInterruptible _ :: rest => closeNames rest
  | _ => []

/-- The frames a *closing value* runs before the region frame answers, and the
shapes that segment may take: `onExit` frames and the mask frames their
`ensure` pushes, and nothing else. -/
def closeable : List Code -> Bool
  | [] => true
  | Effect4.Prim.onExit _ _ flag :: rest => !flag && closeable rest
  | Effect4.Prim.setInterruptible flag :: rest => flag && closeable rest
  | _ :: _ => false

/-! ## The finalizer half of the machine

Two theorems, both general: a failing exit propagating through a fragment
stack, and a closing value propagating to the frame that answers it. They are
what `regions_simulate` is assembled from, and they are stated over an
arbitrary stack rather than over a compiled one, so nothing about
`compileRegion` is assumed. -/

/-- The wire outcome of an exit, at this module's carriers. -/
def outcomeOf (exit : Res) : Outcome Val :=
  Effect4.Exit.toOutcome id id (fun _ => Val.unit) exit

/-- The service-level row a named finalizer writes against an exit. -/
def finalizerRow (exit : Res) (name : RegionName) : Effect4.Trace.Event :=
  Effects.Trace.Event.finalizer name.regionOf (outcomeOf exit)

/-- Two machine observations agree: the same step outcome, and the same
projected service-level trace. Frame pushes, pops and `contAll` runs have no
service-level shadow, so two states that differ only by those agree. -/
def Agree (left right : Effect4.FrameStep RegionName Config Val Val Unit Unit Unit ×
    List (Effect4.FrameEvent RegionName Config Val Val Unit Unit Unit)) : Prop :=
  left.fst = right.fst /\ traceOfRun left.snd = traceOfRun right.snd

/-- Agreement on one step is agreement on the whole run. -/
private theorem run_congr (interp : Table) (left right : Machine) (fuel : Nat)
    (h : Agree (left.step interp) (right.step interp)) :
    Agree (left.run interp (fuel + 1)) (right.run interp (fuel + 1)) := by
  obtain ⟨hfst, hsnd⟩ := h
  cases hl : left.step interp with
  | mk stepL eventsL =>
    cases hr : right.step interp with
    | mk stepR eventsR =>
      rw [hl, hr] at hfst hsnd
      have hstep : stepL = stepR := hfst
      have hevents : traceOfRun eventsL = traceOfRun eventsR := hsnd
      subst hstep
      cases stepL with
      | finished exit =>
        rw [Effect4.FrameFiber.run_succ_finished interp left fuel exit eventsL hl,
          Effect4.FrameFiber.run_succ_finished interp right fuel exit eventsR hr]
        exact ⟨rfl, hevents⟩
      | running nextL =>
        rw [Effect4.FrameFiber.run_succ_running interp left nextL fuel eventsL hl,
          Effect4.FrameFiber.run_succ_running interp right nextL fuel eventsR hr]
        refine ⟨rfl, ?_⟩
        show traceOfRun (eventsL ++ _) = traceOfRun (eventsR ++ _)
        simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append]
        exact congrArg (fun rows => rows ++ _) hevents

/-- Two pops agree: the same answer, the same fiber, and the same projected
service-level trace. -/
def PopAgree (left right : Effect4.FramePop RegionName Config Val Val Unit Unit Unit) : Prop :=
  left.answer = right.answer /\ left.fiber = right.fiber /\
    traceOfRun left.events = traceOfRun right.events

/-- A step on a failing primitive is the cause pop. -/
private theorem step_eq_resumeCause (interp : Table) (self : Machine) (cause : Err)
    (h : self.current = Effect4.Prim.failure cause) :
    self.step interp = self.resumeCause interp cause (some (Effect4.Exit.failure cause)) := by
  cases self with
  | mk current stack interruptible interruptedCause deferredInterrupt =>
    simp only [] at h
    subst h
    rfl

/-- A step on a successful primitive is the value pop. -/
private theorem step_eq_resumeValue (interp : Table) (self : Machine) (value : Val)
    (h : self.current = Effect4.Prim.success value) :
    self.step interp = self.resumeValue interp value (some (Effect4.Exit.success value)) := by
  cases self with
  | mk current stack interruptible interruptedCause deferredInterrupt =>
    simp only [] at h
    subst h
    rfl

/-- Every branch of `resumeCause` reads only the pop's answer, its fiber and
its trace, so agreeing pops drive agreeing steps. -/
private theorem agree_failure (interp : Table) (cause : Err) (left right : Machine)
    (hleft : left.current = Effect4.Prim.failure cause)
    (hright : right.current = Effect4.Prim.failure cause)
    (hpop : PopAgree (left.getCont Effect4.Arm.contE true)
      (right.getCont Effect4.Arm.contE true)) :
    Agree (left.step interp) (right.step interp) := by
  obtain ⟨hanswer, hfiber, hevents⟩ := hpop
  simp only [traceOfRun, Effect4.FrameEvent.traceOf] at hevents
  rw [step_eq_resumeCause interp left cause hleft, step_eq_resumeCause interp right cause hright]
  cases hansR : (right.getCont Effect4.Arm.contE true).answer with
  | empty =>
    rw [Effect4.FrameFiber.resumeCause_empty interp left cause _ (hanswer.trans hansR),
      Effect4.FrameFiber.resumeCause_empty interp right cause _ hansR]
    refine ⟨rfl, ?_⟩
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append, hevents]
  | deferred deferredCause =>
    rw [Effect4.FrameFiber.resumeCause_deferred interp left cause deferredCause _
        (hanswer.trans hansR),
      Effect4.FrameFiber.resumeCause_deferred interp right cause deferredCause _ hansR]
    refine ⟨by rw [hfiber], ?_⟩
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, hevents]
  | replacement next =>
    rw [Effect4.FrameFiber.resumeCause_replacement interp left cause _ next (hanswer.trans hansR),
      Effect4.FrameFiber.resumeCause_replacement interp right cause _ next hansR]
    refine ⟨by rw [hfiber], ?_⟩
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, hevents]
  | frame frame =>
    cases harm : frame.armE interp cause (some (Effect4.Exit.failure cause)) with
    | some pair =>
      obtain ⟨next, pushed⟩ := pair
      rw [Effect4.FrameFiber.resumeCause_frame interp left cause _ frame next pushed
          (hanswer.trans hansR) harm,
        Effect4.FrameFiber.resumeCause_frame interp right cause _ frame next pushed hansR harm]
      refine ⟨by rw [hfiber], ?_⟩
      simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append, hevents]
    | none =>
      have hL : left.resumeCause interp cause (some (Effect4.Exit.failure cause)) =
          (Effect4.FrameStep.finished (Effect4.Exit.failure cause),
            (left.getCont Effect4.Arm.contE true).events ++
              [Effect4.FrameEvent.yielded (Effect4.Exit.failure cause)]) := by
        simp [Effect4.FrameFiber.resumeCause, hanswer.trans hansR, harm]
      have hR : right.resumeCause interp cause (some (Effect4.Exit.failure cause)) =
          (Effect4.FrameStep.finished (Effect4.Exit.failure cause),
            (right.getCont Effect4.Arm.contE true).events ++
              [Effect4.FrameEvent.yielded (Effect4.Exit.failure cause)]) := by
        simp [Effect4.FrameFiber.resumeCause, hansR, harm]
      rw [hL, hR]
      refine ⟨rfl, ?_⟩
      simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append, hevents]

/-- The same, for `resumeValue`. -/
private theorem agree_success (interp : Table) (value : Val) (left right : Machine)
    (hleft : left.current = Effect4.Prim.success value)
    (hright : right.current = Effect4.Prim.success value)
    (hpop : PopAgree (left.getCont Effect4.Arm.contA false)
      (right.getCont Effect4.Arm.contA false)) :
    Agree (left.step interp) (right.step interp) := by
  obtain ⟨hanswer, hfiber, hevents⟩ := hpop
  simp only [traceOfRun, Effect4.FrameEvent.traceOf] at hevents
  rw [step_eq_resumeValue interp left value hleft, step_eq_resumeValue interp right value hright]
  cases hansR : (right.getCont Effect4.Arm.contA false).answer with
  | empty =>
    rw [Effect4.FrameFiber.resumeValue_empty interp left value _ (hanswer.trans hansR),
      Effect4.FrameFiber.resumeValue_empty interp right value _ hansR]
    refine ⟨rfl, ?_⟩
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append, hevents]
  | deferred deferredCause =>
    rw [Effect4.FrameFiber.resumeValue_deferred interp left value _ deferredCause
        (hanswer.trans hansR),
      Effect4.FrameFiber.resumeValue_deferred interp right value _ deferredCause hansR]
    refine ⟨by rw [hfiber], ?_⟩
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, hevents]
  | replacement next =>
    rw [Effect4.FrameFiber.resumeValue_replacement interp left value _ next (hanswer.trans hansR),
      Effect4.FrameFiber.resumeValue_replacement interp right value _ next hansR]
    refine ⟨by rw [hfiber], ?_⟩
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, hevents]
  | frame frame =>
    cases harm : frame.armA interp value (some (Effect4.Exit.success value)) with
    | some pair =>
      obtain ⟨next, pushed⟩ := pair
      rw [Effect4.FrameFiber.resumeValue_frame interp left value _ frame next pushed
          (hanswer.trans hansR) harm,
        Effect4.FrameFiber.resumeValue_frame interp right value _ frame next pushed hansR harm]
      refine ⟨by rw [hfiber], ?_⟩
      simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append, hevents]
    | none =>
      have hL : left.resumeValue interp value (some (Effect4.Exit.success value)) =
          (Effect4.FrameStep.finished (Effect4.Exit.success value),
            (left.getCont Effect4.Arm.contA false).events ++
              [Effect4.FrameEvent.yielded (Effect4.Exit.success value)]) := by
        simp [Effect4.FrameFiber.resumeValue, hanswer.trans hansR, harm]
      have hR : right.resumeValue interp value (some (Effect4.Exit.success value)) =
          (Effect4.FrameStep.finished (Effect4.Exit.success value),
            (right.getCont Effect4.Arm.contA false).events ++
              [Effect4.FrameEvent.yielded (Effect4.Exit.success value)]) := by
        simp [Effect4.FrameFiber.resumeValue, hansR, harm]
      rw [hL, hR]
      refine ⟨rfl, ?_⟩
      simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append, hevents]

/-- A frame that answers neither demandable arm is passed inside the pop: the
traversal continues under the flag its hook leaves, and the frame contributes
no service-level row. -/
private theorem popFrom_passed (demand : Effect4.Arm) (skip : Bool) (current : Code)
    (frame : Code) (stack : List Code) (flagIn flagOut : Bool)
    (hnone : Effect4.Prim.answerOf frame demand
      ((frame.ensure (Effect4.FrameFiber.mk current [] flagIn none false)).snd) = none)
    (hens : (frame.ensure (Effect4.FrameFiber.mk current [] flagIn none false)).fst =
      Effect4.FrameFiber.mk current [] flagOut none false)
    (hpass : traceOfRun (frame.passEvents
      ((frame.ensure (Effect4.FrameFiber.mk current [] flagIn none false)).snd)) = []) :
    PopAgree
      (Effect4.FrameFiber.popFrom demand skip (frame :: stack)
        (Effect4.FrameFiber.mk current [] flagIn none false))
      (Effect4.FrameFiber.popFrom demand skip stack
        (Effect4.FrameFiber.mk current [] flagOut none false)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Effect4.FrameFiber.popFrom_continue_answer demand skip frame stack _ (Or.inl hnone), hens]
  · rw [Effect4.FrameFiber.popFrom_continue_fiber demand skip frame stack _ (Or.inl hnone), hens]
  · rw [Effect4.FrameFiber.popFrom_continue_events demand skip frame stack _ (Or.inl hnone), hens]
    simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append] at hpass ⊢
    rw [hpass, List.nil_append]

/-- An `onSuccess` frame declares no `contE` arm, so a failing exit passes it
inside the same step and it leaves no service-level row. -/
private theorem step_onSuccess_passed (interp : Table) (cause : Err) (body : Code)
    (name : RegionName) (rest : List Code) :
    Agree ((Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
        (Effect4.Prim.onSuccess body name :: rest) true none false).step interp)
      ((Effect4.FrameFiber.mk (Effect4.Prim.failure cause) rest true none false).step interp) := by
  refine agree_failure interp cause _ _ rfl rfl ?_
  rw [Effect4.FrameFiber.getCont_skip_clears_deferred,
    Effect4.FrameFiber.getCont_skip_clears_deferred]
  exact popFrom_passed Effect4.Arm.contE true (Effect4.Prim.failure cause)
    (Effect4.Prim.onSuccess body name) rest true true rfl rfl rfl

/-- The mask frame `ensure` pushes declares neither demandable arm, so it is
passed inside the same step, restoring the flag it stores; it leaves no
service-level row. -/
private theorem step_mask_passed (interp : Table) (cause : Err) (rest : List Code)
    (flag : Bool) :
    Agree ((Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
        (Effect4.Prim.setInterruptible true :: rest) flag none false).step interp)
      ((Effect4.FrameFiber.mk (Effect4.Prim.failure cause) rest true none false).step interp) := by
  refine agree_failure interp cause _ _ rfl rfl ?_
  rw [Effect4.FrameFiber.getCont_skip_clears_deferred,
    Effect4.FrameFiber.getCont_skip_clears_deferred]
  exact popFrom_passed Effect4.Arm.contE true (Effect4.Prim.failure cause)
    (Effect4.Prim.setInterruptible true) rest flag true rfl rfl rfl

/-- The same, for a closing value: `resumeValue` pops without skipping, and the
mask frame answers neither arm. -/
private theorem step_mask_passed_success (interp : Table) (value : Val) (rest : List Code)
    (flag : Bool) :
    Agree ((Effect4.FrameFiber.mk (Effect4.Prim.success value)
        (Effect4.Prim.setInterruptible true :: rest) flag none false).step interp)
      ((Effect4.FrameFiber.mk (Effect4.Prim.success value) rest true none false).step interp) := by
  refine agree_success interp value _ _ rfl rfl ?_
  rw [Effect4.FrameFiber.getCont_eq_popFrom _ _ _ rfl,
    Effect4.FrameFiber.getCont_eq_popFrom _ _ _ rfl]
  exact popFrom_passed Effect4.Arm.contA false (Effect4.Prim.success value)
    (Effect4.Prim.setInterruptible true) rest flag true rfl rfl rfl

/-- An empty stack yields the failing exit. -/
private theorem step_empty_failure (interp : Table) (cause : Err) :
    (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) [] true none false).step interp =
      (Effect4.FrameStep.finished (Effect4.Exit.failure cause),
        [Effect4.FrameEvent.yielded (Effect4.Exit.failure cause)]) := rfl

/-- The `onSuccess` frame a region opens answers the closing value with its
named continuation, under the stack that was below it. -/
private theorem step_onSuccess_answers (interp : Table) (value : Val) (body : Code)
    (name : RegionName) (rest : List Code) :
    (Effect4.FrameFiber.mk (Effect4.Prim.success value)
        (Effect4.Prim.onSuccess body name :: rest) true none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contA name value) rest true none false),
        [Effect4.FrameEvent.popped (Effect4.Prim.onSuccess body name)]) := rfl

/-- A successful finalizer restores the exit it observed, on the nose. -/
private theorem restore_success (exit : Res) :
    Effect4.Exit.restoreAfterFinalizer exit (Effect4.Exit.success ()) = exit := by
  cases exit <;> rfl

/-- **The unwind theorem.** A failing exit propagating through a fragment stack
runs exactly the finalizers that stack names, in pop order, every one of them
against the *same* exit — which is the runner's `closeReleases`, whose
`finalizer` row carries the closing exit for every release of one close — and
then yields that exit. `hfin` is the hypothesis that no release fails; it is
what `regionReleaseFails` violates and why that flow has no host golden
(`E4-TARGET-CE-012`), and the failing-release case is recorded as owed in the
module header. -/
theorem unwind_failure (interp : Table) (cause : Err)
    (hfin : forall name exit, interp.finalizerExit name exit = Effect4.Exit.success ()) :
    forall (stack : List Code), unwindable stack = true ->
      forall fuel, (unwindNames stack).length + 1 <= fuel ->
        (Effect4.FrameFiber.run interp fuel
            (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) stack true none false)).fst =
          Effect4.FrameStep.finished (Effect4.Exit.failure cause) /\
        traceOfRun (Effect4.FrameFiber.run interp fuel
            (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) stack true none false)).snd =
          (unwindNames stack).map (finalizerRow (Effect4.Exit.failure cause)) ++
            [Effects.Trace.Event.done (outcomeOf (Effect4.Exit.failure cause))] := by
  intro stack
  induction stack with
  | nil =>
    intro _ fuel hfuel
    have hnames : (unwindNames ([] : List Code)).length = 0 := rfl
    rw [hnames] at hfuel
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
    have hk' : fuel = k + 1 := by omega
    subst hk'
    rw [Effect4.FrameFiber.run_succ_finished interp _ k _ _ (step_empty_failure interp cause)]
    exact ⟨rfl, rfl⟩
  | cons frame rest ih =>
    intro hstack fuel hfuel
    cases frame
    case onSuccess body name =>
      have hrest : unwindable rest = true := by
        simpa [unwindable] using hstack
      have hnames : unwindNames (Effect4.Prim.onSuccess body name :: rest) = unwindNames rest := rfl
      rw [hnames] at hfuel ⊢
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
      have hk' : fuel = k + (unwindNames rest).length + 1 := by omega
      subst hk'
      obtain ⟨hf, hs⟩ := run_congr interp _ _ (k + (unwindNames rest).length)
        (step_onSuccess_passed interp cause body name rest)
      rw [hf, hs]
      exact ih hrest _ (by omega)
    case setInterruptible flag =>
      have hflag : flag = true := by
        cases flag with
        | true => rfl
        | false => simp [unwindable] at hstack
      subst hflag
      have hrest : unwindable rest = true := by
        simpa [unwindable] using hstack
      have hnames : unwindNames (Effect4.Prim.setInterruptible true :: rest) = unwindNames rest :=
        rfl
      rw [hnames] at hfuel ⊢
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
      have hk' : fuel = k + (unwindNames rest).length + 1 := by omega
      subst hk'
      obtain ⟨hf, hs⟩ := run_congr interp _ _ (k + (unwindNames rest).length)
        (step_mask_passed interp cause rest true)
      rw [hf, hs]
      exact ih hrest _ (by omega)
    case onExit body name flag =>
      have hflag : flag = false := by
        cases flag with
        | false => rfl
        | true => simp [unwindable] at hstack
      subst hflag
      have hrest : unwindable rest = true := by
        simpa [unwindable] using hstack
      have hnames : unwindNames (Effect4.Prim.onExit body name false :: rest) =
        name :: unwindNames rest := rfl
      rw [hnames] at hfuel ⊢
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
      have hlen : (name :: unwindNames rest).length = (unwindNames rest).length + 1 :=
        List.length_cons
      rw [hlen] at hk
      have hk' : fuel = (k + (unwindNames rest).length + 1) + 1 := by omega
      subst hk'
      have hstep : (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          (Effect4.Prim.onExit body name false :: rest) true none false).step interp =
          (Effect4.FrameStep.running
            (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
              (Effect4.Prim.setInterruptible true :: rest) false none false),
            [Effect4.FrameEvent.popped (Effect4.Prim.onExit body name false),
              Effect4.FrameEvent.ranContAll (Effect4.Prim.onExit body name false),
              Effect4.FrameEvent.ranFinalizer name (Effect4.Exit.failure cause)]) := by
        rw [step_onExit_failure interp cause body name rest, hfin]
        rfl
      rw [Effect4.FrameFiber.run_succ_running interp _ _
        (k + (unwindNames rest).length + 1) _ hstep]
      obtain ⟨hf, hs⟩ := run_congr interp
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          (Effect4.Prim.setInterruptible true :: rest) false none false)
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) rest true none false)
        (k + (unwindNames rest).length) (step_mask_passed interp cause rest false)
      obtain ⟨hrf, hrs⟩ := ih hrest (k + (unwindNames rest).length + 1) (by omega)
      refine ⟨?_, ?_⟩
      · show (Effect4.FrameFiber.run interp (k + (unwindNames rest).length + 1) _).fst = _
        rw [hf, hrf]
      · show traceOfRun (_ ++ (Effect4.FrameFiber.run interp
          (k + (unwindNames rest).length + 1) _).snd) = _
        simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append]
        rw [show (List.filterMap
            (Effect4.FrameEvent.toTrace RegionName.regionOf id id (fun _ => Val.unit))
            (Effect4.FrameFiber.run interp (k + (unwindNames rest).length + 1)
              (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
                (Effect4.Prim.setInterruptible true :: rest) false none false)).snd) =
          _ from hs, hrs]
        rfl
    all_goals simp [unwindable] at hstack

/-- **The close theorem.** A closing value runs the `onExit` frames above the
frame that answers it, latest-registered first, every one of them against the
closing exit, and then the region frame answers with its named continuation
under the stack that was below it. -/
theorem close_success (interp : Table) (value : Val)
    (hfin : forall name exit, interp.finalizerExit name exit = Effect4.Exit.success ())
    (body : Code) (name : RegionName) (rest : List Code) :
    forall (frames : List Code), closeable frames = true ->
      (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ Effect4.Prim.onSuccess body name :: rest) true none false)).fst =
        Effect4.FrameStep.running
          (Effect4.FrameFiber.mk (interp.contA name value) rest true none false) /\
      traceOfRun (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ Effect4.Prim.onSuccess body name :: rest) true none false)).snd =
        (closeNames frames).map (finalizerRow (Effect4.Exit.success value)) := by
  intro frames
  induction frames with
  | nil =>
    intro _
    rw [show (closeNames ([] : List Code)).length + 1 = 0 + 1 from rfl,
      show ([] : List Code) ++ Effect4.Prim.onSuccess body name :: rest =
        Effect4.Prim.onSuccess body name :: rest from rfl,
      Effect4.FrameFiber.run_succ_running interp _ _ 0 _
        (step_onSuccess_answers interp value body name rest)]
    exact ⟨rfl, rfl⟩
  | cons frame more ih =>
    intro hframes
    cases frame
    case setInterruptible flag =>
      have hflag : flag = true := by
        cases flag with
        | true => rfl
        | false => simp [closeable] at hframes
      subst hflag
      have hmore : closeable more = true := by
        simpa [closeable] using hframes
      have hnames : closeNames (Effect4.Prim.setInterruptible true :: more) = closeNames more := rfl
      rw [hnames]
      obtain ⟨hf, hs⟩ := run_congr interp _ _ ((closeNames more).length)
        (step_mask_passed_success interp value (more ++ Effect4.Prim.onSuccess body name :: rest)
          true)
      show (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
            (Effect4.FrameFiber.mk (Effect4.Prim.success value)
              (Effect4.Prim.setInterruptible true ::
                (more ++ Effect4.Prim.onSuccess body name :: rest)) true none false)).fst =
            Effect4.FrameStep.running
              (Effect4.FrameFiber.mk (interp.contA name value) rest true none false) /\
          traceOfRun (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
            (Effect4.FrameFiber.mk (Effect4.Prim.success value)
              (Effect4.Prim.setInterruptible true ::
                (more ++ Effect4.Prim.onSuccess body name :: rest)) true none false)).snd =
            (closeNames more).map (finalizerRow (Effect4.Exit.success value))
      rw [hf, hs]
      exact ih hmore
    case onExit finBody finName flag =>
      have hflag : flag = false := by
        cases flag with
        | false => rfl
        | true => simp [closeable] at hframes
      subst hflag
      have hmore : closeable more = true := by
        simpa [closeable] using hframes
      have hnames : closeNames (Effect4.Prim.onExit finBody finName false :: more) =
        finName :: closeNames more := rfl
      rw [hnames]
      rw [show (finName :: closeNames more).length + 1 = (closeNames more).length + 1 + 1 by
        simp [List.length_cons]]
      have hstep : (Effect4.FrameFiber.mk (Effect4.Prim.success value)
          ((Effect4.Prim.onExit finBody finName false :: more) ++
            Effect4.Prim.onSuccess body name :: rest) true none false).step interp =
          (Effect4.FrameStep.running
            (Effect4.FrameFiber.mk (Effect4.Prim.success value)
              (Effect4.Prim.setInterruptible true ::
                (more ++ Effect4.Prim.onSuccess body name :: rest)) false none false),
            [Effect4.FrameEvent.popped (Effect4.Prim.onExit finBody finName false),
              Effect4.FrameEvent.ranContAll (Effect4.Prim.onExit finBody finName false),
              Effect4.FrameEvent.ranFinalizer finName (Effect4.Exit.success value)]) := by
        rw [show (Effect4.Prim.onExit finBody finName false :: more) ++
              Effect4.Prim.onSuccess body name :: rest =
            Effect4.Prim.onExit finBody finName false ::
              (more ++ Effect4.Prim.onSuccess body name :: rest) from rfl,
          step_onExit_success interp value finBody finName
            (more ++ Effect4.Prim.onSuccess body name :: rest), hfin]
        rfl
      rw [Effect4.FrameFiber.run_succ_running interp _ _
        ((closeNames more).length + 1) _ hstep]
      obtain ⟨hf, hs⟩ := run_congr interp _ _ ((closeNames more).length)
        (step_mask_passed_success interp value (more ++ Effect4.Prim.onSuccess body name :: rest)
          false)
      obtain ⟨hrf, hrs⟩ := ih hmore
      refine ⟨?_, ?_⟩
      · show (Effect4.FrameFiber.run interp ((closeNames more).length + 1) _).fst = _
        rw [hf, hrf]
      · show traceOfRun (_ ++ (Effect4.FrameFiber.run interp ((closeNames more).length + 1) _).snd)
          = _
        simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append]
        rw [show (List.filterMap
            (Effect4.FrameEvent.toTrace RegionName.regionOf id id (fun _ => Val.unit))
            (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
              (Effect4.FrameFiber.mk (Effect4.Prim.success value)
                (Effect4.Prim.setInterruptible true ::
                  (more ++ Effect4.Prim.onSuccess body name :: rest)) false none false)).snd) =
          _ from hs, hrs]
        rfl
    all_goals simp [closeable] at hframes

end Effect4.RegionSimulation
