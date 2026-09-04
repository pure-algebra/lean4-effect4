import Effect4.Semantics.FrameSimulation
import Effect4.Flow.Region
import Effect4.Runtime.ScopeMachine
import Effect4.Target.TypeScript.Simulation

/-!
# Semantics.RegionSimulation

Owner: the finalizer half of packet D4 — the simulation between the region
runner of `Effect4/Flow/Region.lean` and the rc.112 frame machine of
`Effect4/Runtime/Runtime.lean`, under the mask that keeps `finalizer` and
`done`.

**Spike S4 (2026-09-03) landed three compile repairs in this file.** They are
`docs/research/2026-09-03-deep-flow-to-frames.md` §2.2's ▲ items P1, P2 and P3,
and they discharge the repair columns of `E4-TARGET-CE-019`, the finalisation
half of `E4-TARGET-CE-020`/`-021`, and the compile half of `E4-FLOW-CE-020`.

* **P1 — one scope per region.** A region is *one* scope, not a nest of
  independent caller-side `OnExit` frames. rc.112 closes that one scope with
  `exitAsVoidAll` (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3826`,
  the loop at `:3815-3827`), which hands **every** registered release the same
  original closing exit and combines the collected exits only after the loop;
  `Effect.acquireRelease` registers on that scope and pushes no frame of its own
  (`:3971-3987`). So the region's `enter` now compiles to *one*
  `Prim.onSuccessAndFailure`, whose value name is `RegionName.regionCont` and
  whose cause name is `RegionName.close`, and the close result is
  `closeExit` — the three-arm `ScopeMachine.finish` of the oracle's release
  exits in `Scope.closeOrder`. Each registered release keeps an
  `onExit` frame whose only job is the `finalizer` row rc.112's release lambda
  writes (`regions.finalizer(1, exit)`), and whose `finalizerExit` is
  `Exit.success ()` — so no release's outcome is ever fed into the exit the
  next release sees. That is `Effect4.Flow.closeReleases` (`Region.lean:134-145`)
  and `Effect4.ScopeMachine.request_uses_original` (`ScopeMachine.lean:100`).
  Because `finalizerExit` is now constantly `Exit.success ()`, the `hfin`
  premise of `unwind_failure`/`close_success` is *discharged* for every compiled
  run (`regionInterp_finalizerExit`), and the two theorems are restated with a
  per-name premise instead of a global one.

  Why the region frame is not a `Prim.onExit`: ruling 7 of
  `test/contracts/frame-simulation.contract.md` already forces it. The only
  `FrameEvent` with a service-level shadow other than `yielded` is
  `ranFinalizer`, and `Prim.onExit` is the only primitive that emits one, so a
  region compiled to `Prim.onExit` would manufacture one `finalizer` row per
  region that neither the runner nor the host writes. `Prim.onSuccessAndFailure`
  answers both arms (rc.112's scope-closing `OnExit` answers both) and emits no
  row.

* **P2 — a live frontier stays live.** The eight arms that sent exhausted
  fuel, a missing block, a stuck plan, an exhausted or mismatched tape, or a
  malformed `acquire`/`leave` to `Prim.failure Cause.empty` now emit
  `Prim.suspend point`, whose `suspendBody` is itself, so `FrameFiber.step` is a
  fixed point (`Runtime.lean` `step_suspend`, `step_parking_is_a_fixed_point`)
  and `FrameFiber.run` answers `FrameStep.running` with no event at all. A live
  frontier is distinct from typed failure and from refusal — `docs/DESIGN-BASIS.md`
  DB-04, `Runtime.lean:2435-2439`. The *classification* half (T8: telling live
  suspension, refusal and completion apart) is packet P5 and is **not** closed
  here: a `mismatch` refusal also compiles to a live suspension.

* **P3 — `performCatch` is `onSuccessAndFailure`.** `Effect.result` is
  `matchEager` → `matchCause` → `matchCauseEffect` = `OnSuccessAndFailure`
  (`internal/effect.ts:3417-3420`, `:3450-3460`). The caught perform compiles to
  `Prim.onSuccessAndFailure (Prim.sync-shaped body) (RegionName.cont point)
  (RegionName.caught point)`, the body is a `Prim.suspend` whose `suspendBody`
  is `Prim.failure (Cause.fail error)` on an erroring answer, and the machine's
  `armE` resumes at the failure successor. The old sleight of hand — the error
  resolved inside `contA` so that no frame ever saw a `Cause` — is gone.
  `compileRegion_catchFree` is the S3-shaped statement that this costs a
  catch-free flow nothing: no `RegionName.caught` name is emitted.

  (The constructor is spelled `caught` rather than `catch` because `catch` is a
  `do`-notation token in Lean 4.)

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
the machine's merged cause and the runner's list are related by a projection,
not divergent:

* `causeOfFailures` sends a failure list to the cause whose reasons are those
  errors, unannotated, in order — a section;
* `failuresOfCause` sends a cause to its `fail` errors in order — the function
  direction, total, and `failuresOfCause_causeOfFailures` says it retracts.

The direction that is a *function* is `failuresOfCause`. `causeOfFailures` is not
surjective — a cause carrying a `die` or an `interrupt` reason has no failure
list preimage — so the projection only ever goes cause-to-list.

**Since P1 the close merge is concatenation, never `Cause.combine`.**
`Cause.combine` is `dedup` of the concatenation, and rc.112's `causeCombine`
dedups by structural equality including annotations (`internal/effect.ts:242-258`)
while `exitAsVoidAll` does not dedup at all (`:2025-2038`). A scope close is the
second one. `closeExit` therefore goes through `Exit.asVoidAll`, and the region's
cause arm appends the closing reasons to the body's rather than combining them —
which is what `E4-FLOW-CE-021` and `merge_is_concatenation_not_union` pin.
`toOutcome_combine` below is retained because it is what makes the *wire*
insensitive to whichever merge is used, with no hypothesis on
`ReasonAnnotations`.

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
names, in pop order, all against the same exit, and yields that exit),
`unwind_to_frame` (the same up to the first frame that declares a cause arm —
the region's scope frame), `close_success_of` and its two corollaries (a closing
value runs the `onExit` frames above the frame that answers it, latest
registered first, all against the same exit), and `regionInterp_finalizerExit`,
which discharges all three theorems' premise for every compiled run.

Owed — the general theorem. `RegionsSimulate` and `RegionsSimulateExit` below
state T5 and T6 of `docs/research/2026-09-03-deep-flow-to-frames.md` §2.3 as
`Prop`s, with `RegionOracleAgrees` naming the missing induction: the agreement
between `oracle.registrations` and the runner's `Frame.releases`, and between
the configuration a region's continuation resumes at and the one the runner
holds at the `leave`. `closeWalk` is the `leaveConfig` function that obligation
needs, spelled here so the instances evaluate; the proof that it agrees with
`Effect4.Flow.regionLoop` is packet P4's remaining obligation and is not in this
file. The instances on `regionNested`, `regionTwoFail`, `regionBothSucceed` and
`releaseFails` are closed by evaluation in
`Effect4Test/Semantics/RegionSimulationContract.lean`, and the harness prints
both sides of the equation for every region program
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
  /-- The failure successor of the `performCatch` at `point`: the cause name of
  the `onSuccessAndFailure` frame `Effect.result` builds
  (`internal/effect.ts:3417-3420`). Spelled `caught` because `catch` is a
  `do`-notation token. -/
  | caught (point : Config)
  /-- The value name of the scope frame the region opened at `point` pushes: its
  `continue_` block, reached once the scope has closed. -/
  | regionCont (region : Nat) (point : Config)
  /-- The cause name of that same scope frame: the region's close on a failing
  body. One per region, never one per registration
  (`internal/effect.ts:3815-3827`). -/
  | close (region : Nat) (point : Config)
  /-- The release the `acquire` at `point` registered on `region`'s scope. Its
  frame writes the `finalizer` row rc.112's release lambda writes and leaves the
  closing exit untouched. -/
  | fin (region : Nat) (point : Config)
deriving DecidableEq

/-- The region a name belongs to, for `FrameEvent.toTrace`. Only `fin` names
ever reach it: a `ranFinalizer` event carries no other constructor, because
`fin` is the only name a `Prim.onExit` in a compiled program carries. -/
def RegionName.regionOf : RegionName -> Nat
  | RegionName.cont _ => 0
  | RegionName.caught _ => 0
  | RegionName.regionCont region _ => region
  | RegionName.close region _ => region
  | RegionName.fin region _ => region

/-- The run point a name belongs to. -/
def RegionName.point : RegionName -> Config
  | RegionName.cont point => point
  | RegionName.caught point => point
  | RegionName.regionCont _ point => point
  | RegionName.close _ point => point
  | RegionName.fin _ point => point

/-- The fragment's cause carrier, as fence B fixes it. -/
abbrev Err := Effect4.Cause Val Unit Unit Unit

/-- The fragment's exit carrier. -/
abbrev Res := Effect4.Exit Val Val Unit Unit Unit

/-- The exit a scope's release reports: `Unit`-valued, as `Scope.closeExitsM`
takes it. -/
abbrev Cleanup := Effect4.Exit Unit Val Unit Unit Unit

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

/-! ## The projection between a merged cause and the runner's failure list

`Effect4.Flow.Failures` is `List Val`, in close order, first failure first
(`closeFrame_failure_merge`). `Effect4.Cause` is a list of `Reason`s. The two
are related by a section and a retraction, and only the retraction is a
function on all of `Cause`. They are declared here because P1's close result and
P3's caught error both read them. -/

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

/-! ## The oracle

`PrimInterp` is a record of pure total functions, so the machine has nowhere to
put the service's monad; the answers are supplied, exactly as fence B's tape
supplies them. Here the key is the *point* rather than an occurrence index,
because `Config.fuel` already distinguishes occurrences. -/

/-- What the service answers along one run: at each point, the answer of the
operation that point performs; for an `acquire`, the answer of the release it
registers when its scope closes; and, for an `enter`, the acquire points that
region's scope holds when it closes — `Scope.closeOrder`, latest registered
first (`Effect4.Flow.Frame.toScope_closeOrder`).

`registrations` is P1's new field. `docs/research/2026-09-03-deep-flow-to-frames.md`
§2.2 recommends exactly this shape: an oracle field whose agreement with the
runner's `Frame.releases` is a *stated hypothesis* rather than a second copy of
the runner buried in the compile. -/
structure RegionOracle where
  /-- The answer of the operation performed at this point. -/
  answer : Config -> Except Val Val
  /-- The answer of the release the `acquire` at this point registered. -/
  release : Config -> Except Val Val
  /-- The acquire points the region entered at this point has registered when it
  closes, latest registered first. -/
  registrations : Config -> List Config

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
      | .performCatch op request _ _ _ _ => some (op, request)
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
      | .performCatch _ _ target env' _ _ => some (target, env', none)
      | _ => none
    | .acquire operation request release target args =>
      match alphabet.lookup operation, alphabet.lookup release, point.env[request.index]?,
          Effect4.Flow.readArgs point.env args, current.region with
      | some _, some _, some _, some values, some region => some (target, values, some region.value)
      | _, _, _, _, _ => none
    | _ => none

/-- Where the *caught* failure of the `performCatch` at `point` continues (Flow
v3): the failure successor and the environment its parameters receive before
the error value is appended. A point that is not a `performCatch` has none, and
its failure unwinds as before. -/
def catchCont (point : Config) : Option (BlockId × Effect4.Flow.Env) :=
  match flow.block? point.block with
  | none => none
  | some current =>
    match current.term with
    | .plain term =>
      match Effect4.Flow.plan alphabet
          { id := current.id, params := current.params, term := term } point.env point.tape with
      | .performCatch _ _ _ _ onError errorEnv => some (onError, errorEnv)
      | _ => none
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

/-! ## `leaveConfig`, spelled

The module header used to record the general induction as blocked on "a
`leaveConfig` function that walks a region body to its close under the oracle".
`closeWalk` is that function. It mirrors `compileRegion`'s recursion arm for
arm — including the fuel and tape a nested region's continuation resumes with —
so every `Config` it records is *the same name* the compile emits. It is used
only to give `statelessOracle` a computable `registrations` field; the general
theorem carries the agreement as `RegionOracleAgrees` rather than assuming this
walk is the runner. -/

/-- The acquire points a region body registers on its own scope, latest
registered first, and the value its `leave` hands on when it reaches one. A body
that fails, runs out of fuel, or stops on a frontier still reports the
registrations it made — which is exactly the runner's `Frame.releases` at the
moment `unwind` closes the frame. -/
def closeWalk {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (answer : Config -> Except Val Val) :
    Nat -> BlockId -> Effect4.Flow.Env -> Effect4.Flow.Tape -> List Config ->
      List Config × Option Val
  | 0, _, _, _, acc => (acc, none)
  | fuel + 1, block, env, tape, acc =>
    match flow.block? block with
    | none => (acc, none)
    | some current =>
      match current.term with
      | .plain term =>
        match Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | .jump target env' => closeWalk alphabet flow answer fuel target env' tape acc
        | .choose _ _ target env' rest => closeWalk alphabet flow answer fuel target env' rest acc
        | .perform _ _ target env' =>
          match answer ⟨fuel + 1, block, env, tape⟩ with
          | .ok value => closeWalk alphabet flow answer fuel target (env' ++ [value]) tape acc
          | .error _ => (acc, none)
        | .performCatch _ _ target env' onError errorEnv =>
          match answer ⟨fuel + 1, block, env, tape⟩ with
          | .ok value => closeWalk alphabet flow answer fuel target (env' ++ [value]) tape acc
          | .error error =>
            closeWalk alphabet flow answer fuel onError (errorEnv ++ [error]) tape acc
        | _ => (acc, none)
      | .enter region body args =>
        match Effect4.Flow.readArgs env args with
        | none => (acc, none)
        | some values =>
          match (closeWalk alphabet flow answer fuel body values tape []).snd with
          | none => (acc, none)
          | some value =>
            match flow.row? region with
            | none => (acc, none)
            | some row => closeWalk alphabet flow answer fuel row.continue_ [value] tape acc
      | .acquire _ _ _ _ _ =>
        match performCont alphabet flow ⟨fuel + 1, block, env, tape⟩,
            answer ⟨fuel + 1, block, env, tape⟩ with
        | some (target, env', _), .ok value =>
          closeWalk alphabet flow answer fuel target (env' ++ [value]) tape
            (⟨fuel + 1, block, env, tape⟩ :: acc)
        | _, _ => (acc, none)
      | .leave value =>
        match env[value.index]? with
        | some v => (acc, some v)
        | none => (acc, none)

/-- The registrations of the region whose `enter` is at `point`. -/
def regionRegistrations {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (answer : Config -> Except Val Val) (point : Config) : List Config :=
  match flow.block? point.block with
  | none => []
  | some current =>
    match current.term with
    | .enter _ body args =>
      match Effect4.Flow.readArgs point.env args with
      | some values =>
        (closeWalk alphabet flow answer (point.fuel - 1) body values point.tape []).fst
      | none => []
    | _ => []

/-! ## One scope per region: the close result

`Effect4.ScopeMachine.finish` is `private` to its module, so its three arms are
spelled again here and `closeFinish_eq_result?` is the bridge. The three arms
matter: at exactly one finalizer the scope returns that finalizer's own exit
*unmerged* (`Effect4.Scope.closeResult_single`), which `E4-RUN-CE-009` exists to
forbid flattening. -/

/-- The exit one registered release reports to its region's scope. -/
def releaseExitOf (oracle : RegionOracle) (point : Config) : Cleanup :=
  match oracle.release point with
  | .ok _ => Effect4.Exit.void
  | .error error => Effect4.Exit.failure (Effect4.Cause.fail error)

/-- The exits a region's registrations report, in close order. -/
def releaseExitsOf (oracle : RegionOracle) (points : List Config) : List Cleanup :=
  points.map (releaseExitOf oracle)

/-- `Effect4.ScopeMachine`'s zero/one/many close policy. -/
def closeFinish : List Cleanup -> Cleanup
  | [] => Effect4.Exit.void
  | [only] => only
  | first :: second :: rest => Effect4.Exit.asVoidAll (first :: second :: rest)

/-- The one exit a region's scope produces: rc.112's `exitAsVoidAll` over the
release exits it collected (`internal/effect.ts:3826`, `:2025-2038`), through
`ScopeMachine`'s three-arm policy. -/
def closeExit (oracle : RegionOracle) (points : List Config) : Cleanup :=
  closeFinish (releaseExitsOf oracle points)

/-- The failures a region's close reports, in close order — the runner's
`Effect4.Flow.closeFailures`. -/
def closeFailuresOf (oracle : RegionOracle) (points : List Config) : Effect4.Flow.Failures :=
  points.filterMap fun point =>
    match oracle.release point with
    | .ok _ => none
    | .error error => some error

/-- Zero registrations close on the void exit. census: scope.close-merge -/
theorem closeFinish_nil : closeFinish [] = Effect4.Exit.void := rfl

/-- **Exactly one registration closes on that finalizer's own exit, unmerged.**
This is `Effect4.Scope.closeResult_single`, and `E4-RUN-CE-009` exists to forbid
flattening it into the many-arm. census: scope.close-merge -/
theorem closeFinish_single (only : Cleanup) : closeFinish [only] = only := rfl

/-- Two or more registrations close on rc.112's `exitAsVoidAll`
(`internal/effect.ts:2025-2038`). census: scope.exit-as-void-all -/
theorem closeFinish_many (first second : Cleanup) (rest : List Cleanup) :
    closeFinish (first :: second :: rest) = Effect4.Exit.asVoidAll (first :: second :: rest) := rfl

/-- The bridge to the residual close machine: on a completed close,
`Effect4.ScopeMachine.result?` is `closeFinish` of the captured replies. The
`ScopeMachine` spelling of the three arms is `private` to its module, so
`closeFinish` restates it and this theorem says the two agree.
census: scope.close-merge -/
theorem closeFinish_eq_result? {κ φ : Type}
    (machine : Effect4.ScopeMachine.State κ φ Val Val Unit Unit Unit)
    (h : machine.phase = Effect4.ScopeMachine.Phase.complete) :
    Effect4.ScopeMachine.result? machine =
      some (closeFinish (machine.captured.map Prod.snd)) := by
  unfold Effect4.ScopeMachine.result?
  rw [h]
  cases hcaptured : machine.captured.map Prod.snd with
  | nil => rfl
  | cons first tail =>
    cases tail with
    | nil => rfl
    | cons second more => rfl

/-- The reasons the release exits contribute, in close order. -/
private theorem releaseExits_reasons (oracle : RegionOracle) :
    forall points : List Config,
      (releaseExitsOf oracle points).flatMap Effect4.Exit.causeReasons =
        (causeOfFailures (closeFailuresOf oracle points)).reasons := by
  intro points
  induction points with
  | nil => rfl
  | cons point rest ih =>
    have hstep : (releaseExitsOf oracle (point :: rest)).flatMap Effect4.Exit.causeReasons =
        (releaseExitOf oracle point).causeReasons ++
          (releaseExitsOf oracle rest).flatMap Effect4.Exit.causeReasons := rfl
    rw [hstep, ih]
    cases hrel : oracle.release point with
    | ok value =>
      have hhead : (releaseExitOf oracle point).causeReasons = [] := by
        simp only [releaseExitOf, hrel]
        rfl
      have htail : closeFailuresOf oracle (point :: rest) = closeFailuresOf oracle rest := by
        simp only [closeFailuresOf, List.filterMap_cons, hrel]
      rw [hhead, htail, List.nil_append]
    | error error =>
      have hhead : (releaseExitOf oracle point).causeReasons =
          [Effect4.Reason.fail error Effect4.ReasonAnnotations.empty] := by
        simp only [releaseExitOf, hrel]
        rfl
      have htail : closeFailuresOf oracle (point :: rest) =
          error :: closeFailuresOf oracle rest := by
        simp only [closeFailuresOf, List.filterMap_cons, hrel]
      rw [hhead, htail]
      rfl

/-- **The close is `asVoidAll`, not `Cause.combine`.** The reasons a region's
close carries are exactly its failure list, in close order, duplicates kept —
which is `Effect4.Flow.closeFrame_failure_merge` on the runner side and
`Exit.asVoidAll_keeps_duplicates` on the scope side.
census: scope.exit-as-void-all -/
theorem closeExit_reasons (oracle : RegionOracle) (points : List Config) :
    (closeExit oracle points).causeReasons =
      (causeOfFailures (closeFailuresOf oracle points)).reasons := by
  have hflat := releaseExits_reasons oracle points
  cases points with
  | nil => rfl
  | cons first rest =>
    cases rest with
    | nil =>
      simp only [releaseExitsOf, List.map_cons, List.map_nil, List.flatMap_cons,
        List.flatMap_nil, List.append_nil] at hflat
      exact hflat
    | cons second more =>
      show (Effect4.Exit.asVoidAll (releaseExitsOf oracle (first :: second :: more))).causeReasons
        = _
      rw [Effect4.Exit.asVoidAll_reasons]
      exact hflat

/-- A close with no failing release is a successful close.
census: scope.close-merge -/
theorem closeExit_success_iff (oracle : RegionOracle) (points : List Config)
    (h : closeFailuresOf oracle points = []) :
    (closeExit oracle points).causeReasons = [] := by
  rw [closeExit_reasons, h]
  rfl

/-! ## The compilation -/

/-- The region-aware compilation into the frame machine.

`enter` pushes the region's **one** scope frame — rc.112's
`Effect.scoped(Effect.onExit(…))` at `internal/effect.ts:3938-3947`, whose value
continues at `continue_` and whose cause arm closes the scope; `acquire`
performs its operation and, in `regionInterp.contA`, registers a release frame
whose only observation is the `finalizer` row rc.112's release lambda writes
(`internal/effect.ts:3971-3987` registers on the scope and pushes no frame of
its own); `leave` yields the closing value, which pops through the release
frames latest registered first, every one of them against the *same* exit.

A shape the runner refuses or has not reached — a missing block, a stuck plan,
an exhausted or mismatched tape, a malformed `acquire`, exhausted fuel —
compiles to `Prim.suspend point`, a live frontier (P2). It is never an exit:
`docs/DESIGN-BASIS.md` DB-04. -/
def compileRegion {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty) :
    Nat -> BlockId -> Effect4.Flow.Env -> Effect4.Flow.Tape -> Code
  | 0, block, env, tape => Effect4.Prim.suspend ⟨0, block, env, tape⟩
  | fuel + 1, block, env, tape =>
    match flow.block? block with
    | none => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩
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
        | .performCatch _ _ _ _ _ _ =>
          Effect4.Prim.onSuccessAndFailure (Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩)
            (RegionName.cont ⟨fuel + 1, block, env, tape⟩)
            (RegionName.caught ⟨fuel + 1, block, env, tape⟩)
        | .choose _ _ target env' rest => compileRegion alphabet flow fuel target env' rest
        | .stuck => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩
        | .exhausted _ => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩
        | .mismatch _ _ => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩
      | .enter region body args =>
        match Effect4.Flow.readArgs env args with
        | some values =>
          Effect4.Prim.onSuccessAndFailure (compileRegion alphabet flow fuel body values tape)
            (RegionName.regionCont region.value ⟨fuel + 1, block, env, tape⟩)
            (RegionName.close region.value ⟨fuel + 1, block, env, tape⟩)
        | none => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩
      | .acquire _ _ _ _ _ =>
        match performCont alphabet flow ⟨fuel + 1, block, env, tape⟩ with
        | some _ =>
          Effect4.Prim.onSuccess (Effect4.Prim.sync ⟨fuel + 1, block, env, tape⟩)
            (RegionName.cont ⟨fuel + 1, block, env, tape⟩)
        | none => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩
      | .leave value =>
        match env[value.index]? with
        | some v => Effect4.Prim.success v
        | none => Effect4.Prim.suspend ⟨fuel + 1, block, env, tape⟩

/-- The compilation at a point. It is `compileRegion` with the point's four
fields spread out; the fuel is the first argument so the recursion is
structural and the compiled program is kernel-reducible, which is what the
receipts on the four region programs evaluate. -/
def compileAt {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (point : Config) : Code :=
  compileRegion alphabet flow point.fuel point.block point.env point.tape

/-- Whether a primitive is a failure. Used only to state P2's general law. -/
def isFailure : Code -> Bool
  | Effect4.Prim.failure _ => true
  | _ => false

/-- **P2's general law: the compile never manufactures a failure.** Every arm of
`compileRegion` emits `success`, `suspend`, `onSuccess` or `onSuccessAndFailure`
and nothing else, so no shape the runner refuses or has not reached can become
an exit. This is the statement `E4-TARGET-CE-020` attacked — "compiling
exhausted source fuel to an empty failure preserves a live region run" — refuted
at the root rather than restricted: there is no empty failure to compile to.
census: op.Suspend -/
theorem compileRegion_not_failure {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) :
    forall (fuel : Nat) (block : BlockId) (env : Effect4.Flow.Env) (tape : Effect4.Flow.Tape),
      isFailure (compileRegion alphabet flow fuel block env tape) = false := by
  intro fuel
  induction fuel with
  | zero => intro block env tape; rfl
  | succ fuel ih =>
    intro block env tape
    cases hblock : flow.block? block with
    | none => simp only [compileRegion, hblock, isFailure]
    | some current =>
      cases hterm : current.term with
      | plain term =>
        cases hplan : Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | ret value => simp only [compileRegion, hblock, hterm, hplan, isFailure]
        | jump target env' => simp only [compileRegion, hblock, hterm, hplan, ih]
        | perform op request target env' =>
          simp only [compileRegion, hblock, hterm, hplan, isFailure]
        | performCatch op request target env' onError errorEnv =>
          simp only [compileRegion, hblock, hterm, hplan, isFailure]
        | choose site branch target env' rest =>
          simp only [compileRegion, hblock, hterm, hplan, ih]
        | stuck => simp only [compileRegion, hblock, hterm, hplan, isFailure]
        | exhausted site => simp only [compileRegion, hblock, hterm, hplan, isFailure]
        | mismatch expected actual =>
          simp only [compileRegion, hblock, hterm, hplan, isFailure]
      | enter region body args =>
        cases hargs : Effect4.Flow.readArgs env args with
        | none => simp only [compileRegion, hblock, hterm, hargs, isFailure]
        | some values => simp only [compileRegion, hblock, hterm, hargs, isFailure]
      | acquire operation request release target args =>
        cases hcont : performCont alphabet flow ⟨fuel + 1, block, env, tape⟩ with
        | none => simp only [compileRegion, hblock, hterm, hcont, isFailure]
        | some triple => simp only [compileRegion, hblock, hterm, hcont, isFailure]
      | leave value =>
        cases hval : env[value.index]? with
        | none => simp only [compileRegion, hblock, hterm, hval, isFailure]
        | some v => simp only [compileRegion, hblock, hterm, hval, isFailure]

/-- The same, as an inequation. census: op.Suspend -/
theorem compileRegion_never_fails {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (fuel : Nat) (block : BlockId) (env : Effect4.Flow.Env)
    (tape : Effect4.Flow.Tape) (cause : Err) :
    compileRegion alphabet flow fuel block env tape ≠ Effect4.Prim.failure cause := by
  intro h
  have hfalse := compileRegion_not_failure alphabet flow fuel block env tape
  rw [h] at hfalse
  exact absurd hfalse (by simp [isFailure])

/-- The `caught` names a compiled program carries. P3 is the only arm that
emits one. -/
def caughtNames : Code -> List Config
  | Effect4.Prim.onSuccessAndFailure body _ (RegionName.caught point) =>
    point :: caughtNames body
  | Effect4.Prim.onSuccessAndFailure body _ _ => caughtNames body
  | Effect4.Prim.onSuccess body _ => caughtNames body
  | Effect4.Prim.onFailure body _ => caughtNames body
  | Effect4.Prim.onExit body _ _ => caughtNames body
  | Effect4.Prim.exitFrame body => caughtNames body
  | _ => []

/-- **P3 costs a catch-free flow nothing.** This is spike S3's
`compileFork_eq_compileRegion` shape: on a flow no configuration of which plans
a `performCatch`, the compile emits no `RegionName.caught` name, so every
existing receipt — the region instances, the boundary battery, the harness's
`frame-trace` output — is about programs P3 did not touch. It covers the
continuations `regionInterp` produces as well, because every one of them is
itself a `compileRegion` output.
census: op.OnSuccessAndFailure -/
theorem compileRegion_catchFree {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (hfree : forall point, catchCont alphabet flow point = none) :
    forall (fuel : Nat) (block : BlockId) (env : Effect4.Flow.Env) (tape : Effect4.Flow.Tape),
      caughtNames (compileRegion alphabet flow fuel block env tape) = [] := by
  intro fuel
  induction fuel with
  | zero => intro block env tape; rfl
  | succ fuel ih =>
    intro block env tape
    cases hblock : flow.block? block with
    | none => simp only [compileRegion, hblock, caughtNames]
    | some current =>
      cases hterm : current.term with
      | plain term =>
        cases hplan : Effect4.Flow.plan alphabet
            { id := current.id, params := current.params, term := term } env tape with
        | ret value => simp only [compileRegion, hblock, hterm, hplan, caughtNames]
        | jump target env' => simp only [compileRegion, hblock, hterm, hplan, ih]
        | perform op request target env' =>
          simp only [compileRegion, hblock, hterm, hplan, caughtNames]
        | performCatch op request target env' onError errorEnv =>
          have hcatch := hfree ⟨fuel + 1, block, env, tape⟩
          simp only [catchCont, hblock, hterm, hplan] at hcatch
          exact nomatch hcatch
        | choose site branch target env' rest =>
          simp only [compileRegion, hblock, hterm, hplan, ih]
        | stuck => simp only [compileRegion, hblock, hterm, hplan, caughtNames]
        | exhausted site => simp only [compileRegion, hblock, hterm, hplan, caughtNames]
        | mismatch expected actual =>
          simp only [compileRegion, hblock, hterm, hplan, caughtNames]
      | enter region body args =>
        cases hargs : Effect4.Flow.readArgs env args with
        | none => simp only [compileRegion, hblock, hterm, hargs, caughtNames]
        | some values =>
          simp only [compileRegion, hblock, hterm, hargs, caughtNames, ih]
      | acquire operation request release target args =>
        cases hcont : performCont alphabet flow ⟨fuel + 1, block, env, tape⟩ with
        | none => simp only [compileRegion, hblock, hterm, hcont, caughtNames]
        | some triple => simp only [compileRegion, hblock, hterm, hcont, caughtNames]
      | leave value =>
        cases hval : env[value.index]? with
        | none => simp only [compileRegion, hblock, hterm, hval, caughtNames]
        | some v => simp only [compileRegion, hblock, hterm, hval, caughtNames]

/-- What a `Prim.suspend` thunk returns. P2 and P3 share the constructor and
split on the point: at a `performCatch` point with fuel to spend it is the
answer *as a primitive*, so the machine's `armE` sees a real `Cause`
(`internal/effect.ts:3417-3420`); everywhere else it is the suspension itself,
so the step is a fixed point and the frontier stays live (DB-04). -/
def regionSuspendBody {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) (point : Config) : Code :=
  match catchCont alphabet flow point with
  | none => Effect4.Prim.suspend point
  | some _ =>
    match point.fuel with
    | 0 => Effect4.Prim.suspend point
    | _ + 1 =>
      match oracle.answer point with
      | .ok value => Effect4.Prim.success value
      | .error error => Effect4.Prim.failure (Effect4.Cause.fail error)

/-- At a frontier point the suspension returns itself. -/
theorem regionSuspendBody_frontier {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (point : Config)
    (h : catchCont alphabet flow point = none) :
    regionSuspendBody alphabet flow oracle point = Effect4.Prim.suspend point := by
  simp only [regionSuspendBody, h]

/-- At a `performCatch` point with fuel to spend the suspension returns the
answer as a primitive, so a failing answer becomes a machine-level `Cause`. -/
theorem regionSuspendBody_catch {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (fuel : Nat) (block : BlockId)
    (env : Effect4.Flow.Env) (tape : Effect4.Flow.Tape) (onError : BlockId)
    (errorEnv : Effect4.Flow.Env)
    (h : catchCont alphabet flow ⟨fuel + 1, block, env, tape⟩ = some (onError, errorEnv)) :
    regionSuspendBody alphabet flow oracle ⟨fuel + 1, block, env, tape⟩ =
      (match oracle.answer ⟨fuel + 1, block, env, tape⟩ with
        | .ok value => Effect4.Prim.success value
        | .error error => Effect4.Prim.failure (Effect4.Cause.fail error)) := by
  simp only [regionSuspendBody, h]

/-- At a point whose source fuel is spent the suspension returns itself, whether
or not the block is a `performCatch`. -/
theorem regionSuspendBody_zero {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (point : Config) (h : point.fuel = 0) :
    regionSuspendBody alphabet flow oracle point = Effect4.Prim.suspend point := by
  cases hcatch : catchCont alphabet flow point with
  | none => simp only [regionSuspendBody, hcatch]
  | some pair => simp only [regionSuspendBody, hcatch, h]

/-- A suspension whose body is itself is a step fixed point that writes no
event. rc.112 has no opcode here: the runner has simply not reached the block.
census: op.Suspend -/
theorem step_suspend_fixed (interp : Table) (point : Config) (stack : List Code) (flag : Bool)
    (h : interp.suspendBody point = Effect4.Prim.suspend point) :
    (Effect4.FrameFiber.mk (Effect4.Prim.suspend point) stack flag none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (Effect4.Prim.suspend point) stack flag none false), []) := by
  show (Effect4.FrameStep.running
      (Effect4.FrameFiber.mk (interp.suspendBody point) stack flag none false), []) = _
  rw [h]

/-- So the bounded runner answers `FrameStep.running` at *every* fuel, with an
empty trace: a live frontier, never an exit (`docs/DESIGN-BASIS.md` DB-04).
census: op.Suspend -/
theorem run_suspend_fixed (interp : Table) (point : Config) (stack : List Code) (flag : Bool)
    (h : interp.suspendBody point = Effect4.Prim.suspend point) :
    forall fuel,
      Effect4.FrameFiber.run interp fuel
          (Effect4.FrameFiber.mk (Effect4.Prim.suspend point) stack flag none false) =
        (Effect4.FrameStep.running
          (Effect4.FrameFiber.mk (Effect4.Prim.suspend point) stack flag none false), []) := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ n ih =>
    rw [Effect4.FrameFiber.run_succ_running interp _ _ n _
      (step_suspend_fixed interp point stack flag h), ih]
    rfl

/-- The externally supplied meaning of every name. `contA` and `contE` are
computed from the flow — a name is a point, and the flow says what happens
there — and only the service's answers, the release outcomes and the
registrations come from the oracle.

Three fields carry the spike's repairs.

* `finalizerExit` is **constantly `Exit.success ()`** (P1). A registered release
  reports its outcome to its region's *scope*, never to the caller-side
  composite `Exit.restoreAfterFinalizer`, so no release's failure is ever fed
  into the exit the next release observes
  (`internal/effect.ts:3815-3827`; `Effect4.ScopeMachine.request_uses_original`).
  The whole close is `closeExit`, applied once, by the region's scope frame.
* `suspendBody` is the identity into `Prim.suspend` at every frontier point
  (P2), so `FrameFiber.run` stays `FrameStep.running` for ever and writes no
  event; and at a `performCatch` point it is the answer as a *primitive*, so the
  machine's `armE` sees a real `Cause` (P3).
* `contE` routes a `caught` name to the `performCatch`'s failure successor and a
  `close` name to the region's scope close, appending the closing reasons to the
  body's — concatenation, as `Exit.asVoidAll` concatenates
  (`internal/effect.ts:2025-2038`), never `Cause.combine`, which dedups
  (`:242-258`). -/
def regionInterp {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) : Table where
  -- No `asyncFinalizer` frame is ever emitted by the compile, so the cancel arm is never
  -- consulted; the honest filler re-fails with the passing cause.
  cancelThenFail := fun _ cause => Effect4.Prim.failure cause
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
        | none => Effect4.Prim.suspend point
    | RegionName.regionCont region point =>
      match closeExit oracle (oracle.registrations point) with
      | Effect4.Exit.failure closing => Effect4.Prim.failure closing
      | Effect4.Exit.success _ =>
        match flow.row? ⟨region⟩ with
        | some row =>
          compileRegion alphabet flow (point.fuel - 1) row.continue_ [value] point.tape
        | none => Effect4.Prim.suspend point
    -- The value arm of a `caught`, `close` or `fin` name is never demanded: the
    -- first two are cause names and the third is an `onExit` finalizer.
    | RegionName.caught point => Effect4.Prim.suspend point
    | RegionName.close _ point => Effect4.Prim.suspend point
    | RegionName.fin _ point => Effect4.Prim.suspend point
  contE := fun name cause =>
    match name with
    | RegionName.caught point =>
      match catchCont alphabet flow point, (failuresOfCause cause).head? with
      | some (onError, errorEnv), some error =>
        compileRegion alphabet flow (point.fuel - 1) onError (errorEnv ++ [error]) point.tape
      | _, _ => Effect4.Prim.failure cause
    | RegionName.close _ point =>
      match closeExit oracle (oracle.registrations point) with
      | Effect4.Exit.success _ => Effect4.Prim.failure cause
      | Effect4.Exit.failure closing =>
        Effect4.Prim.failure ⟨cause.reasons ++ closing.reasons⟩
    | _ => Effect4.Prim.failure cause
  syncValue := fun point =>
    match oracle.answer point with
    | .ok value => value
    | .error _ => Val.unit
  finalizerExit := fun _ _ => Effect4.Exit.success ()
  suspendBody := regionSuspendBody alphabet flow oracle
  reifyExit := fun _ => Val.unit
  iterNext := fun _ _ => ([], Effect4.IterStep.done Val.unit)
  loopTest := fun _ _ => false
  loopBody := fun name _ => Effect4.Prim.suspend name.point
  loopStep := fun _ value => value
  loopDone := fun _ => Val.unit
  notImplemented := ()

/-- **P1's premise, discharged.** Every finalizer of a compiled region run
succeeds, because a registered release reports to its region's scope and not to
the caller-side composite. This is what removes the `hfin` restriction from
`unwind_failure` and `close_success` on every compiled run, and it is the
`E4-TARGET-CE-019` repair in one line: no release's failure can reach the exit
another release observes. rc.112: `internal/effect.ts:3815-3827`.
census: scope.close-sequential -/
theorem regionInterp_finalizerExit {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (name : RegionName) (exit : Res) :
    (regionInterp alphabet flow oracle).finalizerExit name exit = Effect4.Exit.success () := rfl

/-- **P2's fixed point.** A frontier residual steps to itself and writes no
event, so `FrameFiber.run` answers `FrameStep.running` at every fuel: a live
frontier, never an exit (`docs/DESIGN-BASIS.md` DB-04). rc.112 has no opcode
here at all — the runner simply has not reached the block.
census: op.Suspend -/
theorem regionInterp_suspend_fixed {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (point : Config)
    (hfrontier : catchCont alphabet flow point = none) (stack : List Code)
    (flag : Bool) :
    (Effect4.FrameFiber.mk (Effect4.Prim.suspend point) stack flag none false).step
        (regionInterp alphabet flow oracle) =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (Effect4.Prim.suspend point) stack flag none false), []) := by
  exact step_suspend_fixed (regionInterp alphabet flow oracle) point stack flag
    (regionSuspendBody_frontier alphabet flow oracle point hfrontier)

/-- **P2, at the top of a run.** A configuration whose source fuel is spent
compiles to a suspension, and the machine stays on it for ever, writing nothing:
`FrameStep.running` at every machine fuel. That is a live frontier under
`docs/DESIGN-BASIS.md` DB-04 and not an exit, which is exactly what
`E4-TARGET-CE-020` demanded and what the old `Prim.failure Cause.empty` denied
(its `Exit.toOutcome` was `.interrupted`). census: op.Suspend -/
theorem compileAt_zero_fuel_live {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (block : BlockId)
    (env : Effect4.Flow.Env) (tape : Effect4.Flow.Tape) (fuel : Nat) :
    Effect4.FrameFiber.run (regionInterp alphabet flow oracle) fuel
        (Effect4.FrameFiber.start (compileAt alphabet flow ⟨0, block, env, tape⟩)) =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.start (compileAt alphabet flow ⟨0, block, env, tape⟩)), []) :=
  run_suspend_fixed (regionInterp alphabet flow oracle) ⟨0, block, env, tape⟩ [] true
    (regionSuspendBody_zero alphabet flow oracle ⟨0, block, env, tape⟩ rfl) fuel

/-- The oracle of a service that does not read or write its own state: the
answer at a point is what the service returns for the operation that point
performs. -/
def statelessAnswer {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (answerOf : alphabet.Op -> Val -> Except Val Val) (point : Config) : Except Val Val :=
  match performOp alphabet flow point with
  | some (op, request) => answerOf op request
  | none => .ok Val.unit

/-- The release outcome of the `acquire` at a point, statelessly: the release
operation applied to the resource the `acquire` produced. -/
def statelessRelease {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (answerOf : alphabet.Op -> Val -> Except Val Val) (point : Config) : Except Val Val :=
  match performOp alphabet flow point, releaseOp alphabet flow point with
  | some (op, request), some releaser =>
    match answerOf op request with
    | .ok resource => answerOf releaser resource
    | .error error => .error error
  | _, _ => .ok Val.unit

/-- The oracle of a service that does not read or write its own state. This is
the `stateless` hypothesis of `Effect4.Flow.closeFrame_failure_closeResult`, in
oracle form; P1's `registrations` field is computed by `closeWalk`. -/
def statelessOracle {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (answerOf : alphabet.Op -> Val -> Except Val Val) : RegionOracle where
  answer := statelessAnswer alphabet flow answerOf
  release := statelessRelease alphabet flow answerOf
  registrations := regionRegistrations alphabet flow (statelessAnswer alphabet flow answerOf)

/-- The machine fuel a region run needs, re-derived after P1. The runner spends
one unit per block, and a block costs the machine at most four steps:

* `jump`, `choose` — nothing, the compile recurses;
* `perform` — two (push the `OnSuccess` frame; run the `Sync` and pop it);
* `performCatch` — three (push the `OnSuccessAndFailure` frame; run the
  `Suspend`; pop and answer);
* `acquire` — three (the two above, then push the release's `OnExit` frame),
  plus the one step that pops that frame at the close;
* `enter` — one (push the region's one scope frame), plus the one step in which
  that frame answers at the close;
* `ret`, and a `leave` that empties the stack — one.

P1 did not lower the constant: the release frames stay, because they are what
writes the `finalizer` row rc.112's release lambda writes
(`internal/effect.ts:3971-3987`). What P1 removed is the *nesting*, not the
frame count. -/
def regionBound (runnerFuel : Nat) : Nat := 4 * runnerFuel + 1

/-! ## The general theorem, stated

T5 and T6 of `docs/research/2026-09-03-deep-flow-to-frames.md` §2.3, as `Prop`s
so that the shapes elaborate against the built library and the instances below
are instances *of them*. `RegionOracleAgrees` is the exact remaining obligation:
the agreement between the oracle and the runner along one run. Its first two
clauses are the ordinary answer agreement `hOracle` of the flow note; the third
is the missing induction — that `oracle.registrations` is the runner's
`Frame.releases` at the moment the frame closes. -/

/-- The oracle answers what the service answers, and its `registrations` field
is the runner's `Frame.releases`. The third clause is what a proof of
`RegionsSimulate` still owes; `closeWalk` computes a candidate for it and
`statelessOracle` installs that candidate. -/
structure RegionOracleAgrees {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (service : Effect4.Flow.RegionService alphabet Id)
    (answerOf : alphabet.Op -> Val -> Except Val Val) (oracle : RegionOracle) : Prop where
  /-- The service is stateless on this alphabet. -/
  handle : forall op request, service.handle op request = answerOf op request
  /-- The oracle answers a point with the service's answer for the operation
  that point performs. -/
  answer : forall point, oracle.answer point = statelessAnswer alphabet flow answerOf point
  /-- The oracle's release outcome is the service's answer to the release
  operation on the acquired resource. -/
  release : forall point, oracle.release point = statelessRelease alphabet flow answerOf point
  /-- **The missing induction.** The registrations the oracle reports for a
  region are the releases the runner's `Frame` holds when that frame closes, in
  `Scope.closeOrder`. -/
  registrations : forall point,
    oracle.registrations point =
      regionRegistrations alphabet flow (statelessAnswer alphabet flow answerOf) point

/-- `statelessOracle` satisfies three of the four clauses by construction; the
fourth is the service's own statelessness. So the only content of
`RegionOracleAgrees` at this oracle is the `registrations` *definition* being
right, which is the obligation `closeWalk` discharges for the instances and the
general theorem still owes. census: scope.close-sequential -/
theorem statelessOracle_agrees {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (service : Effect4.Flow.RegionService alphabet Id)
    (answerOf : alphabet.Op -> Val -> Except Val Val)
    (hservice : forall op request, service.handle op request = answerOf op request) :
    RegionOracleAgrees alphabet flow service answerOf (statelessOracle alphabet flow answerOf) :=
  { handle := hservice, answer := fun _ => rfl, release := fun _ => rfl,
    registrations := fun _ => rfl }

/-- **T5, the trace equation.** The frame machine's projected service-level
trace equals the runner's log under the mask that keeps `finalizer` and `done`.
Stated as a `Prop` because its proof is packet P4's remaining obligation; the
instances in `Effect4Test/Semantics/RegionSimulationContract.lean` are the
cases that are closed. -/
def RegionsSimulate {Ty : Type} [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (flow : CheckedRegionFlow alphabet)
    (service : Effect4.Flow.RegionService alphabet Id)
    (answerOf : alphabet.Op -> Val -> Except Val Val)
    (nameOf : alphabet.Op -> String) (oracle : RegionOracle)
    (tape : Effect4.Flow.Tape) (input : Val) (fuel' fuel : Nat) : Prop :=
  RegionOracleAgrees alphabet flow.flow service answerOf oracle ->
  regionBound fuel' <= fuel ->
  traceOfRun (Effect4.FrameFiber.run (regionInterp alphabet flow.flow oracle) fuel
      (Effect4.FrameFiber.start
        (compileAt alphabet flow.flow ⟨fuel', flow.flow.entry, [input], tape⟩))).2
    = Effects.Trace.project finalizerAndOutcomeMask
        (((Effect4.Flow.runRegions fuel' flow service nameOf tape input).run []).2)

/-- **T6, the exit equation.** The exit the machine finishes with is the
runner's result, with the *merged* failure list `runRegionsCause` keeps rather
than the head `runRegions` projects. `causeOfFailures` is the section
`failuresOfCause` retracts, and `toOutcome_combine` is why T5 is insensitive to
the merge while T6 is not. Stated as a `Prop` for the same reason as T5. -/
def RegionsSimulateExit {Ty : Type} [DecidableEq Ty] (alphabet : FlowAlphabet Ty)
    (flow : CheckedRegionFlow alphabet)
    (service : Effect4.Flow.RegionService alphabet Id)
    (answerOf : alphabet.Op -> Val -> Except Val Val)
    (nameOf : alphabet.Op -> String) (oracle : RegionOracle)
    (tape : Effect4.Flow.Tape) (input : Val) (fuel' fuel : Nat) : Prop :=
  RegionOracleAgrees alphabet flow.flow service answerOf oracle ->
  regionBound fuel' <= fuel ->
  (Effect4.FrameFiber.run (regionInterp alphabet flow.flow oracle) fuel
      (Effect4.FrameFiber.start
        (compileAt alphabet flow.flow ⟨fuel', flow.flow.entry, [input], tape⟩))).1
    = Effect4.FrameStep.finished
        (match ((Effect4.Flow.runRegionsCause fuel' flow service nameOf tape input).run []).1 with
          | ((.done value, _), _) => Effect4.Exit.success value
          | ((_, _), failures) => Effect4.Exit.failure (causeOfFailures failures))

/-! ## The retraction and the wire projection -/

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

/-- The same, for the *concatenation* P1's close arm uses. A region's close
appends the closing reasons to the body's, so the wire still reads the body's
first failure — and, unlike `Cause.combine`, duplicates survive
(`Exit.asVoidAll_keeps_duplicates`, `E4-FLOW-CE-021`).
census: scope.exit-as-void-all -/
theorem toOutcome_append (self closing : Err) (error : Val)
    (annotations : Effect4.ReasonAnnotations Unit)
    (rest : List (Effect4.Reason Val Unit Unit Unit))
    (h : self.reasons = Effect4.Reason.fail error annotations :: rest) :
    Effect4.Exit.toOutcome (β := Val) id id (fun _ => Val.unit)
        (Effect4.Exit.failure ⟨self.reasons ++ closing.reasons⟩) =
      Outcome.failure error := by
  simp only [Effect4.Exit.toOutcome, h, List.cons_append]
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

/-- The finalizers a *closing exit* runs before the frame that answers it: the
`onExit` frames above it. -/
def closeNames : List Code -> List RegionName
  | Effect4.Prim.onExit _ name _ :: rest => name :: closeNames rest
  | Effect4.Prim.setInterruptible _ :: rest => closeNames rest
  | _ => []

/-- The frames a *closing exit* runs before the answering frame, and the shapes
that segment may take: `onExit` frames and the mask frames their `ensure`
pushes, and nothing else. -/
def closeable : List Code -> Bool
  | [] => true
  | Effect4.Prim.onExit _ _ flag :: rest => !flag && closeable rest
  | Effect4.Prim.setInterruptible flag :: rest => flag && closeable rest
  | _ :: _ => false

/-! ## The finalizer half of the machine

Three theorems, all general: a failing exit propagating through a whole
fragment stack, a failing exit propagating to the frame that answers it, and a
closing value propagating to the frame that answers it. They are what the
general theorem is assembled from, and they are stated over an arbitrary stack
rather than over a compiled one, so nothing about `compileRegion` is assumed.

Their premise is now *per name* rather than global, which is what P1's shape
needs and what makes `regionInterp_finalizerExit` discharge it outright. -/

/-- The wire outcome of an exit, at this module's carriers. -/
def outcomeOf (exit : Res) : Outcome Val :=
  Effect4.Exit.toOutcome id id (fun _ => Val.unit) exit

/-- The service-level row a named finalizer writes against an exit. -/
def finalizerRow (exit : Res) (name : RegionName) : Effect4.Trace.Event :=
  Effects.Trace.Event.finalizer name.regionOf (outcomeOf exit)

/-- Every finalizer of `names` leaves the exit it observed untouched. -/
def FinalizersVoid (interp : Table) (names : List RegionName) : Prop :=
  forall name, name ∈ names ->
    forall exit, interp.finalizerExit name exit = Effect4.Exit.success ()

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
  -- The passed frame pushes nothing (`hens` keeps the empty scratch stack), so the unfused
  -- traversal continues exactly where the fused one did (`popFrom_pass_no_push`).
  have hpush : (frame.ensure (Effect4.FrameFiber.mk current [] flagIn none false)).fst.stack =
      (Effect4.FrameFiber.mk current [] flagIn none false).stack := by
    rw [hens]
  have hcont := Effect4.FrameFiber.popFrom_pass_no_push demand skip frame stack
    (Effect4.FrameFiber.mk current [] flagIn none false) rfl hpush
  refine ⟨?_, ?_, ?_⟩
  · rw [Effect4.FrameFiber.popFrom_continue_answer demand skip frame stack _ (Or.inl hnone),
      hcont, hens]
  · rw [Effect4.FrameFiber.popFrom_continue_fiber demand skip frame stack _ (Or.inl hnone),
      hcont, hens]
  · rw [Effect4.FrameFiber.popFrom_continue_events demand skip frame stack _ (Or.inl hnone),
      hcont, hens]
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

/-- The `onSuccess` frame a fragment opens answers the closing value with its
named continuation, under the stack that was below it. -/
theorem step_onSuccess_answers (interp : Table) (value : Val) (body : Code)
    (name : RegionName) (rest : List Code) :
    (Effect4.FrameFiber.mk (Effect4.Prim.success value)
        (Effect4.Prim.onSuccess body name :: rest) true none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contA name value) rest true none false),
        [Effect4.FrameEvent.popped (Effect4.Prim.onSuccess body name)]) := rfl

/-- The scope frame a region opens answers the closing value with its value
name. rc.112: the value arm of `Effect.scoped`'s frame
(`internal/effect.ts:3938-3947`). census: op.OnSuccessAndFailure -/
theorem step_onSuccessAndFailure_answers (interp : Table) (value : Val) (body : Code)
    (name causeName : RegionName) (rest : List Code) :
    (Effect4.FrameFiber.mk (Effect4.Prim.success value)
        (Effect4.Prim.onSuccessAndFailure body name causeName :: rest) true none false).step
        interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contA name value) rest true none false),
        [Effect4.FrameEvent.popped (Effect4.Prim.onSuccessAndFailure body name causeName)]) := rfl

/-- The same frame answers a failing exit with its cause name — the region's
scope close. rc.112: `internal/effect.ts:3450-3460`.
census: op.OnSuccessAndFailure -/
theorem step_onSuccessAndFailure_answers_cause (interp : Table) (cause : Err) (body : Code)
    (name causeName : RegionName) (rest : List Code) :
    (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
        (Effect4.Prim.onSuccessAndFailure body name causeName :: rest) true none false).step
        interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contE causeName cause) rest true none false),
        [Effect4.FrameEvent.popped (Effect4.Prim.onSuccessAndFailure body name causeName)]) := rfl

/-- A successful finalizer restores the exit it observed, on the nose. -/
private theorem restore_success (exit : Res) :
    Effect4.Exit.restoreAfterFinalizer exit (Effect4.Exit.success ()) = exit := by
  cases exit <;> rfl

/-- **The unwind theorem.** A failing exit propagating through a fragment stack
runs exactly the finalizers that stack names, in pop order, every one of them
against the *same* exit — which is the runner's `closeReleases`, whose
`finalizer` row carries the closing exit for every release of one close — and
then yields that exit.

The premise is now per name (`FinalizersVoid`) rather than a global `hfin`.
After P1 it is discharged outright for every compiled run by
`regionInterp_finalizerExit`, which is why `unwind_failure_region` below carries
no restriction at all: that is `E4-TARGET-CE-019`'s repair column.
census: scope.close-sequential -/
theorem unwind_failure (interp : Table) (cause : Err) :
    forall (stack : List Code), unwindable stack = true ->
      FinalizersVoid interp (unwindNames stack) ->
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
    intro _ _ fuel hfuel
    have hnames : (unwindNames ([] : List Code)).length = 0 := rfl
    rw [hnames] at hfuel
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
    have hk' : fuel = k + 1 := by omega
    subst hk'
    rw [Effect4.FrameFiber.run_succ_finished interp _ k _ _ (step_empty_failure interp cause)]
    exact ⟨rfl, rfl⟩
  | cons frame rest ih =>
    intro hstack hfin fuel hfuel
    cases frame
    case onSuccess body name =>
      have hrest : unwindable rest = true := by
        simpa [unwindable] using hstack
      have hfinRest : FinalizersVoid interp (unwindNames rest) := hfin
      have hnames : unwindNames (Effect4.Prim.onSuccess body name :: rest) = unwindNames rest := rfl
      rw [hnames] at hfuel ⊢
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
      have hk' : fuel = k + (unwindNames rest).length + 1 := by omega
      subst hk'
      obtain ⟨hf, hs⟩ := run_congr interp _ _ (k + (unwindNames rest).length)
        (step_onSuccess_passed interp cause body name rest)
      rw [hf, hs]
      exact ih hrest hfinRest _ (by omega)
    case setInterruptible flag =>
      have hflag : flag = true := by
        cases flag with
        | true => rfl
        | false => simp [unwindable] at hstack
      subst hflag
      have hrest : unwindable rest = true := by
        simpa [unwindable] using hstack
      have hfinRest : FinalizersVoid interp (unwindNames rest) := hfin
      have hnames : unwindNames (Effect4.Prim.setInterruptible true :: rest) = unwindNames rest :=
        rfl
      rw [hnames] at hfuel ⊢
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hfuel
      have hk' : fuel = k + (unwindNames rest).length + 1 := by omega
      subst hk'
      obtain ⟨hf, hs⟩ := run_congr interp _ _ (k + (unwindNames rest).length)
        (step_mask_passed interp cause rest true)
      rw [hf, hs]
      exact ih hrest hfinRest _ (by omega)
    case onExit body name flag =>
      have hflag : flag = false := by
        cases flag with
        | false => rfl
        | true => simp [unwindable] at hstack
      subst hflag
      have hrest : unwindable rest = true := by
        simpa [unwindable] using hstack
      have hfinHere : forall exit, interp.finalizerExit name exit = Effect4.Exit.success () :=
        hfin name (by
          show name ∈ name :: unwindNames rest
          exact List.Mem.head _)
      have hfinRest : FinalizersVoid interp (unwindNames rest) := by
        intro other hother
        exact hfin other (by
          show other ∈ name :: unwindNames rest
          exact List.Mem.tail _ hother)
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
        rw [step_onExit_failure interp cause body name rest, hfinHere]
        rfl
      rw [Effect4.FrameFiber.run_succ_running interp _ _
        (k + (unwindNames rest).length + 1) _ hstep]
      obtain ⟨hf, hs⟩ := run_congr interp
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          (Effect4.Prim.setInterruptible true :: rest) false none false)
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) rest true none false)
        (k + (unwindNames rest).length) (step_mask_passed interp cause rest false)
      obtain ⟨hrf, hrs⟩ := ih hrest hfinRest (k + (unwindNames rest).length + 1) (by omega)
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

/-- **The close theorem, over any answering frame.** A closing value runs the
`onExit` frames above the frame that answers it, latest registered first, every
one of them against the closing exit, and then that frame answers with its named
continuation under the stack that was below it.

`hanswer` is what pins the answering frame; both `Prim.onSuccess` and
`Prim.onSuccessAndFailure` satisfy it by `rfl`, which is what lets the region's
one scope frame (P1) reuse this proof unchanged.
census: scope.close-sequential -/
theorem close_success_of (interp : Table) (value : Val) (answering : Code) (name : RegionName)
    (rest : List Code)
    (hanswer : (Effect4.FrameFiber.mk (Effect4.Prim.success value)
        (answering :: rest) true none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contA name value) rest true none false),
        [Effect4.FrameEvent.popped answering])) :
    forall (frames : List Code), closeable frames = true ->
      FinalizersVoid interp (closeNames frames) ->
      (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ answering :: rest) true none false)).fst =
        Effect4.FrameStep.running
          (Effect4.FrameFiber.mk (interp.contA name value) rest true none false) /\
      traceOfRun (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ answering :: rest) true none false)).snd =
        (closeNames frames).map (finalizerRow (Effect4.Exit.success value)) := by
  intro frames
  induction frames with
  | nil =>
    intro _ _
    rw [show (closeNames ([] : List Code)).length + 1 = 0 + 1 from rfl,
      show ([] : List Code) ++ answering :: rest = answering :: rest from rfl,
      Effect4.FrameFiber.run_succ_running interp _ _ 0 _ hanswer]
    exact ⟨rfl, rfl⟩
  | cons frame more ih =>
    intro hframes hfin
    cases frame
    case setInterruptible flag =>
      have hflag : flag = true := by
        cases flag with
        | true => rfl
        | false => simp [closeable] at hframes
      subst hflag
      have hmore : closeable more = true := by
        simpa [closeable] using hframes
      have hfinMore : FinalizersVoid interp (closeNames more) := hfin
      have hnames : closeNames (Effect4.Prim.setInterruptible true :: more) = closeNames more := rfl
      rw [hnames]
      obtain ⟨hf, hs⟩ := run_congr interp _ _ ((closeNames more).length)
        (step_mask_passed_success interp value (more ++ answering :: rest) true)
      show (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
            (Effect4.FrameFiber.mk (Effect4.Prim.success value)
              (Effect4.Prim.setInterruptible true ::
                (more ++ answering :: rest)) true none false)).fst =
            Effect4.FrameStep.running
              (Effect4.FrameFiber.mk (interp.contA name value) rest true none false) /\
          traceOfRun (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
            (Effect4.FrameFiber.mk (Effect4.Prim.success value)
              (Effect4.Prim.setInterruptible true ::
                (more ++ answering :: rest)) true none false)).snd =
            (closeNames more).map (finalizerRow (Effect4.Exit.success value))
      rw [hf, hs]
      exact ih hmore hfinMore
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
      have hfinHere : forall exit, interp.finalizerExit finName exit = Effect4.Exit.success () :=
        hfin finName (by
          show finName ∈ finName :: closeNames more
          exact List.Mem.head _)
      have hfinMore : FinalizersVoid interp (closeNames more) := by
        intro other hother
        exact hfin other (by
          show other ∈ finName :: closeNames more
          exact List.Mem.tail _ hother)
      rw [hnames]
      rw [show (finName :: closeNames more).length + 1 = (closeNames more).length + 1 + 1 by
        simp [List.length_cons]]
      have hstep : (Effect4.FrameFiber.mk (Effect4.Prim.success value)
          ((Effect4.Prim.onExit finBody finName false :: more) ++ answering :: rest)
            true none false).step interp =
          (Effect4.FrameStep.running
            (Effect4.FrameFiber.mk (Effect4.Prim.success value)
              (Effect4.Prim.setInterruptible true ::
                (more ++ answering :: rest)) false none false),
            [Effect4.FrameEvent.popped (Effect4.Prim.onExit finBody finName false),
              Effect4.FrameEvent.ranContAll (Effect4.Prim.onExit finBody finName false),
              Effect4.FrameEvent.ranFinalizer finName (Effect4.Exit.success value)]) := by
        rw [show (Effect4.Prim.onExit finBody finName false :: more) ++ answering :: rest =
            Effect4.Prim.onExit finBody finName false :: (more ++ answering :: rest) from rfl,
          step_onExit_success interp value finBody finName (more ++ answering :: rest), hfinHere]
        rfl
      rw [Effect4.FrameFiber.run_succ_running interp _ _
        ((closeNames more).length + 1) _ hstep]
      obtain ⟨hf, hs⟩ := run_congr interp _ _ ((closeNames more).length)
        (step_mask_passed_success interp value (more ++ answering :: rest) false)
      obtain ⟨hrf, hrs⟩ := ih hmore hfinMore
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
                  (more ++ answering :: rest)) false none false)).snd) =
          _ from hs, hrs]
        rfl
    all_goals simp [closeable] at hframes

/-- **The close theorem** at an `onSuccess` answering frame — the shape fence C
had before P1, restated with the per-name premise. -/
theorem close_success (interp : Table) (value : Val) (body : Code) (name : RegionName)
    (rest : List Code) :
    forall (frames : List Code), closeable frames = true ->
      FinalizersVoid interp (closeNames frames) ->
      (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ Effect4.Prim.onSuccess body name :: rest) true none false)).fst =
        Effect4.FrameStep.running
          (Effect4.FrameFiber.mk (interp.contA name value) rest true none false) /\
      traceOfRun (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ Effect4.Prim.onSuccess body name :: rest) true none false)).snd =
        (closeNames frames).map (finalizerRow (Effect4.Exit.success value)) :=
  close_success_of interp value (Effect4.Prim.onSuccess body name) name rest
    (step_onSuccess_answers interp value body name rest)

/-- **The close theorem at a region's scope frame.** Exactly `close_success`,
with rc.112's `Effect.scoped` frame in place of the plain `OnSuccess`: every
release of the one scope observes the same closing exit, and then the scope
frame answers. census: scope.close-sequential -/
theorem close_success_region (interp : Table) (value : Val) (body : Code)
    (name causeName : RegionName) (rest : List Code) :
    forall (frames : List Code), closeable frames = true ->
      FinalizersVoid interp (closeNames frames) ->
      (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
            true none false)).fst =
        Effect4.FrameStep.running
          (Effect4.FrameFiber.mk (interp.contA name value) rest true none false) /\
      traceOfRun (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.success value)
            (frames ++ Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
            true none false)).snd =
        (closeNames frames).map (finalizerRow (Effect4.Exit.success value)) :=
  close_success_of interp value (Effect4.Prim.onSuccessAndFailure body name causeName) name rest
    (step_onSuccessAndFailure_answers interp value body name causeName rest)

/-- **The unwind theorem up to the frame that answers.** A failing exit runs the
`onExit` frames above the first frame declaring a cause arm, every one against
the *same* exit, and then that frame answers with its named cause continuation.
This is the failure-side dual of `close_success_of`, and it is what a region's
scope frame needs: on a failing body the releases still write their rows and the
scope still merges once. census: scope.close-sequential -/
theorem unwind_to_frame (interp : Table) (cause : Err) (answering : Code)
    (causeName : RegionName) (rest : List Code)
    (hanswer : (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
        (answering :: rest) true none false).step interp =
      (Effect4.FrameStep.running
        (Effect4.FrameFiber.mk (interp.contE causeName cause) rest true none false),
        [Effect4.FrameEvent.popped answering])) :
    forall (frames : List Code), closeable frames = true ->
      FinalizersVoid interp (closeNames frames) ->
      (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
            (frames ++ answering :: rest) true none false)).fst =
        Effect4.FrameStep.running
          (Effect4.FrameFiber.mk (interp.contE causeName cause) rest true none false) /\
      traceOfRun (Effect4.FrameFiber.run interp ((closeNames frames).length + 1)
          (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
            (frames ++ answering :: rest) true none false)).snd =
        (closeNames frames).map (finalizerRow (Effect4.Exit.failure cause)) := by
  intro frames
  induction frames with
  | nil =>
    intro _ _
    rw [show (closeNames ([] : List Code)).length + 1 = 0 + 1 from rfl,
      show ([] : List Code) ++ answering :: rest = answering :: rest from rfl,
      Effect4.FrameFiber.run_succ_running interp _ _ 0 _ hanswer]
    exact ⟨rfl, rfl⟩
  | cons frame more ih =>
    intro hframes hfin
    cases frame
    case setInterruptible flag =>
      have hflag : flag = true := by
        cases flag with
        | true => rfl
        | false => simp [closeable] at hframes
      subst hflag
      have hmore : closeable more = true := by
        simpa [closeable] using hframes
      have hfinMore : FinalizersVoid interp (closeNames more) := hfin
      have hnames : closeNames (Effect4.Prim.setInterruptible true :: more) = closeNames more := rfl
      rw [hnames]
      obtain ⟨hf, hs⟩ := run_congr interp _ _ ((closeNames more).length)
        (step_mask_passed interp cause (more ++ answering :: rest) true)
      show (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
            (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
              (Effect4.Prim.setInterruptible true ::
                (more ++ answering :: rest)) true none false)).fst =
            Effect4.FrameStep.running
              (Effect4.FrameFiber.mk (interp.contE causeName cause) rest true none false) /\
          traceOfRun (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
            (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
              (Effect4.Prim.setInterruptible true ::
                (more ++ answering :: rest)) true none false)).snd =
            (closeNames more).map (finalizerRow (Effect4.Exit.failure cause))
      rw [hf, hs]
      exact ih hmore hfinMore
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
      have hfinHere : forall exit, interp.finalizerExit finName exit = Effect4.Exit.success () :=
        hfin finName (by
          show finName ∈ finName :: closeNames more
          exact List.Mem.head _)
      have hfinMore : FinalizersVoid interp (closeNames more) := by
        intro other hother
        exact hfin other (by
          show other ∈ finName :: closeNames more
          exact List.Mem.tail _ hother)
      rw [hnames]
      rw [show (finName :: closeNames more).length + 1 = (closeNames more).length + 1 + 1 by
        simp [List.length_cons]]
      have hstep : (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          ((Effect4.Prim.onExit finBody finName false :: more) ++ answering :: rest)
            true none false).step interp =
          (Effect4.FrameStep.running
            (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
              (Effect4.Prim.setInterruptible true ::
                (more ++ answering :: rest)) false none false),
            [Effect4.FrameEvent.popped (Effect4.Prim.onExit finBody finName false),
              Effect4.FrameEvent.ranContAll (Effect4.Prim.onExit finBody finName false),
              Effect4.FrameEvent.ranFinalizer finName (Effect4.Exit.failure cause)]) := by
        rw [show (Effect4.Prim.onExit finBody finName false :: more) ++ answering :: rest =
            Effect4.Prim.onExit finBody finName false :: (more ++ answering :: rest) from rfl,
          step_onExit_failure interp cause finBody finName (more ++ answering :: rest), hfinHere]
        rfl
      rw [Effect4.FrameFiber.run_succ_running interp _ _
        ((closeNames more).length + 1) _ hstep]
      obtain ⟨hf, hs⟩ := run_congr interp _ _ ((closeNames more).length)
        (step_mask_passed interp cause (more ++ answering :: rest) false)
      obtain ⟨hrf, hrs⟩ := ih hmore hfinMore
      refine ⟨?_, ?_⟩
      · show (Effect4.FrameFiber.run interp ((closeNames more).length + 1) _).fst = _
        rw [hf, hrf]
      · show traceOfRun (_ ++ (Effect4.FrameFiber.run interp ((closeNames more).length + 1) _).snd)
          = _
        simp only [traceOfRun, Effect4.FrameEvent.traceOf, List.filterMap_append]
        rw [show (List.filterMap
            (Effect4.FrameEvent.toTrace RegionName.regionOf id id (fun _ => Val.unit))
            (Effect4.FrameFiber.run interp ((closeNames more).length + 1)
              (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
                (Effect4.Prim.setInterruptible true ::
                  (more ++ answering :: rest)) false none false)).snd) =
          _ from hs, hrs]
        rfl
    all_goals simp [closeable] at hframes

/-! ## The three theorems on a compiled run, with no premise at all

This is the concrete content of P1: for `regionInterp` the premise of all three
theorems above is `rfl`, so the failing-release restriction `E4-TARGET-CE-019`
attacked is gone rather than assumed away. -/

/-- `unwind_failure` on a compiled run, unrestricted.
census: scope.close-sequential -/
theorem unwind_failure_region {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) (cause : Err) (stack : List Code) (hstack : unwindable stack = true)
    (fuel : Nat) (hfuel : (unwindNames stack).length + 1 <= fuel) :
    (Effect4.FrameFiber.run (regionInterp alphabet flow oracle) fuel
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) stack true none false)).fst =
      Effect4.FrameStep.finished (Effect4.Exit.failure cause) /\
    traceOfRun (Effect4.FrameFiber.run (regionInterp alphabet flow oracle) fuel
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) stack true none false)).snd =
      (unwindNames stack).map (finalizerRow (Effect4.Exit.failure cause)) ++
        [Effects.Trace.Event.done (outcomeOf (Effect4.Exit.failure cause))] :=
  unwind_failure (regionInterp alphabet flow oracle) cause stack hstack
    (fun _ _ _ => rfl) fuel hfuel

/-- `close_success_region` on a compiled run, unrestricted: **every release of
one region's scope observes the same closing exit**, which is
`E4-TARGET-CE-019`'s and `E4-FLOW-CE-020`'s repair.
census: scope.close-sequential -/
theorem close_success_region_compiled {Ty : Type} (alphabet : FlowAlphabet Ty)
    (flow : RegionFlow Ty) (oracle : RegionOracle) (value : Val) (body : Code)
    (name causeName : RegionName) (rest frames : List Code)
    (hframes : closeable frames = true) :
    (Effect4.FrameFiber.run (regionInterp alphabet flow oracle) ((closeNames frames).length + 1)
        (Effect4.FrameFiber.mk (Effect4.Prim.success value)
          (frames ++ Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
          true none false)).fst =
      Effect4.FrameStep.running
        (Effect4.FrameFiber.mk ((regionInterp alphabet flow oracle).contA name value)
          rest true none false) /\
    traceOfRun (Effect4.FrameFiber.run (regionInterp alphabet flow oracle)
        ((closeNames frames).length + 1)
        (Effect4.FrameFiber.mk (Effect4.Prim.success value)
          (frames ++ Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
          true none false)).snd =
      (closeNames frames).map (finalizerRow (Effect4.Exit.success value)) :=
  close_success_region (regionInterp alphabet flow oracle) value body name causeName rest
    frames hframes (fun _ _ _ => rfl)

/-! ## P1 as a general law: one scope, N rows, one exit

The stack a region's registrations leave above its scope frame, and what the
close writes through it. This is the general statement `E4-TARGET-CE-019`
demanded: *every* release of the one scope observes the same closing exit,
whatever the other releases do, for every registration list. -/

/-- The release frames a region's registrations leave above its scope frame,
latest registered first — the order `Effect4.Flow.Frame.toScope_closeOrder`
proves for the runner. -/
def releaseFrames (region : Nat) (bodyOf : Config -> Code) : List Config -> List Code
  | [] => []
  | point :: rest =>
    Effect4.Prim.onExit (bodyOf point) (RegionName.fin region point) false ::
      releaseFrames region bodyOf rest

/-- Those frames name exactly the registrations. -/
theorem closeNames_releaseFrames (region : Nat) (bodyOf : Config -> Code)
    (points : List Config) :
    closeNames (releaseFrames region bodyOf points) = points.map (RegionName.fin region) := by
  induction points with
  | nil => rfl
  | cons point rest ih =>
    show RegionName.fin region point :: closeNames (releaseFrames region bodyOf rest) = _
    rw [ih, List.map_cons]

/-- And they are a closing segment. -/
theorem closeable_releaseFrames (region : Nat) (bodyOf : Config -> Code)
    (points : List Config) : closeable (releaseFrames region bodyOf points) = true := by
  induction points with
  | nil => rfl
  | cons point rest ih =>
    show (!false && closeable (releaseFrames region bodyOf rest)) = true
    rw [ih]
    rfl

/-- **P1, in general.** A region's close writes one `finalizer region` row per
registration, in `Scope.closeOrder`, and every one of them carries the *same*
closing exit — the exit the scope was closed with, never one another release
has already altered. rc.112: `internal/effect.ts:3815-3827` runs every finalizer
with the same `exit_` and combines the collected exits only after the loop.
census: scope.close-sequential -/
theorem region_close_rows {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) (value : Val) (region : Nat) (bodyOf : Config -> Code)
    (points : List Config) (body : Code) (name causeName : RegionName) (rest : List Code) :
    traceOfRun (Effect4.FrameFiber.run (regionInterp alphabet flow oracle) (points.length + 1)
        (Effect4.FrameFiber.mk (Effect4.Prim.success value)
          (releaseFrames region bodyOf points ++
            Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
          true none false)).snd =
      points.map (fun _ =>
        Effects.Trace.Event.finalizer region (outcomeOf (Effect4.Exit.success value))) := by
  have hnames := closeNames_releaseFrames region bodyOf points
  have hlen : (closeNames (releaseFrames region bodyOf points)).length = points.length := by
    rw [hnames, List.length_map]
  have hclose := close_success_region_compiled alphabet flow oracle value body name causeName rest
    (releaseFrames region bodyOf points) (closeable_releaseFrames region bodyOf points)
  rw [hlen] at hclose
  rw [hclose.2, hnames, List.map_map]
  rfl

/-- `unwind_to_frame` on a compiled run, unrestricted.
census: scope.close-sequential -/
theorem unwind_to_frame_region {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) (cause : Err) (body : Code) (name causeName : RegionName)
    (rest frames : List Code) (hframes : closeable frames = true) :
    (Effect4.FrameFiber.run (regionInterp alphabet flow oracle) ((closeNames frames).length + 1)
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          (frames ++ Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
          true none false)).fst =
      Effect4.FrameStep.running
        (Effect4.FrameFiber.mk ((regionInterp alphabet flow oracle).contE causeName cause)
          rest true none false) /\
    traceOfRun (Effect4.FrameFiber.run (regionInterp alphabet flow oracle)
        ((closeNames frames).length + 1)
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          (frames ++ Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
          true none false)).snd =
      (closeNames frames).map (finalizerRow (Effect4.Exit.failure cause)) :=
  unwind_to_frame (regionInterp alphabet flow oracle) cause
    (Effect4.Prim.onSuccessAndFailure body name causeName) causeName rest
    (step_onSuccessAndFailure_answers_cause (regionInterp alphabet flow oracle) cause body name
      causeName rest)
    frames hframes (fun _ _ _ => rfl)

/-- The failure side of `region_close_rows`: a failing body still writes one row
per registration, all carrying the failing exit, before the region's scope frame
merges once. census: scope.close-sequential -/
theorem region_unwind_rows {Ty : Type} (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (oracle : RegionOracle) (cause : Err) (region : Nat) (bodyOf : Config -> Code)
    (points : List Config) (body : Code) (name causeName : RegionName) (rest : List Code) :
    traceOfRun (Effect4.FrameFiber.run (regionInterp alphabet flow oracle) (points.length + 1)
        (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
          (releaseFrames region bodyOf points ++
            Effect4.Prim.onSuccessAndFailure body name causeName :: rest)
          true none false)).snd =
      points.map (fun _ =>
        Effects.Trace.Event.finalizer region (outcomeOf (Effect4.Exit.failure cause))) := by
  have hnames := closeNames_releaseFrames region bodyOf points
  have hlen : (closeNames (releaseFrames region bodyOf points)).length = points.length := by
    rw [hnames, List.length_map]
  have hunwind := unwind_to_frame_region alphabet flow oracle cause body name causeName rest
    (releaseFrames region bodyOf points) (closeable_releaseFrames region bodyOf points)
  rw [hlen] at hunwind
  rw [hunwind.2, hnames, List.map_map]
  rfl

end Effect4.RegionSimulation
