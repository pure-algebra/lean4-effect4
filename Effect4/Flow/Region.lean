import Effects.Flow.Region
import Effect4.Semantics.Runs
import Effect4.Runtime.Scope
import Effect4.Target.TypeScript.ScriptFlow

/-!
# Flow.Region

Owner: the executable face of an admitted region flow (plan packet P-T7).

A run keeps a stack of open regions. `enter` pushes one and logs `enter`;
`acquire` performs its operation and registers the release for the answer on
the innermost region; `leave` closes the innermost region with a value: it
logs `leave region (success value)`, runs the registered releases latest-first,
each logging `finalizer region (success value)` before its own `op`/`answer`
(or `failed`) rows, and continues at the region's `continue_` block with the
value; a release failure becomes the exit of everything enclosing. A failing
operation closes every open region innermost-first with `failure error` and
the run ends `failed`.

A run failure is a *merged* cause: the failures a run collected, in close
order, first failure first (`Failures`). A close keeps every failing release,
not only the first, which is what the reified rc.112 `Scope.closeResult`
does through `Exit.asVoidAll` and what the frame machine does through
`Cause.combine` (`Effect4/Semantics/Exit.lean`). The wire is unchanged: every
`leave`, `finalizer` and `done` row carries the *first* failure of the merged
cause, and `RunResult.failed` reports that same first failure. `runRegions`
projects it; `runRegionsCause` keeps the whole cause. `E4-FLOW-CE-019` records
that the host is checked on exactly this projection, and `E4-FLOW-CE-021` the
merge the host cannot see (a fallible release has no lowering,
`E4-TARGET-CE-012`).
-/

namespace Effect4.Flow

open Effects Effect4.Target.EffectV4
open Effects.Trace (Val Outcome)

/-- A service whose operations may fail: the aborting reading of an error. -/
structure RegionService (alphabet : FlowAlphabet Ty) (M : Type → Type) where
  handle : alphabet.Op → Val → M (Except Val Val)
  pure : alphabet.Op → Bool := fun _ => false

/-- A table service whose family operations may fail. -/
def tableRegionService [Monad M] (id : AlphabetId) (table : List OpSpec)
    (family : String → Val → M (Except Val Val)) (atom : String → Val → Val) :
    RegionService (tableAlphabet id table) M where
  handle op request :=
    match (OpSpec.at table op).kind with
    | .lit value => pure (.ok value)
    | .atom => pure (.ok (atom (OpSpec.at table op).name request))
    | .family => family (OpSpec.at table op).name request
  pure op :=
    match (OpSpec.at table op).kind with
    | .family => false
    | _ => true

/-- An open region: its identity and the releases registered so far, latest first. -/
structure Frame (alphabet : FlowAlphabet Ty) where
  region : RegionId
  releases : List (alphabet.Op × Val)

/-- A run failure, merged: the failures a run collected in close order, first
failure first. Non-empty exactly on a failing run; the wire keeps the head. -/
abbrev Failures := List Val

/-- The reified `Scope` a frame denotes: a sequential scope whose registration
table is the frame's releases in *registration* order, keyed by position.
`Frame.releases` is stored latest-first, `Scope.finalizers` is registration
order, so the frame's list is reversed here and `Scope.closeOrder` reverses it
back (`Frame.toScope_closeOrder`). -/
def Frame.toScope {alphabet : FlowAlphabet Ty} (frame : Frame alphabet) :
    Effect4.Scope Nat (alphabet.Op × Val) Val Val Unit Unit Unit where
  strategy := .sequential
  state := .openMap (frame.releases.reverse.zipIdx.map fun entry => (entry.2, entry.1))

/-- The scope closes exactly the releases the runner runs, in the runner's
order: `Frame.releases`, latest-registered first. -/
theorem Frame.toScope_closeOrder {alphabet : FlowAlphabet Ty} (frame : Frame alphabet) :
    Effect4.Scope.closeOrder frame.toScope = frame.releases := by
  show ((frame.releases.reverse.zipIdx.map fun entry => (entry.2, entry.1)).map
    Prod.snd).reverse = _
  rw [List.map_map]
  show (frame.releases.reverse.zipIdx.map Prod.fst).reverse = _
  rw [List.zipIdx_map_fst 0 frame.releases.reverse, List.reverse_reverse]

/-- The exit a release reports to the reified scope: `void` on success, a
one-reason `fail` cause on failure. -/
def releaseExit : Except Val Val -> Effect4.Exit Unit Val Unit Unit Unit
  | .ok _ => Effect4.Exit.void
  | .error error => Effect4.Exit.failure ⟨[.fail error Effect4.ReasonAnnotations.empty]⟩

/-- The closing exit a frame is closed with, as the reified scope sees it. -/
def frameExit : Outcome Val -> Effect4.Exit Val Val Unit Unit Unit
  | .success value => Effect4.Exit.success value
  | .failure error => Effect4.Exit.failure ⟨[.fail error Effect4.ReasonAnnotations.empty]⟩
  | .interrupted => Effect4.Exit.failure ⟨[.interrupt none Effect4.ReasonAnnotations.empty]⟩

/-- Running one release as the reified scope's finalizer run: a release
performs its own operation and does not read the closing exit. -/
def runRelease [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M) :
    (alphabet.Op × Val) -> Effect4.Exit Val Val Unit Unit Unit ->
      M (Effect4.Exit Unit Val Unit Unit Unit) :=
  fun release _ => releaseExit <$> service.handle release.fst release.snd

/-- The errors a list of release exits carries, in order. -/
def exitErrors (exits : List (Effect4.Exit Unit Val Unit Unit Unit)) : Failures :=
  (exits.flatMap Effect4.Exit.causeReasons).filterMap Effect4.Reason.error?

/-- Log a family operation's request and answer, or its failure. -/
def logOperation [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (op : alphabet.Op) (request : Val) (result : Except Val Val) :
    RunM M Unit :=
  if service.pure op then pure () else do
    emit (.op (nameOf op) request)
    match result with
    | .ok answer => emit (.answer (nameOf op) answer)
    | .error error => emit (.failed (nameOf op) error)

/-- Run the releases of a close, in close order: each logs `finalizer region
exit` before its own rows, and every failure is kept, in that order. A failing
release does not abort the loop (rc.112 `scopeCloseUnsafe`). -/
def closeReleases [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (region : Nat) (exit : Outcome Val) :
    List (alphabet.Op × Val) → RunM M Failures
  | [] => pure []
  | (release, resource) :: rest => do
      emit (.finalizer region exit)
      let result ← StateT.lift (service.handle release resource)
      logOperation service nameOf release resource result
      let later ← closeReleases service nameOf region exit rest
      match result with
      | .ok _ => pure later
      | .error error => pure (error :: later)

/-- Close one region with `exit`: log `leave`, then run its releases in the
reified scope's close order, latest-registered first, each logging `finalizer`
with the same exit before its own rows. Every release failure is reported, in
close order (`closeFrame_failure`); the wire keeps the first. -/
def closeFrame [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (frame : Frame alphabet) (exit : Outcome Val) :
    RunM M Failures := do
  emit (.leave frame.region.value exit)
  closeReleases service nameOf frame.region.value exit frame.releases

/-- Close every open region, innermost first, with a failure; the failures
merge in close order. -/
def unwind [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) : List (Frame alphabet) → Val → RunM M Failures
  | [], _ => pure []
  | frame :: rest, error => do
      let here ← closeFrame service nameOf frame (.failure error)
      let later ← unwind service nameOf rest error
      pure (here ++ later)

/-- End the run with a failure after closing every open region. The merged
cause is `error :: (rest ++ what the unwind failed with)`, in close order; the
wire and `RunResult.failed` show its first failure, `error`. -/
def fail [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (error : Val)
    (rest : Failures) (tape : Tape) : RunM M ((RunResult × Tape) × Failures) := do
  let closing ← unwind service nameOf stack error
  emit (.done (.failure error))
  pure ((.failed error, tape), error :: (rest ++ closing))

/-- Spend one unit of fuel per block, keeping the region stack. The second
component is the merged failure the run collected, in close order; it is empty
on every run that did not fail. -/
def regionLoop [Monad M] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) :
    Nat → BlockId → Env → Tape → List (Frame alphabet) →
      RunM M ((RunResult × Tape) × Failures)
  | 0, block, _, tape, _ => do
      emit .frontier
      pure ((.frontier (.fuel block), tape), [])
  | fuel + 1, block, env, tape, stack =>
    match flow.block? block with
    | none => pure ((.frontier (.stuck block), tape), [])
    | some current =>
      let stuck : RunM M ((RunResult × Tape) × Failures) :=
        pure ((.frontier (.stuck block), tape), [])
      match current.term with
      | .plain term =>
          let raw : RawBlock Ty := { id := current.id, params := current.params, term := term }
          match plan alphabet raw env tape with
          | .stuck => stuck
          | .ret value => do
              emit (.done (.success value))
              pure ((.done value, tape), [])
          | .jump target env' => regionLoop alphabet flow service nameOf fuel target env' tape stack
          | .perform op request target env' => do
              let result ← StateT.lift (service.handle op request)
              logOperation service nameOf op request result
              match result with
              | .ok answer =>
                  regionLoop alphabet flow service nameOf fuel target (env' ++ [answer]) tape stack
              | .error error => fail service nameOf stack error [] tape
          | .exhausted site => do
              emit .frontier
              pure ((.frontier (.unansweredDecision site), tape), [])
          | .mismatch expected actual => pure ((.refused expected actual, tape), [])
          | .choose site branch target env' rest => do
              emit (.decide site.value branch)
              regionLoop alphabet flow service nameOf fuel target env' rest stack
      | .enter region body args =>
          match readArgs env args with
          | none => stuck
          | some values => do
              emit (.enter region.value)
              regionLoop alphabet flow service nameOf fuel body values tape
                ({ region := region, releases := [] } :: stack)
      | .acquire operation request release target args =>
          match alphabet.lookup operation, alphabet.lookup release, env[request.index]?,
              readArgs env args, stack with
          | some op, some releaser, some requestValue, some values, frame :: rest => do
              let result ← StateT.lift (service.handle op requestValue)
              logOperation service nameOf op requestValue result
              match result with
              | .ok answer =>
                  regionLoop alphabet flow service nameOf fuel target (values ++ [answer]) tape
                    ({ frame with releases := (releaser, answer) :: frame.releases } :: rest)
              | .error error => fail service nameOf stack error [] tape
          | _, _, _, _, _ => stuck
      | .leave value =>
          match env[value.index]?, stack, current.region.bind flow.row? with
          | some v, frame :: rest, some row => do
              match ← closeFrame service nameOf frame (.success v) with
              | [] => regionLoop alphabet flow service nameOf fuel row.continue_ [v] tape rest
              | error :: more => fail service nameOf rest error more tape
          | _, _, _ => stuck

/-- Run an admitted region flow from its entry with no open region, keeping the
merged failure. -/
def runRegionsCause [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) :
    RunM M ((RunResult × Tape) × Failures) :=
  regionLoop alphabet flow.flow service nameOf fuel flow.flow.entry [input] tape []

/-- The wire face of a run: the merged failure projected to its first, which is
the error `RunResult.failed` and the `done` row already carried. -/
def runRegions [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) : RunM M (RunResult × Tape) := do
  let outcome ← runRegionsCause fuel flow service nameOf tape input
  pure outcome.fst

/-- Run with the fuel the erased graph allots. -/
def runRegionsDefault [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) : RunM M (RunResult × Tape) :=
  runRegions (fuelFor flow.flow.erase tape) flow service nameOf tape input

end Effect4.Flow
