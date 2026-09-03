import Effects.Flow.Region
import Effect4.Semantics.Runs
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
the run ends `failed`. The first failure is the run's failure: a release that
fails while closing with a failure does not replace it (E4-FLOW-CE-019 records
that the host is checked on exactly this).
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

/-- Log a family operation's request and answer, or its failure. -/
def logOperation [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (op : alphabet.Op) (request : Val) (result : Except Val Val) :
    RunM M Unit :=
  if service.pure op then pure () else do
    emit (.op (nameOf op) request)
    match result with
    | .ok answer => emit (.answer (nameOf op) answer)
    | .error error => emit (.failed (nameOf op) error)

/-- Close one region with `exit`: log `leave`, run its releases latest-first
(each logs `finalizer` with the same exit), and report the first release
failure, if any. -/
def closeFrame [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (frame : Frame alphabet) (exit : Outcome Val) :
    RunM M (Option Val) := do
  emit (.leave frame.region.value exit)
  let mut failure : Option Val := none
  for (release, resource) in frame.releases do
    emit (.finalizer frame.region.value exit)
    let result ← StateT.lift (service.handle release resource)
    logOperation service nameOf release resource result
    match result with
    | .ok _ => pure ()
    | .error error => if failure.isNone then failure := some error
  pure failure

/-- Close every open region, innermost first, with a failure. -/
def unwind [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (error : Val) :
    RunM M Unit := do
  for frame in stack do
    let _ ← closeFrame service nameOf frame (.failure error)

/-- End the run with a failure after closing every open region. -/
def fail [Monad M] {alphabet : FlowAlphabet Ty} (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (stack : List (Frame alphabet)) (error : Val) (tape : Tape) :
    RunM M (RunResult × Tape) := do
  unwind service nameOf stack error
  emit (.done (.failure error))
  pure (.failed error, tape)

/-- Spend one unit of fuel per block, keeping the region stack. -/
def regionLoop [Monad M] (alphabet : FlowAlphabet Ty) (flow : RegionFlow Ty)
    (service : RegionService alphabet M) (nameOf : alphabet.Op → String) :
    Nat → BlockId → Env → Tape → List (Frame alphabet) → RunM M (RunResult × Tape)
  | 0, block, _, tape, _ => do
      emit .frontier
      pure (.frontier (.fuel block), tape)
  | fuel + 1, block, env, tape, stack =>
    match flow.block? block with
    | none => pure (.frontier (.stuck block), tape)
    | some current =>
      let stuck : RunM M (RunResult × Tape) := pure (.frontier (.stuck block), tape)
      match current.term with
      | .plain term =>
          let raw : RawBlock Ty := { id := current.id, params := current.params, term := term }
          match plan alphabet raw env tape with
          | .stuck => stuck
          | .ret value => do
              emit (.done (.success value))
              pure (.done value, tape)
          | .jump target env' => regionLoop alphabet flow service nameOf fuel target env' tape stack
          | .perform op request target env' => do
              let result ← StateT.lift (service.handle op request)
              logOperation service nameOf op request result
              match result with
              | .ok answer =>
                  regionLoop alphabet flow service nameOf fuel target (env' ++ [answer]) tape stack
              | .error error => fail service nameOf stack error tape
          | .exhausted site => do
              emit .frontier
              pure (.frontier (.unansweredDecision site), tape)
          | .mismatch expected actual => pure (.refused expected actual, tape)
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
              | .error error => fail service nameOf stack error tape
          | _, _, _, _, _ => stuck
      | .leave value =>
          match env[value.index]?, stack, current.region.bind flow.row? with
          | some v, frame :: rest, some row => do
              match ← closeFrame service nameOf frame (.success v) with
              | none => regionLoop alphabet flow service nameOf fuel row.continue_ [v] tape rest
              | some error => fail service nameOf rest error tape
          | _, _, _ => stuck

/-- Run an admitted region flow from its entry with no open region. -/
def runRegions [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty} (fuel : Nat)
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) : RunM M (RunResult × Tape) :=
  regionLoop alphabet flow.flow service nameOf fuel flow.flow.entry [input] tape []

/-- Run with the fuel the erased graph allots. -/
def runRegionsDefault [Monad M] [DecidableEq Ty] {alphabet : FlowAlphabet Ty}
    (flow : CheckedRegionFlow alphabet) (service : RegionService alphabet M)
    (nameOf : alphabet.Op → String) (tape : Tape) (input : Val) : RunM M (RunResult × Tape) :=
  runRegions (fuelFor flow.flow.erase tape) flow service nameOf tape input

end Effect4.Flow
