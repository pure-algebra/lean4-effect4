import Controls
import Effect4.Laws.Machine.ScopeMachine

/-! Finite controls of the stronger host and frontier observations, placed in README.md.
The host checks requests, not just reply order. No theorem here depends on the planned goal. -/
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 0
namespace Test.HostMeaningWidening.Controls
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Denote
open Test.HostMeaningWidening
open Test.Dogfood.Scenario (Move script answer ok failed held live)
open Test.Dogfood.P2HandlerLayers (built?)
open Effect4.Program.Stream (chunkVal endVal)

structure Expected where
  row : String
  request : Val
  reply : ExitV
deriving DecidableEq

structure ScriptState where
  pending : List Expected
  seen : List Expected := []
deriving DecidableEq

/-- A finite host that checks both the row spelling and the request at each answer. -/
def scriptedHost (table : RowTable) : Effects.Comodel (RowSig table) ScriptState where
  answer op state :=
    match externalRow table op.1.val, state.pending with
    | some row, entry :: rest =>
      let request : Val := op.2
      if row.spelling == entry.row && decide (request = entry.request) then
        some (entry.reply, ⟨rest, state.seen ++ [entry]⟩)
      else none
    | _, _ => none

def expected : List Expected :=
  [⟨"Probe.open", .unit, .success (.nat 7)⟩,
   ⟨"Probe.pull", .nat 7, .success (chunkVal [.nat 1, .nat 2])⟩,
   ⟨"Probe.pull", .nat 7, .success (chunkVal [.nat 3])⟩,
   ⟨"Probe.pull", .nat 7, .success (endVal .unit)⟩,
   ⟨"Probe.close", .nat 7, .success .unit⟩]

def hostCheck (s : Run) (state : ScriptState) : Option ScriptState :=
  Run.hostAnsweredCheck s.built.table (scriptedHost s.built.table) s.built.program
    s.budget.fuel (Run.tapeOf s) (Api.load s.built.program s.budget.compileFuel) state

/-- The H9 premises' executable host check and both meaning observations agree in this run. -/
def h9Finite : Bool :=
  match played (collect) twoPages with
  | none => false
  | some s =>
    let host := scriptedHost s.built.table
    let state : ScriptState := ⟨expected, []⟩
    let final : ScriptState := ⟨[], expected⟩
    decide (hostCheck s state = some final ∧
      meaningUnderB host 4 s.built.program [] Stores.empty state =
        s.exit.map (fun ex => ((some ex, s.machine.state), final)) ∧
      observeTree host (denoteRowsB s.built.table 4 s.built.program []) Stores.empty state =
        ⟨.finished (.success (.list [.nat 1, .nat 2, .nat 3])), s.machine.state, final⟩)
#guard h9Finite

/-- Past answers leave the host's next answer unconstrained. Completed-only H9 avoids this. -/
def prefixDoesNotStopHost : Bool :=
  match played (collect) beforeClose with
  | none => false
  | some s =>
    let state : ScriptState := ⟨expected, []⟩
    decide (s.exit = none ∧
      hostCheck s state = some ⟨expected.drop 4, expected.take 4⟩ ∧
      (meaningUnderB (scriptedHost s.built.table) 4 s.built.program [] Stores.empty state).isSome = true)
#guard prefixDoesNotStopHost

/-- A wrong close request is observed even when all answer values are unchanged. -/
def wrongRequestRejected : Bool :=
  match played (collect) twoPages with
  | none => false
  | some s =>
    let wrong := expected.take 4 ++ [⟨"Probe.close", .nat 8, .success .unit⟩]
    let observed := observeTree (scriptedHost s.built.table)
      (denoteRowsB s.built.table 4 s.built.program []) Stores.empty ⟨wrong, []⟩
    decide (hostCheck s ⟨wrong, []⟩ = none ∧
      observed.stop = .waiting 2 (.nat 7) ∧ observed.host.seen = expected.take 4)
#guard wrongRequestRejected

/-- A store write before failure stays visible to the finalizer's host request. -/
def writesBeforeFailure : Src NativeOp :=
  bindWith (Ref.make (nat 0)) fun cell =>
    onExitWith
      (bindWith (Ref.set cell (nat 5)) fun _ => Row.call pullRow (nat 7))
      (fun _ => bindWith (Ref.get cell) fun value => Row.call closeRow value)

def storeWait : List Move := script [[.start],
  answer (.row "Probe.pull") (failed "ProbeError" "pull")]
def storeFinish : List Move := storeWait ++ closing

/-- Waiting retains the updated stores and exact cleanup request in the detailed observation. -/
def waitRetainsState : Bool :=
  match played writesBeforeFailure storeWait with
  | none => false
  | some s =>
    let seen := observeTree (tapeHost s.built.table)
      (denoteRowsB s.built.table 0 s.built.program []) Stores.empty (Run.appliedExits s)
    decide (s.exit = none ∧ seen.stop = .waiting 2 (.nat 5) ∧
      seen.stores = s.machine.state ∧ seen.stores.refs = [.nat 5] ∧ seen.host = [] ∧
      meaningUnderB (tapeHost s.built.table) 0 s.built.program [] Stores.empty (Run.appliedExits s) = none)
#guard waitRetainsState
#guard agrees writesBeforeFailure storeWait 0
#guard agrees writesBeforeFailure storeFinish 0
#guard (played writesBeforeFailure storeFinish).bind (·.exit) =
  some (.failure (Cause.fail (.tagged "ProbeError" "pull")))

/-- On a budget cut, the ordinary nested Option retains the stores, unlike a host wait. -/
def loopAfterWrite : NativeEff :=
  .bind (.perform .refMake (.lit (.nat 9)))
    (.iterate none (.lit .unit) (.lit (.bool false)) (.lit .unit) (.lit (.nat 8))
      (.succeed (.lit .unit)))
#guard (meaningUnderB (tapeHost []) 0 loopAfterWrite [] Stores.empty []).map
  (fun ((ex, stores), rest) => (ex, stores.refs, rest)) = some (none, [.nat 9], [])
#guard (meaningUnderB (tapeHost []) 1 loopAfterWrite [] Stores.empty []).map
  (fun ((ex, stores), rest) => (ex, stores.refs, rest)) = some (some (.success (.nat 8)), [.nat 9], [])
#guard (meaningB 1 loopAfterWrite [] Stores.empty).1 = some (.success (.nat 8))
#guard (meaningB 0 loopAfterWrite [] Stores.empty).1 = none

/- LoopedRows deliberately ignores table admission. The new intersection retains it. -/
#guard LoopedRows (.perform (.external 0) (.lit .unit)) = true
#guard LoopedDataRows [] (.perform (.external 0) (.lit .unit)) = false
#guard LoopedDataRows [(Row.host "Handle.open" .unit (.handle "Cursor") .never "probe").row]
  (.perform (.external 0) (.lit .unit)) = false
#guard LoopedDataRows [openRow.row] (.perform (.external 0) (.lit .unit)) = true

/-- Q11 control: no pending work does not by itself constitute a completed-close receipt. -/
def emptyClose : ScopeMachine.State Nat Nat Unit Unit Unit Nat Unit :=
  ScopeMachine.start (Scope.make .sequential) (.success ())
#guard emptyClose.scope.isClosed = true
#guard emptyClose.pending = []
#guard emptyClose.phase = .ready
#guard ScopeMachine.result? emptyClose = none
#guard ScopeMachine.result? (ScopeMachine.advance emptyClose) = some (.success ())

end Test.HostMeaningWidening.Controls
