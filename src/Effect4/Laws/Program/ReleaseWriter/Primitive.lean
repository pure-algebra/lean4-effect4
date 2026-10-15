import Effect4.Laws.Program.ReleaseWriter.Actions

/-!
Concept: scope-lifetime-finalization R11.
Question: the shared native primitive debit consumes its actual store-write premise.
Reach: direct source-owned programs with sequential scopes and no races.
Consumers: both crews' release-log histories through PlaceFunding.
The dynamic store premise comes from their initialized answer-flow invariant.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- A successful native sync spends at most its own pending direct-write reservation. -/
def SyncBound (target : Target) (root : NativeEff) (table : RowTable) (m : NativeMachine) (code : NCode) : Prop :=
  ∀ suspended after value, code = .sync suspended →
    (interpAt root m.completedExits table).syncState suspended m.state = some (after, value) →
    (ledger target).state after ≤ (ledger target).state m.state + thunk target suspended

/-- A non-synchronous current code requires no store-write premise. -/
theorem SyncBound.of_not_sync (target : Target) (root : NativeEff) (table : RowTable)
    (m : NativeMachine) (code : NCode) (different : ∀ suspended, code ≠ .sync suspended) :
    SyncBound target root table m code := by
  intro suspended _ _ selected _
  exact (different suspended selected).elim

/-- Keeping the reference heap keeps its observed release count. -/
theorem state_le_of_refs (target : Target) (before after : Stores) (same : after.refs = before.refs) :
    (ledger target).state after ≤ (ledger target).state before := by
  dsimp only [ledger, log]
  rw [same]
  exact Nat.le_refl _

/-- A native terminal reply holds no pending release write. -/
theorem terminal_zero (target : Target) (code : NCode) (reply : TerminalReply code) : Free target code := by
  cases reply <;> rfl

/-- Native Async cancellation names carry no reservation. -/
theorem async_cancel_zero (target : Target) (callback : EffName) (held : AsyncCancelAt callback) :
    name target callback = 0 := by
  cases callback
  case cancelAwait => rfl
  case store callback =>
    cases callback
    case cancelAwait | cancelSleep => rfl
    all_goals cases held
  all_goals cases held

/-- Every primitive evaluation of an owned fiber spends only its acting frame's reservation or a
recorded start. -/
theorem primitive_debit {target : Target} {root : NativeEff} (source : Source target root) (table : RowTable)
    (sequential : SequentialSource root) (raceFree : RaceFreeSource root) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) (syncBound : SyncBound target root table m fiber.frame.current) :
    (ledger target).IterDebit m fiber
      (evaluatePrim (interpAt root m.completedExits table) m fiber yielding) := by
  have inputs : PlaceFunding.PrimitiveInputs (ledger target) (Free target)
      (interpAt root m.completedExits table) m fiber yielding := {
    success := fun _ => rfl
    failure := fun _ => rfl
    exitValue := fun exit mode => by cases mode <;> cases exit <;> rfl
    step := source.step_frame_debit table m fiber yielding held.frame
    finalizer := fun exit => source.finalizer_debit table m fiber yielding exit held.frame
    action := by
      intro suspended next selected produced
      have thunkOwned := held.frame.1
      rw [selected] at thunkOwned
      exact action_debit source table sequential m fiber yielding suspended next selected thunkOwned produced
    sync := by
      intro suspended state value selected written
      have bounded := syncBound suspended state value selected written
      change (ledger target).state state + (0 + (fiber.frame.stack.map (saved target)).sum) ≤
        (ledger target).state m.state + (current target fiber.frame.current + (fiber.frame.stack.map (saved target)).sum)
      rw [selected]
      change (ledger target).state state + (0 + (fiber.frame.stack.map (saved target)).sum) ≤
        (ledger target).state m.state + (thunk target suspended + (fiber.frame.stack.map (saved target)).sum)
      omega
    registerState := by
      intro register signal cancel state code _ produced
      have same := register_refs root m.completedExits table register fiber.id m.nextToken m.state
      rw [produced] at same
      exact state_le_of_refs target _ _ same
    registerReply := fun register _ _ _ code _ produced =>
      terminal_zero target code (register_reply root m.completedExits table register fiber.id
        m.nextToken m.state code (congrArg Prod.snd produced))
    cancel := by
      intro register signal cancel state selected _
      have callbacks := held.frame.1
      rw [selected] at callbacks
      have zero : name target ((interpAt root m.completedExits table).cancelName
          (cancel.getD (interpAt root m.completedExits table).abortName) fiber.id m.nextToken) = 0 := by
        cases cancel with
        | none => rfl
        | some callback => exact async_cancel_zero target callback (callbacks.2 callback rfl).2
      simp only [ledger, frame, FrameWeights.frame, model, List.map_cons, List.sum_cons, saved, zero, Nat.zero_add,
        Nat.le_refl]
    joinCancel := by
      have zero : name target ((interpAt root m.completedExits table).cancelName
          (interpAt root m.completedExits table).parkCancelName fiber.id m.nextToken) = 0 := rfl
      simp only [ledger, frame, FrameWeights.frame, model, List.map_cons, List.sum_cons, saved, zero, Nat.zero_add,
        Nat.le_refl]
    countdown := by
      intro targets next returned parked edits _ counted
      have debit := PlaceFunding.countdown_debit (no_queue target) (events target) (model target) (fun _ => rfl) _
        (action_inputs target root m.completedExits table) m fiber yielding targets
        .exitsValue false (fun _ => rfl)
      rw [counted] at debit
      exact debit
    race := by
      intro race _
      have empty := Opportunities.races_nil root m raceFree owned
      unfold registerRace RunMachine.race?
      rw [empty]
      exact Nat.le_refl _ }
  exact PlaceFunding.primitive_debit (no_queue target) (control target) (events target) _ m fiber yielding inputs


end Effect4.Program.ReleaseWriter
