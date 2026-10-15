import Effect4.Laws.Program.FinalizerNativePrimitive
import Effect4.Laws.Program.CodeClosure.ScopedFunding

/-!
Concept: scope-lifetime-finalization R11.
Question: actual native scope dispatch serves FinalizerRun.once_placed_outside_census.
Consumer: the full native evaluator and its existing command lift.
The shared scope connector accounts for the actual pop and captured close program.
Source closure and complete history funding remain separate obligations.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Actual scoped entry transfers its source reservation to the captured body. -/
theorem enter_scoped_debit (root : NativeEff) (q : List Nat) (point : Point) (body : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff (.scoped body)))
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (selected : fiber.frame.current = .withFiber (.act point)) :
    (ledger root q).IterDebit machine fiber (enterScoped root point machine fiber yielding) := by
  apply PlaceFunding.local_debit machine fiber _ rfl rfl rfl
  have bounded := Nat.le_trans (resolve_le root q (point.child 0))
    (SourceScope.Opportunities.child_le q point.path 0)
  change _ + 0 + frame root q (enterScoped root point machine fiber yielding).fiber.frame + _ ≤
    _ + 0 + frame root q fiber.frame + _
  simp only [enterScoped, PlaceLedger.spent, PlaceLedger.issued, frame, selected,
    current, cata_prim, nativeWeights, name, thunk, SourceScope.Opportunities.thunk, found,
    SourceScope.Opportunities.name, exitPush, Nat.add_zero]
  change _ + (current root q (resolve root (point.child 0)) + _) + _ ≤ _ + (SourceScope.Opportunities.below q point.path + _) + _
  omega

/-- A terminal primitive delegates to the existing actual finalizer dispatcher. -/
theorem terminal_primitive_fields (root : NativeEff) (view) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (selected : fiber.frame.current = .ofExit exit) :
    let next := evaluatePrim (interpAt root view table) machine fiber yielding
    next.machine.fibers = machine.fibers ∧ next.machine.races = machine.races ∧ next.nested = [] := by
  have fields := CodeClosure.Funding.finalizer_fields (interpAt root view table) machine fiber yielding exit
  cases exit <;> simp only [evaluatePrim, selected, Prim.ofExit, interpAt, interpOf]
  all_goals exact ⟨fields.2.1, fields.2.2.1, fields.2.2.2.2⟩

/-- Scope closure installs only zero active weight before its captured release custody opens. -/
theorem exit_scoped_debit (root : NativeEff) (q : List Nat)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (frames : FrameAt q fiber.frame) (currentAt : TemplateAt q fiber.frame.current)
    (scopes : ScopesAt q machine.state.scopes) (unique : (machine.races.map Race.id).Nodup)
    (selected : fiber.frame.current = .ofExit exit) :
    (ledger root q).IterDebit machine fiber (exitScoped root machine fiber yielding exit) := by
  have fields := terminal_primitive_fields root machine.completedExits [] machine fiber yielding exit selected
  have fallback := primitive_debit root q machine.completedExits [] placed machine fiber yielding
    frames currentAt scopes unique
  have delegated :
      let next := evaluatePrim (interpAt root machine.completedExits []) machine fiber yielding
      CodeClosure.Funding.recorded (consumedFrame q) next.machine + frame root q next.fiber.frame +
          CodeClosure.Funding.recorded (producedFrame q) machine ≤
        CodeClosure.Funding.recorded (consumedFrame q) machine + frame root q fiber.frame +
          CodeClosure.Funding.recorded (producedFrame q) next.machine := by
    have consume : (ledger root q).consumed = CodeClosure.Funding.runWeight (consumedFrame q) := by
      funext event
      cases event <;> rfl
    have produce : (ledger root q).produced = CodeClosure.Funding.runWeight (producedFrame q) := by
      funext event
      cases event <;> rfl
    unfold PlaceLedger.IterDebit PlaceLedger.outside at fallback
    simp only [PlaceLedger.spent, PlaceLedger.issued, consume, produce] at fallback
    simp only [FiberSum.outside, fields.1, fields.2.1, fields.2.2, List.map_nil, List.sum_nil,
      ledger, Nat.zero_add, Nat.add_zero] at fallback
    unfold CodeClosure.Funding.recorded
    omega
  have bounded := CodeClosure.Funding.exit_scoped_bound (frameModel root q) (successPush q) (exitPush q)
    (producedFrame q) root machine fiber yielding exit (fun result => by cases result <;> rfl)
    (by
      intro scope flag state code closed
      have zero := (Machine.ScopeFields.close_unsafe_at (scopeModel q) _ (closeWeightPrograms root q)
        scope _ flag machine.state state (some code) scopes closed).2 code rfl
      have held := (close_unsafe_at q scope _ flag machine.state state (some code) scopes closed).2 code rfl
      change current root q (finalizerCode _ _ (embed code)) = 0
      rw [(finalizer_code root q machine.completedExits [] _ (embed code) held).2]
      exact zero)
    (by rw [← consumed_slots]; exact delegated)
  have ambient := CodeClosure.Funding.exit_scoped_fields root machine fiber yielding exit fields
  apply PlaceFunding.local_debit machine fiber _ ambient.1 ambient.2.1
    (by rw [ambient.2.2]; rfl)
  rw [← consumed_slots] at bounded
  exact bounded

/-- The complete actual native evaluator transfers the selected reservation at its real places. -/
theorem native_debit (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (frames : FrameAt q fiber.frame) (currentAt : TemplateAt q fiber.frame.current)
    (scopes : ScopesAt q machine.state.scopes) (unique : (machine.races.map Race.id).Nodup) :
    (ledger root q).IterDebit machine fiber (evaluateNative root machine fiber yielding table) := by
  have primitive := primitive_debit root q machine.completedExits table placed machine fiber yielding
    frames currentAt scopes unique
  unfold evaluateNative
  split
  · rename_i point selected
    split
    · exact enter_scoped_debit root q point _ ‹_› machine fiber yielding selected
    · exact primitive
  · exact exit_scoped_debit root q placed machine fiber yielding _ frames currentAt scopes unique ‹_›
  · exact exit_scoped_debit root q placed machine fiber yielding _ frames currentAt scopes unique ‹_›
  · exact primitive

end Effect4.Program.FinalizerSource
