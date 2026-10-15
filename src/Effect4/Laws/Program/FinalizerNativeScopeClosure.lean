import Effect4.Laws.Program.FinalizerNativeClosure
import Effect4.Laws.Program.CodeClosure.ScopedClosure

/-!
Concept: scope-lifetime-finalization R11.
Question: the complete native evaluator retains full finalizer source templates.
Consumer: the source configuration through the existing command lift.
The actual scoped entry and captured exit instantiate the shared scope connector.
The history and funding obligations remain separate.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Scoped entry retains the captured body and administrative exit callback. -/
theorem enter_scoped_frame (root : NativeEff) (q : List Nat) (point : Point)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (selected : fiber.frame.current = .withFiber (.act point)) (held : TemplateFrame q fiber.frame) :
    TemplateFrame q (enterScoped root point machine fiber yielding).fiber.frame := by
  have owned := held.1.1
  rw [selected] at owned
  refine ⟨?_, held.2⟩
  have child := resolve_at root q (point.child 0) owned
  change TemplateAt q (.onExit (resolve root (point.child 0)) (.scopedExit fiber.context machine.state.nextName) false)
  aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [TemplateAt, CodeClosure.RegistrationBody,
    NameAt, OrdinaryNameAt, CodeClosure.Slots.NameAt, CodeClosure.Qualified.NameAt])

/-- Scoped exit retains its actual saved suffix and captured close program. -/
theorem exit_scoped_frame (root : NativeEff) (q : List Nat)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (held : TemplateFrame q fiber.frame) (scopes : ScopesAt q machine.state.scopes) :
    TemplateFrame q (exitScoped root machine fiber yielding exit).fiber.frame := by
  apply CodeClosure.PredicateFamily.exit_scoped_frame root (TemplateAt q)
    (templateRules root q [] placed) machine fiber yielding exit held
  · intro scope flag state code closed
    have owned := (close_unsafe_at q scope _ flag machine.state state (some code) scopes closed).2 code rfl
    exact (finalizer_code root q machine.completedExits [] _ (embed code) owned).1
  · exact primitive_frame root q machine.completedExits [] placed machine fiber yielding held scopes

/-- Every actual native dispatch retains the current and saved full source templates. -/
theorem native_frame (root : NativeEff) (q : List Nat) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (machine : NativeMachine)
    (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : TemplateFrame q fiber.frame) (scopes : ScopesAt q machine.state.scopes) :
    TemplateFrame q (evaluateNative root machine fiber yielding table).fiber.frame := by
  have primitive := primitive_frame root q machine.completedExits table placed machine fiber yielding held scopes
  unfold evaluateNative
  split
  · rename_i point selected
    split
    · exact enter_scoped_frame root q point machine fiber yielding selected held
    · exact primitive
  · exact exit_scoped_frame root q placed machine fiber yielding _ held scopes
  · exact exit_scoped_frame root q placed machine fiber yielding _ held scopes
  · exact primitive

/-- Scope dispatch changes no stored fiber row beyond the common primitive producer. -/
theorem native_rows (root : NativeEff) (q : List Nat) (table : RowTable)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (held : TemplateFrame q fiber.frame) (rows : ∀ row ∈ machine.fibers, TemplateFrame q row.frame) :
    ∀ row ∈ (evaluateNative root machine fiber yielding table).machine.fibers, TemplateFrame q row.frame := by
  have primitive := primitive_rows root q machine.completedExits table machine fiber yielding held rows
  have exiting (exit : ExitV) :
      ∀ row ∈ (exitScoped root machine fiber yielding exit).machine.fibers, TemplateFrame q row.frame := by
    unfold exitScoped
    dsimp only
    split
    · split
      · exact rows
      · rename_i state program closed
        cases program <;> exact rows
    · exact primitive_rows root q machine.completedExits [] machine fiber yielding held rows
  unfold evaluateNative
  split
  · split
    · exact rows
    · exact primitive
  · exact exiting _
  · exact exiting _
  · exact primitive

end Effect4.Program.FinalizerSource
