import Effect4.Program.Compile

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: Atomic root, daemon and request actual native transitions.
Actual source and selected-frame exclusions reuse one native dispatcher equation.
The caller retains source ownership and saved-frame permissions separately.
-/
set_option autoImplicit false
namespace Effect4.Program
open Effect4 Effect4.Machine

/-- A native actor without an actual scoped entry or selected scoped exit uses primitive evaluation. -/
theorem evaluateNative_primitive (root : NativeEff) (table : RowTable)
    (machine : RunMachine EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (entry : ∀ point, fiber.frame.current = .withFiber (.act point) → ∀ body,
      Node.at_ (.eff root) point.path ≠ some (.eff (.scoped body)))
    (value : ∀ value, fiber.frame.current = .success value → ∀ body previous scope flag,
      (fiber.frame.getCont .contA false).answer ≠ .frame (.onExit body (.scopedExit previous scope) flag))
    (cause : ∀ cause, fiber.frame.current = .failure cause → ∀ body previous scope flag,
      (fiber.frame.getCont .contE true (some cause)).answer ≠ .frame (.onExit body (.scopedExit previous scope) flag)) :
    evaluateNative root machine fiber yielding table =
      evaluatePrim (interpAt root machine.completedExits table) machine fiber yielding := by
  unfold evaluateNative
  split
  · rename_i point current
    split
    · rename_i body found
      exact (entry point current body found).elim
    · rfl
  · rename_i answer current
    unfold exitScoped
    dsimp only
    split
    · rename_i body previous scope flag chosen
      exact (value answer current body previous scope flag chosen).elim
    · simp only [evaluatePrim, current]
      rfl
  · rename_i failure current
    unfold exitScoped
    dsimp only
    split
    · rename_i body previous scope flag chosen
      exact (cause failure current body previous scope flag chosen).elim
    · simp only [evaluatePrim, current]
      rfl
  · rfl

end Effect4.Program
