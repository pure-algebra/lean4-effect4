import Effect4.Laws.Program.CodeClosure.NativeClosure
import Effect4.Laws.Program.CodeClosure.ScopedFunding

/-!
Concept: scope-lifetime-finalization R11.
Question: native scope closure retains the supplied current and saved code certificate.
Consumer: the complete finalizer source configuration.
The existing saved-family producer supplies the actual pop and retained suffix.
This local result establishes no source funding or history bound.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.PredicateFamily
open Effect4 Effect4.Machine Effect4.Program

/-- The actual selected callback and saved suffix retain one supplied code certificate. -/
theorem pop_owned (root : NativeEff) (table : RowTable) (P : NCode → Prop)
    (rules : Rules root table P) (view : List (FiberId × ExitV)) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (exit : ExitV) (selected : NCode) (stack : ∀ code ∈ fiber.stack, P code)
    (found : (WriterWeights.popFor fiber exit).answer = .frame selected) :
    P selected ∧ ∀ code ∈ (WriterWeights.popFor fiber exit).fiber.stack, P code := by
  cases exit with
  | success value =>
    obtain ⟨incoming, middle, good, owned, suffix⟩ := AnswerFlow.External.getCont_value_selected
      ((spec root table P rules).model view) (interpAt root view table).toPrimInterp (edge P)
      (family root table P rules view) (fun _ _ => rules.mask true)
      () () () fiber value selected True.intro (path P fiber.stack stack) found
    exact ⟨owned, path_owned P suffix⟩
  | failure cause =>
    obtain ⟨incoming, middle, delivered, carried, good, owned, suffix⟩ := AnswerFlow.External.getCont_cause_selected
      ((spec root table P rules).model view) (interpAt root view table).toPrimInterp (edge P)
      (family root table P rules view) (fun _ _ => rules.mask true)
      () () () fiber cause selected True.intro (fun _ _ _ _ _ => trivial)
      (path P fiber.stack stack) found
    exact ⟨owned, path_owned P suffix⟩

/-- Native scope dispatch reuses the actual selected suffix and its captured close program. -/
theorem exit_scoped_frame (root : NativeEff) (P : NCode → Prop) (rules : Rules root [] P)
    (machine : NativeMachine) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (yielding : Bool) (exit : ExitV) (held : Frame P fiber.frame)
    (closing : ∀ scope flag state code,
      storesCloseScopeUnsafe scope ((WriterWeights.popFor fiber.frame exit).deliveredExit exit)
        flag machine.state = some (state, some code) →
      P (finalizerCode (interpAt root machine.completedExits [])
        ((WriterWeights.popFor fiber.frame exit).deliveredExit exit) (embed code)))
    (delegated : Frame P (evaluatePrim (interpAt root machine.completedExits []) machine fiber yielding).fiber.frame) :
    Frame P (exitScoped root machine fiber yielding exit).fiber.frame := by
  have terminal (result : ExitV) : P (.ofExit result) := by
    cases result with
    | success value => exact rules.success value
    | failure cause => exact rules.failure cause
  have popped (selected : NCode)
      (found : (WriterWeights.popFor fiber.frame exit).answer = .frame selected) :=
    (pop_owned root [] P rules machine.completedExits fiber.frame exit selected held.2 found).2
  cases exit
  all_goals
    simp only [WriterWeights.popFor] at closing popped
    unfold exitScoped
    dsimp only
    split
    · rename_i body previous scope flag selected
      have suffix := popped _ selected
      split
      · dsimp only [Frame]
        exact ⟨terminal _, suffix⟩
      · rename_i state program closed
        cases program with
        | none =>
          dsimp only [Frame]
          exact ⟨terminal _, suffix⟩
        | some code =>
          dsimp only [Frame]
          exact ⟨closing scope _ state code closed, suffix⟩
    · exact delegated

end Effect4.Program.CodeClosure.PredicateFamily
