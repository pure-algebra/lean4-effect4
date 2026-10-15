import Test.Dogfood.Scenario.Atomic.StageRoles

/-!
Concept: store-typing R4.
Consumer: the Atomic root native actor and coupled stage history.
The actual root action point selects only its ordered forks or its final daemon interruption.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program
open StageWorld

/-- A successful root source-action lookup retains its actual fork binder or daemon interruption. -/
theorem action_shape (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (world : StageWorld.World) (point : Point) (held : PointAt built.program world point)
    (action : NAction) (actual : actionAt built.program (point.child 0) = some action) :
    (∃ owner body options rest, owner < 7 ∧ point.env.length = StageSource.forkBinder owner ∧
      Node.at_ (.eff built.program) point.path = some (.eff (.bind (.withFiber (.fork body options)) rest)) ∧
      action = .fork (resolve built.program (((point.child 0).child 0).child 0)) options ((point.child 0).child 0).path) ∨
    (point.env.length = 17 ∧ action = .interrupt ⟨1⟩) := by
  have lower := held.2.2.1
  obtain fork | wait | sleep | interrupt | read := RootSource.forms built accepted point.env.length held.2.2.1 held.2.2.2.1
  · obtain ⟨body, options, rest, binder, found⟩ := fork
    rw [← held.2.1.2] at found
    have child := Agreement.at_child found 0
    simp only [actionAt, child] at actual
    cases actual
    by_cases early : point.env.length < 9
    · refine .inl ⟨point.env.length - 3, body, options, rest, ?_, ?_, found, rfl⟩
      · omega
      · simp only [StageSource.forkBinder, if_pos (show point.env.length - 3 < 6 by omega)]
        omega
    · have last : point.env.length = 15 := by omega
      exact .inl ⟨6, body, options, rest, by decide, last, found, rfl⟩
  · obtain ⟨slot, rest, binder, found⟩ := wait
    rw [← held.2.1.2] at found
    have child := Agreement.at_child found 0
    simp only [actionAt, child] at actual
    cases actual
  · obtain ⟨rest, binder, found⟩ := sleep
    rw [← held.2.1.2] at found
    have child := Agreement.at_child found 0
    simp only [actionAt, child] at actual
    cases actual
  · obtain ⟨rest, binder, found⟩ := interrupt
    rw [← held.2.1.2] at found
    have child := Agreement.at_child found 0
    have captured : point.env[3]? = some (.fiber ⟨1⟩) :=
      held.2.1.1 3 (.fiber ⟨1⟩) (by decide) (by omega)
    simp only [actionAt, child] at actual
    change some (match (point.env[3]? : Option Val) with
      | some (.handle 1 id) => WithFiberAction.interrupt ⟨id⟩
      | _ => WithFiberAction.refuse (Cause.die Defect.badName)) = some action at actual
    rw [captured] at actual
    cases actual
    exact .inr ⟨binder, rfl⟩
  · obtain ⟨binder, found⟩ := read
    rw [← held.2.1.2] at found
    have child := Agreement.at_child found 0
    simp only [actionAt, child] at actual
    cases actual
/-- The public daemon interruption installs its actual native interrupt-as program at the same root answer class. -/
theorem interrupt_code (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV))
    (world : StageWorld.World) (point : Point) (held : PointAt root world point)
    (binder : point.env.length = 17) (target who : FiberId) :
    CodeAt root table world (.rootAnswer point.env.length) ((interpAt root view table).interruptAsCode target who) := by
  apply CodeAt.interrupting
  · have counter := held.2.2.2.2
    rw [binder] at counter ⊢
    exact counter
  · rw [binder]
    rfl

end Test.Dogfood.Scenario.Atomic.RootGraph
