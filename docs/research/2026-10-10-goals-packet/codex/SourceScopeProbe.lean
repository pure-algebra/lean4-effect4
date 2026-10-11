import Test.Dogfood.Scenario.QueueWorkers.Source
import Effect4.Laws.Program.SourceScope

open Effect4 Effect4.Machine Effect4.Program

-- A real generator allocates a reference, then modifies it at its second statement.
private def edit : Term := .app "pair" (.cons (.lit .unit) (.cons (.lit (.nat 1)) .nil))
private def tree : NativeEff := .gen (.cons
  (.bindYield (.perform .refMake (.lit (.nat 0))))
  (.cons (.yieldDiscard (.perform (.refModifyWith edit) (.var 0))) .nil))
private def point : Point := { path := [], env := [], fuel := 3, tape := [] }

-- Reader: the PC-aware law emits the actual operation and a correctly scoped advanced name.
example :
    (interpOf tree).iterNext (.gen point [1] true) (.cell ⟨0⟩) =
      ([], IterStep.resume (.sync (.op (.refModify ⟨0⟩ edit [.cell ⟨0⟩])))
        (.gen { point with env := [.cell ⟨0⟩] } [1, 1] false)) ∧
    SourceScope.GenAt tree { point with env := [.cell ⟨0⟩] } [1, 1] false :=
  SourceScope.gen_modify tree point [1] true false (.cell ⟨0⟩) edit (.var 0) .nil 2 ⟨0⟩
    rfl rfl rfl rfl

-- Control: the advanced name retains the generator root, whose raw level is still zero.
#guard SourceScope.levelAt (.eff tree) 0 point.path = some 0
#guard ({ point with env := [Val.cell ⟨0⟩] } : Point).env.length = 1
example : ¬ SourceScope.At tree { point with env := [.cell ⟨0⟩] } := by
  intro h
  cases h

-- Reader at the actual queue crew writer, for every job count.
example (total : Nat) :
    SourceScope.levelAt (.eff (Test.Dogfood.Scenario.Programs.queueProgram total)) 0
      Test.Dogfood.Scenario.QueueWorkers.Source.takePath = some 12 :=
  Test.Dogfood.Scenario.QueueWorkers.Source.take_level total
