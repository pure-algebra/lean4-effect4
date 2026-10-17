import Test.Dogfood.Scenario.Todo

/-!
# The to-do application's entries as programs

Each entry of the application (`Test/Dogfood/Scenario/Todo.lean`) as the program its open form
elaborates to, under one bind of its argument. The cached consumer
(`Test/Dogfood/Scenario/Todo/Cached.lean`) and the scenario's controls
(`Test/Dogfood/Scenario/Todo/Scenario.lean`) read them.
-/

set_option autoImplicit false

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring

/-- An entry's open program, or a unit program where the entry does not elaborate. -/
def openOf (name : String) : NativeEff :=
  match (application.entry? name).map application.openProgram with
  | some (.ok p) => p
  | _ => .succeed (.lit .unit)

/-- `add` at a title: the open program under one bind of the title. -/
def addAt (title : String) : NativeEff := .bind (.succeed (.lit (.str title))) (openOf "add")

/-- `complete` at an id: the open program under one bind of the id. -/
def completeAt (id : Nat) : NativeEff := .bind (.succeed (.lit (.nat id))) (openOf "complete")

/-- `list`: the open program, which has no parameter. -/
def listAt : NativeEff := openOf "list"

/-- The failure of an empty title, at the root. -/
def emptyTitleExit : ExitV := .failure (Cause.fail (.tagged "EmptyTitle" "a title is required"))

end Test.Dogfood.Scenario.Todo
