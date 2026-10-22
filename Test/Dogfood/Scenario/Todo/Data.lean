import Test.Dogfood.Scenario.Data
import Test.Dogfood.P2HandlerLayers.Data
import Examples.CachedTodo

/-! The to-do's reference model and the helpers that the batteries and fixture writers share. The
program is `Examples.Todo` (`examples/Examples/Todo.lean`). -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.Todo

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (eq pair)
open Test.Dogfood.P2HandlerLayers (recordVal built?)
open Examples.Todo

/-- One entry at its arguments, built through the application's module. -/
def builtAt (name : String) (args : List TermSrc) : Option Api.Built :=
  (application.entry? name).bind fun e => built? (application.moduleOf e args)

/-! ## 4. Finite runs under a scripted host -/

/-- A to-do value, its fields in canonical order. -/
def todo (id : Nat) (title : String) (done : Bool) : Val :=
  recordVal ["id", "title", "done"] [.nat id, .str title, .bool done]

/-! ## 7. The reference model of the repository

The claims packet's reference model (§3.6): a host as a function, written in Lean, that states
what the four rows do. It moved here from `Test/Api/SessionMeaning.lean`, which reads it, so the
application has one model. -/

/-- The repository's state: the next id and the to-dos. -/
abbrev Repo := Nat × List (Nat × String × Bool)

/-- A stored to-do as a value. -/
def todoOf (entry : Nat × String × Bool) : Val := todo entry.1 entry.2.1 entry.2.2

/-- An in-memory repository as a host function, row by row: the reference model. -/
def repository : Run.Reactor Repo := fun row sent state =>
  if row.spelling == "TodoRepo.insert" then
    match sent with
    | .str title =>
      some (ok (todo state.1 title false), (state.1 + 1, state.2 ++ [(state.1, title, false)]))
    | _ => none
  else if row.spelling == "TodoRepo.all" then
    some (ok (.list (state.2.map todoOf)), state)
  else if row.spelling == "TodoRepo.setDone" then
    match sent with
    | .list [.nat id, .bool done] =>
      match state.2.find? (·.1 == id) with
      | some entry =>
        some (ok (.some (todo id entry.2.1 done)),
          (state.1, state.2.map fun e => if e.1 == id then (e.1, e.2.1, done) else e))
      | none => some (ok .none, state)
    | _ => none
  else if row.spelling == "TodoRepo.delete" then
    match sent with
    | .nat id => some (ok (.bool (state.2.any (·.1 == id))), (state.1, state.2.filter (·.1 != id)))
    | _ => none
  else none

end Test.Dogfood.Scenario.Todo
