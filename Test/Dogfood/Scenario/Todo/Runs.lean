import Test.Dogfood.Scenario.Todo.Data

/-! Data shared by the scenario battery and fixture writers. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Dogfood.Scenario.Todo

open Examples.Todo
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P2HandlerLayers (recordVal)

/-- A built entry, opened under the application's name. -/
def opened (b : Api.Built) : Run := Run.open b application.name

/-- The script that fails the one call of `complete` with the repository's tag. -/
def repoFails (message : String) : List Move :=
  script [[.start], answer (.row "TodoRepo.setDone") (failed "SqlError" message)]

/-- A host that forgets what it stores: it answers as the model and keeps its state. The red
control of "after add". -/
def forgetful : Run.Reactor Repo := fun row request s =>
  (repository row request s).map fun step => (step.1, s)

/-- A host whose `setDone` flips the stored flag: the red control of "idempotent". -/
def toggling : Run.Reactor Repo := fun row request s =>
  match row.spelling, request with
  | "TodoRepo.setDone", .list [.nat id, .bool _] =>
    match s.2.find? (·.1 == id) with
    | some t =>
      some (ok (.some (todo id t.2.1 !t.2.2)),
        (s.1, s.2.map fun u => if u.1 == id then (u.1, u.2.1, !u.2.2) else u))
    | none => some (ok .none, s)
  | _, _ => repository row request s

/-- A run of a built entry driven by a host as a function (`Run.runWith`), as a named run: its
journal holds the host's rows, so the run replays with no host. -/
def drivenRun {σ : Type} (name : String) (b : Api.Built) (host : Run.Reactor σ) (st : σ) :
    NamedRun :=
  ⟨name, opened b, (Run.runWith b host st application.name).1.journal.map .wire⟩

/-- The host's state after it drives a run of a built entry. -/
def drivenState {σ : Type} (b : Api.Built) (host : Run.Reactor σ) (st : σ) : σ :=
  (Run.runWith b host st application.name).2

/-- The model's state where the runs under a host start: one to-do stored. -/
def stocked : Repo := (2, [(1, "milk", false)])

/-- The named runs: each script once, from one build of each entry at its argument. -/
def runsOf (empty milk done listed : Api.Built) : List NamedRun :=
  [ ⟨"empty", opened empty,
      script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "" false))]⟩
  , ⟨"milk", opened milk,
      script [[.start], answer (.row "TodoRepo.insert") (ok (todo 1 "milk" false))]⟩
  , ⟨"locked", opened done, repoFails "locked"⟩
  , ⟨"other-tag", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (failed "Timeout" "slow")]⟩
  , ⟨"done", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 1 "milk" true)))]⟩
  , ⟨"other-todo", opened done,
      script [[.start], answer (.row "TodoRepo.setDone") (ok (.some (todo 2 "tea" true)))]⟩
  , ⟨"wide", opened done,
      script [[.start], answer (.row "TodoRepo.setDone")
        (ok (.some (recordVal ["id", "title", "done", "at"]
          [.nat 1, .str "milk", .bool true, .nat 0])))]⟩
  , drivenRun "model-add" milk repository (1, [])
  , drivenRun "model-list" listed repository (drivenState milk repository (1, []))
  , drivenRun "forgetful-add" milk forgetful (1, [])
  , drivenRun "forgetful-list" listed forgetful (drivenState milk forgetful (1, []))
  , drivenRun "model-once" done repository stocked
  , drivenRun "model-twice" done repository (drivenState done repository stocked)
  , drivenRun "toggling-once" done toggling stocked
  , drivenRun "toggling-twice" done toggling (drivenState done toggling stocked) ]


/-- The programs of this scenario, each admitted once. -/
def builtInputs : Option (Api.Built × Api.Built × Api.Built × Api.Built) := do
  let empty ← builtAt "add" [str ""]
  let milk ← builtAt "add" [str "milk"]
  let done ← builtAt "complete" [nat 1]
  let listed ← builtAt "list" []
  pure (empty, milk, done, listed)

/-- One inventory of the named scripts, read by every lane. -/
def runSet : RunSet :=
  { name := "todo"
    runs := match builtInputs with
      | some (empty, milk, done, listed) => runsOf empty milk done listed
      | none => [] }

end Test.Dogfood.Scenario.Todo
