import Effect4.Author
import Effect4.Library
import Effect4.Laws.Author

/-!
# Acceptance: an edit session on an authored module, through the entry modules alone

Codex's overwatch of the edit session (finding EDIT-OW-02,
`docs/research/2026-10-08-edit-session-overwatch-receipt.md`) found that the author's entry modules
did not reach the edit session. This program imports `Effect4.Author`, `Effect4.Library` and
`Effect4.Laws.Author` only. It builds a module with the Queue's definitions installed, a block at
its root, and opens an edit session on it.

* **Finite evaluations.** An edit inside the main program that keeps its focus's type splices the
  table, and the view keeps the module's type; an edit inside a body splices too.
* **Reader.** The law of what a session shows (`EditSession.reached_view`) at this program.
-/

set_option autoImplicit false

namespace Test.Dogfood.EditSession

open Effect4 Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- The Queue's definitions at numbers. -/
def numbers := Queue.Definitions.make "numbers" .nat

/-- The client: a queue, one offer through the installed definition, and a take. -/
def client : Module NativeOp :=
  numbers.module (eff do
    let q ← Queue.bounded .nat 2
    let _ ← numbers.offer q (nat 3)
    let x ← numbers.take q
    return x)

/-- The built client as a sketch with no hole, and its application. -/
def built : Option (Sketch × SigApp) :=
  (Api.Author.build client).toOption.map fun b => ({ program := b.program.expandRefs }, ⟨b.table, []⟩)

/-- The sketch, or the empty program where the build refuses. -/
def sketch : Sketch := (built.map (·.1)).getD { program := .succeed (.lit .unit) }

/-- The application, or the empty one where the build refuses. -/
def app : SigApp := (built.map (·.2)).getD {}

/-- The session opened on the client. -/
def opened : EditSession := EditSession.open app sketch

/-- The edit that wraps the sub-program at an address in `suspend`, which keeps its type. -/
def wrap (a : List Nat) : Option Edit :=
  match (Node.eff sketch.program).at_ a with
  | some (.eff q) => some (.fill a (.suspend q))
  | _ => none

/-- Whether an edit spliced, and whether the view keeps the opened session's type. -/
def splicesKeepingType (e : Edit) : Bool :=
  let (l', d) := opened.feed e
  (match d with
    | .spliced _ => true
    | _ => false) && l'.view.type == opened.view.type && opened.view.type.isSome

-- finite evaluation: the client builds, with a block at its root, and the session shows a type
#guard built.isSome && opened.view.type.isSome && opened.view.refusals.isEmpty
-- finite evaluation: an edit inside the main program, under `[1]`, splices and keeps the type
#guard (wrap [1, 0]).map splicesKeepingType == some true
-- finite evaluation: an edit inside the first body, under `[0, 0]`, splices and keeps the type
#guard (wrap [0, 0]).map splicesKeepingType == some true

-- reader: what a session reached by any edits shows is the checker's answer on its sketch
example (edits : List Edit) :
    ((EditSession.open app sketch).run edits).view.type =
      (((EditSession.open app sketch).run edits).sketch.check app).toOption :=
  (EditSession.reached_view app sketch edits).2

end Test.Dogfood.EditSession
