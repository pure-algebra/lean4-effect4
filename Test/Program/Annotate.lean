import Effect4.Laws.Program.Typing.Annotate
import Test.Dogfood.Scenario.Todo
import Test.Program.TableControls

/-!
# The address table in one traversal: the battery of slice P1

`annotate` (`Program/Typing/Annotate.lean`) computes the address table in one traversal, and
`annotate_eq_table` (`Laws/Program/Typing/Annotate.lean`) proves it equal to `table` at every
program. Each line here is a finite evaluation (decisions row 301): the evaluator runs the
traversal and the table on one real program and compares them.

* **The to-do's four programs** (`Test/Dogfood/Scenario/Todo.lean`), built as
  `Test/Program/CallInstance.lean` builds them.
* **A refused node and a sibling that is not reached**: a chain of `bind` whose first program is
  refused (`chained`, `Test/Program/TableControls.lean`). The programs after it have no
  environment.
* **A refused head whose later statements are visited**: a body with two refused statements
  (`twoBad`, the same file). The checker stops at the first, and the traversal visits the
  second at the head's environment.

No line restates a theorem, and no line prints axioms.
-/

namespace Test.Program.Annotate

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P2HandlerLayers (built?)
open Test.Dogfood.Scenario.Todo
open Test.Program.FocusControls Test.Program.TableControls

/-- Whether the traversal answers the table on a built request, at the request's signature;
false where the request does not build. -/
def agrees (m : Module NativeOp) : Bool :=
  match built? m with
  | some b =>
    annotate (nativeSignature b.table) [] b.program == table (nativeSignature b.table) [] b.program
  | none => false

-- finite evaluation: the to-do's four programs
#guard agrees (request (add (str "milk")))
#guard agrees (request list)
#guard agrees (request (complete (nat 1)))
#guard agrees (request (remove (nat 1)))

-- finite evaluation: a refused node, and the programs after it not reached
#guard annotate sig [] chained = table sig [] chained

-- finite evaluation: a refused head, and the statements after it visited at its environment
#guard annotate sig [] twoBad = table sig [] twoBad

end Test.Program.Annotate
