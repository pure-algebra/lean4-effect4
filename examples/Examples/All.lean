import Examples.Todo
import Examples.CachedTodo

/-!
# The examples, as one list

Each example is one application, a module `Examples.<Name>` beside this one. `all` lists them,
and `lake exe effect4` reads each as a group under its application's name. Adding an example is
one module, one import here and one entry of `all`.
-/

namespace Examples

open Effect4.Program Effect4.Program.Authoring

/-- **The examples**, in the order the index lists them. -/
def all : List (Application NativeOp) :=
  [Todo.application, CachedTodo.application]

end Examples
