module

public import Effect4.Program.Authoring

/-!
# Program.Authoring.Defs — an operation as a definition, in one call (decisions row 328)

A library operation is a Lean function from its arguments' terms to a program: `Queue.take A`
is `TermSrc → Src NativeOp`, `Queue.offer A` is `TermSrc → TermSrc → Src NativeOp`. `Def.of`
turns one into a definition of a program's block and its invocation, together:

- the definition's body is the operation itself, applied to the parts of its request;
- the invocation has the operation's own type, so a caller writes the same call as before, and
  each site becomes one invocation.

The arity is read off the operation's type by `Params`, so no operation is written twice and no
operation of any arity needs code of its own. `Def.of` checks the parameter count against this
arity. The declared columns stay the author's: a
definition is typed by its declaration (decisions row 328, point 3), and the checker checks the
body against it.
-/

@[expose] public section

namespace Effect4.Program.Authoring

open Effect4.Program

/-- **An operation's arguments as a list**: the curried function type over argument terms that
ends in a program, read both ways. `uncurry` applies an operation to a list of terms, and
`curry` makes an operation of that type from a function of the list. -/
class Params (F : Type) where
  arity : Nat
  uncurry : F → List TermSrc → Src NativeOp
  curry : (List TermSrc → Src NativeOp) → F

/-- A program takes no argument. -/
instance : Params (Src NativeOp) where
  arity := 0
  uncurry f _ := f
  curry g := g []

/-- One more argument term in front. -/
instance {F : Type} [Params F] : Params (TermSrc → F) where
  arity := Params.arity (F := F) + 1
  uncurry f args := Params.uncurry (f (args.headD unit)) args.tail
  curry g := fun x => Params.curry fun rest => g (x :: rest)

/-- A definition and its invocation: what a module declares (`src`), and what a caller writes
(`call`). -/
structure Defined (F : Type) where
  src : DefSrc NativeOp
  call : F

/-- **An operation as a definition, in one call**: the definition's body is the operation on the
parts of its request, and the invocation has the operation's type. `params` names and types the
operation's arguments, in its order; `answer`, `error` and `requires` are the declared row.
The parameter count must equal `Params.arity`; concrete declarations discharge this check
automatically. Low-level `DefSrc` remains explicit, and invocation still resolves by name. -/
def Def.of {F : Type} [Params F] (name : String) (params : List (String × Ty)) (answer : Ty)
    (op : F) (error : Ty := .never) (requires : List Effect4.ServiceKey := [])
    (_arity : params.length = Params.arity (F := F) := by rfl) : Defined F :=
  { src := { name, params, answer, error, requires, body := Params.uncurry op }
    call := Params.curry (Def.invoke name) }

end Effect4.Program.Authoring
