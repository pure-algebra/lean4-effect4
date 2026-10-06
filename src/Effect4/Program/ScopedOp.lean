module

public import Effect4.Machine.Term

/-!
# Program.ScopedOp — the scope of an operation's own data

`Eff Op` is generic in its operation alphabet, so the scope check (`Eff.scopedAt`,
`Program/Scoped.lean`) cannot see inside an operation: the alphabet answers for it, through
`ScopedOp`. Scope is syntax, decided from the program alone. The authoring laws state it of every
elaborated program with no signature at hand (`Src.Scoped`, `Laws/Program/Authoring.lean`), so it
is a class of the alphabet and not a field of `Signature` (state plan T0,
`docs/research/2026-10-04-claude-lead/state-any-type-plan.md`).

The same class maps an operation's term (`mapTerm`). The generated frontier map (`frontierMap`,
`Program/Fold.lean`) applies it, so `Eff.weaken` shifts an operation's binder term with the rest
of the program (state plan T3b). An operation that carries no term is fixed.

The same class reads an operation's term (`term?`). The raw annotation collector
(`Formation.argumentAnnotations`, `Program/Formation.lean`) reads it, so a record declaration or
a list fold's stated type inside an operation's term is a program annotation: raw formation and
the integer scan reach it at a located path (decisions row 228, the fold's addendum 2).

The same class reads an operation's type arguments (`typeArgs`). The raw annotation collector
reads them too, so the types of `Deferred.make<A, E>()` are program annotations: raw formation,
the integer scan, the module's representability check and its class table reach them at a located
path (decisions row 212, the state plan's T5, part B).

The native alphabet's instance is beside `NativeOp` (`Program/Native.lean`); the unit alphabet's
is below. Scope is not typing: `ScopedOp` says which variables an operation's data may name, and
nothing about their types.
-/

@[expose] public section

namespace Effect4.Program

/-- The scope of an operation's own data: `scopedAt op n` holds when every variable the
operation carries is in scope at a `perform` node of level `n`, the level the scope fold
(`scopedAlgebra`) gives that node.

The convention for a binder term. A term the operation carries and evaluates at
`env ++ [current]` is checked at level `n + 1`:
- the current value is the variable at index `n`;
- a variable below `n` is an outer capture, a value bound around the `perform`;
- a variable at `n + 1` or above is out of scope, and the check answers `false`.

This is the binder convention of `iterate`'s step (`tools/Effect4Gen/binders.json`: the step is
checked at `n + 1`, the cursor at index `n`). An operation that carries no term answers `true`. -/
class ScopedOp (Op : Type) where
  /-- Every variable the operation carries is in scope at a `perform` node of level `n`. -/
  scopedAt : Op → Nat → Bool
  /-- The operation with its own binder term mapped by `g`; the default fixes an operation that
  carries no term. Weakening maps every term slot of a program by `Term.weaken cut`, and an
  operation's term is such a slot: its current value at index `n` moves with the node's level. -/
  mapTerm : (Term → Term) → Op → Op := fun _ op => op
  /-- The binder term the operation carries, when it carries one: the reading view of what
  `mapTerm` rewrites. The default is an operation that carries none. An operation's type
  arguments are types and no term, so this view does not show them: `typeArgs` does. -/
  term? : Op → Option Term := fun _ => none
  /-- The type arguments the operation carries: the reading view of what a signature prints on
  the call's head (`Signature.typeArgsOf`, `Program/Typing/Rules.lean`). They are types of the
  program, so the raw annotation collector reads them (`Formation.argumentAnnotations`,
  decisions row 212). The default is an operation that carries none. The term map leaves them
  as they are: a type binds no term variable. -/
  typeArgs : Op → List Ty := fun _ => []

/-- The unit alphabet carries no data. The scope fold's guards and the scope-preservation
guards instantiate `Eff` at it. -/
instance : ScopedOp Unit where
  scopedAt _ _ := true

end Effect4.Program
