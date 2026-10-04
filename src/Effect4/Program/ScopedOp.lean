module

/-!
# Program.ScopedOp — the scope of an operation's own data

`Eff Op` is generic in its operation alphabet, so the scope check (`Eff.scopedAt`,
`Program/Scoped.lean`) cannot see inside an operation: the alphabet answers for it, through
`ScopedOp`. Scope is syntax, decided from the program alone. The authoring laws state it of every
elaborated program with no signature at hand (`Src.Scoped`, `Laws/Program/Authoring.lean`), so it
is a class of the alphabet and not a field of `Signature` (state plan T0,
`docs/research/2026-10-04-claude-lead/state-any-type-plan.md`).

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

/-- The unit alphabet carries no data. The scope fold's guards and the scope-preservation
guards instantiate `Eff` at it. -/
instance : ScopedOp Unit := ⟨fun _ _ => true⟩

end Effect4.Program
