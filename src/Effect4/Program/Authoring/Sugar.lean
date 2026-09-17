import Effect4.Program.Authoring.Lifts
import Effect4.Program.Authoring.Rows

/-!
# Program.Authoring.Sugar — binders over a fresh name, and derived forms

The native rows' wrappers (`Ref.make`, `Deferred.await`) are generated from the row table
(`Authoring/Rows.lean`) and the derived forms (`Forms.tapContinuation`, `Forms.ensuring`)
from the form table (`Authoring/Forms.lean`, each pinned against the printer's expansion);
this module is the five conveniences that are neither: the binders over a fresh name and
the short spellings `flatMap`, `andThen`, `map`, `ifElse`, `Src`-level functions over the
generated lifts with no constructor and no second expansion owner.
-/

namespace Effect4.Program.Authoring

open Effect4.Program

/-! ## Binders as Lean functions over a fresh name.

The fresh name is minted from the scope's length, so it can shadow nothing an author wrote
with a different spelling and resolves to itself at the nearest binder. -/

/-- `bindWith first (fun r => rest)` is `bind "_<level>" first rest` with `r` the variable. -/
def bindWith {Op : Type} (first : Src Op) (rest : TermSrc → Src Op) : Src Op := fun env p =>
  let x := "_" ++ toString env.names.length
  bind x first (rest (var x)) env p

/-- `Effect.flatMap` under its Effect name. -/
def flatMap {Op : Type} (answer : String) (first rest : Src Op) : Src Op := bind answer first rest

/-- `Effect.andThen` with a discarded answer. -/
def andThen {Op : Type} (first rest : Src Op) : Src Op := bind "_" first rest

/-- `Effect.map` through a pure atom: `bind` then `succeed` of the atom applied to the answer. -/
def map {Op : Type} (atom : String) (effect : Src Op) : Src Op :=
  bindWith effect fun v => succeed (app atom [v])

/-- `Effect.if`: `if` is a Lean keyword. -/
def ifElse {Op : Type} (test : TermSrc) (thenB elseB : Src Op) : Src Op :=
  selectBool test thenB elseB

end Effect4.Program.Authoring
