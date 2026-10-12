import Effect4.Laws.Data.ListRel
import Effect4.Laws.Machine.Book
import Effect4.Laws.Step.Reading
import Effect4.Laws.Program.Typed

/-!
# Effect4.Laws.Data.ListRelConnectors

Owner: the connectors to the shared pointwise list relation,
`Effect4.ListRel` (`Laws/Data/ListRel.lean`). Item 11, step 1, of
`docs/research/2026-10-11-machine-models/CODEX-PROMPT.md`.

- `Book.lean` uses the shared relation directly.
- `Reading.lean` uses the shared relation directly.
- `Program.Fits` (`Laws/Program/Typed.lean`) is the relation at `Val.hasTy`.

The machine and reading connectors are reflexive. The Fits connector relates its remaining copy to the shared relation.
A caller moves to the shared relation through its connector before its copy goes.

What this module does not claim: anything beyond the three equivalences.
-/

set_option autoImplicit false

namespace Effect4.Data

universe w

/-- `Book.lean`'s relation is the shared one. -/
theorem machineListRel_iff {α β : Type w} {R : α → β → Prop} {l : List α} {l' : List β} :
    _root_.Effect4.ListRel R l l' ↔ _root_.Effect4.ListRel R l l' := Iff.rfl

/-- `Reading.lean`'s relation is the shared one. -/
theorem pointwise_iff {α β : Type} {r : α → β → Prop} {l : List α} {l' : List β} :
    _root_.Effect4.ListRel r l l' ↔ _root_.Effect4.ListRel r l l' := Iff.rfl

/-- An environment fits its typing exactly when the shared relation at `Val.hasTy` holds. -/
theorem fits_iff {env : List Store.Val} {tys : Program.TyEnv} :
    Program.Fits env tys ↔
      _root_.Effect4.ListRel (fun v t => Program.Val.hasTy v t = true) env tys := by
  constructor
  · intro h
    induction h with
    | nil => exact .nil
    | cons hd _ ih => exact .cons hd ih
  · intro h
    induction h with
    | nil => exact .nil
    | cons hd _ ih => exact .cons hd ih

end Effect4.Data
