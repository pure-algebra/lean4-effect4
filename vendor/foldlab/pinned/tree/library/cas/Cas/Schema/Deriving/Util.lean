import Cas.Schema.Described

/-!
# Runtime utilities for schema derivation

These helpers let the deriving handler infer a field's schema from its
getter. Optionality is a property of the field type: `Option α` becomes
an omittable field whose present value is described by `α`.
-/

namespace Cas.Schema.Deriving

/-- The schema representation of one native structure field. -/
class FieldDescription (α : Type u) where
  optional : Bool
  code : Ast
  wf : code.WF
  toEl : α → cond optional (Option (El code)) (El code)
  ofEl : cond optional (Option (El code)) (El code) → α
  ofEl_toEl : ∀ x, ofEl (toEl x) = x
  toEl_ofEl : ∀ x, toEl (ofEl x) = x

instance (priority := low) {α : Type u} [d : Described α] :
    FieldDescription α where
  optional := false
  code := d.code
  wf := d.wf
  toEl := d.toEl
  ofEl := d.ofEl
  ofEl_toEl := d.ofEl_toEl
  toEl_ofEl := d.toEl_ofEl

instance {α : Type u} [d : Described α] : FieldDescription (Option α) where
  optional := true
  code := d.code
  wf := d.wf
  toEl := Option.map d.toEl
  ofEl := Option.map d.ofEl
  ofEl_toEl := by
    intro x
    cases x with
    | none => rfl
    | some x => simp only [Option.map_some, d.ofEl_toEl]
  toEl_ofEl := by
    intro x
    cases x with
    | none => rfl
    | some x => simp only [Option.map_some, d.toEl_ofEl]

/-- Build the code-level field triple while inferring its native type
from a structure getter. -/
def fieldSpec {ρ : Type v} {α : Type u} [d : FieldDescription α]
    (name : String) (_getter : ρ → α) : String × Bool × Ast :=
  (name, d.optional, d.code)

theorem fieldWF {ρ : Type v} {α : Type u} [d : FieldDescription α]
    (_getter : ρ → α) : d.code.WF :=
  d.wf

def fieldToEl {ρ : Type v} {α : Type u} [d : FieldDescription α]
    (getter : ρ → α) (x : ρ) :
    cond d.optional (Option (El d.code)) (El d.code) :=
  d.toEl (getter x)

def fieldOfEl {ρ : Type v} {α : Type u} [d : FieldDescription α]
    (_getter : ρ → α)
    (x : cond d.optional (Option (El d.code)) (El d.code)) : α :=
  d.ofEl x

/-! ## Constructor alternatives — the inductive path

A STRUCTURE field arrives with a getter, and the getter's return type
is what names its `FieldDescription`. A CONSTRUCTOR field has no
getter, so the native type is passed in directly. Same class, same
instance, same three operations — one different way in, so the
structure path's helpers stay byte-identical. -/

/-- The code-level field triple for a constructor field, named by its
type rather than by a getter. -/
def altSpec (name : String) (α : Type u) [d : FieldDescription α] :
    String × Bool × Ast :=
  (name, d.optional, d.code)

theorem altWF (α : Type u) [d : FieldDescription α] : d.code.WF := d.wf

/-- The type is inferred from the constructor binder here: inside a
generated match alternative the binder already carries it. -/
def altToEl {α : Type u} [d : FieldDescription α] (x : α) :
    cond d.optional (Option (El d.code)) (El d.code) :=
  d.toEl x

/-- The type is inferred from the constructor's argument position
here — the constructor is what fixes it. -/
def altOfEl {α : Type u} [d : FieldDescription α]
    (x : cond d.optional (Option (El d.code)) (El d.code)) : α :=
  d.ofEl x

/-- Rebuild the right-nested product used by `ElFields`. This explicit
identity traversal gives generated inverse proofs one stable lemma
instead of a variable-length chain of product-eta rewrites. -/
def rebuildFields : ∀ (fs : List (String × Bool × Ast)),
    ElFields fs → ElFields fs
  | [], _ => ()
  | _ :: fs, x => (x.1, rebuildFields fs x.2)

theorem rebuildFields_eq : ∀ (fs : List (String × Bool × Ast))
    (x : ElFields fs), rebuildFields fs x = x
  | [], x => by cases x; rfl
  | _ :: fs, x => by
    apply Prod.ext
    · rfl
    · exact rebuildFields_eq fs x.2

end Cas.Schema.Deriving
