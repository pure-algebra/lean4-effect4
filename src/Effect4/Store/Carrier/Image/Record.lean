module

public import Effect4.Store.Carrier.Image

/-! The record image: a record's carrier written into the machine's record frame, a column of
names and a column of values (`Machine.Record.frame`). The columns are built one field at a time
(`Columns.cons`), so the image is exact by construction. The carrier fold of the schema plane
(`Effect4.Schema.Model.alg`) gives each record type its columns. -/

@[expose] public section
namespace Effect4.Store

/-- The columns of a record frame: its names, and its values for a carrier, exactly. -/
structure Columns (ρ : Type) where
  names : List String
  toVals : ρ → List Val
  ofVals : List Val → Option ρ
  ofVals_toVals : ∀ r, ofVals (toVals r) = some r
  ofVals_exact : ∀ {vs r}, ofVals vs = some r → vs = toVals r

namespace Columns

/-- No column. -/
def nil : Columns Unit where
  names := []
  toVals _ := []
  ofVals
    | [] => some ()
    | _ :: _ => none
  ofVals_toVals _ := rfl
  ofVals_exact := by
    intro vs r h
    cases vs with
    | nil => rfl
    | cons _ _ => nomatch h

/-- One more column, first: its name and the image of its values. -/
def cons {α ρ : Type} (n : String) (I : Image α) (R : Columns ρ) : Columns (α × ρ) where
  names := n :: R.names
  toVals x := I.toVal x.1 :: R.toVals x.2
  ofVals
    | v :: vs => (I.ofVal v).bind fun a => (R.ofVals vs).map fun r => (a, r)
    | [] => none
  ofVals_toVals x := by
    show (I.ofVal (I.toVal x.1)).bind (fun a => (R.ofVals (R.toVals x.2)).map fun r => (a, r)) =
      some x
    rw [I.ofVal_toVal, R.ofVals_toVals]
    rfl
  ofVals_exact := by
    intro vs x h
    cases vs with
    | nil => nomatch h
    | cons v vs =>
      change (I.ofVal v).bind (fun a => (R.ofVals vs).map fun r => (a, r)) = some x at h
      cases hv : I.ofVal v with
      | none => rw [hv] at h; nomatch h
      | some a =>
        cases hr : R.ofVals vs with
        | none => rw [hv, hr] at h; nomatch h
        | some r =>
          rw [hv, hr] at h
          cases h
          show v :: vs = I.toVal a :: R.toVals r
          rw [I.ofVal_exact hv, R.ofVals_exact hr]

end Columns

namespace Image

/-- **A record's image**: the record frame, names first, values second. A frame reads back only
under the columns' own names, in their order. -/
def record {ρ : Type} (R : Columns ρ) : Image ρ where
  toVal r := .ctor 0 [.list (R.names.map .str), .list (R.toVals r)]
  ofVal v := match v with
    | .ctor 0 [.list ns, .list vs] => if ns = R.names.map .str then R.ofVals vs else none
    | _ => none
  ofVal_toVal r := by
    show (if R.names.map Val.str = R.names.map Val.str then R.ofVals (R.toVals r) else none) =
      some r
    rw [if_pos rfl, R.ofVals_toVals]
  ofVal_exact := by
    intro v r h
    split at h
    · rename_i ns vs
      split at h
      · rename_i hns
        rw [hns, R.ofVals_exact h]
      · nomatch h
    · nomatch h

/-- The image of the empty carrier: no value, and every value refused. -/
def empty : Image Empty where
  toVal e := e.elim
  ofVal _ := none
  ofVal_toVal e := e.elim
  ofVal_exact := by intro _ _ h; nomatch h

end Image
end Effect4.Store
