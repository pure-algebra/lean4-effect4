/-! Verifier of seat TREE (2026-10-01): the third record design the seat's dichotomy omits.

TREE-D08 offers two coherent designs: exact records (positional values, no width rule) and
width records (values carry names). rc.112's own Schema decoder takes a third road: a struct
decode **strips** the keys its type does not name (`onExcessProperty: "ignore"` is the default,
`vendor/effect-4.0.0-rc.112/src/SchemaAST.ts:445`, applied at `:2250-2290`), so a decoded value
has exactly its type's fields, and width is a projection at the boundary.

This file is a small, self-contained model of that third road: positional exact values, the
width-and-depth `sub`, and a projection `coerce a v b` from a value at `a` to a value at `b`.
The law that replaces `fits_sub` is `fits_coerce`: `sub a b → Fits v a → Fits (coerce a v b) b`.
It is proved here for the model (nat, string, records), by structural recursion on the target.
It is not the tree's judgment: no handles, no worlds, no unions. Scratch, not in the tree. -/

set_option autoImplicit false

namespace VerifyTree.Coerce

inductive T
  | nat
  | str
  | record (fields : List (String × T))

inductive V
  | unit
  | nat (n : Nat)
  | str (s : String)
  | ctor (args : List V)

-- Positional exact membership: a record value has one argument per field, in field order.
mutual
def Fits (v : V) : T → Prop
  | .nat => match v with | .nat _ => True | _ => False
  | .str => match v with | .str _ => True | _ => False
  | .record fs => match v with | .ctor args => FitsF args fs | _ => False
def FitsF : List V → List (String × T) → Prop
  | [], [] => True
  | v :: vs, (_, t) :: fs => Fits v t ∧ FitsF vs fs
  | _, _ => False
end

/-- The first field type of a name. -/
def findT (m : String) : List (String × T) → Option T
  | [] => none
  | (n, s) :: fs => if n = m then some s else findT m fs

/-- The first field of a name, with the positional argument beside it. -/
def find (m : String) : List (String × T) → List V → Option (T × V)
  | (n, s) :: fs, w :: ws => if n = m then some (s, w) else find m fs ws
  | _, _ => none

-- Width and depth: every field the target names is present in the source at a subtype.
-- Structural on the target.
mutual
def sub (a : T) : T → Bool
  | .nat => match a with | .nat => true | _ => false
  | .str => match a with | .str => true | _ => false
  | .record gs => match a with | .record fs => subF fs gs | _ => false
def subF (fs : List (String × T)) : List (String × T) → Bool
  | [] => true
  | (m, t) :: gs =>
    (match findT m fs with
     | some s => sub s t
     | none => false) && subF fs gs
end

-- The projection: a record value at `a` read at `b` keeps, in `b`'s order, the argument of
-- each field `b` names, itself projected. Structural on the target.
mutual
def coerce (a : T) (v : V) : T → V
  | .record gs =>
    match a, v with
    | .record fs, .ctor args => .ctor (coerceF fs args gs)
    | _, _ => v
  | _ => v
def coerceF (fs : List (String × T)) (args : List V) : List (String × T) → List V
  | [] => []
  | (m, t) :: gs =>
    (match find m fs args with
     | some (s, w) => coerce s w t
     | none => .unit) :: coerceF fs args gs
end

/-- A fitting argument list answers every name its types answer, with a fitting argument. -/
theorem find_fits (m : String) : ∀ (fs : List (String × T)) (args : List V) (s : T),
    FitsF args fs → findT m fs = some s → ∃ w, find m fs args = some (s, w) ∧ Fits w s := by
  intro fs
  induction fs with
  | nil => intro args s _ h; simp only [findT, reduceCtorEq] at h
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    intro args s hargs hfind
    cases args with
    | nil => exact hargs.elim
    | cons w ws =>
      obtain ⟨hw, hws⟩ := hargs
      by_cases hn : n = m
      · simp only [findT, hn, ↓reduceIte, Option.some.injEq] at hfind
        subst hfind
        exact ⟨w, by simp only [find, hn, ↓reduceIte], hw⟩
      · simp only [findT, hn, ↓reduceIte] at hfind
        obtain ⟨w', hfound, hfit⟩ := ih ws s hws hfind
        exact ⟨w', by simp only [find, hn, ↓reduceIte]; exact hfound, hfit⟩

-- The law of the third design: subsumption is a projection that lands in the target.
mutual
theorem fits_coerce (a : T) (v : V) : (b : T) → sub a b = true → Fits v a → Fits (coerce a v b) b
  | .nat, h, hv => by
    cases a with
    | nat => simpa only [coerce] using hv
    | str => simp only [sub] at h; exact Bool.noConfusion h
    | record fs => simp only [sub] at h; exact Bool.noConfusion h
  | .str, h, hv => by
    cases a with
    | nat => simp only [sub] at h; exact Bool.noConfusion h
    | str => simpa only [coerce] using hv
    | record fs => simp only [sub] at h; exact Bool.noConfusion h
  | .record gs, h, hv => by
    cases a with
    | nat => simp only [sub] at h; exact Bool.noConfusion h
    | str => simp only [sub] at h; exact Bool.noConfusion h
    | record fs =>
      simp only [sub] at h
      cases v with
      | ctor args =>
        simp only [Fits] at hv
        simp only [coerce, Fits]
        exact fitsF_coerceF fs args hv gs h
      | unit => simp only [Fits] at hv
      | nat n => simp only [Fits] at hv
      | str s => simp only [Fits] at hv
theorem fitsF_coerceF (fs : List (String × T)) (args : List V) (hargs : FitsF args fs) :
    (gs : List (String × T)) → subF fs gs = true → FitsF (coerceF fs args gs) gs
  | [], _ => by simp only [coerceF, FitsF]
  | (m, t) :: gs, h => by
    simp only [subF, Bool.and_eq_true] at h
    obtain ⟨hhead, hrest⟩ := h
    cases hfind : findT m fs with
    | none => rw [hfind] at hhead; exact Bool.noConfusion hhead
    | some s =>
      rw [hfind] at hhead
      obtain ⟨w, hw, hfit⟩ := find_fits m fs args s hargs hfind
      simp only [coerceF, hw, FitsF]
      exact ⟨fits_coerce s w t hhead hfit, fitsF_coerceF fs args hargs gs hrest⟩
end

/-! The seat's example, read in this design: `{ id; name } ≤ { id }`, the wider value projects
to one argument and fits the narrower record. Without the projection it does not fit
(the seat's `positional_width_unsound`, here as a red control). -/

def wide : T := .record [("id", .nat), ("name", .str)]
def narrow : T := .record [("id", .nat)]
def ada : V := .ctor [.nat 7, .str "Ada"]

theorem wide_sub_narrow : sub wide narrow = true := by decide

theorem ada_fits_wide : Fits ada wide := ⟨trivial, trivial, trivial⟩

theorem ada_projects : coerce wide ada narrow = .ctor [.nat 7] := rfl

theorem projected_fits : Fits (coerce wide ada narrow) narrow :=
  fits_coerce wide ada narrow wide_sub_narrow ada_fits_wide

/-- Red control: positional values with the width rule and no projection. -/
theorem unprojected_not_fits : ¬ Fits ada narrow := by
  intro h
  simp only [ada, narrow, Fits, FitsF] at h
  exact h.2

end VerifyTree.Coerce

#print axioms VerifyTree.Coerce.find_fits
#print axioms VerifyTree.Coerce.fits_coerce
#print axioms VerifyTree.Coerce.fitsF_coerceF
#print axioms VerifyTree.Coerce.ada_projects
#print axioms VerifyTree.Coerce.projected_fits
#print axioms VerifyTree.Coerce.unprojected_not_fits
