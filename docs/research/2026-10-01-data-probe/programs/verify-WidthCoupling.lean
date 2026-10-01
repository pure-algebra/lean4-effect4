/-! Verifier of seat PROGRAMS (2026-10-01): decision V (a record's value shape) and the row-68
shape (TypeScript's width and depth subtyping) are coupled, which the note does not say. The tree
proves that subtyping is sound for membership (`hasTy_sub`, `Laws/Program/Admits.lean:183`;
`fits_sub`, `Laws/Program/Typed/Membership.lean:837`). With width subtyping, that law holds only if
a record value carries its labels: a positional value (V1's `.list`, or `Val.ctor`) of the wider
record is not a member of the narrower one. Miniature, no tree import; one red guard (the law
fails for positional values) and one green guard (it holds for labeled values on the same pair),
plus a proof that the labeled membership is sound for width over field lookups. Scratch. -/

set_option autoImplicit false

namespace Verify.Width

/-- A record type: labels with base types (`true` = number, `false` = string). -/
abbrev RTy := List (String × Bool)

inductive V where
  | num (n : Nat)
  | str (s : String)
  | pos (vs : List V)                    -- positional record value (V1, or `Val.ctor 0 vs`)
  | obj (kvs : List (String × V))       -- labeled record value (V2)

def baseFits : Bool → V → Bool
  | true, .num _ => true
  | false, .str _ => true
  | _, _ => false

/-- Width and depth (depth is trivial on base types): every field of `b` is in `a`. -/
def sub (a b : RTy) : Bool := b.all fun (l, t) => a.any fun (l', t') => l' == l && t' == t

/-- Positional membership: one value per field, in order. -/
def fitsPos : RTy → List V → Bool
  | [], [] => true
  | (_, t) :: fs, v :: vs => baseFits t v && fitsPos fs vs
  | _, _ => false

def hasTyPos (r : RTy) : V → Bool
  | .pos vs => fitsPos r vs
  | _ => false

/-- Labeled membership: every field of the type is found by its label. -/
def hasTyObj (r : RTy) : V → Bool
  | .obj kvs => r.all fun (l, t) => match kvs.lookup l with
    | some v => baseFits t v
    | none => false
  | _ => false

def wide : RTy := [("id", true), ("name", false)]
def narrow : RTy := [("id", true)]

#guard sub wide narrow = true
-- RED: the positional value of the wider record is not a member of the narrower one
#guard hasTyPos wide (.pos [.num 2, .str "bob"]) = true
#guard hasTyPos narrow (.pos [.num 2, .str "bob"]) = false
-- GREEN: the labeled value is a member of both
#guard hasTyObj wide (.obj [("id", .num 2), ("name", .str "bob")]) = true
#guard hasTyObj narrow (.obj [("id", .num 2), ("name", .str "bob")]) = true

/-- Labeled membership is sound for width subtyping. -/
theorem hasTyObj_sub (a b : RTy) (kvs : List (String × V)) (hs : sub a b = true)
    (ha : hasTyObj a (.obj kvs) = true) : hasTyObj b (.obj kvs) = true := by
  simp only [hasTyObj, List.all_eq_true] at ha ⊢
  simp only [sub, List.all_eq_true, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hs
  intro p hp
  obtain ⟨q, hq, hl, ht⟩ := hs p hp
  have hqa := ha q hq
  rw [hl, ht] at hqa
  exact hqa

#print axioms hasTyObj_sub

end Verify.Width
