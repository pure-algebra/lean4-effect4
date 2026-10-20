import Effect4.Program.ProfileSupport
import Effect4.Laws.Program.PathFold
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.ProfileSupport — the profile's refusal is complete against its judgment

Profile support (`Program/ProfileSupport.lean`) refuses with a located refusal. Here it is
complete against the judgment it locates: the refusal is absent exactly when the profile supports
the value, and exactly when it supports every natural literal of the program.

- **A value.** `supports` is the judgment unlocated: an algebra of the value tree's fold whose
  leaves ask `admitsNat`. Absence of the refusal, `Option.isNone ∘ valueRefusal`, is a
  homomorphism into it, so the two folds agree by the fold's uniqueness (`hom_eq_cata_val`).
- **A program.** The refusal reads each node's literals through the path fold. Through `isNone`,
  and through `List.all`, the path fold is the fold with no path (`foldMapAt_eff_fuse`), so the
  refusal is absent exactly when the literal fold's naturals are all admitted.

## Placement

- Concept: translation-simulation (`docs/core/semantics.md` §2.10); property: a face equals the
  reference inside its profile and refuses outside it (DI-56), here the refusal at ingress.
- Question: registry claim `profile-support-located` (role decidability), pointer
  `valueRefusal_eq_none_iff`, with `literalRefusal_eq_none_iff` beside it. Consumers: the claim,
  and the TypeScript face's certificates (`ModuleEmission.inProfile`, `ModuleReading.inProfile`),
  whose premise `rc112.literalRefusal program = none` has by it the value the literal check had.
- Reach: every profile, every value tree and every program over the native operations. Decisions
  rows 108 and 417 (1), DI-56: the bound is the ingress rule.
- Does not establish: which face reads a supported value, or that it reads it exactly; arithmetic
  inside a run, which the builtin rows' crossing refuses until M4; the native carrier's own domain
  (a natural below zero, a string that is not UTF-8), which the host checks (`Eff_val.valid`).
- Unlocks: R8's refusal outside the profile, at ingress, for the TypeScript face, the tool's JSON
  and the native engine and kit, through one lowered judgment.
-/

set_option autoImplicit false

namespace Effect4.Program.ProfileData

open Effect4

/-- **Profile support, unlocated**: every natural of the value tree inside the bound. The
specification the located refusal is complete against (`valueRefusal_eq_none_iff`). -/
def supportsAlgebra (profile : ProfileData) : Store.ValAlgebra (fun _ => Bool) where
  val_unit := true
  val_bool _ := true
  val_nat n := profile.admitsNat n
  val_str _ := true
  val_bytes _ := true
  val_list bs := bs.all id
  val_pair a b := a && b
  val_none := true
  val_some a := a
  val_ctor i bs := profile.admitsNat i && bs.all id
  val_ref _ _ := true
  val_handle _ key := profile.admitsNat key
  val_negInt n := profile.admitsNat (n + 1)
  val_float _ := true

/-- **The profile supports the value**: the unlocated judgment's fold. -/
def supports (profile : ProfileData) (v : Store.Val) : Bool :=
  Store.cata_val profile.supportsAlgebra v

/-- A choice of the first refusal is absent when both sides are. A step of both claims' laws. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem orElse_isNone {α : Type} (a b : Option α) : (a <|> b).isNone = (a.isNone && b.isNone) := by
  cases a <;> rfl

/-- The leaf's refusal is absent exactly when the leaf is admitted. A step of
`valueRefusal_isNone`. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem natRefusal_isNone (profile : ProfileData) (n : Nat) :
    (profile.natRefusal n).isNone = profile.admitsNat n := by
  unfold natRefusal
  cases profile.admitsNat n <;> rfl

/-- The children's first refusal is absent exactly when every child's is. A step of
`valueRefusal_isNone`. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem firstUnder_isNone : ∀ (i : Nat) (rs : List (Option ProfileRefusal)),
    (firstUnder i rs).isNone = rs.all Option.isNone
  | _, [] => rfl
  | i, r :: rs => by
    cases r <;> simp only [firstUnder, orElse_isNone, Option.map_none, Option.map_some,
      Option.isNone_none, Option.isNone_some, firstUnder_isNone (i + 1) rs, List.all_cons]

/-- **The absence of the refusal is a homomorphism into the unlocated judgment**: at each node it
is the node's own leaf and its children's absences. A step of `valueRefusal_isNone`. -/
def refusalHom (profile : ProfileData) : Store.ValHom profile.supportsAlgebra where
  f_val v := (profile.valueRefusal v).isNone
  h_val_unit := rfl
  h_val_bool _ := rfl
  h_val_nat n := natRefusal_isNone profile n
  h_val_str _ := rfl
  h_val_bytes _ := rfl
  h_val_list xs := by
    simp only [valueRefusal, Store.cata_val_list, valueAlgebra, supportsAlgebra, firstUnder_isNone,
      List.all_map]
    rfl
  h_val_pair a b := by
    simp only [valueRefusal, Store.cata_val_pair, valueAlgebra, supportsAlgebra, firstUnder_isNone,
      List.all_cons, List.all_nil, Bool.and_true]
  h_val_none := rfl
  h_val_some a := by
    simp only [valueRefusal, Store.cata_val_some, valueAlgebra, supportsAlgebra, firstUnder_isNone,
      List.all_cons, List.all_nil, Bool.and_true]
  h_val_ctor i xs := by
    simp only [valueRefusal, Store.cata_val_ctor, valueAlgebra, supportsAlgebra, orElse_isNone,
      natRefusal_isNone, firstUnder_isNone, List.all_map]
    rfl
  h_val_ref _ _ := rfl
  h_val_handle _ key := natRefusal_isNone profile key
  h_val_negInt n := by
    show (if n < profile.natBound then none else some _ : Option ProfileRefusal).isNone =
      decide (n + 1 ≤ profile.natBound)
    split
    · next h => exact (decide_eq_true (Nat.succ_le_of_lt h)).symm
    · next h => exact (decide_eq_false fun le => h (Nat.lt_of_succ_le le)).symm
  h_val_float _ := rfl

/-- The refusal is absent exactly when the unlocated judgment holds, as one Boolean: the two folds
agree because their algebras do. A step of `valueRefusal_eq_none_iff`. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem valueRefusal_isNone (profile : ProfileData) (v : Store.Val) :
    (profile.valueRefusal v).isNone = profile.supports v :=
  Store.hom_eq_cata_val profile.refusalHom v

/-- **The profile's refusal of a value is absent exactly when the profile supports it.** The
pointer of `profile-support-located`. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem valueRefusal_eq_none_iff (profile : ProfileData) (v : Store.Val) :
    profile.valueRefusal v = none ↔ profile.supports v = true := by
  rw [← valueRefusal_isNone, Option.isNone_iff_eq_none]

/-- A node's refusal is absent exactly when each of its literals is admitted, at any address. A
step of `literalRefusal_isNone`. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem literalsRefusal_isNone (profile : ProfileData) (literals address : List Nat) :
    (profile.literalsRefusal literals address).isNone = literals.all profile.admitsNat := by
  unfold literalsRefusal
  induction literals with
  | nil => rfl
  | cons n ns ih =>
    cases h : profile.admitsNat n <;>
      simp only [List.find?_cons, h, Bool.not_true, Bool.not_false, Option.map_some,
        Option.isNone_some, List.all_cons, Bool.true_and, Bool.false_and, ih]

/-- A node's own literals, by its sort: the literal fold's and the judgment's reading of a node,
as one function of the family (the path fold's laws quantify over one). A step of
`literalRefusal_isNone`. -/
def nodeLiterals : (fam : EffFam) → EffSelfCarrier NativeOp fam → List Nat
  | .eff, n => (readArgs_eff literalReader n).flatten
  | .stmt, n => (readArgs_stmt literalReader n).flatten
  | .stmts, n => (readArgs_stmts literalReader n).flatten
  | .effs, n => (readArgs_effs literalReader n).flatten
  | .action, n => (readArgs_action literalReader n).flatten
  | .layer, n => (readArgs_layer literalReader n).flatten
  | .layers, n => (readArgs_layers literalReader n).flatten

/-- The program's refusal is absent exactly when every literal of the literal fold is admitted,
as one Boolean. A step of `literalRefusal_eq_none_iff`. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem literalRefusal_isNone (profile : ProfileData) (program : NativeEff) :
    (profile.literalRefusal program).isNone = (natLiterals program).all profile.admitsNat :=
  have refusal := foldMapAt_eff_fuse Option.isNone (unit := none) (op := (· <|> ·))
    (unit' := true) (op' := (· && ·)) orElse_isNone
    (f := fun fam n a => profile.literalsRefusal (nodeLiterals fam n) a)
    (g := fun fam n => (nodeLiterals fam n).all profile.admitsNat)
    (fun fam n a => literalsRefusal_isNone profile (nodeLiterals fam n) a) program []
  have admitted := foldMapAt_eff_fuse (fun l : List Nat => l.all profile.admitsNat) (unit := [])
    (op := (· ++ ·)) (unit' := true) (op' := (· && ·)) (fun _ _ => List.all_append)
    (f := fun fam n (_ : List Nat) => nodeLiterals fam n)
    (g := fun fam n => (nodeLiterals fam n).all profile.admitsNat) (fun _ _ _ => rfl) program []
  have literals := foldMapAt_eff_fuse (fun l : List Nat => l) (unit := []) (op := (· ++ ·))
    (unit' := []) (op' := (· ++ ·)) (fun _ _ => rfl)
    (f := fun fam n (_ : List Nat) => nodeLiterals fam n)
    (g := fun fam n => nodeLiterals fam n) (fun _ _ _ => rfl) program []
  refusal.trans (admitted.symm.trans (congrArg (fun l : List Nat => l.all profile.admitsNat)
    literals))

/-- **The profile's refusal of a program is absent exactly when the profile supports every
natural literal the program states** (`natLiterals`). Beside `profile-support-located`'s pointer;
at `rc112` it gives the TypeScript face's restated premise the literal check's value. -/
@[semantics "translation-simulation" (requirement := R8)]
theorem literalRefusal_eq_none_iff (profile : ProfileData) (program : NativeEff) :
    profile.literalRefusal program = none ↔ (natLiterals program).all profile.admitsNat = true := by
  rw [← literalRefusal_isNone, Option.isNone_iff_eq_none]

end Effect4.Program.ProfileData
