module
public import Effect4.Modules.Step

/-! Typed input renaming is an authoring transformation into the existing Step data.
The transformation is a Step algebra; a fold lifts it under both private binders.
Its consumers are shared list builders and named authoring binders.
It stores no renaming function in syntax and introduces no program representation. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Modules
open Effect4.Program

/-- A typed input renaming, external to stored syntax. -/
abbrev Input.Renaming (Γ Δ : List Ty) := {t : Ty} → Input Γ t → Input Δ t

/-- Preserve a leading binder and rename the outer inputs below it. -/
def Input.liftRenaming (u : Ty) {Γ Δ : List Ty} (ρ : Input.Renaming Γ Δ) :
    Input.Renaming (u :: Γ) (u :: Δ)
  | _, .here _ _ => .here _ _
  | _, .there _ x => .there _ (ρ x)

namespace Step

/-- Reconstruct required record fields from the transformed child results. -/
def renamedFields {Γ Δ : List Ty} (ρ : Input.Renaming Γ Δ) :
    (fs : List (String × Bool × Ty)) →
      FieldResults (fun t => {Θ : List Ty} → Input.Renaming Γ Θ → Step Θ t) fs → StepFields Δ fs
  | [], _ => .nil
  | (name, false, _) :: fs, children => .cons name (children.1 ρ) (renamedFields ρ fs children.2)
  | (_, true, _) :: _, children => children.elim

/-- Renaming interprets every Step constructor into the same first-order syntax. -/
def renameAlg : StepAlgebra (fun Γ t => {Δ : List Ty} → Input.Renaming Γ Δ → Step Δ t) where
  var x := fun ρ => .var (ρ x)
  bool b := fun _ => .bool b
  nat n := fun _ => .nat n
  unit := fun _ => .unit
  not a := fun ρ => .not (a ρ)
  and a b := fun ρ => .and (a ρ) (b ρ)
  or a b := fun ρ => .or (a ρ) (b ρ)
  ite c a b := fun ρ => .ite (c ρ) (a ρ) (b ρ)
  add a b := fun ρ => .add (a ρ) (b ρ)
  sub a b := fun ρ => .sub (a ρ) (b ρ)
  lt a b := fun ρ => .lt (a ρ) (b ρ)
  eq a b := fun ρ => .eq (a ρ) (b ρ)
  isZero a := fun ρ => .isZero (a ρ)
  pair a b := fun ρ => .pair (a ρ) (b ρ)
  tuple2 a b := fun ρ => .tuple2 (a ρ) (b ρ)
  tuple3 a b c := fun ρ => .tuple3 (a ρ) (b ρ) (c ρ)
  fst p := fun ρ => .fst (p ρ)
  snd p := fun ρ => .snd (p ρ)
  some a := fun ρ => .some (a ρ)
  getOrElse x fallback := fun ρ => .getOrElse (x ρ) (fallback ρ)
  get r f := fun ρ => .get (r ρ) f
  set r f v := fun ρ => .set (r ρ) f (v ρ)
  emptyLike xs := fun ρ => .emptyLike (xs ρ)
  len xs := fun ρ => .len (xs ρ)
  snoc xs x := fun ρ => .snoc (xs ρ) (x ρ)
  append xs ys := fun ρ => .append (xs ρ) (ys ρ)
  take xs n := fun ρ => .take (xs ρ) (n ρ)
  drop xs n := fun ρ => .drop (xs ρ) (n ρ)
  head xs := fun ρ => .head (xs ρ)
  fold {_Γ} {acc item} xs init body := fun ρ =>
    .fold (xs ρ) (init ρ) (body (Input.liftRenaming acc (Input.liftRenaming item ρ)))
  record {_Γ} {fs} fields := fun ρ => .record (renamedFields ρ fs fields)
  nil := fun _ => .nil
  none := fun _ => .none
  cons x xs := fun ρ => .cons (x ρ) (xs ρ)
  sameDeferred a b := fun ρ => .sameDeferred (a ρ) (b ρ)

/-- Rename typed inputs by folding into the same Step syntax. -/
def rename {Γ Δ : List Ty} {t : Ty} (ρ : Input.Renaming Γ Δ) (e : Step Γ t) : Step Δ t :=
  cata renameAlg e ρ

end Step
end Effect4.Modules
