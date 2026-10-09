import Effect4.Program.LayerView

/-!
# The view's folds: fusion, the product, and fold induction

Slice A of the view plane's algebra audit (`docs/research/2026-10-09-view-algebra-audit.md`). The
view reads a program by folds of generic layers (`EffAlgebra.ofLayer`, `Program/LayerView.lean`).
This module states, once, the laws that let every channel of the view compose as the program
does:

- **fusion** (`cata_fusion`): a map that commutes with each layer commutes with the whole fold.
  Its proof is the core's uniqueness (`hom_eq_cata_eff` and its siblings): the map after the fold
  is a homomorphism of the other algebra, so it is that algebra's fold;
- **the product** (`cata_prod`): the fold of two layers side by side is the pair of their folds.
  So several readings of one program come from one fold, and each can be stated alone;
- **fold induction** (`cata_keeps`): a property of the carrier that each layer keeps, when the
  children have it, holds of every fold.

The product and fold induction are both fusion: the first along each projection, the second
along the map out of the subtype of the carrier that has the property. The laws are a tool's,
outside the semantics registry (decisions row 334, point 3).
-/

namespace Tools.View.Algebra

open Effect4.Program

universe u

variable {Op : Type}

/-- A generic layer into the carrier `R`: one function of a sort, a constructor's name and its
arguments by sort. -/
abbrev Layer (Op : Type) (R : EffFam → Type u) : Type u :=
  (fam : EffFam) → String → List (ArgF Op R) → R fam

/-- An argument with its child mapped; a leaf is itself. -/
def mapChild {R S : EffFam → Type u} (f : (fam : EffFam) → R fam → S fam) : ArgF Op R → ArgF Op S
  | .child fam r => .child fam (f fam r)
  | .term v => .term v
  | .cause v => .cause v
  | .op v => .op v
  | .nat v => .nat v
  | .mode v => .mode v
  | .bool v => .bool v
  | .key v => .key v
  | .decision v => .decision v
  | .optTy v => .optTy v
  | .decls v => .decls v
  | .forkOptions v => .forkOptions v
  | .optTerm v => .optTerm v
  | .lit v => .lit v
  | .path v => .path v

/-- The fold of a layer, at each sort. -/
abbrev fold {R : EffFam → Type u} (l : Layer Op R) : (fam : EffFam) → EffSelfCarrier Op fam → R fam :=
  cataFam (EffAlgebra.ofLayer l)

/-- A map after a fold, as a homomorphism of the other layer's algebra, when the map commutes
with each layer. Every equation is the hypothesis at that constructor. -/
def fusionHom {R S : EffFam → Type u} (l1 : Layer Op R) (l2 : Layer Op S)
    (φ : (fam : EffFam) → R fam → S fam)
    (hφ : ∀ fam ctor args, φ fam (l1 fam ctor args) = l2 fam ctor (args.map (mapChild φ))) :
    EffHom (EffAlgebra.ofLayer l2) := by
  apply EffHom.mk (f_eff := fun e => φ .eff (fold l1 .eff e)) (f_stmt := fun e => φ .stmt (fold l1 .stmt e))
    (f_stmts := fun e => φ .stmts (fold l1 .stmts e)) (f_effs := fun e => φ .effs (fold l1 .effs e))
    (f_action := fun e => φ .action (fold l1 .action e)) (f_layer := fun e => φ .layer (fold l1 .layer e))
    (f_layers := fun e => φ .layers (fold l1 .layers e))
  all_goals
    intros
    exact hφ _ _ _

/-- **Fusion.** A map that commutes with each layer commutes with the fold: the map after the
first layer's fold is the second layer's fold, at every sort. -/
theorem cata_fusion {R S : EffFam → Type u} (l1 : Layer Op R) (l2 : Layer Op S)
    (φ : (fam : EffFam) → R fam → S fam)
    (hφ : ∀ fam ctor args, φ fam (l1 fam ctor args) = l2 fam ctor (args.map (mapChild φ))) :
    ∀ fam e, φ fam (fold l1 fam e) = fold l2 fam e
  | .eff, e => hom_eq_cata_eff (fusionHom l1 l2 φ hφ) e
  | .stmt, e => hom_eq_cata_stmt (fusionHom l1 l2 φ hφ) e
  | .stmts, e => hom_eq_cata_stmts (fusionHom l1 l2 φ hφ) e
  | .effs, e => hom_eq_cata_effs (fusionHom l1 l2 φ hφ) e
  | .action, e => hom_eq_cata_action (fusionHom l1 l2 φ hφ) e
  | .layer, e => hom_eq_cata_layer (fusionHom l1 l2 φ hφ) e
  | .layers, e => hom_eq_cata_layers (fusionHom l1 l2 φ hφ) e

/-! ## The product -/

/-- Two layers side by side: each reads the arguments with its own component of every child. -/
def Layer.prod {R S : EffFam → Type u} (l1 : Layer Op R) (l2 : Layer Op S) :
    Layer Op (fun fam => R fam × S fam) :=
  fun fam ctor args =>
    (l1 fam ctor (args.map (mapChild fun _ x => x.1)), l2 fam ctor (args.map (mapChild fun _ x => x.2)))

/-- **The product.** The fold of two layers side by side is the pair of their folds. -/
theorem cata_prod {R S : EffFam → Type u} (l1 : Layer Op R) (l2 : Layer Op S) (fam : EffFam)
    (e : EffSelfCarrier Op fam) : fold (l1.prod l2) fam e = (fold l1 fam e, fold l2 fam e) := by
  have h1 := cata_fusion (l1.prod l2) l1 (fun _ x => x.1)
    (fun _ _ _ => rfl) fam e
  have h2 := cata_fusion (l1.prod l2) l2 (fun _ x => x.2)
    (fun _ _ _ => rfl) fam e
  rw [← h1, ← h2]

/-! ## Fold induction -/

/-- A child that has the property; a leaf has it. -/
def childOk {R : EffFam → Type u} (P : (fam : EffFam) → R fam → Prop) : ArgF Op R → Prop
  | .child fam r => P fam r
  | _ => True

/-- The layer on the subtype of the carrier that has the property, when every layer keeps it. -/
def Layer.keeping {R : EffFam → Type u} (l : Layer Op R) (P : (fam : EffFam) → R fam → Prop)
    (keeps : ∀ fam ctor args, (∀ a ∈ args, childOk P a) → P fam (l fam ctor args)) :
    Layer Op (fun fam => { r : R fam // P fam r }) :=
  fun fam ctor args =>
    ⟨l fam ctor (args.map (mapChild fun _ x => x.1)), keeps fam ctor _ fun a ha => by
      obtain ⟨b, -, rfl⟩ := List.mem_map.mp ha
      cases b with
      | child fam x => exact x.2
      | _ => trivial⟩

/-- **Fold induction.** A property of the carrier that each layer keeps, when every child has
it, holds of the fold of every program, at every sort. -/
theorem cata_keeps {R : EffFam → Type u} (l : Layer Op R) (P : (fam : EffFam) → R fam → Prop)
    (keeps : ∀ fam ctor args, (∀ a ∈ args, childOk P a) → P fam (l fam ctor args))
    (fam : EffFam) (e : EffSelfCarrier Op fam) : P fam (fold l fam e) := by
  have h := cata_fusion (l.keeping P keeps) l (fun _ x => x.1) (fun _ _ _ => rfl) fam e
  rw [← h]
  exact (fold (l.keeping P keeps) fam e).2

end Tools.View.Algebra
