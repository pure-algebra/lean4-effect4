import Effect4.Program.Typing

/-! Checked authoring views over the existing Eff and Term syntax. Signature functions
are interpretation inputs; saved transforms contain only first-order program data.
Protocol projection contract: Test/contracts/protocol-projection.contract.md. -/
set_option autoImplicit false
namespace Effect4.Schema
open Effect4.Program
open Effect4.Machine.Env (Requirement)
variable {Op : Type}

/-- A first-order descriptor. Use `check` before relying on its declared signature. -/
structure SchemaTransform (Op : Type) where
  name : String := ""
  source : Ty
  target : Ty
  error : Ty := .never
  requires : Requirement := Requirement.empty
  program : Eff Op

namespace SchemaTransform
def id (t : Ty) : SchemaTransform Op :=
  { name := "id", source := t, target := t, program := .succeed (.var 0) }

/-- Composition over one input slot. The appended result is the second input.
This raw constructor is retained for authoring; `compose?` checks intermediate types
and `check` verifies the entire program/signature before execution or projection. -/
def compose (g f : SchemaTransform Op) : SchemaTransform Op :=
  { name := f.name ++ ";" ++ g.name
    source := f.source, target := g.target
    error := f.error.join g.error, requires := f.requires.union g.requires
    program := .bind f.program (Eff.weaken 0 g.program) }

def compose? (g f : SchemaTransform Op) : Option (SchemaTransform Op) :=
  if f.target.normalize = g.source.normalize then some (compose g f) else none
end SchemaTransform

/-- A checked arrow with its input appended after captured context slots. -/
structure Transform (σ : Signature Op) (Γ : TyEnv) (A B E : Ty) (R : Requirement) where
  program : Eff Op
  typed : effTy σ (Γ ++ [A]) program = some ⟨B, E, R⟩

/-- A checked pure term, not an additional expression language. -/
structure PureMap (σ : Signature Op) (Γ : TyEnv) (A B : Ty) where
  term : Term
  typed : termTy σ (Γ ++ [A]) term = some B

namespace Transform
variable {σ : Signature Op} {Γ : TyEnv} {A B C E E₁ E₂ : Ty} {R R₁ R₂ : Requirement}

def id (σ : Signature Op) (Γ : TyEnv) (A : Ty) :
    Transform σ Γ A A .never Requirement.empty where
  program := .succeed (.var Γ.length)
  typed := by simp [effTy, termTy, EffTy.pure]

def pure (f : PureMap σ Γ A B) : Transform σ Γ A B .never Requirement.empty where
  program := .succeed f.term
  typed := by simp [effTy, f.typed, EffTy.pure]

def andThen (f : Transform σ Γ A B E₁ R₁) (g : Transform σ Γ B C E₂ R₂) :
    Transform σ Γ A C (E₁.join E₂) (R₁.union R₂) where
  program := .bind f.program (Eff.weaken Γ.length g.program)
  typed := by
    simp only [effTy, f.typed, Option.bind_eq_bind, Option.bind_some]
    have hg := effTy_weaken σ Γ [B] A g.program
    rw [g.typed] at hg
    have hg' : effTy σ ((Γ ++ [A]) ++ [B]) (Eff.weaken Γ.length g.program) =
        some ⟨C, E₂, R₂⟩ := by simpa only [List.append_assoc, List.cons_append,
          List.nil_append] using hg
    rw [hg']
    rfl

/-- Input adaptation retains the pure stage explicitly in ordinary Eff. -/
def mapInput (f : PureMap σ Γ A B) (g : Transform σ Γ B C E R) :=
  (pure f).andThen g

def mapOutput (f : Transform σ Γ A B E R) (g : PureMap σ Γ B C) :=
  f.andThen (pure g)

def dimap (before : PureMap σ Γ A B) (f : Transform σ Γ B C E R)
    {D : Ty} (after : PureMap σ Γ C D) :=
  ((pure before).andThen f).andThen (pure after)

/-- Supply services through the existing Layer typing rule. Layer acquisition may fail
and require its own services; both remain in the resulting signature. -/
def provide (f : Transform σ Γ A B E R) (layer : LayerTerm Op) (layerType : LayerTy)
    (typedLayer : layerTy σ layer = some layerType) :=
  (show Transform σ Γ A B (E.join layerType.error)
      (Effect4.Row.union layerType.requires (Effect4.Row.diff R layerType.out)) from
    { program := .provideLayer layer false f.program
      typed := by simp [effTy, typedLayer, f.typed] })
end Transform

/-- Admit a descriptor at its declared signature. An arbitrary annotation cannot forge typing. -/
def SchemaTransform.check (d : SchemaTransform Op) (σ : Signature Op) :
    Option (Transform σ [] d.source d.target d.error d.requires) :=
  if h : effTy σ [d.source] d.program = some ⟨d.target, d.error, d.requires⟩ then
    some ⟨d.program, h⟩
  else none

end Effect4.Schema
