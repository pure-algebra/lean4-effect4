import Effects.Algebra.Program

/-!
# One step of a system

`Step S A X` is what a system over the signature `S` does from a state: it ends with a result in
`A`, or it issues one operation and continues in `X` for each answer. `Program S A` is the initial
algebra of this functor, and `Program.out` reads a program back as one step
(`Effects.Coalgebra.System`); a system is a coalgebra of it. Read as polynomials, the operations
are positions and the answers are directions.

`Step.Lift` is the relation lifting a bisimulation preserves: two steps end with one result, or
issue one operation and relate their continuations at every answer.
-/

namespace Effects

universe uOp uAns uX uY uZ

/-- One step over `S`: the result, or one operation and a continuation for each answer. -/
inductive Step (S : Signature.{uOp, uAns}) (A : Type uAns) (X : Type uX) :
    Type (max uOp uAns uX) where
  | done (value : A)
  | call (operation : S.Op) (next : S.Answer operation → X)

namespace Step

variable {S : Signature.{uOp, uAns}} {A : Type uAns} {X : Type uX} {Y : Type uY} {Z : Type uZ}

/-- Change the states the continuations reach. -/
def map (f : X → Y) : Step S A X → Step S A Y
  | .done value => .done value
  | .call operation next => .call operation (fun answer => f (next answer))

theorem map_id (step : Step S A X) : step.map (fun state => state) = step := by
  cases step <;> rfl

theorem map_comp (f : X → Y) (g : Y → Z) (step : Step S A X) :
    (step.map f).map g = step.map (fun state => g (f state)) := by
  cases step <;> rfl

/-- **Relation lifting.** Both steps end with one result, or both issue one operation and relate
their continuations at every answer. -/
inductive Lift (R : X → Y → Prop) : Step S A X → Step S A Y → Prop
  | done (value : A) : Lift R (.done value) (.done value)
  | call (operation : S.Op) {next : S.Answer operation → X} {next' : S.Answer operation → Y}
      (related : ∀ answer, R (next answer) (next' answer)) :
      Lift R (.call operation next) (.call operation next')

namespace Lift

theorem mono {R R' : X → Y → Prop} (weaker : ∀ x y, R x y → R' x y)
    {step : Step S A X} {step' : Step S A Y} (h : Lift R step step') : Lift R' step step' := by
  cases h with
  | done value => exact .done value
  | call operation related => exact .call operation (fun answer => weaker _ _ (related answer))

/-- Equality lifts to equality. -/
theorem refl (step : Step S A X) : Lift (fun x y => x = y) step step := by
  cases step with
  | done value => exact .done value
  | call operation next => exact .call operation (fun _ => rfl)

/-- A lifting of equality is equality. -/
theorem eq {step step' : Step S A X} (h : Lift (fun x y => x = y) step step') : step = step' := by
  cases h with
  | done value => rfl
  | call operation related => exact congrArg (Step.call operation) (funext related)

theorem symm {R : X → Y → Prop} {step : Step S A X} {step' : Step S A Y} (h : Lift R step step') :
    Lift (fun y x => R x y) step' step := by
  cases h with
  | done value => exact .done value
  | call operation related => exact .call operation related

/-- Liftings compose along the relational composite. -/
theorem comp {R : X → Y → Prop} {R' : Y → Z → Prop} {step : Step S A X} {step' : Step S A Y}
    {step'' : Step S A Z} (h : Lift R step step') (h' : Lift R' step' step'') :
    Lift (fun x z => ∃ y, R x y ∧ R' y z) step step'' := by
  cases h with
  | done value =>
    cases h' with
    | done _ => exact .done value
  | call operation related =>
    cases h' with
    | call _ related' => exact .call operation (fun answer => ⟨_, related answer, related' answer⟩)

/-- A lifting of the relation of the images lifts through the two maps. -/
theorem map {W : Type uX} {R : Y → Z → Prop} {f : X → Y} {g : W → Z} {step : Step S A X}
    {step' : Step S A W} (h : Lift (fun x w => R (f x) (g w)) step step') :
    Lift R (step.map f) (step'.map g) := by
  cases h with
  | done value => exact .done value
  | call operation related => exact .call operation related

end Lift

end Step

end Effects
