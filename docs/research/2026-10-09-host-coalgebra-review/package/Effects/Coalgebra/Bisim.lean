import Effects.Coalgebra.System

/-!
# Bisimulations and simulations

A **bisimulation** between two systems over one signature relates states whose next steps are
both cuts, or are related by `Step.Lift`. A **simulation** of a system `c` by a system `d` asks
less: where `c` takes a step, `d` takes a related one; where `c` is cut, `d` may do anything. A
simulation is how a partial system (a machine whose budget ran out, a session whose host has not
answered yet) is compared with a total one (a program's meaning).

The two theorems everything else uses:

* `unfold_eq_of_bisim`: bisimilar states have equal unfoldings at every depth;
* `unfold_approx_of_sim`: a simulated state's unfolding approximates the other's at every depth.

Both are proved once here, so a consumer states its relation, proves it is a (bi)simulation, and
reads the rest off. Bisimulations and simulations compose (`IsBisim.comp`, `IsSim.comp`), so a
chain of relations (a machine to a local run to a meaning) is one relation.
-/

namespace Effects

universe uOp uAns uX uY uZ

/-- `Option` lifting: both are `none`, or both hold related values. -/
inductive OptionLift {α : Type uX} {β : Type uY} (R : α → β → Prop) : Option α → Option β → Prop
  | none : OptionLift R none none
  | some {a : α} {b : β} (h : R a b) : OptionLift R (some a) (some b)

namespace OptionLift

variable {α : Type uX} {β : Type uY} {γ : Type uZ}

theorem imp {R R' : α → β → Prop} (f : ∀ a b, R a b → R' a b) :
    ∀ {o : Option α} {o' : Option β}, OptionLift R o o' → OptionLift R' o o'
  | _, _, .none => .none
  | _, _, .some h => .some (f _ _ h)

theorem flip {R : α → β → Prop} :
    ∀ {o : Option α} {o' : Option β}, OptionLift R o o' → OptionLift (fun b a => R a b) o' o
  | _, _, .none => .none
  | _, _, .some h => .some h

theorem comp {R : α → β → Prop} {R' : β → γ → Prop} :
    ∀ {o : Option α} {o' : Option β} {o'' : Option γ}, OptionLift R o o' → OptionLift R' o' o'' →
      OptionLift (fun a c => ∃ b, R a b ∧ R' b c) o o''
  | _, _, _, .none, .none => .none
  | _, _, _, .some h, .some h' => .some ⟨_, h, h'⟩

theorem none_inv {R : α → β → Prop} {o' : Option β} :
    OptionLift R Option.none o' → o' = Option.none
  | .none => rfl

theorem some_inv {R : α → β → Prop} {a : α} {o' : Option β} :
    OptionLift R (Option.some a) o' → ∃ b, o' = Option.some b ∧ R a b
  | .some h => ⟨_, rfl, h⟩

end OptionLift

variable {S : Signature.{uOp, uAns}} {A : Type uAns} {X : Type uX} {Y : Type uY} {Z : Type uZ}

/-- **A bisimulation**: related states are both cut, or take steps related by `Step.Lift R`. -/
def IsBisim (c : System S A X) (d : System S A Y) (R : X → Y → Prop) : Prop :=
  ∀ x y, R x y → OptionLift (Step.Lift R) (c x) (d y)

/-- **A simulation of `c` by `d`**: where `c` steps, `d` takes a step related by `Step.Lift R`. -/
def IsSim (c : System S A X) (d : System S A Y) (R : X → Y → Prop) : Prop :=
  ∀ x y, R x y → ∀ step, c x = some step → ∃ step', d y = some step' ∧ Step.Lift R step step'

namespace IsBisim

theorem isSim {c : System S A X} {d : System S A Y} {R : X → Y → Prop} (h : IsBisim c d R) :
    IsSim c d R := by
  intro x y hxy step hstep
  have l := h x y hxy
  rw [hstep] at l
  exact l.some_inv

/-- Equality is a bisimulation of a system with itself. -/
theorem eq (c : System S A X) : IsBisim c c (fun x y => x = y) := by
  intro x y hxy
  subst hxy
  cases c x with
  | none => exact .none
  | some step => exact .some (Step.Lift.refl step)

theorem symm {c : System S A X} {d : System S A Y} {R : X → Y → Prop} (h : IsBisim c d R) :
    IsBisim d c (fun y x => R x y) :=
  fun y x hxy => (h x y hxy).flip.imp (fun _ _ hs => hs.symm)

/-- Bisimulations compose along the relational composite. -/
theorem comp {c : System S A X} {d : System S A Y} {e : System S A Z} {R : X → Y → Prop}
    {R' : Y → Z → Prop} (h : IsBisim c d R) (h' : IsBisim d e R') :
    IsBisim c e (fun x z => ∃ y, R x y ∧ R' y z) :=
  fun x z ⟨y, hxy, hyz⟩ =>
    ((h x y hxy).comp (h' y z hyz)).imp (fun _ _ ⟨_, l, l'⟩ => l.comp l')

end IsBisim

namespace IsSim

/-- Simulations compose along the relational composite. -/
theorem comp {c : System S A X} {d : System S A Y} {e : System S A Z} {R : X → Y → Prop}
    {R' : Y → Z → Prop} (h : IsSim c d R) (h' : IsSim d e R') :
    IsSim c e (fun x z => ∃ y, R x y ∧ R' y z) := by
  intro x z ⟨y, hxy, hyz⟩ step hstep
  obtain ⟨step', hstep', hrel⟩ := h x y hxy step hstep
  obtain ⟨step'', hstep'', hrel'⟩ := h' y z hyz step' hstep'
  exact ⟨step'', hstep'', hrel.comp hrel'⟩

end IsSim

/-- **Bisimilar states have equal unfoldings at every depth.** -/
theorem unfold_eq_of_bisim {c : System S A X} {d : System S A Y} {R : X → Y → Prop}
    (h : IsBisim c d R) : ∀ (depth : Nat) (x : X) (y : Y), R x y →
      c.unfold depth x = d.unfold depth y
  | 0, _, _, _ => rfl
  | depth + 1, x, y, hxy => by
    have l := h x y hxy
    rcases hc : c x with _ | step
    · rw [hc] at l
      rw [System.unfold_cut hc, System.unfold_cut l.none_inv]
    · rw [hc] at l
      obtain ⟨step', hd, hrel⟩ := l.some_inv
      cases hrel with
      | done value => rw [System.unfold_done hc, System.unfold_done hd]
      | call operation related =>
        rw [System.unfold_call hc, System.unfold_call hd]
        exact congrArg (Program.vis operation)
          (funext fun answer => unfold_eq_of_bisim h depth _ _ (related answer))

/-- **A simulated state's unfolding approximates the simulating state's, at every depth.** -/
theorem unfold_approx_of_sim {c : System S A X} {d : System S A Y} {R : X → Y → Prop}
    (h : IsSim c d R) : ∀ (depth : Nat) (x : X) (y : Y), R x y →
      Program.Approx (c.unfold depth x) (d.unfold depth y)
  | 0, _, _, _ => .cut _
  | depth + 1, x, y, hxy => by
    rcases hc : c x with _ | step
    · rw [System.unfold_cut hc]
      exact .cut _
    · obtain ⟨step', hd, hrel⟩ := h x y hxy step hc
      cases hrel with
      | done value =>
        rw [System.unfold_done hc, System.unfold_done hd]
        exact .done value
      | call operation related =>
        rw [System.unfold_call hc, System.unfold_call hd]
        exact .vis operation (fun answer => unfold_approx_of_sim h depth _ _ (related answer))

end Effects
