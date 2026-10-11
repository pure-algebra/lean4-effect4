import Effects.Coalgebra.Step
import Effects.Algebra.Laws

/-!
# Systems: coalgebras of one step

A system over `S` with results in `A` and states in `X` takes a state to its next step, or to
`none`: a cut, where the system says nothing yet (a frontier, a spent budget). A cut is never an
error. A program is a system that is never cut (`Program.system`).

Lean's core has no coinductive types, and nothing here needs one. A system's behaviour is read
through its finite unfoldings (`System.unfold`): depth `n` gives a program over `S` with results
in `Option A`, whose cut branches end in `none`. Unfoldings grow with depth (`unfold_succ`), and
a program's own unfolding approximates it at every depth (`Program.unfold_system`).
`Program.Approx` is the order: a cut is below everything; otherwise the shapes agree pointwise.
-/

namespace Effects

universe uOp uAns uX

/-- A system over `S`: a state's next step, or `none` where the system is cut. -/
abbrev System (S : Signature.{uOp, uAns}) (A : Type uAns) (X : Type uX) :=
  X → Option (Step S A X)

namespace Program

variable {S : Signature.{uOp, uAns}} {A : Type uAns}

/-- A program's first step: the free monad read back as one step. -/
def out : Program S A → Step S A (Program S A)
  | .pure value => .done value
  | .vis operation next => .call operation next

/-- A program is a system over its own signature, never cut. -/
def system : System S A (Program S A) := fun program => some program.out

/-- A program read as an unfolding that is never cut: each result in `some`. -/
def uncut (program : Program S A) : Program S (Option A) :=
  program.bind fun value => .pure (Option.some value)

/-- **The approximation order.** A cut is below every program; otherwise both end with one result,
or both issue one operation and are ordered at every answer. -/
inductive Approx : Program S (Option A) → Program S (Option A) → Prop
  | cut (other : Program S (Option A)) : Approx (.pure none) other
  | done (value : A) : Approx (.pure (Option.some value)) (.pure (Option.some value))
  | vis (operation : S.Op) {next next' : S.Answer operation → Program S (Option A)}
      (below : ∀ answer, Approx (next answer) (next' answer)) :
      Approx (.vis operation next) (.vis operation next')

namespace Approx

/-- Every program approximates itself. -/
theorem refl : ∀ (program : Program S (Option A)), Approx program program
  | .pure none => .cut _
  | .pure (Option.some value) => .done value
  | .vis operation next => .vis operation (fun answer => refl (next answer))

theorem trans {p q r : Program S (Option A)} (h : Approx p q) (h' : Approx q r) : Approx p r := by
  induction h generalizing r with
  | cut _ => exact .cut r
  | done value => exact h'
  | vis operation _ ih =>
    cases h' with
    | vis _ below' => exact .vis operation (fun answer => ih answer (below' answer))

end Approx

end Program

namespace System

variable {S : Signature.{uOp, uAns}} {A : Type uAns} {X : Type uX}

/-- **The unfolding of a system to depth `n`.** Depth zero, or a cut, ends in `none`; a result
ends in it; a call issues its operation and unfolds each continuation one level less deep. -/
def unfold (system : System S A X) : Nat → X → Program S (Option A)
  | 0, _ => .pure none
  | depth + 1, state =>
    match system state with
    | none => .pure none
    | some (.done value) => .pure (some value)
    | some (.call operation next) =>
      .vis operation (fun answer => unfold system depth (next answer))

theorem unfold_zero (system : System S A X) (state : X) : system.unfold 0 state = .pure none :=
  rfl

theorem unfold_cut {system : System S A X} {state : X} (h : system state = none) (depth : Nat) :
    system.unfold (depth + 1) state = .pure none := by
  simp only [unfold, h]

theorem unfold_done {system : System S A X} {state : X} {value : A}
    (h : system state = some (.done value)) (depth : Nat) :
    system.unfold (depth + 1) state = .pure (some value) := by
  simp only [unfold, h]

theorem unfold_call {system : System S A X} {state : X} {operation : S.Op}
    {next : S.Answer operation → X} (h : system state = some (.call operation next))
    (depth : Nat) :
    system.unfold (depth + 1) state =
      .vis operation (fun answer => system.unfold depth (next answer)) := by
  simp only [unfold, h]

/-- **Unfoldings grow with depth.** -/
theorem unfold_succ (system : System S A X) :
    ∀ (depth : Nat) (state : X),
      Program.Approx (system.unfold depth state) (system.unfold (depth + 1) state)
  | 0, _ => .cut _
  | depth + 1, state => by
    rcases h : system state with _ | (_ | ⟨operation, next⟩)
    · rw [unfold_cut h, unfold_cut h]
      exact .cut _
    · rw [unfold_done h, unfold_done h]
      exact .done _
    · rw [unfold_call h, unfold_call h]
      exact .vis operation (fun answer => unfold_succ system depth (next answer))

theorem unfold_mono (system : System S A X) {depth depth' : Nat} (h : depth ≤ depth') (state : X) :
    Program.Approx (system.unfold depth state) (system.unfold depth' state) := by
  induction h generalizing state with
  | refl => exact Program.Approx.refl _
  | step _ ih => exact (ih state).trans (unfold_succ system _ state)

end System

namespace Program

variable {S : Signature.{uOp, uAns}} {A : Type uAns}

/-- **A program's own unfolding approximates it at every depth.** -/
theorem unfold_system : ∀ (depth : Nat) (program : Program S A),
    Approx (Program.system.unfold depth program) program.uncut
  | 0, _ => .cut _
  | _ + 1, .pure value => .done value
  | depth + 1, .vis operation next =>
    .vis operation (fun answer => unfold_system depth (next answer))

end Program

end Effects
