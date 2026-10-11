import Effect4.Laws.Machine.Lift

/-!
Concept: scope-lifetime-finalization, R11, through the saved-mask region bracket.
Question: lift the region assertion through exactly the command prefix before its detached exit.
Reach: the existing command loop, its actual budget and a predicate at each executed command.
Limit: the predicate remains an explicit premise; fuel exhaustion retains the actual residue.
Consumer: Program.StackRegion's finite command-prefix law.
-/
set_option autoImplicit false
namespace Effect4.Machine.Lift
open Effect4 Effect4.Machine
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [FiberCore ν β ε δ ι α κ φ]
variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-- A side condition on every command actually executed in this finite prefix.
Stopped and exhausted cuts ask for no next-command premise. -/
def PrefixAllows (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (allowed : RunMachine ν σ β ε δ ι α χ St κ φ η →
      Cmd ν σ β ε δ ι α κ → List (Cmd ν σ β ε δ ι α κ) → Prop) :
    Nat → RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop
  | 0, _, _ => True
  | _ + 1, _, [] => True
  | fuel + 1, machine, head :: rest =>
    if machine.stuck.isSome then True
    else allowed machine head rest ∧
      PrefixAllows interp allowed fuel (driveStep interp machine head rest).1
        (driveStep interp machine head rest).2

/-- The command lift with side conditions tied to the actual finite execution.
Consumer: stack locality up to the detached region boundary. -/
theorem driveState_lift_allowed (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (I : RunMachine ν σ β ε δ ι α χ St κ φ η → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (allowed : RunMachine ν σ β ε δ ι α χ St κ φ η →
      Cmd ν σ β ε δ ι α κ → List (Cmd ν σ β ε δ ι α κ) → Prop)
    (step : ∀ machine head rest, machine.stuck = none → allowed machine head rest →
      I machine (head :: rest) → I (driveStep interp machine head rest).1 (driveStep interp machine head rest).2)
    (fuel : Nat) (machine : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (commands : List (Cmd ν σ β ε δ ι α κ)) (held : I machine commands)
    (permitted : PrefixAllows interp allowed fuel machine commands) :
    I (driveState interp fuel machine commands).1 (driveState interp fuel machine commands).2 := by
  induction fuel generalizing machine commands with
  | zero => exact held
  | succ fuel ih =>
    cases commands with
    | nil => exact held
    | cons head rest =>
      rw [driveState_succ_cons]
      by_cases stopped : machine.stuck.isSome = true
      · rw [if_pos stopped]
        exact held
      · rw [if_neg stopped]
        simp only [PrefixAllows, stopped] at permitted
        exact ih _ _ (step machine head rest (stuck_none_of_not stopped) permitted.1 held) permitted.2

end Effect4.Machine.Lift
