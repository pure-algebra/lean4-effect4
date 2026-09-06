import Effect4.Machine.Approximation
import Effect4.Machine.StoresLaws

/-!
# Observations and behavior on a settled decision tape

Packet: `Test/contracts/machine-behaviour.contract.md`. Nodes BEH/obs and BEH/tape
of `docs/research/2026-09-05-runtime-proof-graph.md`.

An observation contains every fiber's exit and the stores. It omits the trace
(`E4-DEN-CE-003`). `Beh_fuel_irrelevant` proves equality for any two sufficient
command budgets, with the initial machine and tape fixed.

Refusal `BEH-FB-TRACE-ORDER` (`E4-BEH-CE-001`): the trace-only order on arbitrary
frontiers does not imply the observation order. Identical traces can accompany
different stores or exits. Terminal results do support the projection, proved by
`obs_mono_of_le_terminal`. `Suffices` certifies that the tape's commands settled;
it does not say every fiber exited (`E4-BEH-CE-002`). Nothing here relates this
machine to rc.112 or supplies the later program-agreement theorem.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4

/-- The application observation: exits, including live fibers, and the stores. -/
structure Obs where
  exits : List (FiberId × Option ExitV)
  stores : Stores
deriving DecidableEq

/-- Recorded exits remain present and allocated store handles remain available.
This order compares allocation, not the values held in mutable cells. -/
def Obs.le (a b : Obs) : Prop :=
  (∀ id ex, (id, some ex) ∈ a.exits → (id, some ex) ∈ b.exits) ∧
    a.stores.le b.stores

theorem Obs.le_refl (a : Obs) : a.le a :=
  ⟨fun _ _ h => h, Stores.le_refl a.stores⟩

theorem Obs.le_trans {a b c : Obs} (h : a.le b) (h' : b.le c) : a.le c :=
  ⟨fun id ex hx => h'.1 id ex (h.1 id ex hx), Stores.le_trans h.2 h'.2⟩

variable {ν σ χ κ φ η : Type}

/-- Forget code, scheduling details and trace; keep every exit and the stores. -/
def obs (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η) : Obs :=
  ⟨m.fibers.map fun f => (f.id, f.exit), m.state⟩

/-- A terminal result can only be related to itself by `ReplayResult.le`. -/
theorem obs_mono_of_le_terminal
    {a b : ReplayResult ν σ Val Err Defect FiberId Ann χ Stores κ φ η}
    (ht : a.terminal = true) (h : ReplayResult.le a b) :
    (obs a.machine).le (obs b.machine) := by
  cases a with
  | frontier m => cases ht
  | finished m =>
    change b = ReplayResult.finished m at h
    subst b
    exact Obs.le_refl _
  | stuck why m =>
    change b = ReplayResult.stuck why m at h
    subst b
    exact Obs.le_refl _

variable [FiberCore ν Val Err Defect FiberId Ann κ φ]
variable [FiberEvaluator ν σ Val Err Defect FiberId Ann χ Stores κ φ η]

/-- The observation of a tape whose command budget suffices, at a fixed initial
machine. The machine can still hold fibers waiting for further decisions. -/
def Beh (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (tape : List (RunDecision ν σ Val Err Defect FiberId Ann)) (fuel : Nat)
    (_h : Suffices interp fuel tape m = true) : Obs :=
  obs (replayEval interp fuel tape m).machine

/-- Adding fuel to a sufficient command budget leaves the observation unchanged. -/
theorem Beh_add (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (tape : List (RunDecision ν σ Val Err Defect FiberId Ann)) (n k : Nat)
    (h : Suffices interp n tape m = true)
    (h' : Suffices interp (n + k) tape m = true) :
    Beh interp m tape (n + k) h' = Beh interp m tape n h := by
  unfold Beh
  rw [replay_stable interp n tape m h k]

/-- Any two sufficient command budgets give the same observation. The machine,
including its compiled code and compile budget, is held fixed. -/
theorem Beh_fuel_irrelevant (interp : RunInterp ν σ Val Err Defect FiberId Ann χ Stores κ)
    (m : RunMachine ν σ Val Err Defect FiberId Ann χ Stores κ φ η)
    (tape : List (RunDecision ν σ Val Err Defect FiberId Ann)) (n n' : Nat)
    (h : Suffices interp n tape m = true) (h' : Suffices interp n' tape m = true) :
    Beh interp m tape n h = Beh interp m tape n' h' := by
  rcases Nat.le_total n n' with hle | hle
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact (Beh_add interp m tape n k h h').symm
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
    exact Beh_add interp m tape n' k h' h

end Effect4.Machine
