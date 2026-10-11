import Effect4.Laws.Machine.FiberSumMessages

/-!
Concept: scope-lifetime-finalization, R11, and reactive-scheduling.
Question: shared place accounting serves the original release and log debit claims.
Consumers: release custody, source opportunities, saved-stack credits, and Atomic writer credits.
Reach: weights on existing fibers, races, state, pending commands, detached tasks, and trace events.
Balance composes accounting inequalities. Each instance still proves its actual source and transfer premises.
The laws establish no progress, allocation identity, ordered cleanup, or host agreement.
-/
set_option autoImplicit false
namespace Effect4.Machine
open Effect4
universe u v

/-- One observation table over the machine's existing code and data places. -/
structure PlaceLedger (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u)
    (St : Type (max u v)) where
  fiber : RunFiber ν σ β ε δ ι α χ → Nat
  race : Race ν σ β ε δ ι α → Nat
  state : St → Nat
  command : Cmd ν σ β ε δ ι α → Nat
  task : Task ν σ β ε δ ι α → Nat
  consumed : RunEvent ν σ β ε δ ι α χ → Nat
  produced : RunEvent ν σ β ε δ ι α χ → Nat

namespace PlaceLedger
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
  {St : Type (max u v)}
variable (L : PlaceLedger ν σ β ε δ ι α χ St)

def held (m : RunMachine ν σ β ε δ ι α χ St)
    (pending : List (Cmd ν σ β ε δ ι α))
    (snapshot : List (Task ν σ β ε δ ι α)) : Nat :=
  L.state m.state + FiberSum.total L.fiber m + (m.races.map L.race).sum +
    (pending.map L.command).sum + (snapshot.map L.task).sum

def spent (m : RunMachine ν σ β ε δ ι α χ St) : Nat :=
  (m.trace.map L.consumed).sum

def issued (m : RunMachine ν σ β ε δ ι α χ St) : Nat :=
  (m.trace.map L.produced).sum

def Funded (cap : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (pending : List (Cmd ν σ β ε δ ι α))
    (snapshot : List (Task ν σ β ε δ ι α)) : Prop :=
  L.spent m + L.held m pending snapshot ≤ L.issued m + cap

/-- Balance is a relation over existing configurations; it introduces no execution judgment. -/
def Balanced (m : RunMachine ν σ β ε δ ι α χ St)
    (pending : List (Cmd ν σ β ε δ ι α))
    (snapshot : List (Task ν σ β ε δ ι α))
    (n : RunMachine ν σ β ε δ ι α χ St)
    (next : List (Cmd ν σ β ε δ ι α))
    (remaining : List (Task ν σ β ε δ ι α)) : Prop :=
  L.spent n + L.held n next remaining + L.issued m ≤
    L.spent m + L.held m pending snapshot + L.issued n

theorem Balanced.funded {cap m pending snapshot n next remaining}
    (balance : L.Balanced m pending snapshot n next remaining)
    (held : L.Funded cap m pending snapshot) : L.Funded cap n next remaining := by
  unfold Balanced Funded at *
  omega

theorem Balanced.trans {m pending snapshot n next remaining o final rest}
    (first : L.Balanced m pending snapshot n next remaining)
    (second : L.Balanced n next remaining o final rest) :
    L.Balanced m pending snapshot o final rest := by
  unfold Balanced at *
  omega

/-- All places except the acting stored row, before its local replacement is installed. -/
def outside (owner : FiberId) (m : RunMachine ν σ β ε δ ι α χ St)
    (pending : List (Cmd ν σ β ε δ ι α)) : Nat :=
  L.state m.state + FiberSum.outside L.fiber owner m + (m.races.map L.race).sum +
    (pending.map L.command).sum

/-- The local debit reads the same places, with the evaluator's returned owner counted once. -/
def IterDebit (m : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (it : Iter ν σ β ε δ ι α χ St) : Prop :=
  L.spent it.machine + L.outside fiber.id it.machine it.nested + L.fiber it.fiber + L.issued m ≤
    L.spent m + L.outside fiber.id m [] + L.fiber fiber + L.issued it.machine

/-- Actual owner installation lifts a local debit while retaining queued and detached work.
Consumers: the original release installation and Atomic settlement bounds. -/
theorem install_balanced (m : RunMachine ν σ β ε δ ι α χ St)
    (fiber : RunFiber ν σ β ε δ ι α χ) (it : Iter ν σ β ε δ ι α χ St)
    (rest : List (Cmd ν σ β ε δ ι α)) (snapshot : List (Task ν σ β ε δ ι α))
    (unique : (m.fibers.map RunFiber.id).Nodup) (member : fiber ∈ m.fibers)
    (installed : FiberSum.total L.fiber (it.machine.update it.fiber) ≤
      FiberSum.outside L.fiber fiber.id it.machine + L.fiber it.fiber)
    (debit : L.IterDebit m fiber it) :
    L.Balanced m rest snapshot (it.machine.update it.fiber) (it.nested ++ rest) snapshot := by
  have partition := FiberSum.split L.fiber m fiber unique member
  unfold IterDebit outside at debit
  unfold Balanced held
  simp only [RunMachine.update, spent, issued, List.map_append, List.sum_append] at debit ⊢
  simp only [List.map_nil, List.sum_nil, Nat.add_zero] at debit
  dsimp only [RunMachine.update] at installed
  omega

/-- Settlement uses the existing fiber and pending-command bounds once for every reading. -/
theorem settle_balanced [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (observers : ∀ f entries, L.fiber {f with observers := entries} = L.fiber f)
    (interrupts : ∀ cause f, L.fiber (interruptWithCause cause f).1 ≤ L.fiber f)
    (stopped : ∀ f, L.fiber {f with running := false} = L.fiber f)
    (unparked : ∀ f, L.fiber {f with parked := .notParked, pending := []} = L.fiber f)
    (evaluateZero : ∀ id, L.command (.evaluate id) = 0)
    (loopZero : ∀ id yielding, L.command (.loop id yielding) = 0)
    (deliverZero : ∀ id yielding, L.command (.deliver id yielding) = 0)
    (finishZero : ∀ id exit, L.command (.finish id exit) = 0)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α))
    (it : Iter ν σ β ε δ ι α χ St) (snapshot : List (Task ν σ β ε δ ι α))
    (unique : (it.machine.fibers.map RunFiber.id).Nodup) :
    L.Balanced (it.machine.update it.fiber) (it.nested ++ rest) snapshot
      (settle id rest it).1 (settle id rest it).2 snapshot := by
  have fibers := FiberSum.settle_le L.fiber observers interrupts stopped unparked id rest it unique
  have fields := FiberSum.settle_fields id rest it
  have state := congrArg Prod.fst fields
  have races := congrArg (fun fields => fields.2.1) fields
  have trace := congrArg (fun fields => fields.2.2) fields
  have commands := FiberSum.settle_commands_le L.command evaluateZero loopZero deliverZero finishZero id rest it
  unfold Balanced spent held issued
  dsimp only at state races trace
  rw [state, races, trace]
  dsimp only [RunMachine.update] at fibers ⊢
  omega

/-- Funding follows the common balance without repeating settlement accounting. -/
theorem settle_funded [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (observers : ∀ f entries, L.fiber {f with observers := entries} = L.fiber f)
    (interrupts : ∀ cause f, L.fiber (interruptWithCause cause f).1 ≤ L.fiber f)
    (stopped : ∀ f, L.fiber {f with running := false} = L.fiber f)
    (unparked : ∀ f, L.fiber {f with parked := .notParked, pending := []} = L.fiber f)
    (evaluateZero : ∀ id, L.command (.evaluate id) = 0)
    (loopZero : ∀ id yielding, L.command (.loop id yielding) = 0)
    (deliverZero : ∀ id yielding, L.command (.deliver id yielding) = 0)
    (finishZero : ∀ id exit, L.command (.finish id exit) = 0)
    (cap : Nat) (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α))
    (it : Iter ν σ β ε δ ι α χ St) (snapshot : List (Task ν σ β ε δ ι α))
    (unique : (it.machine.fibers.map RunFiber.id).Nodup)
    (funded : L.Funded cap (it.machine.update it.fiber) (it.nested ++ rest) snapshot) :
    L.Funded cap (settle id rest it).1 (settle id rest it).2 snapshot :=
  (L.settle_balanced observers interrupts stopped unparked evaluateZero loopZero deliverZero
    finishZero id rest it snapshot unique).funded L funded


/-- Zero-weight places contribute nothing to a ledger instance. -/
theorem zero_sum {A : Type u} (xs : List A) : (xs.map (fun _ => (0 : Nat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, Nat.zero_add, ih]

end PlaceLedger

end Effect4.Machine
