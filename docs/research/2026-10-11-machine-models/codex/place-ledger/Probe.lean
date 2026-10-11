import Effect4.Laws.Machine.Ledger
import Effect4.Laws.Machine.FinalizerBookkeeping
import Effect4.Laws.Program.ReleaseCustody.IterationDebit
import Effect4.Laws.Program.SourceOpportunityMachine
import Test.Dogfood.Scenario.Atomic.WriterSync
import ProofGraph.AxiomAudit

/-!
Design probe for one accounting table over the existing machine places.
Placement and consumers are recorded in PLAN.md.
This file supplies connectors and arithmetic, not an execution producer.
-/
set_option autoImplicit false
namespace Effect4.Machine.PlaceLedgerProbe
open Effect4 Effect4.Machine Effect4.Program
universe u v

structure Weights (ν σ : Type u) (β : Type v) (ε δ ι α χ : Type u)
    (St : Type (max u v)) where
  fiber : RunFiber ν σ β ε δ ι α χ → Nat
  race : Race ν σ β ε δ ι α → Nat
  state : St → Nat
  command : Cmd ν σ β ε δ ι α → Nat
  task : Task ν σ β ε δ ι α → Nat
  consumed : RunEvent ν σ β ε δ ι α χ → Nat
  produced : RunEvent ν σ β ε δ ι α χ → Nat

namespace Weights
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
  {St : Type (max u v)}
variable (L : Weights ν σ β ε δ ι α χ St)

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

end Weights

theorem zero_sum {A : Type u} (xs : List A) : (xs.map (fun _ => (0 : Nat))).sum = 0 := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
    simp only [List.map_cons, List.sum_cons, Nat.zero_add, ih]

def stack {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    (L : StackLedger ν σ β ε δ ι α) :
    Weights ν σ β ε δ ι α χ St where
  fiber := L.held
  race := fun _ => 0
  state := fun _ => 0
  command := fun _ => 0
  task := fun _ => 0
  consumed := L.eventConsumed
  produced := L.eventProduced

theorem stack_funded {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    (L : StackLedger ν σ β ε δ ι α) (cap : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) :
    (stack L).Funded cap m [] [] ↔ L.Funded cap m := by
  simp only [Weights.Funded, Weights.spent, Weights.held, Weights.issued, stack,
    zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    StackLedger.Funded, StackLedger.consumedIn, StackLedger.producedIn, StackLedger.total, FiberSum.total]

abbrev NativeWeights := Weights EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

def custody (q : List Nat) : NativeWeights where
  fiber := ReleaseCustody.Control.fiberCredits q
  race := fun race => (race.programs.map (ReleaseCustody.Control.currentCredits q)).sum
  state := fun state => (state.scopes.entries.map fun entry => ReleaseCustody.scopeCredits q entry.scope).sum
  command := ReleaseCustody.Control.commandCredits q
  task := ReleaseCustody.Control.taskCredits q
  consumed := fun event => if ReleaseTrace.releaseAt q event then 1 else 0
  produced := fun event => if ReleaseTrace.registeredAt q event then 1 else 0

def source (root : NativeEff) (q : List Nat) : NativeWeights where
  fiber := fun fiber => SourceScope.Opportunities.frame root q fiber.frame
  race := fun _ => 0
  state := fun _ => 0
  command := fun _ => 0
  task := fun _ => 0
  consumed := SourceScope.Opportunities.runEvent q
  produced := fun _ => 0

theorem source_funded (root : NativeEff) (q : List Nat) (cap : Nat) (m : NativeMachine) :
    (source root q).Funded cap m [] [] ↔
      SourceScope.Opportunities.recorded q m + SourceScope.Opportunities.fibers root q m ≤ cap := by
  simp only [Weights.Funded, Weights.spent, Weights.held, Weights.issued, source,
    zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    SourceScope.Opportunities.recorded, SourceScope.Opportunities.fibers, FiberSum.total]

theorem custody_funded (q : List Nat) (m : NativeMachine)
    (pending : List ReleaseCustody.Control.Command) :
    (custody q).Funded 0 m pending [] ↔ ReleaseCustody.Control.Funded q m pending := by
  simp only [Weights.Funded, Weights.spent, Weights.held, Weights.issued, custody,
    List.map_nil, List.sum_nil, Nat.add_zero, FinalizerCredits.indicator_sum,
    ReleaseCustody.Control.Funded, ReleaseCustody.Control.machineCredits,
    FiberSum.total, Nat.add_assoc]

open Test.Dogfood.Scenario.Atomic in
def atomic (id : Nat) : NativeWeights where
  fiber := fun fiber => WriterPhase.frame id fiber.frame
  race := fun _ => 0
  state := fun state => Writer.heapCount id state.refs
  command := fun _ => 0
  task := fun _ => 0
  consumed := fun _ => 0
  produced := fun event => if FinalizerRun.startedAt (SourcePaths.requestPath id) event then 1 else 0

open Test.Dogfood.Scenario.Atomic in
theorem atomic_funded (id cap : Nat) (m : NativeMachine) :
    (atomic id).Funded cap m [] [] ↔
      Writer.heapCount id m.state.refs +
        (m.fibers.map fun fiber => WriterPhase.frame id fiber.frame).sum ≤
          m.trace.countP (FinalizerRun.startedAt (SourcePaths.requestPath id)) + cap := by
  simp only [Weights.Funded, Weights.spent, Weights.held, Weights.issued, atomic,
    zero_sum, List.map_nil, List.sum_nil, Nat.zero_add, Nat.add_zero,
    FinalizerCredits.indicator_sum, FiberSum.total]

end Effect4.Machine.PlaceLedgerProbe

namespace Effect4.Program.ReleaseCustody
open Effect4 Effect4.Machine Effect4.Program
open Control RuntimeShape Machine.PlaceLedgerProbe

/-- Prototype replacement of the existing settlement composition, with its original premises. -/
theorem settle_funded_probe (q : List Nat) (before : NativeMachine) (fiber : RuntimeShape.Fiber)
    (it : Iteration) (rest : List Control.Command)
    (unique : (before.fibers.map RunFiber.id).Nodup) (found : before.fiber? fiber.id = some fiber)
    (afterUnique : (it.machine.fibers.map RunFiber.id).Nodup)
    (old : RuntimeShape.Fiber) (afterFound : it.machine.fiber? fiber.id = some old)
    (key : it.fiber.id = fiber.id) (debit : IterDebit q before fiber it)
    (funded : Funded q before rest) :
    Funded q (settle fiber.id rest it).1 (settle fiber.id rest it).2 := by
  apply (custody_funded q _ _).mp
  apply (custody q).settle_funded (fun _ _ => rfl) (Evaluation.interrupt_fiber_le q)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) 0 fiber.id rest it [] afterUnique
  exact (custody_funded q _ _).mpr
    (install_funded q before fiber it rest unique found afterUnique old afterFound key debit funded)

end Effect4.Program.ReleaseCustody
