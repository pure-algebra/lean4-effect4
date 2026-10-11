import Effect4.Laws.Program.LedgerRun
import Effect4.Laws.Program.FinalizerRun

/-!
# Laws.Program.LedgerFinalizer — finalizer custody as a stack ledger

The connector of `Laws/Machine/Ledger.lean`'s first instance. The finalizer credits of
`Machine.FinalizerCredits` are a stack ledger (`finalizer`): a pushed `onExit` frame of a chosen name
produces one credit, a run of its finalizer consumes one (a frame's `ranFinalizer` event or a reified
program's start), and a saved stack holds one credit per chosen `onExit` frame. This module shows:

* the two readings agree: `funded_iff` (the place invariant) and `iterKept` (an evaluation's debit);
* the ledger supplies what the run law asks (`kept`), from `FinalizerTransfer.evaluate_kept`;
* the run law's instance re-derives `FinalizerRun.funded_reachable` (`funded_reachable`), with no
  command case of its own.

So `FinalizerCommands`' command proof and `FinalizerBookkeeping`'s edit lemmas are instances of
`LedgerRun.command_funded` and `Ledger`'s edits. Codex's lane replaces them (the machine-models
note, `CODEX-PROMPT.md`, item 3).

Placement (AGENTS.md, Trust): concept `scope-lifetime-finalization`, R11; the consumer is
`Atomic.cleans_once`, through `FinalizerRun.starts_le_pushes`. Reach: every native program, row
table, compile budget and decision history. It establishes nothing beyond the finalizer custody
law it re-derives: no source-use uniqueness, log provenance or progress.
-/

set_option autoImplicit false

namespace Effect4.Program.LedgerFinalizer

open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.StackLedger Effect4.Machine.FinalizerCredits
open Effect4.Machine.ForkLedger.Invariant Effect4.Program.Guard

/-- **The finalizer ledger** of the chosen names. -/
def finalizer (choose : EffName → Bool) : NLedger where
  produced event := if registered choose event then 1 else 0
  consumed event := if started choose event then 1 else 0
  program name := if choose name then 1 else 0
  stack := FinalizerCredits.stack choose
  empty := rfl

/-- A sum of indicators is a count. -/
theorem indicator_sum {γ : Type _} (p : γ → Bool) :
    ∀ (items : List γ), (items.map fun x => if p x then 1 else 0).sum = items.countP p
  | [] => rfl
  | x :: rest => by
    rw [List.map_cons, List.sum_cons, indicator_sum p rest, List.countP_cons]
    exact Nat.add_comm _ _

/-- What a run event consumes is its finalizer-start indicator. -/
theorem eventConsumed_eq (choose : EffName → Bool) :
    (finalizer choose).eventConsumed (χ := Ctx) = fun e => if runStarted choose e then 1 else 0 := by
  funext e
  cases e <;> rfl

/-- What a run event produces is its registration indicator. -/
theorem eventProduced_eq (choose : EffName → Bool) :
    (finalizer choose).eventProduced (χ := Ctx) = fun e => if runRegistered choose e then 1 else 0 := by
  funext e
  cases e <;> rfl

theorem consumedIn_eq (choose : EffName → Bool) (trace : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    (finalizer choose).consumedIn trace = trace.countP (runStarted choose) := by
  unfold consumedIn
  rw [eventConsumed_eq]
  exact indicator_sum _ trace

theorem producedIn_eq (choose : EffName → Bool) (trace : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)) :
    (finalizer choose).producedIn trace = trace.countP (runRegistered choose) := by
  unfold producedIn
  rw [eventProduced_eq]
  exact indicator_sum _ trace

/-- **The place invariants agree.** -/
theorem funded_iff (choose : EffName → Bool) (m : NativeMachine) :
    FinalizerCredits.Funded choose m ↔ (finalizer choose).Funded 0 m := by
  unfold FinalizerCredits.Funded StackLedger.Funded
  rw [consumedIn_eq, producedIn_eq, Nat.add_zero]
  exact Iff.rfl

/-- **An evaluation's debit agrees.** -/
theorem iterKept (choose : EffName → Bool) (m : NativeMachine) (f : NFiber) (next : Native.NIter)
    (kept : FinalizerCredits.IterKept choose m f next) : (finalizer choose).IterKept m f next := by
  obtain ⟨total, at_, key, debit⟩ := kept
  refine ⟨total, at_, key, ?_⟩
  unfold StackLedger.IterDebit
  rw [consumedIn_eq, consumedIn_eq, producedIn_eq, producedIn_eq]
  exact debit

/-- **The finalizer ledger supplies the run law's premises.** -/
theorem kept (choose : EffName → Bool) (p : NativeEff) (table : RowTable) :
    (finalizer choose).Kept p table where
  evaluate m f y ok := iterKept choose m f _ (FinalizerTransfer.evaluate_kept choose p table m f y ok)
  cancel _ _ := Nat.le_refl _
  iterator _ _ _ := Nat.le_refl _

/-- **The run law's instance**: finalizer custody at every reachable machine, re-derived through
`StackLedger.funded_reachable` with no command case of its own. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem funded_reachable (p : NativeEff) (table : RowTable) (cf : Nat) (m : NativeMachine)
    (q : List Nat) (reached : Guard.Reachable p table cf m) :
    FinalizerCredits.Funded (FinalizerRun.atPath q) m :=
  (funded_iff _ m).mpr ((finalizer (FinalizerRun.atPath q)).funded_reachable 0 p table cf
    (kept _ p table) ((funded_iff _ _).mp (FinalizerRun.load_funded p cf q)) m reached)

end Effect4.Program.LedgerFinalizer
