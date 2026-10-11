import Effect4.Laws.Machine.FinalizerRun
import Effect4.Laws.Machine.Ledger

/-!
# Finalizer credits through machine bookkeeping

Concept: scope-lifetime-finalization, R11, at most one start per registration.
These helpers serve `Program.FinalizerRun.funded_reachable`, consumed by `Atomic.cleans_once`.
The projection reads total stack credits, credits at each fiber, and the two trace counts.
It connects neutral machine edits with the checked evaluator debit.
Reach: arbitrary interpreters and machines with the stated distinct-fiber premise.
It establishes neither source-use uniqueness, log-writer provenance nor progress.
-/

set_option autoImplicit false
namespace Effect4.Machine.FinalizerCredits
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}

/-- The finalizer count is an instance of the shared saved-stack ledger. -/
def ledger (choose : ν → Bool) : StackLedger ν σ β ε δ ι α where
  produced event := if registered choose event then 1 else 0
  consumed event := if started choose event then 1 else 0
  program name := if choose name then 1 else 0
  stack := stack choose
  empty := rfl

/-- The existing count is the sum of its event indicators. -/
theorem indicator_sum {γ : Type _} (p : γ → Bool) :
    ∀ (items : List γ), (items.map fun x => if p x then 1 else 0).sum = items.countP p
  | [] => rfl
  | x :: rest => by
    rw [List.map_cons, List.sum_cons, indicator_sum p rest, List.countP_cons]
    exact Nat.add_comm _ _

/-- The shared consumed sum is the existing finalizer-start count. -/
theorem ledger_consumed (choose : ν → Bool) (trace : List (RunEvent ν σ β ε δ ι α χ)) :
    (ledger choose).consumedIn trace = trace.countP (runStarted choose) := by
  have weight : (ledger choose).eventConsumed (χ := χ) = fun e : RunEvent ν σ β ε δ ι α χ => if runStarted choose e then 1 else 0 := by
    funext e
    cases e <;> rfl
  rw [StackLedger.consumedIn, weight]
  exact indicator_sum _ trace

/-- The shared produced sum is the existing finalizer-registration count. -/
theorem ledger_produced (choose : ν → Bool) (trace : List (RunEvent ν σ β ε δ ι α χ)) :
    (ledger choose).producedIn trace = trace.countP (runRegistered choose) := by
  have weight : (ledger choose).eventProduced (χ := χ) = fun e : RunEvent ν σ β ε δ ι α χ => if runRegistered choose e then 1 else 0 := by
    funext e
    cases e <;> rfl
  rw [StackLedger.producedIn, weight]
  exact indicator_sum _ trace

/-- The complete ledger and the existing credit bound have the same reading. -/
theorem ledger_funded (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St) :
    (ledger choose).Funded 0 m ↔ Funded choose m := by
  simp only [StackLedger.Funded, ledger_consumed, ledger_produced, Nat.add_zero]
  exact Iff.rfl

/-- The shared local debit is exactly the existing local debit. -/
theorem ledger_debit (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St) :
    (ledger choose).IterDebit m f next ↔ IterDebit choose m f next := by
  simp only [StackLedger.IterDebit, ledger_consumed, ledger_produced]
  exact Iff.rfl

/-- All outstanding frame credits in the actual fiber table. -/
def total (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St) : Nat :=
  (m.fibers.map (fiberCredits choose)).sum

/-- Missing fibers own no credit. -/
def atFiber (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) : Nat :=
  ((m.fiber? id).map (fiberCredits choose)).getD 0

/-- The complete projection needed by a later replacement of one selected fiber. -/
def Same (choose : ν → Bool) (m n : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  total choose n = total choose m ∧
  (∀ id, atFiber choose n id = atFiber choose m id) ∧
  n.trace.countP (runStarted choose) = m.trace.countP (runStarted choose) ∧
  n.trace.countP (runRegistered choose) = m.trace.countP (runRegistered choose)

/-- The shared bookkeeping projection agrees with the existing one. -/
theorem ledger_same (choose : ν → Bool) (m n : RunMachine ν σ β ε δ ι α χ St) :
    (ledger choose).Same m n ↔ Same choose m n := by
  simp only [StackLedger.Same, ledger_consumed, ledger_produced]
  exact Iff.rfl

theorem Same.refl (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St) : Same choose m m :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

theorem Same.trans {choose : ν → Bool} {a b c : RunMachine ν σ β ε δ ι α χ St}
    (ab : Same choose a b) (bc : Same choose b c) : Same choose a c :=
  ⟨bc.1.trans ab.1, fun id => (bc.2.1 id).trans (ab.2.1 id),
    bc.2.2.1.trans ab.2.2.1, bc.2.2.2.trans ab.2.2.2⟩

/-- Neutral bookkeeping carries the machine's credit bound unchanged. -/
theorem Same.funded {choose : ν → Bool} {m n : RunMachine ν σ β ε δ ι α χ St}
    (same : Same choose m n) (funded : Funded choose m) : Funded choose n := by
  change _ + total choose n ≤ _
  rw [same.1, same.2.2.1, same.2.2.2]
  exact funded

/-- Emitting events that record no starts or pushes keeps the credit projection. -/
theorem same_emit (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (events : List (RunEvent ν σ β ε δ ι α χ))
    (starts : events.countP (runStarted choose) = 0)
    (pushes : events.countP (runRegistered choose) = 0) : Same choose m (m.emit events) := by
  apply (ledger_same choose _ _).mp
  exact (ledger choose).same_emit m events
    (by rwa [ledger_consumed]) (by rwa [ledger_produced])

/-- Replacing a looked-up fiber by one with the same credits keeps the complete projection. -/
theorem same_update (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (old next : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? old.id = some old)
    (sameId : next.id = old.id) (sameCredit : fiberCredits choose next = fiberCredits choose old) :
    Same choose m (m.update next) :=
  (ledger_same choose _ _).mp ((ledger choose).same_update m old next unique found sameId sameCredit)

/-- A metadata edit of a looked-up fiber keeps its credits. -/
theorem same_modify (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (id : FiberId)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id)
    (credits : ∀ f, fiberCredits choose (edit f) = fiberCredits choose f) :
    Same choose m (m.modify id edit) :=
  (ledger_same choose _ _).mp ((ledger choose).same_modify m unique id edit ids credits)

/-- A pointwise metadata edit retains both the total and each lookup's credits. -/
theorem same_map (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id)
    (credits : ∀ f, fiberCredits choose (edit f) = fiberCredits choose f) :
    Same choose m { m with fibers := m.fibers.map edit } :=
  (ledger_same choose _ _).mp ((ledger choose).same_map m edit ids credits)

/-- An empty newborn stack contributes zero, at every lookup and to the total. -/
theorem same_append_empty (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (child : RunFiber ν σ β ε δ ι α χ) (empty : fiberCredits choose child = 0) :
    Same choose m { m with fibers := m.fibers ++ [child] } :=
  (ledger_same choose _ _).mp ((ledger choose).same_append_empty m child empty)

/-- The spawn appends an empty frame stack and records no finalizer event. -/
theorem same_spawn (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat) :
    Same choose m (spawn interp m parent program options site).1 :=
  (ledger_same choose _ _).mp ((ledger choose).same_spawn interp m parent program options site)

/-- Starting a child only changes dispatcher metadata and records a scheduling event. -/
theorem same_start (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (child : FiberId) (immediately : Bool) :
    Same choose m (start m parent child immediately).1 :=
  (ledger_same choose _ _).mp ((ledger choose).same_start m parent child immediately)

/-- Every parallel finalizer child starts with an empty frame stack. -/
theorem same_forkFinalizers (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (programs : List (Prim ν σ β ε δ ι α)) :
    Same choose m (forkFinalizers interp m parent programs).1 :=
  (ledger_same choose _ _).mp ((ledger choose).same_forkFinalizers interp m parent programs)

/-- A countdown edits observers, while its callback frame owns no selected credit. -/
theorem same_countdown (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId) (resume : Resume ν) (fast : Bool) :
    Same choose m (countdownPark interp m f targets resume fast).1 :=
  (ledger_same choose _ _).mp ((ledger choose).same_countdown interp m unique f targets resume fast)

/-- Countdown's asynchronous callback frame contributes no finalizer registration credit. -/
theorem countdown_credit (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (targets : List FiberId) (resume : Resume ν) (fast : Bool) :
    fiberCredits choose (countdownPark interp m f targets resume fast).2.1 = fiberCredits choose f := by
  unfold countdownPark
  dsimp only
  split <;> rfl

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Interrupt delivery changes the current code but retains every frame credit. -/
theorem interruptRecord_credit (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (who : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    fiberCredits choose (interruptRecord interp who extra f).1 = fiberCredits choose f :=
  (ledger choose).interruptRecord_held interp who extra f

/-- Interrupt delivery keeps the selected table key. -/
theorem interruptRecord_key (interp : RunInterp ν σ β ε δ ι α χ St)
    (who : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    (interruptRecord interp who extra f).1.id = f.id :=
  StackLedger.interruptRecord_key interp who extra f

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Race allocation changes no stack or finalizer count, in either selection mode. -/
theorem same_beginRace (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (programs : List (Prim ν σ β ε δ ι α)) (site : Option (List Nat))
    (mode : Supervision.RaceMode) :
    Same choose m (beginRace interp m f yielding programs site mode).machine :=
  (ledger_same choose _ _).mp ((ledger choose).same_beginRace interp m f yielding programs site mode)

/-- Updating an absent key leaves the actual machine unchanged. -/
theorem update_absent (m : RunMachine ν σ β ε δ ι α χ St)
    (next : RunFiber ν σ β ε δ ι α χ) (missing : m.fiber? next.id = none) : m.update next = m :=
  StackLedger.update_absent m next missing

/-- Replacing a fiber spends its previous lookup credit; an absent key creates no table row. -/
theorem update_bound (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : RunFiber ν σ β ε δ ι α χ) (unique : (m.fibers.map RunFiber.id).Nodup) :
    total choose (m.update next) + atFiber choose m next.id ≤ total choose m + fiberCredits choose next :=
  (ledger choose).update_bound m next unique

/-- The complete iteration debit includes the selected fiber outside the stored table. -/
def Balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  next.machine.trace.countP (runStarted choose) + total choose next.machine +
      fiberCredits choose next.fiber + m.trace.countP (runRegistered choose) ≤
    m.trace.countP (runStarted choose) + total choose m +
      atFiber choose next.machine next.fiber.id + next.machine.trace.countP (runRegistered choose)

/-- The shared complete iteration debit agrees with the existing one. -/
theorem ledger_balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St) : (ledger choose).Balanced m next ↔ Balanced choose m next := by
  simp only [StackLedger.Balanced, ledger_consumed, ledger_produced]
  exact Iff.rfl

/-- The local evaluator debit combines with the unchanged table projection. -/
theorem balanced_of_debit (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (old : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St)
    (sum : total choose next.machine = total choose m)
    (stored : atFiber choose next.machine next.fiber.id = fiberCredits choose old)
    (debit : IterDebit choose m old next) : Balanced choose m next :=
  (ledger_balanced choose _ _).mp ((ledger choose).balanced_of_debit m old next sum stored
    ((ledger_debit choose _ _ _).mpr debit))

/-- The balanced iteration preserves the complete machine bound when written back. -/
theorem update_balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup)
    (funded : Funded choose m) (balanced : Balanced choose m next) :
    Funded choose (next.machine.update next.fiber) :=
  (ledger_funded choose _).mp ((ledger choose).update_balanced m next unique
    ((ledger_funded choose _).mpr funded) ((ledger_balanced choose _ _).mpr balanced))

/-- Settling edits no credited frame in the iteration's result. -/
theorem settle_balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup)
    (funded : Funded choose m) (balanced : Balanced choose m next)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) :
    Funded choose (settle id rest next).1 :=
  (ledger_funded choose _).mp ((ledger choose).settle_balanced m next unique
    ((ledger_funded choose _).mpr funded) ((ledger_balanced choose _ _).mpr balanced) id rest)

/-- Posting a task edits dispatcher metadata and records no finalizer event. -/
theorem same_postTask (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (owner : FiberId) (priority : Nat)
    (task : Task ν σ β ε δ ι α) : Same choose m (m.postTask owner priority task) :=
  (ledger_same choose _ _).mp ((ledger choose).same_postTask m unique owner priority task)

/-- Draining store work only posts tasks; evaluation runs in subsequent commands. -/
theorem same_drainOwed (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (ok : ForkLedger.Invariant.Ok m) (owed : List (Owed (Prim ν σ β ε δ ι α))) :
    Same choose m (drainOwed m owed).1 :=
  (ledger_same choose _ _).mp ((ledger choose).same_drainOwed m ok owed)

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Recording an interrupt in its actual table row leaves all credits available. -/
theorem same_interruptUpdate (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (id : FiberId) (old : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? id = some old)
    (who : Option FiberId) (extra : ReasonAnnotations α) :
    Same choose m (m.update (interruptRecord interp who extra old).1) :=
  (ledger_same choose _ _).mp
    ((ledger choose).same_interruptUpdate interp m unique id old found who extra)

/-- Scope linking writes observers or records an interrupt, without executing a finalizer. -/
theorem same_linkScope (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations α) :
    Same choose m (linkScope interp m mode scope target who extra).1 :=
  (ledger_same choose _ _).mp
    ((ledger choose).same_linkScope interp m unique mode scope target who extra)

/-- Interrupting a sequence retains each row's credits. The nested commands have not run. -/
theorem same_interruptEach (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (ok : ForkLedger.Invariant.Ok acc.1) :
    Same choose acc.1 (interruptEach interp who extra targets acc).1 :=
  (ledger_same choose _ _).mp
    ((ledger choose).same_interruptEach interp who extra targets acc ok)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The evaluator's table projection and local debit, before the selected row is replaced. -/
def IterKept (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  total choose next.machine = total choose m ∧
  (∀ id, atFiber choose next.machine id = atFiber choose m id) ∧
  next.fiber.id = f.id ∧ IterDebit choose m f next

/-- The shared evaluation projection agrees with the existing one. -/
theorem ledger_iterKept (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St) :
    (ledger choose).IterKept m f next ↔ IterKept choose m f next := by
  rw [StackLedger.IterKept, ledger_debit]
  exact Iff.rfl

/-- A neutral table edit and equal stack credit suffice for the evaluator relation. -/
theorem IterKept.of_same {choose : ν → Bool} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (same : Same choose m next.machine) (key : next.fiber.id = f.id)
    (credit : fiberCredits choose next.fiber = fiberCredits choose f) : IterKept choose m f next :=
  (ledger_iterKept choose _ _ _).mp
    (StackLedger.IterKept.of_same ((ledger_same choose _ _).mpr same) key credit)

/-- Reading the selected row turns the evaluator relation into the complete debit. -/
theorem IterKept.balanced {choose : ν → Bool} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (kept : IterKept choose m f next) (found : m.fiber? f.id = some f) : Balanced choose m next :=
  (ledger_balanced choose _ _).mp
    (((ledger_iterKept choose _ _ _).mpr kept).balanced found)

/-- The credit at a found key is the found row's credit. -/
theorem atFiber_found (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? id = some f) :
    atFiber choose m id = fiberCredits choose f :=
  (ledger choose).atFiber_found m id f found

/-- A replacement may use the credit view instead of the old row's complete metadata. -/
theorem same_update_view (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (next : RunFiber ν σ β ε δ ι α χ)
    (credit : atFiber choose m next.id = fiberCredits choose next) : Same choose m (m.update next) :=
  (ledger_same choose _ _).mp ((ledger choose).same_update_view m unique next credit)

/-- A replacement that discards credits cannot overspend the registration bound. -/
theorem update_funded_le (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (next : RunFiber ν σ β ε δ ι α χ)
    (credit : fiberCredits choose next ≤ atFiber choose m next.id) (funded : Funded choose m) :
    Funded choose (m.update next) :=
  (ledger_funded choose _).mp
    ((ledger choose).update_funded_le m unique next credit ((ledger_funded choose _).mpr funded))

end Effect4.Machine.FinalizerCredits
