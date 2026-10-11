import Effect4.Laws.Machine.FinalizerRun
import Effect4.Laws.Machine.ControlWeights
import Effect4.Laws.Machine.Keeps
import Effect4.Laws.Machine.ForkLedgerInvariant

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
  refine ⟨rfl, fun _ => rfl, ?_, ?_⟩
  · rw [RunMachine.emit_trace, List.countP_append, starts, Nat.add_zero]
  · rw [RunMachine.emit_trace, List.countP_append, pushes, Nat.add_zero]

/-- Replacing a looked-up fiber by one with the same credits keeps the complete projection. -/
theorem same_update (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (old next : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? old.id = some old)
    (sameId : next.id = old.id) (sameCredit : fiberCredits choose next = fiberCredits choose old) :
    Same choose m (m.update next) := by
  have member := RunMachine.mem_of_fiber? found
  have changed := ControlWeights.replace_sum RunFiber.id (fiberCredits choose)
    old next sameId m.fibers unique member
  refine ⟨?_, ?_, rfl, rfl⟩
  · change ((m.fibers.map fun f => if f.id = next.id then next else f).map (fiberCredits choose)).sum = _
    rw [sameCredit] at changed
    exact Nat.add_right_cancel changed
  · intro id
    by_cases equal : id = next.id
    · subst id
      unfold atFiber
      rw [RunMachine.fiber?_update_self next m ⟨old, member, sameId.symm⟩, sameId, found]
      exact sameCredit
    · unfold atFiber
      rw [RunMachine.fiber?_update_other next m id equal]

/-- A metadata edit of a looked-up fiber keeps its credits. -/
theorem same_modify (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (id : FiberId)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id)
    (credits : ∀ f, fiberCredits choose (edit f) = fiberCredits choose f) :
    Same choose m (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact .refl choose m
  · rename_i old found
    apply same_update choose m old (edit old) unique
    · simpa only [RunMachine.id_of_fiber? found] using found
    · exact ids old
    · exact credits old

/-- A pointwise metadata edit retains both the total and each lookup's credits. -/
theorem same_map (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id)
    (credits : ∀ f, fiberCredits choose (edit f) = fiberCredits choose f) :
    Same choose m { m with fibers := m.fibers.map edit } := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [total, List.map_map, Function.comp_def, credits]
  · intro id
    unfold atFiber RunMachine.fiber?
    rw [List.find?_map]
    have predicate : ((fun f : RunFiber ν σ β ε δ ι α χ => decide (f.id = id)) ∘ edit) =
        (fun f => decide (f.id = id)) := by
      funext f
      simp only [Function.comp_def, ids]
    rw [predicate]
    cases m.fibers.find? (fun f => decide (f.id = id)) with
    | none => rfl
    | some f => exact credits f

/-- An empty newborn stack contributes zero, at every lookup and to the total. -/
theorem same_append_empty (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (child : RunFiber ν σ β ε δ ι α χ) (empty : fiberCredits choose child = 0) :
    Same choose m { m with fibers := m.fibers ++ [child] } := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [total, List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, empty, Nat.add_zero]
  · intro id
    unfold atFiber RunMachine.fiber?
    rw [List.find?_append]
    cases found : m.fibers.find? (fun f => decide (f.id = id)) with
    | some f => rfl
    | none =>
      simp only [Option.none_or, List.find?_cons, List.find?_nil]
      split
      · exact empty
      · rfl


/-- The spawn appends an empty frame stack and records no finalizer event. -/
theorem same_spawn (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat) :
    Same choose m (spawn interp m parent program options site).1 := by
  have born := same_append_empty choose m
    (RunFiber.make (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α)
      ⟨m.nextId⟩ program
      (match options.maskMode with
       | .interruptible => true | .uninterruptible => false | .inherit => parent.frame.interruptible)
      (interp.budgetOf parent.context) parent.context) rfl
  exact born.trans (same_emit choose _ [.forked parent.id ⟨m.nextId⟩ options.daemon] rfl rfl)

/-- Starting a child only changes dispatcher metadata and records a scheduling event. -/
theorem same_start (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (child : FiberId) (immediately : Bool) :
    Same choose m (start m parent child immediately).1 := by
  cases immediately
  · exact same_emit choose m [.scheduledTask parent.id 0 (.start child)] rfl rfl
  · exact .refl choose m

/-- Every parallel finalizer child starts with an empty frame stack. -/
theorem same_forkFinalizers (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (programs : List (Prim ν σ β ε δ ι α)) :
    Same choose m (forkFinalizers interp m parent programs).1 := by
  induction programs generalizing m with
  | nil => exact .refl choose m
  | cons program rest ih =>
    exact (same_spawn choose interp m parent program ⟨true, true, .inherit⟩ []).trans (ih _)

/-- A countdown edits observers, while its callback frame owns no selected credit. -/
theorem same_countdown (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (f : RunFiber ν σ β ε δ ι α χ) (targets : List FiberId) (resume : Resume ν) (fast : Bool) :
    Same choose m (countdownPark interp m f targets resume fast).1 := by
  unfold countdownPark
  dsimp only
  split
  · exact .refl choose m
  · rename_i exits target remaining found
    let edit (g : RunFiber ν σ β ε δ ι α χ) : RunFiber ν σ β ε δ ι α χ :=
      { g with observers := g.observers ++ [Observer.countdown f.id m.nextToken] }
    let bumped : RunMachine ν σ β ε δ ι α χ St := { m with nextToken := m.nextToken + 1 }
    exact (same_modify choose bumped unique target edit (fun _ => rfl) (fun _ => rfl)).trans
      (same_emit choose (bumped.modify target edit) [.parkedOn f.id m.nextToken] rfl rfl)

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
    fiberCredits choose (interruptRecord interp who extra f).1 = fiberCredits choose f := by
  unfold interruptRecord
  dsimp only
  (repeat' split) <;> rfl

/-- Interrupt delivery keeps the selected table key. -/
theorem interruptRecord_key (interp : RunInterp ν σ β ε δ ι α χ St)
    (who : Option FiberId) (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    (interruptRecord interp who extra f).1.id = f.id := by
  unfold interruptRecord
  dsimp only
  (repeat' split) <;> rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Race allocation changes no stack or finalizer count, in either selection mode. -/
theorem same_beginRace (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (yielding : Bool) (programs : List (Prim ν σ β ε δ ι α)) (site : Option (List Nat))
    (mode : Supervision.RaceMode) :
    Same choose m (beginRace interp m f yielding programs site mode).machine :=
  same_emit choose m [.raceStarted m.nextRace f.id programs.length] rfl rfl

/-- Updating an absent key leaves the actual machine unchanged. -/
theorem update_absent (m : RunMachine ν σ β ε δ ι α χ St)
    (next : RunFiber ν σ β ε δ ι α χ) (missing : m.fiber? next.id = none) : m.update next = m := by
  have unchanged : (m.fibers.map fun g => if g.id = next.id then next else g) = m.fibers := by
    calc
      _ = m.fibers.map id := List.map_congr_left fun g member => by
        have no := List.find?_eq_none.mp missing g member
        exact if_neg (fun equal => no (decide_eq_true equal))
      _ = m.fibers := List.map_id _
  simp only [RunMachine.update, unchanged]

/-- Replacing a fiber spends its previous lookup credit; an absent key creates no table row. -/
theorem update_bound (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : RunFiber ν σ β ε δ ι α χ) (unique : (m.fibers.map RunFiber.id).Nodup) :
    total choose (m.update next) + atFiber choose m next.id ≤ total choose m + fiberCredits choose next := by
  cases found : m.fiber? next.id with
  | none =>
    rw [update_absent m next found]
    simp only [atFiber, found, Option.map_none, Option.getD_none, Nat.add_zero]
    exact Nat.le_add_right _ _
  | some old =>
    have changed := ControlWeights.replace_sum RunFiber.id (fiberCredits choose)
      old next (RunMachine.id_of_fiber? found).symm m.fibers unique (RunMachine.mem_of_fiber? found)
    change _ + ((m.fiber? next.id).map (fiberCredits choose)).getD 0 ≤ _
    rw [found]
    exact Nat.le_of_eq changed

/-- The complete iteration debit includes the selected fiber outside the stored table. -/
def Balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  next.machine.trace.countP (runStarted choose) + total choose next.machine +
      fiberCredits choose next.fiber + m.trace.countP (runRegistered choose) ≤
    m.trace.countP (runStarted choose) + total choose m +
      atFiber choose next.machine next.fiber.id + next.machine.trace.countP (runRegistered choose)

/-- The local evaluator debit combines with the unchanged table projection. -/
theorem balanced_of_debit (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (old : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St)
    (sum : total choose next.machine = total choose m)
    (stored : atFiber choose next.machine next.fiber.id = fiberCredits choose old)
    (debit : IterDebit choose m old next) : Balanced choose m next := by
  unfold Balanced
  rw [sum, stored]
  unfold IterDebit at debit
  change _ + _ + stack choose next.fiber.frame.stack + _ ≤
    _ + _ + stack choose old.frame.stack + _
  omega

/-- The balanced iteration preserves the complete machine bound when written back. -/
theorem update_balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup)
    (funded : Funded choose m) (balanced : Balanced choose m next) :
    Funded choose (next.machine.update next.fiber) := by
  have replaced := update_bound choose next.machine next.fiber unique
  unfold Balanced at balanced
  change _ + total choose m ≤ _ at funded
  change next.machine.trace.countP (runStarted choose) + total choose (next.machine.update next.fiber) ≤
    next.machine.trace.countP (runRegistered choose)
  omega

/-- Settling edits no credited frame in the iteration's result. -/
theorem settle_balanced (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup)
    (funded : Funded choose m) (balanced : Balanced choose m next)
    (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) :
    Funded choose (settle id rest next).1 := by
  have changed (f : RunFiber ν σ β ε δ ι α χ)
      (key : f.id = next.fiber.id) (credit : fiberCredits choose f = fiberCredits choose next.fiber) :
      Funded choose (next.machine.update f) := by
    apply update_balanced choose m { next with fiber := f } unique funded
    change next.machine.trace.countP (runStarted choose) + total choose next.machine +
      fiberCredits choose f + m.trace.countP (runRegistered choose) ≤
      m.trace.countP (runStarted choose) + total choose m +
      atFiber choose next.machine f.id + next.machine.trace.countP (runRegistered choose)
    rw [key, credit]
    exact balanced
  unfold settle
  split
  · exact changed _ rfl rfl
  · exact changed _ rfl rfl
  · split <;> exact changed _ rfl rfl
  · exact changed _ rfl rfl
  · exact changed _ rfl rfl
  · exact changed _ rfl rfl

/-- Posting a task edits dispatcher metadata and records no finalizer event. -/
theorem same_postTask (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (owner : FiberId) (priority : Nat)
    (task : Task ν σ β ε δ ι α) : Same choose m (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact .refl choose m
  · rename_i old found
    have same := same_update choose m old
      { old with dispatcher := old.dispatcher.enqueue priority task } unique
      (by simpa only [RunMachine.id_of_fiber? found] using found) rfl rfl
    exact same.trans (same_emit choose _ [.scheduledTask owner priority task] rfl rfl)

/-- Draining store work only posts tasks; evaluation runs in subsequent commands. -/
theorem same_drainOwed (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (ok : ForkLedger.Invariant.Ok m) (owed : List (Owed (Prim ν σ β ε δ ι α))) :
    Same choose m (drainOwed m owed).1 := by
  induction owed generalizing m with
  | nil => exact .refl choose m
  | cons entry rest ih =>
    unfold drainOwed
    split
    · exact ih m ok
    · exact (same_postTask choose m ok.idsUnique _ _ _).trans
        (ih _ (ForkLedger.Invariant.postTask_ok ok _ _ _))

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Recording an interrupt in its actual table row leaves all credits available. -/
theorem same_interruptUpdate (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (id : FiberId) (old : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? id = some old)
    (who : Option FiberId) (extra : ReasonAnnotations α) :
    Same choose m (m.update (interruptRecord interp who extra old).1) :=
  same_update choose m old _ unique
    (by simpa only [RunMachine.id_of_fiber? found] using found)
    (interruptRecord_key interp who extra old) (interruptRecord_credit choose interp who extra old)

/-- Scope linking writes observers or records an interrupt, without executing a finalizer. -/
theorem same_linkScope (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations α) :
    Same choose m (linkScope interp m mode scope target who extra).1 := by
  unfold linkScope
  split
  · exact .refl choose m
  · split
    · exact .refl choose m
    · rename_i old found
      exact (same_interruptUpdate choose interp m unique target old found who extra).trans
        (same_emit choose _ [.scopeClosedOnLink scope target, .interruptRecorded who target] rfl rfl)
  · split
    · exact .refl choose m
    · split
      · exact .refl choose m
      · split
        · exact .refl choose m
        · rename_i state key _
          exact (same_modify choose { m with state } unique target
            (fun f => { f with observers := f.observers ++ [.dropScopeFinalizer scope key] })
            (fun _ => rfl) (fun _ => rfl)).trans
            (same_emit choose _ [.scopeLinked mode scope key target] rfl rfl)

/-- Interrupting a sequence retains each row's credits. The nested commands have not run. -/
theorem same_interruptEach (choose : ν → Bool) (interp : RunInterp ν σ β ε δ ι α χ St)
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (ok : ForkLedger.Invariant.Ok acc.1) :
    Same choose acc.1 (interruptEach interp who extra targets acc).1 := by
  unfold interruptEach
  induction targets generalizing acc with
  | nil => exact .refl choose acc.1
  | cons target rest ih =>
    rw [List.foldl_cons]
    split
    · exact ih acc ok
    · rename_i old found
      exact ((same_interruptUpdate choose interp acc.1 ok.idsUnique target old found (some who) extra).trans
        (same_emit choose _ [.interruptRecorded (some who) target] rfl rfl)).trans
        (ih _ (ForkLedger.Invariant.emit_ok (ForkLedger.Invariant.update_ok ok _) _))

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- The evaluator's table projection and local debit, before the selected row is replaced. -/
def IterKept (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  total choose next.machine = total choose m ∧
  (∀ id, atFiber choose next.machine id = atFiber choose m id) ∧
  next.fiber.id = f.id ∧ IterDebit choose m f next

/-- A neutral table edit and equal stack credit suffice for the evaluator relation. -/
theorem IterKept.of_same {choose : ν → Bool} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (same : Same choose m next.machine) (key : next.fiber.id = f.id)
    (credit : fiberCredits choose next.fiber = fiberCredits choose f) : IterKept choose m f next := by
  refine ⟨same.1, same.2.1, key, ?_⟩
  unfold IterDebit
  rw [same.2.2.1, same.2.2.2]
  change _ + fiberCredits choose next.fiber + _ ≤ _ + fiberCredits choose f + _
  rw [credit]
  exact Nat.le_refl _

/-- Reading the selected row turns the evaluator relation into the complete debit. -/
theorem IterKept.balanced {choose : ν → Bool} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (kept : IterKept choose m f next) (found : m.fiber? f.id = some f) : Balanced choose m next := by
  apply balanced_of_debit choose m f next kept.1 _ kept.2.2.2
  rw [kept.2.1, kept.2.2.1]
  simp only [atFiber, found, Option.map_some, Option.getD_some]

/-- The credit at a found key is the found row's credit. -/
theorem atFiber_found (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (id : FiberId) (f : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? id = some f) :
    atFiber choose m id = fiberCredits choose f := by
  simp only [atFiber, found, Option.map_some, Option.getD_some]

/-- A replacement may use the credit view instead of the old row's complete metadata. -/
theorem same_update_view (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (next : RunFiber ν σ β ε δ ι α χ)
    (credit : atFiber choose m next.id = fiberCredits choose next) : Same choose m (m.update next) := by
  cases found : m.fiber? next.id with
  | none => rw [update_absent m next found]; exact .refl choose m
  | some old =>
    exact same_update choose m old next unique
      (by simpa only [RunMachine.id_of_fiber? found] using found)
      (RunMachine.id_of_fiber? found).symm
      (credit.symm.trans (atFiber_found choose m next.id old found))

/-- A replacement that discards credits cannot overspend the registration bound. -/
theorem update_funded_le (choose : ν → Bool) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (next : RunFiber ν σ β ε δ ι α χ)
    (credit : fiberCredits choose next ≤ atFiber choose m next.id) (funded : Funded choose m) :
    Funded choose (m.update next) := by
  have bound := update_bound choose m next unique
  change _ + total choose m ≤ _ at funded
  change m.trace.countP (runStarted choose) + total choose (m.update next) ≤
    m.trace.countP (runRegistered choose)
  omega

end Effect4.Machine.FinalizerCredits
