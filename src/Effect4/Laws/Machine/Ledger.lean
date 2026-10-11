import Effect4.Laws.Machine.MaskRuns
import Effect4.Laws.Machine.ControlWeights
import Effect4.Laws.Machine.Keeps
import Effect4.Laws.Machine.ForkLedgerInvariant

/-!
# Laws.Machine.Ledger — a place invariant whose places are the saved stacks

A **stack ledger** is the one shape of the goals lane's "at most once" accounting
(`docs/research/2026-10-11-machine-models/README.md`, §2): what the trace consumed, plus what the
machine still holds, is at most what the trace produced, plus a cap. It is a Petri net's place
invariant, read on the fiber machine:

* the **events** weigh through the frame machine's events (`produced`, `consumed`) and the start of a
  reified finalizer program (`program`); every other event weighs nothing, by definition;
* the **places** are the fibers' saved stacks: a fiber holds the weight of its stack (`stack`), and
  the empty stack holds nothing (`empty`).

So every edit that leaves the stacks alone and records no frame event keeps the ledger by
definition: an observer, a child, a dispatcher task, a yield verdict, a recorded interrupt, an
answer installed as the current code. This module proves the edits once:

* `Same`: the bookkeeping relation (the total, each fiber's weight and both event sums kept), with
  `same_emit`, `same_update`, `same_modify`, `same_map`, `same_spawn`, `same_start`,
  `same_forkFinalizers`, `same_countdown`, `same_beginRace`, `same_postTask`, `same_drainOwed`,
  `same_interruptUpdate`, `same_linkScope`, `same_interruptEach`;
* the frame rule over distinct fiber ids (`update_bound`): replacing a fiber spends its old weight
  and holds its new one;
* the bridge from one evaluation's local debit to the machine (`IterDebit`, `IterKept`, `Balanced`,
  `settle_balanced`).

The command loop and the run lift are `Laws/Program/LedgerRun.lean`. `FinalizerCredits` is the first
instance (`Laws/Program/LedgerFinalizer.lean`); the module generalizes `FinalizerBookkeeping` from its
one weight to every stack weight.

Placement (AGENTS.md, Trust): concept `scope-lifetime-finalization`, R11 (at most once per
registration), and `reactive-scheduling` (invariants over execution traces). Reach: every
interpreter and machine, under distinct fiber ids. It establishes no instance's local debit, no
progress, and nothing about a weight that reads the current code: such a weight is not kept by a
recorded interrupt, and a stale fiber copy written back can raise it (`E4-RUN-CE-046`; the repair R2
of the note makes it generic too).
-/

set_option autoImplicit false

namespace Effect4.Machine

universe u v

/-- **A stack ledger.** What a frame event produces and consumes, what the start of a reified
finalizer program consumes, and what a saved stack holds. -/
structure StackLedger (ν σ : Type u) (β : Type v) (ε δ ι α : Type u) where
  produced : FrameEvent ν σ β ε δ ι α → Nat
  consumed : FrameEvent ν σ β ε δ ι α → Nat
  program : ν → Nat
  stack : List (Prim ν σ β ε δ ι α) → Nat
  empty : stack [] = 0

namespace StackLedger

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable (L : StackLedger ν σ β ε δ ι α)

/-! ## The ledger's reading of a machine -/

/-- What a run event consumes: a frame event's, a finalizer program's start, nothing else. -/
def eventConsumed : RunEvent ν σ β ε δ ι α χ → Nat
  | .frame _ event => L.consumed event
  | .finalizerProgram _ name _ => L.program name
  | _ => 0

/-- What a run event produces: a frame event's, nothing else. -/
def eventProduced : RunEvent ν σ β ε δ ι α χ → Nat
  | .frame _ event => L.produced event
  | _ => 0

/-- What a trace consumed. -/
def consumedIn (trace : List (RunEvent ν σ β ε δ ι α χ)) : Nat := (trace.map L.eventConsumed).sum

/-- What a trace produced. -/
def producedIn (trace : List (RunEvent ν σ β ε δ ι α χ)) : Nat := (trace.map L.eventProduced).sum

/-- What one fiber holds: the weight of its saved stack. -/
def held (f : RunFiber ν σ β ε δ ι α χ) : Nat := L.stack f.frame.stack

/-- What the machine's fibers hold. -/
def total (m : RunMachine ν σ β ε δ ι α χ St) : Nat := (m.fibers.map L.held).sum

/-- What the fiber an id names holds; a missing fiber holds nothing. -/
def atFiber (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId) : Nat :=
  ((m.fiber? id).map L.held).getD 0

/-- **The place invariant.** Consumed plus held is at most produced plus the cap. -/
def Funded (cap : Nat) (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  L.consumedIn m.trace + L.total m ≤ L.producedIn m.trace + cap

theorem consumedIn_append (a b : List (RunEvent ν σ β ε δ ι α χ)) :
    L.consumedIn (a ++ b) = L.consumedIn a + L.consumedIn b := by
  simp only [consumedIn, List.map_append, List.sum_append]

theorem producedIn_append (a b : List (RunEvent ν σ β ε δ ι α χ)) :
    L.producedIn (a ++ b) = L.producedIn a + L.producedIn b := by
  simp only [producedIn, List.map_append, List.sum_append]

/-! ## Bookkeeping -/

/-- **A bookkeeping edit**: the total, each fiber's weight and both event sums are kept. -/
def Same (m n : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  L.total n = L.total m ∧ (∀ id, L.atFiber n id = L.atFiber m id) ∧
    L.consumedIn n.trace = L.consumedIn m.trace ∧ L.producedIn n.trace = L.producedIn m.trace

theorem Same.refl (m : RunMachine ν σ β ε δ ι α χ St) : L.Same m m :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

theorem Same.trans {L : StackLedger ν σ β ε δ ι α} {a b c : RunMachine ν σ β ε δ ι α χ St}
    (ab : L.Same a b) (bc : L.Same b c) : L.Same a c :=
  ⟨bc.1.trans ab.1, fun id => (bc.2.1 id).trans (ab.2.1 id),
    bc.2.2.1.trans ab.2.2.1, bc.2.2.2.trans ab.2.2.2⟩

/-- A bookkeeping edit keeps the place invariant. -/
theorem Same.funded {L : StackLedger ν σ β ε δ ι α} {cap : Nat} {m n : RunMachine ν σ β ε δ ι α χ St}
    (same : L.Same m n) (funded : L.Funded cap m) : L.Funded cap n := by
  unfold Funded at funded ⊢
  rw [same.1, same.2.2.1, same.2.2.2]
  exact funded

/-- Emitting events that weigh nothing. For an event other than a frame event or a finalizer
program's start, both sums are `rfl`. -/
theorem same_emit (m : RunMachine ν σ β ε δ ι α χ St) (events : List (RunEvent ν σ β ε δ ι α χ))
    (consumed : L.consumedIn events = 0) (produced : L.producedIn events = 0) :
    L.Same m (m.emit events) := by
  refine ⟨rfl, fun _ => rfl, ?_, ?_⟩
  · rw [RunMachine.emit_trace, consumedIn_append, consumed, Nat.add_zero]
  · rw [RunMachine.emit_trace, producedIn_append, produced, Nat.add_zero]

/-- Replacing a looked-up fiber by one of the same id and weight. -/
theorem same_update (m : RunMachine ν σ β ε δ ι α χ St) (old next : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) (found : m.fiber? old.id = some old)
    (sameId : next.id = old.id) (sameWeight : L.held next = L.held old) :
    L.Same m (m.update next) := by
  have member := RunMachine.mem_of_fiber? found
  have changed := ControlWeights.replace_sum RunFiber.id L.held old next sameId m.fibers unique member
  refine ⟨?_, ?_, rfl, rfl⟩
  · change ((m.fibers.map fun f => if f.id = next.id then next else f).map L.held).sum = _
    rw [sameWeight] at changed
    exact Nat.add_right_cancel changed
  · intro id
    by_cases equal : id = next.id
    · subst id
      unfold atFiber
      rw [RunMachine.fiber?_update_self next m ⟨old, member, sameId.symm⟩, sameId, found]
      exact congrArg (fun w => (some w).getD 0) sameWeight
    · unfold atFiber
      rw [RunMachine.fiber?_update_other next m id equal]

/-- A metadata edit of a looked-up fiber that keeps its id and weight. -/
theorem same_modify (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (id : FiberId) (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id) (weights : ∀ f, L.held (edit f) = L.held f) :
    L.Same m (m.modify id edit) := by
  unfold RunMachine.modify
  split
  · exact .refl L m
  · rename_i old found
    apply L.same_update m old (edit old) unique
    · simpa only [RunMachine.id_of_fiber? found] using found
    · exact ids old
    · exact weights old

/-- A pointwise edit of every fiber that keeps ids and weights. -/
theorem same_map (m : RunMachine ν σ β ε δ ι α χ St)
    (edit : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ)
    (ids : ∀ f, (edit f).id = f.id) (weights : ∀ f, L.held (edit f) = L.held f) :
    L.Same m { m with fibers := m.fibers.map edit } := by
  refine ⟨?_, ?_, rfl, rfl⟩
  · simp only [total, List.map_map, Function.comp_def, weights]
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
    | some f => exact congrArg (fun w => (some w).getD 0) (weights f)

/-- Appending a fiber that holds nothing. -/
theorem same_append_empty (m : RunMachine ν σ β ε δ ι α χ St) (child : RunFiber ν σ β ε δ ι α χ)
    (empty : L.held child = 0) : L.Same m { m with fibers := m.fibers ++ [child] } := by
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

/-- A new fiber starts with an empty stack, so it holds nothing. -/
theorem held_make (id : FiberId) (program : Prim ν σ β ε δ ι α) (flag : Bool) (budget : Nat × Bool)
    (context : χ) : L.held (RunFiber.make (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι)
      (α := α) id program flag budget context) = 0 :=
  L.empty

/-- A spawn appends a fiber with an empty stack and records the fork. -/
theorem same_spawn (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) :
    L.Same m (spawn interp m parent program options site).1 := by
  have born := L.same_append_empty m
    (RunFiber.make (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α)
      ⟨m.nextId⟩ program
      (match options.maskMode with
       | .interruptible => true | .uninterruptible => false | .inherit => parent.frame.interruptible)
      (interp.budgetOf parent.context) parent.context) (L.held_make _ _ _ _ _)
  exact born.trans (L.same_emit _ [.forked parent.id ⟨m.nextId⟩ options.daemon] rfl rfl)

/-- Starting a spawned child records at most a scheduling event. -/
theorem same_start (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (child : FiberId) (immediately : Bool) : L.Same m (start m parent child immediately).1 := by
  cases immediately
  · exact L.same_emit m [.scheduledTask parent.id 0 (.start child)] rfl rfl
  · exact .refl L m

/-- The parallel close's finalizer fibers each start with an empty stack. -/
theorem same_forkFinalizers (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (programs : List (Prim ν σ β ε δ ι α)) : L.Same m (forkFinalizers interp m parent programs).1 := by
  induction programs generalizing m with
  | nil => exact .refl L m
  | cons program rest ih =>
    exact (L.same_spawn interp m parent program ⟨true, true, .inherit⟩ []).trans (ih _)

/-- A countdown park appends an observer to a target and records the park. -/
theorem same_countdown (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (f : RunFiber ν σ β ε δ ι α χ)
    (targets : List FiberId) (resume : Resume ν) (fast : Bool) :
    L.Same m (countdownPark interp m f targets resume fast).1 := by
  unfold countdownPark
  dsimp only
  split
  · exact .refl L m
  · rename_i exits target remaining found
    let edit (g : RunFiber ν σ β ε δ ι α χ) : RunFiber ν σ β ε δ ι α χ :=
      { g with observers := g.observers ++ [Observer.countdown f.id m.nextToken] }
    let bumped : RunMachine ν σ β ε δ ι α χ St := { m with nextToken := m.nextToken + 1 }
    exact (L.same_modify bumped unique target edit (fun _ => rfl) (fun _ => rfl)).trans
      (L.same_emit (bumped.modify target edit) [.parkedOn f.id m.nextToken] rfl rfl)

/-- A race's allocation records its start. -/
theorem same_beginRace (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (programs : List (Prim ν σ β ε δ ι α))
    (site : Option (List Nat)) (mode : Supervision.RaceMode) :
    L.Same m (beginRace interp m f yielding programs site mode).machine :=
  L.same_emit m [.raceStarted m.nextRace f.id programs.length] rfl rfl

/-- Posting a task edits a dispatcher and records the post. -/
theorem same_postTask (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α) :
    L.Same m (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split
  · exact .refl L m
  · rename_i old found
    have same := L.same_update m old { old with dispatcher := old.dispatcher.enqueue priority task }
      unique (by simpa only [RunMachine.id_of_fiber? found] using found) rfl rfl
    exact same.trans (L.same_emit _ [.scheduledTask owner priority task] rfl rfl)

/-- Draining store work only posts tasks. -/
theorem same_drainOwed (m : RunMachine ν σ β ε δ ι α χ St) (ok : ForkLedger.Invariant.Ok m)
    (owed : List (Owed (Prim ν σ β ε δ ι α))) : L.Same m (drainOwed m owed).1 := by
  induction owed generalizing m with
  | nil => exact .refl L m
  | cons entry rest ih =>
    unfold drainOwed
    split
    · exact ih m ok
    · exact (L.same_postTask m ok.idsUnique _ _ _).trans
        (ih _ (ForkLedger.Invariant.postTask_ok ok _ _ _))

/-- Updating an absent id leaves the machine unchanged. -/
theorem update_absent (m : RunMachine ν σ β ε δ ι α χ St) (next : RunFiber ν σ β ε δ ι α χ)
    (missing : m.fiber? next.id = none) : m.update next = m := by
  have unchanged : (m.fibers.map fun g => if g.id = next.id then next else g) = m.fibers := by
    calc
      _ = m.fibers.map id := List.map_congr_left fun g member => by
        have no := List.find?_eq_none.mp missing g member
        exact if_neg (fun equal => no (decide_eq_true equal))
      _ = m.fibers := List.map_id _
  simp only [RunMachine.update, unchanged]

/-- **The frame rule over distinct ids.** Replacing a fiber spends the weight its id held and holds
the new one's. -/
theorem update_bound (m : RunMachine ν σ β ε δ ι α χ St) (next : RunFiber ν σ β ε δ ι α χ)
    (unique : (m.fibers.map RunFiber.id).Nodup) :
    L.total (m.update next) + L.atFiber m next.id ≤ L.total m + L.held next := by
  cases found : m.fiber? next.id with
  | none =>
    rw [StackLedger.update_absent m next found]
    simp only [atFiber, found, Option.map_none, Option.getD_none, Nat.add_zero]
    exact Nat.le_add_right _ _
  | some old =>
    have changed := ControlWeights.replace_sum RunFiber.id L.held old next
      (RunMachine.id_of_fiber? found).symm m.fibers unique (RunMachine.mem_of_fiber? found)
    change _ + ((m.fiber? next.id).map L.held).getD 0 ≤ _
    rw [found]
    exact Nat.le_of_eq changed

/-- A replacement that holds no more than its id held keeps the place invariant. -/
theorem update_funded_le {cap : Nat} (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (next : RunFiber ν σ β ε δ ι α χ)
    (weight : L.held next ≤ L.atFiber m next.id) (funded : L.Funded cap m) :
    L.Funded cap (m.update next) := by
  have bound := L.update_bound m next unique
  unfold Funded at funded
  change L.consumedIn m.trace + L.total (m.update next) ≤ L.producedIn m.trace + cap
  omega

/-- The weight at a found id is the found fiber's. -/
theorem atFiber_found (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId)
    (f : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? id = some f) : L.atFiber m id = L.held f := by
  simp only [atFiber, found, Option.map_some, Option.getD_some]

/-- A replacement read through the ledger's view of its id. -/
theorem same_update_view (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (next : RunFiber ν σ β ε δ ι α χ)
    (weight : L.atFiber m next.id = L.held next) : L.Same m (m.update next) := by
  cases found : m.fiber? next.id with
  | none =>
    rw [StackLedger.update_absent m next found]
    exact .refl L m
  | some old =>
    exact L.same_update m old next unique
      (by simpa only [RunMachine.id_of_fiber? found] using found)
      (RunMachine.id_of_fiber? found).symm
      (weight.symm.trans (L.atFiber_found m next.id old found))

/-! ## Interrupts: they write the current code and the interrupt fields, never the stack -/

variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Recording an interrupt keeps the stack, so the weight. -/
theorem interruptRecord_held (interp : RunInterp ν σ β ε δ ι α χ St) (who : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    L.held (interruptRecord interp who extra f).1 = L.held f := by
  unfold interruptRecord
  dsimp only
  (repeat' split) <;> rfl

/-- Recording an interrupt keeps the fiber's id. -/
theorem interruptRecord_key (interp : RunInterp ν σ β ε δ ι α χ St) (who : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    (interruptRecord interp who extra f).1.id = f.id := by
  unfold interruptRecord
  dsimp only
  (repeat' split) <;> rfl

/-- Recording an interrupt in a looked-up fiber is bookkeeping. -/
theorem same_interruptUpdate (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup) (id : FiberId)
    (old : RunFiber ν σ β ε δ ι α χ) (found : m.fiber? id = some old) (who : Option FiberId)
    (extra : ReasonAnnotations α) :
    L.Same m (m.update (interruptRecord interp who extra old).1) :=
  L.same_update m old _ unique (by simpa only [RunMachine.id_of_fiber? found] using found)
    (StackLedger.interruptRecord_key interp who extra old) (L.interruptRecord_held interp who extra old)

/-- A scope link writes an observer or records an interrupt. -/
theorem same_linkScope (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α) :
    L.Same m (linkScope interp m mode scope target who extra).1 := by
  unfold linkScope
  split
  · exact .refl L m
  · split
    · exact .refl L m
    · rename_i old found
      exact (L.same_interruptUpdate interp m unique target old found who extra).trans
        (L.same_emit _ [.scopeClosedOnLink scope target, .interruptRecorded who target] rfl rfl)
  · split
    · exact .refl L m
    · split
      · exact .refl L m
      · split
        · exact .refl L m
        · rename_i state key _
          exact (L.same_modify { m with state } unique target
            (fun f => { f with observers := f.observers ++ [.dropScopeFinalizer scope key] })
            (fun _ => rfl) (fun _ => rfl)).trans
            (L.same_emit _ [.scopeLinked mode scope key target] rfl rfl)

/-- Interrupting a list of fibers records each interrupt. The nested commands have not run. -/
theorem same_interruptEach (interp : RunInterp ν σ β ε δ ι α χ St) (who : FiberId)
    (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (ok : ForkLedger.Invariant.Ok acc.1) :
    L.Same acc.1 (interruptEach interp who extra targets acc).1 := by
  unfold interruptEach
  induction targets generalizing acc with
  | nil => exact .refl L acc.1
  | cons target rest ih =>
    rw [List.foldl_cons]
    split
    · exact ih acc ok
    · rename_i old found
      exact ((L.same_interruptUpdate interp acc.1 ok.idsUnique target old found (some who) extra).trans
        (L.same_emit _ [.interruptRecorded (some who) target] rfl rfl)).trans
        (ih _ (ForkLedger.Invariant.emit_ok (ForkLedger.Invariant.update_ok ok _) _))

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-! ## One evaluation, then its write-back -/

/-- **An evaluation's local debit**: what the evaluation consumed, plus what its fiber holds after,
is at most what its fiber held, plus what the evaluation produced. -/
def IterDebit (m : RunMachine ν σ β ε δ ι α χ St) (fiber : RunFiber ν σ β ε δ ι α χ)
    (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  L.consumedIn next.machine.trace + L.held next.fiber + L.producedIn m.trace ≤
    L.consumedIn m.trace + L.held fiber + L.producedIn next.machine.trace

/-- The local debit read with the machine's other fibers and the stored copy of the evaluated one. -/
def Balanced (m : RunMachine ν σ β ε δ ι α χ St) (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  L.consumedIn next.machine.trace + L.total next.machine + L.held next.fiber + L.producedIn m.trace ≤
    L.consumedIn m.trace + L.total m + L.atFiber next.machine next.fiber.id +
      L.producedIn next.machine.trace

/-- The local debit, with the other fibers unchanged and the stored copy the evaluated fiber. -/
theorem balanced_of_debit (m : RunMachine ν σ β ε δ ι α χ St) (old : RunFiber ν σ β ε δ ι α χ)
    (next : Iter ν σ β ε δ ι α χ St) (sum : L.total next.machine = L.total m)
    (stored : L.atFiber next.machine next.fiber.id = L.held old) (debit : L.IterDebit m old next) :
    L.Balanced m next := by
  unfold Balanced
  rw [sum, stored]
  unfold IterDebit at debit
  omega

/-- **The write-back.** A balanced evaluation, written back over its stored copy, keeps the place
invariant. -/
theorem update_balanced {cap : Nat} (m : RunMachine ν σ β ε δ ι α χ St) (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup) (funded : L.Funded cap m)
    (balanced : L.Balanced m next) : L.Funded cap (next.machine.update next.fiber) := by
  have replaced := L.update_bound next.machine next.fiber unique
  unfold Balanced at balanced
  unfold Funded at funded
  change L.consumedIn next.machine.trace + L.total (next.machine.update next.fiber) ≤
    L.producedIn next.machine.trace + cap
  omega

/-- Settling writes the evaluated fiber back, with its weight unchanged. -/
theorem settle_balanced {cap : Nat} (m : RunMachine ν σ β ε δ ι α χ St) (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup) (funded : L.Funded cap m)
    (balanced : L.Balanced m next) (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) :
    L.Funded cap (settle id rest next).1 := by
  have changed (f : RunFiber ν σ β ε δ ι α χ)
      (key : f.id = next.fiber.id) (weight : L.held f = L.held next.fiber) :
      L.Funded cap (next.machine.update f) := by
    apply L.update_balanced m { next with fiber := f } unique funded
    unfold Balanced at balanced ⊢
    change _ + _ + L.held f + _ ≤ _ + _ + L.atFiber next.machine f.id + _
    rw [key, weight]
    exact balanced
  unfold settle
  split
  · exact changed _ rfl rfl
  · exact changed _ rfl rfl
  · split <;> exact changed _ rfl rfl
  · exact changed _ rfl rfl
  · exact changed _ rfl rfl
  · exact changed _ rfl rfl

/-- **An evaluation kept**: the other fibers' bookkeeping is kept, the id is the fiber's, and the
local debit holds. -/
def IterKept (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (next : Iter ν σ β ε δ ι α χ St) : Prop :=
  L.total next.machine = L.total m ∧ (∀ id, L.atFiber next.machine id = L.atFiber m id) ∧
    next.fiber.id = f.id ∧ L.IterDebit m f next

/-- A bookkeeping evaluation with an unchanged weight is kept. -/
theorem IterKept.of_same {L : StackLedger ν σ β ε δ ι α} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (same : L.Same m next.machine) (key : next.fiber.id = f.id)
    (weight : L.held next.fiber = L.held f) : L.IterKept m f next := by
  refine ⟨same.1, same.2.1, key, ?_⟩
  unfold IterDebit
  rw [same.2.2.1, same.2.2.2, weight]
  exact Nat.le_refl _

/-- A kept evaluation of a looked-up fiber is balanced. -/
theorem IterKept.balanced {L : StackLedger ν σ β ε δ ι α} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (kept : L.IterKept m f next) (found : m.fiber? f.id = some f) : L.Balanced m next := by
  apply L.balanced_of_debit m f next kept.1 _ kept.2.2.2
  rw [kept.2.1, kept.2.2.1]
  exact L.atFiber_found m f.id f found

/-- A bookkeeping edit and a caller's edit of equal weight rebase a kept evaluation. -/
theorem IterKept.rebase {L : StackLedger ν σ β ε δ ι α} {m n : RunMachine ν σ β ε δ ι α χ St}
    {f g : RunFiber ν σ β ε δ ι α χ} {next : Iter ν σ β ε δ ι α χ St}
    (same : L.Same m n) (key : g.id = f.id) (weight : L.held g = L.held f)
    (kept : L.IterKept n g next) : L.IterKept m f next := by
  refine ⟨kept.1.trans same.1, fun id => (kept.2.1 id).trans (same.2.1 id), kept.2.2.1.trans key, ?_⟩
  have debit := kept.2.2.2
  unfold IterDebit at debit ⊢
  rw [same.2.2.1, same.2.2.2, weight] at debit
  exact debit

end StackLedger

end Effect4.Machine
