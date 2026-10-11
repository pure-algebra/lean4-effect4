import Effect4.Laws.Machine.MaskRuns
import Effect4.Laws.Machine.ControlWeights
import Effect4.Laws.Machine.Keeps
import Effect4.Laws.Machine.EditWords
import Effect4.Laws.Machine.FiberSumMessages
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

/-- The local payload obligations of a bookkeeping write, at its actual prefix state. -/
def Neutral (edit : Edit ν σ β ε δ ι α χ St
    (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) : Prop :=
  match edit with
  | .update next => (m.fibers.map RunFiber.id).Nodup ∧
      ∃ old, m.fiber? old.id = some old ∧ next.id = old.id ∧ L.held next = L.held old
  | .emit events => L.consumedIn events = 0 ∧ L.producedIn events = 0
  | .appendFiber child => L.held child = 0
  | .observe _ _ => (m.fibers.map RunFiber.id).Nodup
  | _ => True

/-- The ledger's per-edit instance. Helpers supply only their actual payload obligations. -/
theorem same_edit (m : RunMachine ν σ β ε δ ι α χ St)
    (edit : Edit ν σ β ε δ ι α χ St
      (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α))
    (payload : L.Neutral edit m) : L.Same m (edit.apply m) := by
  cases edit with
  | update next =>
    obtain ⟨unique, old, found, key, weight⟩ := payload
    exact L.same_update m old next unique found key weight
  | emit events => exact L.same_emit m events payload.1 payload.2
  | appendFiber child => exact L.same_append_empty m child payload
  | observe target observer =>
    exact L.same_modify m payload target (fun f => {f with observers := f.observers ++ [observer]})
      (fun _ => rfl) (fun _ => rfl)
  | dropToken token =>
    exact L.same_map m (fun f => {f with observers := f.observers.filter fun
      | .resumeAwait _ t _ => t ≠ token
      | .countdown _ t => t ≠ token
      | _ => true}) (fun _ => rfl) (fun _ => rfl)
  | _ => exact .refl L m

/-- Bookkeeping words compose through the existing actual-prefix Path. -/
theorem same_word {m n : RunMachine ν σ β ε δ ι α χ St}
    {word : List (Edit ν σ β ε δ ι α χ St
      (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α))}
    (path : Effect4.Contracts.Path (fun before after edit =>
      after = edit.apply before ∧ L.Neutral edit before) m n word) : L.Same m n := by
  have same := Edits.run_preserves_at (fun _ _ _ edge => edge.1) (L.Same m)
    (fun before after edit edge held => by
      rw [edge.1]
      exact held.trans (L.same_edit before edit edge.2)) path (.refl L m)
  rwa [Edits.run_of_path (fun _ _ _ edge => edge.1) path] at same

/-- Prefix-independent payloads need no lookup path from the caller. -/
theorem same_run (m : RunMachine ν σ β ε δ ι α χ St)
    (word : List (Edit ν σ β ε δ ι α χ St
      (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α)))
    (payload : ∀ edit ∈ word, ∀ held, L.Neutral edit held) : L.Same m (Edits.run word m) :=
  Edits.run_preserves (L.Same m) word
    (fun edit member held same => same.trans (L.same_edit held edit (payload edit member held))) m (.refl L m)

/-- Spawn payloads satisfy the ledger's primitive obligations, independently of the prefix. -/
theorem spawn_neutral (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (program : Prim ν σ β ε δ ι α) (options : Supervision.ForkOptions) (site : List Nat)
    (edit : Edit ν σ β ε δ ι α χ St
      (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α))
    (member : edit ∈ Edits.spawnWord interp m parent program options site)
    (held : RunMachine ν σ β ε δ ι α χ St) : L.Neutral edit held := by
  simp only [Edits.spawnWord, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact L.held_make _ _ _ _ _
  · exact True.intro
  · exact True.intro
  · exact ⟨rfl, rfl⟩

/-- A spawn appends a fiber with an empty stack and records the fork. -/
theorem same_spawn (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (parent : RunFiber ν σ β ε δ ι α χ) (program : Prim ν σ β ε δ ι α)
    (options : Supervision.ForkOptions) (site : List Nat) :
    L.Same m (spawn interp m parent program options site).1 := by
  rw [Edits.spawn_word]
  exact L.same_run m _ (L.spawn_neutral interp m parent program options site)

/-- Starting a spawned child records at most a scheduling event. -/
theorem same_start (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (child : FiberId) (immediately : Bool) : L.Same m (start m parent child immediately).1 := by
  rw [Edits.start_word]
  apply L.same_run
  intro edit member held
  cases immediately with
  | true => exact False.elim (List.not_mem_nil member)
  | false =>
    simp only [Edits.startWord, Bool.false_eq_true, ite_false, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact True.intro
    · exact ⟨rfl, rfl⟩

/-- The parallel close's finalizer fibers each start with an empty stack. -/
theorem same_forkFinalizers (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (parent : RunFiber ν σ β ε δ ι α χ)
    (programs : List (Prim ν σ β ε δ ι α)) : L.Same m (forkFinalizers interp m parent programs).1 := by
  apply L.same_word
  apply Edits.forks_path interp parent
  intro held program
  rw [Edits.spawn_word]
  exact Edits.run_path _ (fun edit member before =>
    ⟨rfl, L.spawn_neutral interp held parent program ⟨true, true, .inherit⟩ [] edit member before⟩) held

/-- A race's allocation records its start. -/
theorem same_beginRace (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (f : RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (programs : List (Prim ν σ β ε δ ι α))
    (site : Option (List Nat)) (mode : Supervision.RaceMode) :
    L.Same m (beginRace interp m f yielding programs site mode).machine  := by
  rw [Edits.race_word]
  apply L.same_run
  intro edit member held
  simp only [Edits.raceWord, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact True.intro
  · exact True.intro
  · exact True.intro
  · exact ⟨rfl, rfl⟩

/-- Posting a task edits a dispatcher and records the post. -/
theorem same_postTask (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup)
    (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α) :
    L.Same m (m.postTask owner priority task) := by
  rw [Edits.postTask_word]
  cases found : m.fiber? owner with
  | none =>
    apply L.same_run
    intro edit member held
    simp only [Edits.postTaskWord, found, List.mem_singleton] at member
    subst edit
    exact True.intro
  | some old =>
    simp only [Edits.postTaskWord, found]
    apply L.same_word (word := [.update {old with dispatcher := old.dispatcher.enqueue priority task},
      .arm owner, .emit [.scheduledTask owner priority task]])
    refine .cons ⟨rfl, ?_⟩ (.cons ⟨rfl, True.intro⟩ (.cons ⟨rfl, ⟨rfl, rfl⟩⟩ (.nil _)))
    exact ⟨unique, old, by simpa only [RunMachine.id_of_fiber? found] using found, rfl, rfl⟩

/-- Actual-prefix payload obligations compose with the existing fork-key invariant. -/
theorem same_ok_word {m n : RunMachine ν σ β ε δ ι α χ St}
    {word : List (Edit ν σ β ε δ ι α χ St
      (Prim ν σ β ε δ ι α) (FrameFiber ν σ β ε δ ι α) (FrameEvent ν σ β ε δ ι α))}
    (path : Effect4.Contracts.Path
      (fun before after edit => after = edit.apply before ∧
        (ForkLedger.Invariant.Ok before → L.Neutral edit before ∧ ForkLedger.Invariant.Ok after))
      m n word) (ok : ForkLedger.Invariant.Ok m) : L.Same m n := by
  have kept := Edits.run_preserves_at (fun _ _ _ edge => edge.1)
    (fun after => L.Same m after ∧ ForkLedger.Invariant.Ok after)
    (fun before after edit edge previous => by
      have next := edge.2 previous.2
      refine ⟨previous.1.trans ?_, next.2⟩
      rw [edge.1]
      exact L.same_edit before edit next.1) path ⟨.refl L m, ok⟩
  rw [Edits.run_of_path (fun _ _ _ edge => edge.1) path] at kept
  exact kept.1

/-- Task-post payloads retain the ledger and the fork-key premise at their actual prefixes. -/
theorem postTask_payload_path (m : RunMachine ν σ β ε δ ι α χ St)
    (owner : FiberId) (priority : Nat) (task : Task ν σ β ε δ ι α) :
    Effect4.Contracts.Path
      (fun before after edit => after = edit.apply before ∧
        (ForkLedger.Invariant.Ok before → L.Neutral edit before ∧ ForkLedger.Invariant.Ok after))
      m (m.postTask owner priority task) (Edits.postTaskWord m owner priority task) := by
  rw [Edits.postTask_word]
  cases found : m.fiber? owner with
  | none =>
    simp only [Edits.postTaskWord, found]
    exact .cons ⟨rfl, fun ok => ⟨True.intro, ForkLedger.Invariant.halt_ok ok _⟩⟩ (.nil _)
  | some old =>
    simp only [Edits.postTaskWord, found]
    refine .cons ⟨rfl, ?_⟩ (.cons ⟨rfl, fun ok => ⟨True.intro, ForkLedger.Invariant.arm_ok ok _⟩⟩
      (.cons ⟨rfl, fun ok => ⟨⟨rfl, rfl⟩, ForkLedger.Invariant.emit_ok ok _⟩⟩ (.nil _)))
    intro ok
    exact ⟨⟨ok.idsUnique, old, by simpa only [RunMachine.id_of_fiber? found] using found, rfl, rfl⟩,
      ForkLedger.Invariant.update_ok ok _⟩

/-- Draining store work only posts tasks. -/
theorem same_drainOwed (m : RunMachine ν σ β ε δ ι α χ St) (ok : ForkLedger.Invariant.Ok m)
    (owed : List (Owed (Prim ν σ β ε δ ι α))) : L.Same m (drainOwed m owed).1 := by
  exact L.same_ok_word (Edits.drain_path L.postTask_payload_path m owed) ok

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

/-- An interrupt delta keeps the saved-stack weight. The R2 message interpretation consumes this law. -/
theorem interruptWithCause_held (cause : Cause ε δ ι α) (f : RunFiber ν σ β ε δ ι α χ) :
    L.held (interruptWithCause cause f).1 = L.held f := by
  unfold interruptWithCause
  dsimp only
  (repeat' split) <;> rfl

/-- An interrupt delta keeps the addressed record's identity. -/
theorem interruptWithCause_key (cause : Cause ε δ ι α) (f : RunFiber ν σ β ε δ ι α χ) :
    (interruptWithCause cause f).1.id = f.id := by
  unfold interruptWithCause
  dsimp only
  (repeat' split) <;> rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Replacing records by a record at their own key keeps the key list, including duplicate raw keys. -/
theorem update_keys (m : RunMachine ν σ β ε δ ι α χ St) (next : RunFiber ν σ β ε δ ι α χ) :
    ((m.update next).fibers.map RunFiber.id) = m.fibers.map RunFiber.id := by
  simp only [RunMachine.update, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro old _
  split
  · next same => exact same.symm
  · rfl

/-- One first-order edit keeps every stack weight and the actual stored key list.
The R2 settlement proof consumes this result. -/
theorem fiberEdit_kept (edit : FiberEdit ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) :
    L.Same m (applyFiberEdit edit m).1 ∧
      ((applyFiberEdit edit m).1.fibers.map RunFiber.id) = m.fibers.map RunFiber.id := by
  cases edit with
  | observe target observer =>
    refine ⟨L.same_modify m unique target (fun f => {f with observers := f.observers ++ [observer]})
      (fun _ => rfl) (fun _ => rfl), ?_⟩
    simp only [applyFiberEdit]
    unfold RunMachine.modify
    dsimp only
    split
    · rfl
    · exact update_keys m _
  | dropToken token =>
    refine ⟨L.same_map m (fun f => {f with observers := f.observers.filter fun
      | .resumeAwait _ t _ => t ≠ token
      | .countdown _ t => t ≠ token
      | _ => true}) (fun _ => rfl) (fun _ => rfl), ?_⟩
    simp only [applyFiberEdit, RunMachine.dropToken, List.map_map, Function.comp_def]
  | interrupt target cause =>
    simp only [applyFiberEdit]
    split
    · exact ⟨.refl L m, rfl⟩
    · next old found =>
      refine ⟨L.same_update m old (interruptWithCause cause old).1 unique ?_
        (interruptWithCause_key cause old) (L.interruptWithCause_held cause old), update_keys m _⟩
      simpa only [RunMachine.id_of_fiber? found] using found

/-- The edit fold keeps the ledger and the stored key list without another command census. -/
theorem fiberEdits_kept (edits : List (FiberEdit ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) (unique : (m.fibers.map RunFiber.id).Nodup) :
    L.Same m (applyFiberEdits edits m).1 ∧
      ((applyFiberEdits edits m).1.fibers.map RunFiber.id) = m.fibers.map RunFiber.id := by
  have path := Edits.fiberWords_path
    (Edge := fun before after edit => after = edit.apply before ∧
      ((before.fibers.map RunFiber.id).Nodup → L.Same before after ∧
        after.fibers.map RunFiber.id = before.fibers.map RunFiber.id))
    edits (fun message _ before => Edits.fiberWord_path message before (fun edit single => by
      refine ⟨?_, fun held => L.fiberEdit_kept message before held⟩
      rw [Edits.fiber_word, single]
      rfl)) m
  have kept := Edits.run_preserves_at (fun _ _ _ edge => edge.1)
    (fun after => L.Same m after ∧ after.fibers.map RunFiber.id = m.fibers.map RunFiber.id)
    (fun before after edit edge previous => by
      have next := edge.2 (by rw [previous.2]; exact unique)
      exact ⟨previous.1.trans next.1, next.2.trans previous.2⟩) path ⟨.refl L m, rfl⟩
  rwa [← Edits.fiber_words] at kept

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The canonical countdown plan only changes the token counter and emits a neutral park event. -/
theorem same_countdown_plan (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ)
    (targets : List FiberId) (resume : Resume ν) (fast : Bool) :
    L.Same m (countdownParkEdits interp m f targets resume fast).1 := by
  rw [Edits.countdown_word]
  apply L.same_run
  intro edit member held
  simp only [Edits.countdownWord] at member
  split at member
  · simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at member
    subst edit
    exact True.intro
  · simp only [List.mem_append, List.mem_singleton] at member
    rcases member with rfl | rfl
    · exact True.intro
    · exact ⟨rfl, rfl⟩

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The canonical scope-link plan has only neutral store, halt and diagnostic writes. -/
theorem same_linkScope_plan (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations α) :
    L.Same m (linkScopeEdits interp m mode scope target who extra).1 := by
  rw [Edits.link_plan_word]
  apply L.same_run
  intro edit member held
  unfold Edits.linkWord at member
  repeat' split at member
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  all_goals rcases member with rfl | rfl
  all_goals aesop (add norm [Neutral, consumedIn, producedIn, eventConsumed, eventProduced])

/-- A countdown park appends an observer to a target and records the park. -/
theorem same_countdown (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (unique : (m.fibers.map RunFiber.id).Nodup) (f : RunFiber ν σ β ε δ ι α χ)
    (targets : List FiberId) (resume : Resume ν) (fast : Bool) :
    L.Same m (countdownPark interp m f targets resume fast).1 := by
  change L.Same m (applyFiberEdits (countdownParkEdits interp m f targets resume fast).2.2.2
    (countdownParkEdits interp m f targets resume fast).1).1
  have rows : (countdownParkEdits interp m f targets resume fast).1.fibers = m.fibers := by
    rw [Edits.countdown_word]
    exact Edits.run_keeps (fun held => held.fibers) _
      (fun edit member => edit.keeps_fibers (Edits.countdown_misses m f targets edit member)) m
  exact (L.same_countdown_plan interp m f targets resume fast).trans
    (L.fiberEdits_kept _ _ (by rw [rows]; exact unique)).1

/-- Recording an interrupt keeps the stack, so the weight. -/
theorem interruptRecord_held (interp : RunInterp ν σ β ε δ ι α χ St) (who : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    L.held (interruptRecord interp who extra f).1 = L.held f := by
  exact L.interruptWithCause_held (interruptCause interp who extra f.id) f

/-- Recording an interrupt keeps the fiber's id. -/
theorem interruptRecord_key (interp : RunInterp ν σ β ε δ ι α χ St) (who : Option FiberId)
    (extra : ReasonAnnotations α) (f : RunFiber ν σ β ε δ ι α χ) :
    (interruptRecord interp who extra f).1.id = f.id := by
  exact interruptWithCause_key (interruptCause interp who extra f.id) f

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
  change L.Same m (applyFiberEdits (linkScopeEdits interp m mode scope target who extra).2
    (linkScopeEdits interp m mode scope target who extra).1).1
  have rows : (linkScopeEdits interp m mode scope target who extra).1.fibers = m.fibers := by
    rw [Edits.link_plan_word]
    exact Edits.run_keeps (fun held => held.fibers) _
      (fun edit member => edit.keeps_fibers (Edits.link_misses interp m mode scope target who edit member)) m
  exact (L.same_linkScope_plan interp m mode scope target who extra).trans
    (L.fiberEdits_kept _ _ (by rw [rows]; exact unique)).1

/-- An interrupt word uses the current lookup's stack and then emits a neutral record event. -/
theorem interrupt_payload_path (interp : RunInterp ν σ β ε δ ι α χ St) (who : FiberId)
    (extra : ReasonAnnotations α) (target : FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) :
    Effect4.Contracts.Path
      (fun before after edit => after = edit.apply before ∧
        (ForkLedger.Invariant.Ok before → L.Neutral edit before ∧ ForkLedger.Invariant.Ok after))
      acc.1 (interruptEach interp who extra [target] acc).1
      (Edits.interruptWord interp who extra target acc.1) := by
  apply Edits.interrupt_path interp who extra
  · intro m target old found
    refine ⟨rfl, fun ok => ⟨?_, ForkLedger.Invariant.update_ok ok _⟩⟩
    exact ⟨ok.idsUnique, old, by simpa only [RunMachine.id_of_fiber? found] using found,
      StackLedger.interruptRecord_key interp (some who) extra old,
      L.interruptRecord_held interp (some who) extra old⟩
  · intro m target
    exact ⟨rfl, fun ok => ⟨⟨rfl, rfl⟩, ForkLedger.Invariant.emit_ok ok _⟩⟩

/-- Interrupting a list of fibers records each interrupt. The nested commands have not run. -/
theorem same_interruptEach (interp : RunInterp ν σ β ε δ ι α χ St) (who : FiberId)
    (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α))
    (ok : ForkLedger.Invariant.Ok acc.1) :
    L.Same acc.1 (interruptEach interp who extra targets acc).1 := by
  exact L.same_ok_word
    (Edits.interrupts_path interp who extra (L.interrupt_payload_path interp who extra) targets acc) ok

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

/-- Settlement applies the ordered edit word between local write-back and disposition.
The edit interpretation keeps the saved-stack ledger. -/
theorem settle_balanced [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    {cap : Nat} (m : RunMachine ν σ β ε δ ι α χ St) (next : Iter ν σ β ε δ ι α χ St)
    (unique : (next.machine.fibers.map RunFiber.id).Nodup) (funded : L.Funded cap m)
    (balanced : L.Balanced m next) (id : FiberId) (rest : List (Cmd ν σ β ε δ ι α)) :
    L.Funded cap (settle id rest next).1 := by
  have installed := L.update_balanced m next unique funded balanced
  have bound := FiberSum.settle_le L.held (fun _ _ => rfl)
    (fun cause fiber => Nat.le_of_eq (L.interruptWithCause_held cause fiber))
    (fun _ => rfl) (fun _ => rfl) id rest next unique
  have fields := FiberSum.settle_fields id rest next
  have trace := congrArg (fun value => value.2.2) fields
  change (settle id rest next).1.trace = next.machine.trace at trace
  change L.consumedIn (settle id rest next).1.trace + L.total (settle id rest next).1 ≤
    L.producedIn (settle id rest next).1.trace + cap
  rw [trace]
  unfold Funded at installed
  change L.consumedIn next.machine.trace + L.total (next.machine.update next.fiber) ≤
    L.producedIn next.machine.trace + cap at installed
  exact Nat.le_trans (Nat.add_le_add_left bound _) installed

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
