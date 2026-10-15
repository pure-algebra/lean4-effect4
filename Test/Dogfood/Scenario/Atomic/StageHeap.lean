import Test.Dogfood.Scenario.Atomic.StageCounts

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the joint native transition and observation of `Atomic.Store.shop_stages`.
The three actual cells retain the finite stage counts, deposited identities and positive cleanup witnesses.
This relation is not yet a history invariant.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageWorld
open Effect4 Effect4.Machine Effect4.Program
open Store (Stage)

local instance : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq

/-- A cleanup log contains an actual entry for this request with a positive observed decision count. -/
def PositiveLog (id : Nat) (log : List Val) : Prop :=
  ∃ seen, .list [.nat id, .nat seen] ∈ log ∧ 1 ≤ seen

/-- The actual shop heap agrees with one shared request stage assignment. -/
structure HeapAt (world : World) (state : Stores) : Prop where
  witness : ∃ used ids log,
    state.refs = [Test.Dogfood.P4RateLimiter.windowVal used (admittedCount world) (rejectedCount world),
      Store.Writes.account ids, .list log] ∧
    (∀ id ∈ requests, ids.count id = if world.stages id = .deposited then 1 else 0) ∧
    ids.length = depositedCount world ∧
    (∀ id ∈ ids, id ∈ requests) ∧
    (∀ id, world.cleaned id = true → PositiveLog id log)

/-- The actual three-cell initializer starts before every request decision and cleanup. -/
def initialWorld : World := ⟨fun _ => .waiting, fun _ => false, 1⟩

/-- The bare initializer's exact heap supplies the numeric stage base case. -/
theorem initial_heap (state : Stores)
    (refs : state.refs = [Test.Dogfood.P4RateLimiter.windowVal 0 0 0,
      Store.Writes.account [], .list []]) : HeapAt initialWorld state := by
  refine ⟨⟨0, [], [], refs, ?_, rfl, ?_, ?_⟩⟩
  · intro id member
    rfl
  · intro id member
    cases member
  · intro id impossible
    cases impossible

/-- A request write retains the root counter and every other request's stage and cleanup flag. -/
def RequestChange (before after : World) (owner : Nat) : Prop :=
  after.nextId = before.nextId ∧ ∀ other, other ≠ owner →
    before.stages other = after.stages other ∧ before.cleaned other = after.cleaned other

theorem request_change_refl (world : World) (owner : Nat) : RequestChange world world owner :=
  ⟨rfl, fun _ _ => ⟨rfl, rfl⟩⟩

theorem request_change_stage (world : World) (owner : Nat) (stage : Stage) :
    RequestChange world (setStage world owner stage) owner := by
  refine ⟨rfl, ?_⟩
  intro other different
  exact ⟨by simp only [setStage, if_neg different], rfl⟩

theorem request_change_cleanup (world : World) (owner : Nat) (positive : Bool) :
    RequestChange world (markCleaned world owner positive) owner := by
  refine ⟨rfl, ?_⟩
  intro other different
  exact ⟨rfl, by simp only [markCleaned, if_neg different]⟩

/-- An actual deposit stage certifies that the current window has observed a decision. -/
theorem deposited_positive (world : World) (id : Nat) (member : id ∈ requests)
    (deposited : world.stages id = .deposited) :
    1 ≤ admittedCount world + rejectedCount world := by
  have present : id ∈ requests.filter (fun key => (world.stages key).counts) :=
    List.mem_filter.mpr ⟨member, by rw [deposited]; rfl⟩
  have positive := List.length_pos_of_mem present
  change 0 < admittedCount world at positive
  omega

/-- Reading the real first cell retains the request-specific positive-count obligation. -/
theorem window_answer (world : World) (state : Stores) (heap : HeapAt world state)
    (id : Nat) (member : id ∈ requests) :
    ∃ used, refPeek state.refs ⟨0⟩ = some
      (Test.Dogfood.P4RateLimiter.windowVal used (admittedCount world) (rejectedCount world)) ∧
      ValueAt world (.seen id)
        (Test.Dogfood.P4RateLimiter.windowVal used (admittedCount world) (rejectedCount world)) := by
  obtain ⟨used, ids, log, refs, counts, length, owned, cleaned⟩ := heap.witness
  refine ⟨used, ?_, used, admittedCount world, rejectedCount world, rfl, ?_⟩
  · rw [refPeek, refs]
    rfl
  · exact deposited_positive world id member
/-- A window write preserves the remaining heap fields when no request changes deposit status. -/
theorem HeapAt.window_write (before after : World) (state : Stores) (heap : HeapAt before state)
    (used : Nat) (depositStatus : ∀ id, (after.stages id = .deposited) ↔ (before.stages id = .deposited))
    (deposits : depositedCount after = depositedCount before)
    (cleaned : ∀ id, after.cleaned id = before.cleaned id) :
    HeapAt after {state with refs := (refPoke state.refs ⟨0⟩
      (Test.Dogfood.P4RateLimiter.windowVal used (admittedCount after) (rejectedCount after)))} := by
  obtain ⟨oldUsed, ids, log, refs, counts, length, owned, logged⟩ := heap.witness
  refine ⟨⟨used, ids, log, ?_, ?_, length.trans deposits.symm, owned, ?_⟩⟩
  · change refPoke state.refs ⟨0⟩ _ = _
    rw [refs]
    rfl
  · intro id member
    simpa only [depositStatus id] using counts id member
  · intro id positive
    exact logged id ((cleaned id) ▸ positive)

/-- An admitted or rejected decision does not create a deposited request. -/
theorem setStage_deposit_iff (world : World) (id : Nat) (next : Stage)
    (waiting : world.stages id = .waiting) (undeposited : next ≠ .deposited) (selected : Nat) :
    ((setStage world id next).stages selected = .deposited) ↔ world.stages selected = .deposited := by
  by_cases same : selected = id
  · subst selected
    simp only [setStage, ↓reduceIte, waiting, undeposited, reduceCtorEq]
  · simp only [setStage, if_neg same]

/-- The actual atomic decision advances its heap counts and its answer in one shared world. -/
theorem decision_heap (world : World) (id : Nat) (member : id ∈ requests)
    (waiting : world.stages id = .waiting) (state : Stores) (env : List Val) (heap : HeapAt world state) :
    ∃ after next answer,
      syncOpStep (.refModify ⟨0⟩ (Store.decisionAt env.length) env) state = some (after, answer) ∧
      Future world next ∧ RequestChange world next id ∧ HeapAt next after ∧ ValueAt next (.decision id) answer := by
  obtain ⟨used, ids, log, refs, counts, length, owned, logged⟩ := heap.witness
  have peek : refPeek state.refs ⟨0⟩ = some
      (Test.Dogfood.P4RateLimiter.windowVal used (admittedCount world) (rejectedCount world)) := by
    rw [refPeek, refs]
    rfl
  have actual := Store.Writes.decision_step state ⟨0⟩ env used (admittedCount world) (rejectedCount world) peek
  cases selected : decide (used < 3) with
  | false =>
    rw [selected] at actual
    obtain ⟨admitted, rejected, deposited⟩ := count_reject world id member waiting
    refine ⟨_, setStage world id .rejected, .bool false, actual, ?_, request_change_stage world id .rejected, ?_, ?_⟩
    · apply setStage_future
      rw [waiting]
      exact .waiting _
    · have held := HeapAt.window_write world (setStage world id .rejected) state heap used
        (setStage_deposit_iff world id .rejected waiting (by intro impossible; cases impossible)) deposited (fun _ => rfl)
      rw [admitted, rejected] at held
      exact held
    · simp only [ValueAt, setStage, ↓reduceIte, Bool.false_eq_true]
  | true =>
    rw [selected] at actual
    obtain ⟨admitted, rejected, deposited⟩ := count_admit world id member waiting
    refine ⟨_, setStage world id .admitted, .bool true, actual, ?_, request_change_stage world id .admitted, ?_, ?_⟩
    · apply setStage_future
      rw [waiting]
      exact .waiting _
    · have held := HeapAt.window_write world (setStage world id .admitted) state heap (used + 1)
        (setStage_deposit_iff world id .admitted waiting (by intro impossible; cases impossible)) deposited (fun _ => rfl)
      rw [admitted, rejected] at held
      exact held
    · simp only [ValueAt, setStage, ↓reduceIte]
/-- The actual atomic deposit appends this identity once and advances the same stage world. -/
theorem deposit_heap (world : World) (id : Nat) (member : id ∈ requests)
    (selected : world.stages id = .admitted) (state : Stores) (env : List Val) (heap : HeapAt world state) :
    ∃ after answer,
      syncOpStep (.refModify ⟨1⟩ (Store.depositAt id env.length) env) state = some (after, answer) ∧
      Future world (setStage world id .deposited) ∧
      RequestChange world (setStage world id .deposited) id ∧ HeapAt (setStage world id .deposited) after ∧
      ValueAt (setStage world id .deposited) (.deposit id) answer := by
  obtain ⟨used, ids, log, refs, counts, length, owned, logged⟩ := heap.witness
  have peek : refPeek state.refs ⟨1⟩ = some (Store.Writes.account ids) := by
    rw [refPeek, refs]
    rfl
  refine ⟨_, .nat (ids.sum + id), Store.Writes.deposit_step state ⟨1⟩ env ids id peek, ?_, request_change_stage world id .deposited, ?_, ?_⟩
  · apply setStage_future
    rw [selected]
    exact .deposit
  · obtain ⟨admitted, rejected, deposited⟩ := count_deposit world id member selected
    refine ⟨⟨used, ids ++ [id], log, ?_, ?_, ?_, ?_, logged⟩⟩
    · change refPoke state.refs ⟨1⟩ _ = _
      rw [refs, admitted, rejected]
      rfl
    · intro key present
      rw [List.count_append, List.count_singleton, counts key present]
      by_cases same : key = id
      · subst key
        simp only [selected, setStage, ↓reduceIte, reduceCtorEq, Nat.zero_add, beq_self_eq_true]
      · have different : (id == key) = false := beq_eq_false_iff_ne.mpr (Ne.symm same)
        simp only [setStage, if_neg same, different, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    · rw [List.length_append, List.length_singleton, length, deposited]
    · intro key present
      rcases List.mem_append.mp present with old | fresh
      · exact owned key old
      · have same := List.mem_singleton.mp fresh
        exact same ▸ member
  · simp only [ValueAt, setStage, ↓reduceIte]
/-- A refill changes only the current window usage and retains every stage count. -/
theorem refill_heap (world : World) (state : Stores) (env : List Val) (heap : HeapAt world state) :
    ∃ after, syncOpStep (.refUpdate ⟨0⟩ (Store.refillAt env.length) env) state = some (after, .unit) ∧
      HeapAt world after := by
  obtain ⟨used, ids, log, refs, counts, length, owned, logged⟩ := heap.witness
  have peek : refPeek state.refs ⟨0⟩ = some
      (Test.Dogfood.P4RateLimiter.windowVal used (admittedCount world) (rejectedCount world)) := by
    rw [refPeek, refs]
    rfl
  exact ⟨_, Store.Writes.refill_step state ⟨0⟩ env used (admittedCount world) (rejectedCount world) peek,
    HeapAt.window_write world world state heap 0 (fun _ => Iff.rfl) rfl (fun _ => rfl)⟩

/-- Appending an actual cleanup entry retains earlier positive log witnesses. -/
theorem PositiveLog.append (id : Nat) (before extra : List Val) (held : PositiveLog id before) :
    PositiveLog id (before ++ extra) := by
  obtain ⟨seen, member, positive⟩ := held
  exact ⟨seen, List.mem_append_left extra member, positive⟩

/-- The actual cleanup note records precisely the captured count and its positive witness. -/
theorem note_heap (world : World) (id : Nat) (state : Stores) (env : List Val)
    (used admitted rejected : Nat) (heap : HeapAt world state)
    (positive : world.stages id = .deposited → 1 ≤ admitted + rejected) :
    let next := markCleaned world id (decide (1 ≤ admitted + rejected))
    ∃ after,
      syncOpStep (.refUpdate ⟨2⟩ (Store.noteAt id (env.length + 1))
        (env ++ [Test.Dogfood.P4RateLimiter.windowVal used admitted rejected])) state = some (after, .unit) ∧
      Future world next ∧ RequestChange world next id ∧ HeapAt next after ∧ ValueAt next (.note id) .unit := by
  dsimp only
  obtain ⟨currentUsed, ids, log, refs, counts, length, owned, logged⟩ := heap.witness
  have peek : refPeek state.refs ⟨2⟩ = some (.list log) := by
    rw [refPeek, refs]
    rfl
  refine ⟨_, Store.Writes.note_step state ⟨2⟩ env used admitted rejected id log peek,
    markCleaned_future world id _, request_change_cleanup world id _, ?_, rfl, ?_⟩
  · refine ⟨⟨currentUsed, ids, log ++ [.list [.nat id, .nat (admitted + rejected)]], ?_, counts, length, owned, ?_⟩⟩
    · change refPoke state.refs ⟨2⟩ _ = _
      rw [refs]
      rfl
    · intro key marked
      by_cases same : key = id
      · subst key
        simp only [markCleaned, ↓reduceIte] at marked
        rcases Bool.or_eq_true_iff.mp marked with prior | fresh
        · exact PositiveLog.append id log _ (logged id prior)
        · exact ⟨admitted + rejected, List.mem_append_right log (List.mem_singleton_self _), of_decide_eq_true fresh⟩
      · have prior : world.cleaned key = true := by
          simpa only [markCleaned, if_neg same] using marked
        exact PositiveLog.append key log _ (logged key prior)
  · intro deposited
    have seen := positive deposited
    simp only [markCleaned, decide_eq_true seen, Bool.or_true, ↓reduceIte]
end Test.Dogfood.Scenario.Atomic.StageWorld
