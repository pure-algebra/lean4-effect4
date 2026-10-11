import Test.Dogfood.Scenario.Atomic.WriterFrames

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: actual primitive writer debit of Atomic.Cleanup.log_debits.
The native source-site census bounds every reference write by its active note reservation.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterSync
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Program.HeapSites Effect4.Laws.Auto
open WriterPhase WriterOwnership
local instance : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq

/-- An actual zero-count allocation leaves the total cleanup count unchanged. -/
theorem allocation_count (id : Nat) (value : Val) (state next : Stores) (answer : Val)
    (zero : Writer.valueCount id value = 0)
    (written : syncOpStep (.refMake value) state = some (next, answer)) :
    Writer.heapCount id next.refs = Writer.heapCount id state.refs := by
  change some ({state with refs := state.refs ++ [value]}, .cell ⟨state.refs.length⟩) = some (next, answer) at written
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj written)
  simp only [Writer.heapCount, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, zero, Nat.add_zero]

/-- A known update spends at most its actual chosen-note reservation. -/
theorem update_bound (id : Nat) (cell : RefKey) (env : List Val) (term : Term)
    (known : knownUpdate term env.length = true) (state next : Stores) (answer : Val)
    (written : syncOpStep (.refUpdate cell term env) state = some (next, answer)) :
    Writer.heapCount id next.refs ≤ Writer.heapCount id state.refs + operation id (.refUpdate cell term env) := by
  simp only [knownUpdate, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at known
  rcases known with rfl | ⟨request, _, rfl⟩
  · have bounded := Writer.refill_count_le id cell env state next answer written
    omega
  · rw [Writer.note_heap_count request id cell env state next answer written]
    by_cases same : request = id
    · subst request
      simp only [operation, beq_self_eq_true, ↓reduceIte, Nat.le_refl]
    · have excluded := beq_eq_false_iff_ne.mpr same
      rw [excluded]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      omega

/-- Every actual source-owned operation spends at most its active note reservation. -/
theorem origin_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (op : SyncOp) (origin : OpOrigin built.program op)
    (state next : Stores) (answer : Val) (written : syncOpStep op state = some (next, answer)) :
    Writer.heapCount id next.refs ≤ Writer.heapCount id state.refs + operation id op := by
  obtain ⟨point, row, request, value, found, scope, evaluated, produced⟩ := origin
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have listed := performSites_complete found
  change HeapSites.levelAt (.eff built.program) 0 point.path = some point.env.length at scope
  rw [scope] at listed
  have families := Store.shop_census
  have known := known_census
  rw [source] at families known
  have family := Store.family_of_siteOk (List.all_eq_true.mp (Option.some.inj families) _ listed)
  have site := List.all_eq_true.mp (Option.some.inj known) _ listed
  cases family with
  | make selected =>
    have same : op = .refMake value := (Option.some.inj produced).symm
    rw [same] at written ⊢
    rw [allocation_count id value state next answer (Writer.allocation_zero id point.env request value selected evaluated) written]
    exact Nat.le_refl _
  | get =>
    obtain ⟨key, rfl⟩ := Store.get_inv produced
    rw [syncOpStep_refGet_refs written]
    exact Nat.le_refl _
  | sleep => cases produced
  | decision =>
    obtain ⟨key, rfl⟩ := Store.modify_inv produced
    exact Writer.decision_count_le id _ point.env state next answer written
  | deposit requestId =>
    obtain ⟨key, rfl⟩ := Store.modify_inv produced
    exact Writer.deposit_count_le id requestId _ point.env state next answer written
  | refill =>
    obtain ⟨key, rfl⟩ := Store.update_inv produced
    exact update_bound id _ point.env _ site state next answer written
  | note requestId =>
    obtain ⟨key, rfl⟩ := Store.update_inv produced
    exact update_bound id _ point.env _ site state next answer written

/-- Actual administrative operations preserve the aggregate; owned writers consume their reservation. -/
theorem op_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (op : SyncOp) (owned : OpAt built.program op)
    (state next : Stores) (answer : Val) (written : syncOpStep op state = some (next, answer)) :
    Writer.heapCount id next.refs ≤ Writer.heapCount id state.refs + operation id op := by
  cases op
  case refMake | refSet | refGetAndSet | refSetAndGet | refUpdate | refGetAndUpdate
    | refUpdateAndGet | refUpdateSome | refGetAndUpdateSome | refUpdateSomeAndGet
    | refModify | refModifySome => exact origin_bound built admitted id _ owned state next answer written
  all_goals unfold syncOpStep at written
  all_goals repeat' split at written
  all_goals aesop (add norm unfold [refStep]) (add norm simp [operation])

/-- The actual native sync evaluator spends at most its suspended operation reservation. -/
theorem sync_bound (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (view : List (FiberId × ExitV)) (suspended : EffThunk)
    (owned : ThunkAt built.program suspended) (state next : Stores) (answer : Val)
    (written : (interpAt built.program view built.table).syncState suspended state = some (next, answer)) :
    Writer.heapCount id next.refs ≤ Writer.heapCount id state.refs + thunk id suspended := by
  cases suspended
  case op op => exact op_bound built admitted id op owned state next answer written
  case store stored =>
    cases stored
    case op op => exact op_bound built admitted id op owned state next answer written
    all_goals cases written
  all_goals cases written

end Test.Dogfood.Scenario.Atomic.WriterSync
