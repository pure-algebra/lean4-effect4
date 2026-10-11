import Test.Dogfood.Scenario.Atomic.Writer
import Test.Dogfood.Scenario.SourceOpportunity

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: the identity-membership clause of Atomic.Cleanup.log_debits.
The existing heap predicate and native history transport retain every cleanup identity.
The statement establishes membership, not the finalizer-start count bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterOwnership
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.HeapSites Effect4.Laws.Auto

local instance : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq

/-- Every identity outside the request list has zero count in this existing cell value. -/
def Owned (value : Val) : Prop := ∀ id, id ∉ requests → Writer.valueCount id value = 0

/-- A zero aggregate bounds each actual cell projection. -/
theorem heap_zero (chosen : Nat) (refs : RefHeap) (held : HeapOk Owned refs)
    (outside : chosen ∉ requests) : Writer.heapCount chosen refs = 0 := by
  revert held
  induction refs with
  | nil => intro _; rfl
  | cons value rest ih =>
    intro held
    have first := held 0 value rfl chosen outside
    have tail : HeapOk Owned rest := by
      intro index value found
      exact held (index + 1) value found
    simp only [Writer.heapCount, List.map_cons, List.sum_cons]
    rw [first, Nat.zero_add]
    exact ih tail

/-- An actual operation that cannot increase an outside identity keeps the existing heap predicate. -/
theorem count_keeps (op : SyncOp)
    (bound : ∀ id, id ∉ requests → ∀ state next answer,
      syncOpStep op state = some (next, answer) →
        Writer.heapCount id next.refs ≤ Writer.heapCount id state.refs) : OpKeeps Owned op := by
  intro state next answer stepped held index value found chosen outside
  have old := heap_zero chosen state.refs held outside
  have total := bound chosen outside state next answer stepped
  have cell : Writer.valueCount chosen value ≤ Writer.heapCount chosen next.refs :=
    Program.le_sum_of_mem _ _ (List.mem_map.mpr ⟨value, List.mem_of_getElem? found, rfl⟩)
  omega

/-- The actual update term is either the daemon refill or a request's literal note. -/
def knownUpdate (term : Term) (level : Nat) : Bool :=
  term == Store.refillAt level || requests.any (fun id => term == Store.noteAt id level)

/-- The additional source census keeps the literal note identities in the actual request list. -/
def knownSite : NativeOp → Option Nat → Bool
  | .refUpdateWith term, some level => knownUpdate term level
  | _, _ => true

theorem known_census :
    (Store.shopProgram.map fun root => (performSites root).all fun site =>
      knownSite site.2.1 site.2.2.2) = some true := by kernel_rfl

/-- A known native update cannot create an identity outside the actual request list. -/
theorem update_keeps (cell : RefKey) (env : List Val) (term : Term)
    (known : knownUpdate term env.length = true) : OpKeeps Owned (.refUpdate cell term env) := by
  simp only [knownUpdate, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at known
  rcases known with rfl | ⟨request, member, rfl⟩
  · apply count_keeps
    intro id _ state next answer stepped
    exact Writer.refill_count_le id cell env state next answer stepped
  · apply count_keeps
    intro id outside state next answer stepped
    have different : request ≠ id := by intro equal; subst id; exact outside member
    have flag : (request == id) = false := beq_eq_false_iff_ne.mpr different
    rw [Writer.note_heap_count request id cell env state next answer stepped, flag]
    exact Nat.le_refl _

/-- Each source allocation has no outside identity. -/
theorem allocations_owned (env : List Val) (request : Term) (value : Val)
    (selected : (request == Store.window0T || request == Store.account0T || request == Store.logT) = true)
    (evaluated : evalTerm env request = some value) : Owned value := by
  intro id _
  exact Writer.allocation_zero id env request value selected evaluated

/-- The actual shop's write sites retain the request identity predicate.
Consumer: the existing native heap history theorem. -/
theorem sites_owned (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built) :
    SitesKeep built.program Owned := by
  intro path row request env value op found level evaluated produced
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have listed := performSites_complete found
  rw [level] at listed
  have families := Store.shop_census
  have known := known_census
  rw [source] at families known
  have family := Store.family_of_siteOk (List.all_eq_true.mp (Option.some.inj families) _ listed)
  have site := List.all_eq_true.mp (Option.some.inj known) _ listed
  cases family with
  | make selected =>
    have operation : op = .refMake value := (Option.some.inj produced).symm
    rw [operation]
    exact Store.make_keeps value (allocations_owned env request value selected evaluated)
  | get => obtain ⟨key, rfl⟩ := Store.get_inv produced; exact Store.get_keeps ⟨key⟩
  | sleep => cases produced
  | decision =>
    obtain ⟨key, rfl⟩ := Store.modify_inv produced
    apply count_keeps
    intro id _ state next answer stepped
    exact Writer.decision_count_le id _ env state next answer stepped
  | deposit requestId =>
    obtain ⟨key, rfl⟩ := Store.modify_inv produced
    apply count_keeps
    intro id _ state next answer stepped
    exact Writer.deposit_count_le id requestId _ env state next answer stepped
  | refill =>
    obtain ⟨key, rfl⟩ := Store.update_inv produced
    exact update_keeps _ env _ site
  | note requestId =>
    obtain ⟨key, rfl⟩ := Store.update_inv produced
    exact update_keeps _ env _ site

/-- Every actual admitted history retains the request identities in all reference cells. -/
theorem history_owned (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (machine : NativeMachine) (history : Run.HistoryOf built budget.compileFuel machine) :
    HeapOk Owned machine.state.refs := by
  exact heap_sites_keep built budget.compileFuel Owned
    (SourceFragment.atomic_built_fragment built admitted) (sites_owned built admitted) machine
    (Run.history_control (Store.shop_table built admitted) history)

/-- The actual cleanup observation contains only request identities.
This closes the membership clause of the original cleanup-log obligation. -/
theorem logged_requests (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (machine : NativeMachine) (history : Run.HistoryOf built budget.compileFuel machine) :
    ∀ id ∈ (Store.observeM machine).cleaned, id ∈ requests := by
  intro id member
  by_contra outside
  have heap := history_owned built admitted machine history
  have zero := heap_zero id machine.state.refs heap outside
  have observed := Writer.observe_count_le_heap machine id
  have positive : 0 < (Store.observeM machine).cleaned.count id := List.count_pos_iff.mpr member
  omega

end Test.Dogfood.Scenario.Atomic.WriterOwnership
