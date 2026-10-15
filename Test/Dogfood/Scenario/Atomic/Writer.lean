import Test.Dogfood.Scenario.Atomic.StoreFacts
import Effect4.Laws.Program.ControlSteps
import Test.Dogfood.Scenario.Atomic.SourcePaths
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: the existing Atomic.Cleanup.log_debits obligation.
These laws read the actual Atomic note term and its native store operation.
The command law retains other fibers and unfinished commands.
They establish one write, not its history-level permission from a finalizer start.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.Writer
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto

/-- Two-argument atom inversion used by the actual cleanup note. -/
private theorem eval_two (env : List Val) (atom : String) (left right : Term) (value : Val)
    (evaluated : evalTerm env (.app atom (.cons left (.cons right .nil))) = some value) :
    ∃ a b, evalTerm env left = some a ∧ evalTerm env right = some b ∧
      nativeAtom atom [a, b] = some value := by
  simp only [evalTerm, evalTerms, Option.bind_eq_bind, Option.bind_eq_some_iff] at evaluated
  obtain ⟨values, ⟨a, leftEval, rest, ⟨b, rightEval, tail, nilEval, restEq⟩, valuesEq⟩, atomEval⟩ := evaluated
  cases nilEval
  cases restEq
  cases valuesEq
  exact ⟨a, b, leftEval, rightEval, atomEval⟩

/-- The actual note term preserves the old list and appends one literal request identity.
Consumer: the cleanup-log writer debit. -/
theorem note_eval (id : Nat) (env : List Val) (old value : Val)
    (evaluated : evalTerm (env ++ [old]) (Store.noteAt id env.length) = some value) :
    ∃ entries seen, Val.asList? old = some entries ∧
      value = .list (entries ++ [.list [.nat id, seen]]) := by
  obtain ⟨front, back, oldEval, consEval, appended⟩ := eval_two (env ++ [old]) "append" _ _ value evaluated
  rw [Store.eval_var_last] at oldEval
  cases oldEval
  obtain ⟨entry, empty, entryEval, nilEval, consed⟩ := eval_two (env ++ [old]) "cons" _ _ back consEval
  change some (Val.list []) = some empty at nilEval
  cases nilEval
  change some (Val.list [entry]) = some back at consed
  cases consed
  change (Val.asList? old).bind (fun entries => some (Val.list (entries ++ [entry]))) = some value at appended
  obtain ⟨entries, oldList, result⟩ := Option.bind_eq_some_iff.mp appended
  have resultEq := Option.some.inj result
  obtain ⟨first, seen, literal, _, pairValue⟩ := Store.eval_pair entryEval
  have identity : first = .nat id := (Option.some.inj literal).symm
  subst first
  exact ⟨entries, seen, oldList, resultEq.symm.trans (by rw [pairValue])⟩

/-- The actual native update replaces only its selected cell with the one-entry append.
Consumer: the cleanup-log writer command clause. -/
theorem note_update (id : Nat) (cell : RefKey) (env : List Val)
    (state next : Stores) (answer : Val)
    (step : syncOpStep (.refUpdate cell (Store.noteAt id env.length) env) state = some (next, answer)) :
    ∃ old entries seen, refPeek state.refs cell = some old ∧ Val.asList? old = some entries ∧
      next.refs = refPoke state.refs cell (.list (entries ++ [.list [.nat id, seen]])) := by
  obtain ⟨old, value, peek, evaluated, written⟩ := Store.refUpdate_step step
  obtain ⟨entries, seen, oldList, valueEq⟩ := note_eval id env old value evaluated
  exact ⟨old, entries, seen, peek, oldList, written.trans (by rw [valueEq])⟩

/-- The existing cleanup observation applied to one list of log entries. -/
abbrev identities (entries : List Val) : List Nat :=
  Observation.cleaned {decisions := [], window := none, account := none, completed := 0, cleanups := entries}

/-- The actual observation reads one new identity from a singleton cleanup append. -/
theorem identities_append (entries : List Val) (id : Nat) (seen : Val) :
    identities (entries ++ [.list [.nat id, seen]]) = identities entries ++ [id] := by
  simp only [identities, Observation.cleaned, List.filterMap_append,
    List.filterMap_cons, List.filterMap_nil]

/-- The list view gives a scalar projection without assigning a new heap carrier. -/
def valueCount (id : Nat) (value : Val) : Nat :=
  (identities ((Val.asList? value).getD [])).count id

/-- One actual note adds exactly its literal identity to the selected cell's projection. -/
theorem note_value_count (id chosen : Nat) (env : List Val) (old value : Val)
    (evaluated : evalTerm (env ++ [old]) (Store.noteAt id env.length) = some value) :
    valueCount chosen value = valueCount chosen old + (if id == chosen then 1 else 0) := by
  obtain ⟨entries, seen, oldList, rfl⟩ := note_eval id env old value evaluated
  change (identities (entries ++ [.list [.nat id, seen]])).count chosen =
    (identities ((Val.asList? old).getD [])).count chosen + _
  rw [oldList, identities_append]
  simp only [Option.getD_some, List.count_append, List.count_cons, List.count_nil, Nat.zero_add]

/-- The existing heap rows retain a sum of the cleanup observation's scalar projections. -/
def heapCount (id : Nat) (refs : RefHeap) : Nat := (refs.map (valueCount id)).sum

/-- An indexed replacement changes only the selected cell's scalar projection.
Consumer: the actual Atomic note store update. -/
private theorem set_sum (weight : Val → Nat) (old value : Val) :
    ∀ (refs : RefHeap) (index : Nat), refs[index]? = some old →
      ((refs.set index value).map weight).sum + weight old =
        (refs.map weight).sum + weight value := by
  intro refs
  induction refs with
  | nil => intro index found; cases found
  | cons head tail ih =>
    intro index found
    cases index with
    | zero =>
      cases found
      simp only [List.set_cons_zero, List.map_cons, List.sum_cons]
      omega
    | succ index =>
      have result := ih index found
      simp only [List.set_cons_succ, List.map_cons, List.sum_cons]
      omega

/-- The actual note operation increments the heap projection once, independently of its cell key.
Consumer: the history-level finalizer issue and write-consumption invariant. -/
theorem note_heap_count (id chosen : Nat) (cell : RefKey) (env : List Val)
    (state next : Stores) (answer : Val)
    (step : syncOpStep (.refUpdate cell (Store.noteAt id env.length) env) state = some (next, answer)) :
    heapCount chosen next.refs = heapCount chosen state.refs + (if id == chosen then 1 else 0) := by
  obtain ⟨old, value, peek, evaluated, written⟩ := Store.refUpdate_step step
  have increment := note_value_count id chosen env old value evaluated
  have replacement := set_sum (valueCount chosen) old value state.refs cell.index peek
  rw [written]
  change ((state.refs.set cell.index value).map (valueCount chosen)).sum = _
  unfold heapCount
  omega

/-- A record write creates no cleanup pair in the existing observation.
Consumer: the other actual shop write families. -/
theorem record_frame_zero (id : Nat) (fields : List (String × Val)) :
    valueCount id (Record.frame fields) = 0 := rfl

/-- A successful record overwrite creates no cleanup pair, regardless of its old contents. -/
theorem record_set_zero (id : Nat) (old value next : Val) (field : String)
    (written : Record.set old field value = some next) : valueCount id next = 0 := by
  unfold Record.set at written
  obtain ⟨fields, _, result⟩ := Option.bind_eq_some_iff.mp written
  cases result
  rfl

/-- Replacing a selected cell with a zero-count value cannot increase the aggregate. -/
theorem poke_count_le (id : Nat) (refs : RefHeap) (cell : RefKey) (old value : Val)
    (found : refPeek refs cell = some old) (zero : valueCount id value = 0) :
    heapCount id (refPoke refs cell value) ≤ heapCount id refs := by
  have equation := set_sum (valueCount id) old value refs cell.index found
  change ((refs.set cell.index value).map (valueCount id)).sum ≤ _
  unfold heapCount
  omega

/-- The actual daemon refill cannot create a cleanup identity. -/
theorem refill_count_le (id : Nat) (cell : RefKey) (env : List Val)
    (state next : Stores) (answer : Val)
    (step : syncOpStep (.refUpdate cell (Store.refillAt env.length) env) state = some (next, answer)) :
    heapCount id next.refs ≤ heapCount id state.refs := by
  obtain ⟨old, value, peek, evaluated, written⟩ := Store.refUpdate_step step
  obtain ⟨target, replacement, _, _, result⟩ := Store.eval_recordSet evaluated
  rw [written]
  exact poke_count_le id state.refs cell old value peek
    (record_set_zero id target replacement value "used" result)

/-- The actual deposit writes a record and cannot create a cleanup identity. -/
theorem deposit_count_le (id request : Nat) (cell : RefKey) (env : List Val)
    (state next : Stores) (answer : Val)
    (step : syncOpStep (.refModify cell (Store.depositAt request env.length) env) state = some (next, answer)) :
    heapCount id next.refs ≤ heapCount id state.refs := by
  obtain ⟨old, value, pair, peek, evaluated, decoded, written⟩ := Store.refModify_step step
  obtain ⟨returned, updated, _, updateEval, rfl⟩ := Store.eval_pair evaluated
  have same : pair = (returned, updated) := (Option.some.inj decoded).symm
  obtain ⟨target, replacement, _, _, result⟩ := Store.eval_recordSet updateEval
  rw [written, same]
  exact poke_count_le id state.refs cell old updated peek
    (record_set_zero id target replacement updated "history" result)

/-- Either actual decision branch writes a record and cannot create a cleanup identity. -/
theorem decision_count_le (id : Nat) (cell : RefKey) (env : List Val)
    (state next : Stores) (answer : Val)
    (step : syncOpStep (.refModify cell (Store.decisionAt env.length) env) state = some (next, answer)) :
    heapCount id next.refs ≤ heapCount id state.refs := by
  obtain ⟨old, value, pair, peek, evaluated, decoded, written⟩ := Store.refModify_step step
  obtain ⟨used, admitted, rejected, first, yes, no, _, _, _, _, yesSet, noSet, selected⟩ :=
    Store.decision_eval evaluated
  rw [selected] at decoded
  cases branch : decide (used < 3) with
  | false =>
    rw [branch] at decoded
    have same : pair = (.bool false, no) := (Option.some.inj decoded).symm
    rw [written, same]
    exact poke_count_le id state.refs cell old no peek
      (record_set_zero id old (.nat (rejected + 1)) no "rejected" noSet)
  | true =>
    rw [branch] at decoded
    have same : pair = (.bool true, yes) := (Option.some.inj decoded).symm
    rw [written, same]
    exact poke_count_le id state.refs cell old yes peek
      (record_set_zero id first (.nat (admitted + 1)) yes "admitted" yesSet)

/-- Each actual initial allocation has no cleanup identity at any leading environment. -/
theorem allocation_zero (id : Nat) (env : List Val) (request : Term) (value : Val)
    (selected : (request == Store.window0T || request == Store.account0T || request == Store.logT) = true)
    (evaluated : evalTerm env request = some value) : valueCount id value = 0 := by
  simp only [Bool.or_eq_true, beq_iff_eq] at selected
  rcases selected with (rfl | rfl) | rfl
  · have result : evalTerm env Store.window0T = some (Record.frame
        [("admitted", .nat 0), ("rejected", .nat 0), ("used", .nat 0)]) := rfl
    rw [result] at evaluated
    cases evaluated
    rfl
  · have result : evalTerm env Store.account0T = some (Record.frame
        [("balance", .nat 0), ("history", .list []), ("id", .str "acc-1")]) := rfl
    rw [result] at evaluated
    cases evaluated
    rfl
  · have result : evalTerm env Store.logT = some (.list []) := rfl
    rw [result] at evaluated
    cases evaluated
    rfl

/-- An actual Atomic note command commits the one-entry increment before queued resumes.
This is a ControlSteps instance on the actual native operation and retains command residue. -/
theorem note_loop_count (root : NativeEff) (table : RowTable) (m : Api.Machine)
    (owner : FiberId) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (id chosen : Nat) (cell : RefKey) (env : List Val) (state : Stores) (value : Val)
    (yielding : Bool) (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : m.fiber? owner = some fiber)
    (current : fiber.frame.current = .sync (.op (.refUpdate cell (Store.noteAt id env.length) env)))
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 1 < fiber.maxOpsBeforeYield)
    (answer : syncOpStep (.refUpdate cell (Store.noteAt id env.length) env) m.state = some (state, value)) :
    heapCount chosen (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
      (.loop owner yielding) rest).1.state.refs =
        heapCount chosen m.state.refs + (if id == chosen then 1 else 0) := by
  rw [ControlSteps.loop_sync_op root table m owner fiber _ state value yielding rest
    found current interrupt override budget answer]
  exact note_heap_count id chosen cell env m.state state value answer

/-- The cleanup note is in the finalizer's continuation after its window read. -/
def notePath (id : Nat) : List Nat := SourcePaths.requestPath id ++ [1, 1, 0]

/-- The source uses the literal request identity and the captured cleanup reference slot. -/
def noteSite (root : NativeEff) (id : Nat) : Bool :=
  match SourceScope.levelAt (.eff root) 0 (notePath id), Node.at_ (.eff root) (notePath id) with
  | some level, some (.eff (.perform (.refUpdateWith term) request)) =>
      term == Store.noteAt id level && request == .var 2
  | _, _ => false

/-- Every actual Atomic finalizer contains this exact note operation at its source address.
This census certifies source data; the history writer permission remains separate. -/
theorem actual_note_census :
    (Store.shopProgram.map fun root => requests.all (noteSite root)) = some true := by
  kernel_rfl

/-- Successful admission retains the exact six-site cleanup operation census. -/
theorem actual_note_sites (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b) :
    ∀ id ∈ requests, noteSite b.program id = true := by
  have program : Store.shopProgram = some b.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains built).1]
    rfl
  have census := actual_note_census
  rw [program] at census
  exact List.all_eq_true.mp (Option.some.inj census)

/-- The actual note census gives the existing source node and its exact lexical level. -/
theorem actual_note_at (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (id : Nat) (member : id ∈ requests) :
    ∃ level, SourceScope.levelAt (.eff b.program) 0 (notePath id) = some level ∧
      Node.at_ (.eff b.program) (notePath id) =
        some (.eff (.perform (.refUpdateWith (Store.noteAt id level)) (.var 2))) := by
  have site := actual_note_sites b built id member
  unfold noteSite at site
  split at site
  · next level term request levelEq nodeEq =>
    have both := Bool.and_eq_true_iff.mp site
    have termEq := beq_iff_eq.mp both.1
    have requestEq := beq_iff_eq.mp both.2
    subst term
    subst request
    exact ⟨level, levelEq, nodeEq⟩
  · cases site

/-- Resolution at the actual cleanup note retains the captured key and literal request identity.
The source point supplies only its actual lexical length and captured request value. -/
theorem resolve_note (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (id : Nat) (member : id ∈ requests) (env : List Val) (fuel : Nat) (cell : RefKey)
    (scopeOwned : SourceScope.At b.program {path := notePath id, env, fuel := fuel + 1, tape := []})
    (captured : env[2]? = some (.cell cell)) :
    resolve b.program {path := notePath id, env, fuel := fuel + 1, tape := []} =
      .sync (.op (.refUpdate cell (Store.noteAt id env.length) env)) := by
  obtain ⟨level, levelEq, nodeEq⟩ := actual_note_at b built id member
  have same : level = env.length := Option.some.inj (levelEq.symm.trans scopeOwned)
  subst level
  rw [SourceScope.resolve_at _ _ _ nodeEq]
  simp only [compileEff, evalTerm, captured]
  rfl

/-- An actual resolved cleanup source command commits its literal identity once.
Consumer: the source-slot and finalizer-permission instance of the shared frame contract. -/
theorem note_source_loop_count (b : Api.Built) (built : Api.Author.build (shop .none) = .ok b)
    (m : Api.Machine) (owner : FiberId) (fiber : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (id chosen : Nat) (member : id ∈ requests) (env : List Val) (fuel : Nat) (cell : RefKey)
    (state : Stores) (value : Val) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (scopeOwned : SourceScope.At b.program {path := notePath id, env, fuel := fuel + 1, tape := []})
    (captured : env[2]? = some (.cell cell)) (found : m.fiber? owner = some fiber)
    (current : fiber.frame.current = resolve b.program {path := notePath id, env, fuel := fuel + 1, tape := []})
    (interrupt : fiber.frame.deferredInterrupt = false) (override : fiber.yieldOverride = none)
    (budget : fiber.currentOpCount + 1 < fiber.maxOpsBeforeYield)
    (answer : syncOpStep (.refUpdate cell (Store.noteAt id env.length) env) m.state = some (state, value)) :
    heapCount chosen (driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
      (.loop owner yielding) rest).1.state.refs =
        heapCount chosen m.state.refs + (if id == chosen then 1 else 0) := by
  rw [resolve_note b built id member env fuel cell scopeOwned captured] at current
  exact note_loop_count b.program b.table m owner fiber id chosen cell env state value yielding rest
    found current interrupt override budget answer

/-- The original cleanup observation reads no more identities than the heap projection.
Consumer: the existing cleanup-log debit, once finalizer issue and consumption transport closes. -/
theorem observe_count_le_heap (m : Api.Machine) (id : Nat) :
    (Store.observeM m).cleaned.count id ≤ heapCount id m.state.refs := by
  cases found : m.state.refs[2]? with
  | none =>
    change (identities (entries (m.state.refs[2]?))).count id ≤ _
    rw [found]
    exact Nat.zero_le _
  | some value =>
    have member := List.mem_of_getElem? found
    have selected : valueCount id value ≤ heapCount id m.state.refs :=
      Program.le_sum_of_mem _ _ (List.mem_map.mpr ⟨value, member, rfl⟩)
    cases value with
    | list values =>
      change (identities (entries (m.state.refs[2]?))).count id ≤ _
      rw [found]
      exact selected
    | _ =>
      change (identities (entries (m.state.refs[2]?))).count id ≤ _
      rw [found]
      exact Nat.zero_le _

end Test.Dogfood.Scenario.Atomic.Writer
