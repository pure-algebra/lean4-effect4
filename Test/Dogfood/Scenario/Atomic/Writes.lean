import Test.Dogfood.Scenario.Atomic.StoreFacts
import Effect4.Laws.Auto.KernelRfl

/-!
Concept: store-typing R4, serving `Atomic.Store.shop_stages`.
The actual write terms connect their returned values to exact store changes.
These local transitions do not establish source uniqueness or a complete native history.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Scenario.Atomic.Store.Writes
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.P4RateLimiter (windowVal)

/-- The actual account value with its accumulated deposit identities. -/
def account (ids : List Nat) : Val :=
  recordOf ["balance", "history", "id"]
    [.nat ids.sum, .list (ids.map fun id => recordOf ["_tag", "amount"] [.str "Deposit", .nat id]), .str "acc-1"]

/-- An atomic admission returns its decision and updates the corresponding count. -/
theorem decision_exact (env : List Val) (used admitted rejected : Nat) :
    evalTerm (env ++ [windowVal used admitted rejected]) (decisionAt env.length) =
      some (if decide (used < 3) then .list [.bool true, windowVal (used + 1) (admitted + 1) rejected]
        else .list [.bool false, windowVal used admitted (rejected + 1)]) := by
  simp only [decisionAt, tfield, tsucc, tpair, evalTerm, evalTerms,
    List.getElem?_concat_length, Option.bind_eq_bind, Option.bind_some]
  kernel_rfl

/-- An atomic deposit appends its own identity and returns the new balance. -/
theorem deposit_exact (env : List Val) (ids : List Nat) (id : Nat) :
    evalTerm (env ++ [account ids]) (depositAt id env.length) =
      some (.list [.nat (ids.sum + id), account (ids ++ [id])]) := by
  simp only [depositAt, tpair, tfield, evalTerm, evalTerms,
    List.getElem?_concat_length, Option.bind_eq_bind, Option.bind_some]
  simp only [account, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero, List.map_append,
    List.map_cons, List.map_nil]
  kernel_rfl

/-- Refilling changes the used capacity and retains both decision counts. -/
theorem refill_exact (env : List Val) (used admitted rejected : Nat) :
    evalTerm (env ++ [windowVal used admitted rejected]) (refillAt env.length) =
      some (windowVal 0 admitted rejected) := by
  simp only [refillAt, evalTerm, List.getElem?_concat_length, Option.bind_eq_bind, Option.bind_some]
  kernel_rfl

/-- A cleanup appends the identity and the count captured by its preceding read. -/
theorem note_exact (env : List Val) (used admitted rejected id : Nat) (log : List Val) :
    evalTerm ((env ++ [windowVal used admitted rejected]) ++ [.list log])
      (noteAt id (env.length + 1)) =
      some (.list (log ++ [.list [.nat id, .nat (admitted + rejected)]])) := by
  simp only [noteAt, tpair, tfield, evalTerm, evalTerms, Nat.add_sub_cancel,
    Option.bind_eq_bind]
  simp only [List.getElem?_append, List.length_append, List.length_cons, List.length_nil]
  simp only [Nat.lt_irrefl, if_false, Nat.sub_self, List.getElem?_cons_zero, Nat.zero_add, Nat.lt_succ_self, if_true]
  kernel_rfl

/-- The native atomic modify uses the term's paired answer and next cell in one step. -/
theorem modify_exact (state : Stores) (cell : RefKey) (env : List Val)
    (term : Term) (before answer after : Val)
    (stored : refPeek state.refs cell = some before)
    (evaluated : evalTerm (env ++ [before]) term = some (.list [answer, after])) :
    syncOpStep (.refModify cell term env) state =
      some ({state with refs := refPoke state.refs cell after}, answer) := by
  change (refStep (.refModify cell term env) state.refs).map
    (fun step => ({state with refs := step.2}, step.1)) = _
  simp only [refStep, stored, Option.bind_some, evaluated]
  rfl

/-- The native atomic update writes the evaluated cell and returns unit. -/
theorem update_exact (state : Stores) (cell : RefKey) (env : List Val)
    (term : Term) (before after : Val)
    (stored : refPeek state.refs cell = some before)
    (evaluated : evalTerm (env ++ [before]) term = some after) :
    syncOpStep (.refUpdate cell term env) state =
      some ({state with refs := refPoke state.refs cell after}, .unit) := by
  change (refStep (.refUpdate cell term env) state.refs).map
    (fun step => ({state with refs := step.2}, step.1)) = _
  simp only [refStep, stored, Option.bind_some, evaluated, Option.map_some]

/-- The real decision writes and answers the same selected branch. -/
theorem decision_step (state : Stores) (cell : RefKey) (env : List Val)
    (used admitted rejected : Nat)
    (stored : refPeek state.refs cell = some (windowVal used admitted rejected)) :
    syncOpStep (.refModify cell (decisionAt env.length) env) state =
      if decide (used < 3) then
        some ({state with refs := (refPoke state.refs cell
          (windowVal (used + 1) (admitted + 1) rejected))}, .bool true)
      else some ({state with refs := (refPoke state.refs cell
        (windowVal used admitted (rejected + 1)))}, .bool false) := by
  have evaluated := decision_exact env used admitted rejected
  cases selected : decide (used < 3) with
  | true =>
    rw [selected] at evaluated
    exact modify_exact state cell env _ _ _ _ stored evaluated
  | false =>
    rw [selected] at evaluated
    exact modify_exact state cell env _ _ _ _ stored evaluated

/-- The real deposit appends one identity and retains the other stores. -/
theorem deposit_step (state : Stores) (cell : RefKey) (env : List Val) (ids : List Nat) (id : Nat)
    (stored : refPeek state.refs cell = some (account ids)) :
    syncOpStep (.refModify cell (depositAt id env.length) env) state =
      some ({state with refs := refPoke state.refs cell (account (ids ++ [id]))}, .nat (ids.sum + id)) :=
  modify_exact state cell env _ _ _ _ stored (deposit_exact env ids id)

/-- The real refill retains the admission and rejection totals. -/
theorem refill_step (state : Stores) (cell : RefKey) (env : List Val)
    (used admitted rejected : Nat)
    (stored : refPeek state.refs cell = some (windowVal used admitted rejected)) :
    syncOpStep (.refUpdate cell (refillAt env.length) env) state =
      some ({state with refs := refPoke state.refs cell (windowVal 0 admitted rejected)}, .unit) :=
  update_exact state cell env _ _ _ stored (refill_exact env used admitted rejected)

/-- The real cleanup appends the count retained by its preceding window read. -/
theorem note_step (state : Stores) (cell : RefKey) (env : List Val)
    (used admitted rejected id : Nat) (log : List Val)
    (stored : refPeek state.refs cell = some (.list log)) :
    syncOpStep (.refUpdate cell (noteAt id (env.length + 1))
      (env ++ [windowVal used admitted rejected])) state =
      some ({state with refs := (refPoke state.refs cell
        (.list (log ++ [.list [.nat id, .nat (admitted + rejected)]])))}, .unit) :=
  update_exact state cell _ _ _ _ stored (note_exact env used admitted rejected id log)

/-- The actual deposit observation reads precisely the accumulated identities. -/
theorem deposits_account (o : Observation) (ids : List Nat) :
    ({o with account := some (account ids)} : Observation).deposits = ids := by
  change (ids.map (fun id => recordOf ["_tag", "amount"] [.str "Deposit", .nat id])).filterMap
    (fun entry => match Record.read false entry "amount" with
      | some (.nat amount) => some amount
      | _ => none) = ids
  induction ids with
  | nil => rfl
  | cons id rest ih =>
    simp only [List.map_cons, List.filterMap_cons]
    change id :: _ = id :: rest
    rw [ih]

end Test.Dogfood.Scenario.Atomic.Store.Writes
