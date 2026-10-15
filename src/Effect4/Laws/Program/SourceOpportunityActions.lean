import Effect4.Laws.Program.SourceOpportunityEvaluation

/-!
Concept: scope-lifetime-finalization, R11.
Question: native action debit for the original application registration bounds.
Consumer: actual native evaluation and complete source opportunity command accounting.
This numeric projection reads the programs of existing actions.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.SourceScope.Opportunities
open Effect4 Effect4.Machine Effect4.Program

/-- Action programs reserve only the existing code which the action can launch.
Consumer: native fork, mask and race installation debit. -/
def actionWeight (weight : NCode → Nat) : NAction → Nat
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ => weight body
  | .raceAll bodies _ | .raceAllFirst bodies _ | .closePar bodies => (bodies.map weight).sum
  | _ => 0

/-- The lexical source ledger instantiates the shared action reading. -/
abbrev action (root : NativeEff) (q : List Nat) := actionWeight (current root q)

/-- A source race's distinct entrant addresses share its parent reservation.
Consumer: native race action debit. -/
theorem entrants_le_with (root : NativeEff) (q : List Nat) (weight : NCode → Nat)
    (compileBound : ∀ program point, Node.at_ (.eff root) point.path = some (.eff program) →
      weight (compileEff program point) ≤ below q point.path) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) :
    ((actionAt.entrants bodies p).map (weight)).sum ≤ below q p.path := by
  revert found
  fun_induction actionAt.entrants bodies p
  case case1 point => intro found; exact Nat.zero_le _
  case case2 head rest point ih =>
    intro found
    have first : Node.at_ (.eff root) (point.child 0).path = some (.eff head) := by
      change Node.at_ (.eff root) (point.path ++ [0]) = some (.eff head)
      rw [Node.at_snoc, found]
      rfl
    have tail : Node.at_ (.eff root) (point.child 1).path = some (.effs rest) := by
      change Node.at_ (.eff root) (point.path ++ [1]) = some (.effs rest)
      rw [Node.at_snoc, found]
      rfl
    have left := compileBound head (point.child 0) first
    have right := ih tail
    have combined := siblings_le q point.path 0 1 (by decide)
    change weight (compileEff head (point.child 0)) +
      ((actionAt.entrants rest (point.child 1)).map (weight)).sum ≤ below q point.path
    change weight (compileEff head (point.child 0)) ≤ below q (point.path ++ [0]) at left
    change ((actionAt.entrants rest (point.child 1)).map (weight)).sum ≤ below q (point.path ++ [1]) at right
    omega

/-- The original entrant budget is an instance of the common source-address bound. -/
theorem entrants_le (root : NativeEff) (q : List Nat) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) :
    ((actionAt.entrants bodies p).map (current root q)).sum ≤ below q p.path :=
  entrants_le_with root q (current root q) (compile_le root q) bodies p found

/-- A stored administrative action cannot introduce another selected source opportunity.
Consumer: native action interpreter debit. -/
theorem store_action_zero (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (callback : ActionName) (owned : StoreActionAt root callback) :
    action root q (embedAction (actionOf callback)) = 0 := by
  cases callback
  case fork | forkIn | forkScoped | setInterruptible => exact prog_zero root q clear _ owned
  case closePar order exit =>
    change ((order.map (fun fin => finProgram fin exit)).map embed |>.map (current root q)).sum = 0
    simp only [List.map_map, Function.comp_def]
    have zero (items : List FinName) (held : ∀ fin ∈ items, FinAt root fin) :
        (items.map (fun fin => current root q (embed (finProgram fin exit)))).sum = 0 := by
      induction items with
      | nil => rfl
      | cons first rest ih =>
        have head := fin_program_zero root q clear first exit (held first (.head _))
        have tail := ih (fun fin member => held fin (.tail _ member))
        simp only [List.map_cons, List.sum_cons, head, tail, Nat.add_zero]
    exact zero order owned.1
  case raceAll race =>
    cases race
    all_goals aesop (add norm simp [actionOf, embedAction, action, actionWeight, raceEntrants, current, cata_prim, thunk, name, push, embed, StoreActionAt]) (add safe apply [(prog_zero root q clear)])
  all_goals rfl

/-- A source action reserves only descendants of its existing suspension point.
Consumer: actual fork and race evaluator accounting. -/
theorem source_action_le_with (root : NativeEff) (q : List Nat) (weight : NCode → Nat)
    (compileBound : ∀ program point, Node.at_ (.eff root) point.path = some (.eff program) →
      weight (compileEff program point) ≤ below q point.path)
    (resolveBound : ∀ point, weight (resolve root point) ≤ below q point.path) (point : Point) (next : NAction)
    (found : actionAt root point = some next) :
    actionWeight weight next ≤ thunk root q (.act point) := by
  fun_cases actionAt root point
  case case1 body source =>
    simp only [actionAt, source] at found
    cases found
    simpa only [actionWeight, thunk, source] using
      Nat.le_trans (resolveBound (point.child 0)) (child_le q point.path 0)
  case case2 body source =>
    simp only [actionAt, source] at found
    cases found
    simpa only [actionWeight, thunk, source] using
      Nat.le_trans (resolveBound (point.child 0)) (child_le q point.path 0)
  case case3 saved body source =>
    simp only [actionAt, source] at found
    cases found
    simpa only [actionWeight, thunk, source] using
      Nat.le_trans (resolveBound (point.child 0)) (child_le q point.path 0)
  case case4 a source child refusal handles =>
    have forkBound : weight (resolve root ((point.child 0).child 0)) ≤ below q point.path := by
      have body := resolveBound ((point.child 0).child 0)
      have inner := child_le q (point.child 0).path 0
      exact Nat.le_trans body (Nat.le_trans inner (child_le q point.path 0))
    have raceBound (bodies : Effs NativeOp)
        (node : (.action a : Node NativeOp).child 0 = some (.effs bodies)) :
        ((actionAt.entrants bodies ((point.child 0).child 0)).map (weight)).sum ≤ below q point.path := by
      have location : Node.at_ (.eff root) ((point.child 0).child 0).path = some (.effs bodies) := by
        change Node.at_ (.eff root) (point.path ++ [0] ++ [0]) = some (.effs bodies)
        rw [Node.at_snoc, Node.at_snoc, source]
        exact node
      have entered := entrants_le_with root q weight compileBound bodies ((point.child 0).child 0) location
      exact Nat.le_trans entered (Nat.le_trans (child_le q (point.child 0).path 0) (child_le q point.path 0))
    simp only [actionAt, source] at found
    cases a
    all_goals repeat' split at found
    all_goals aesop (add norm simp [actionWeight, thunk, source, Node.child]) (add safe apply [raceBound, forkBound])
  case case5 noMask noInterrupt noRestore noAction =>
    unfold actionAt at found
    repeat' split at found
    all_goals aesop

/-- The original source action uses the common program-slot budget. -/
theorem source_action_le (root : NativeEff) (q : List Nat) (point : Point) (next : NAction)
    (found : actionAt root point = some next) :
    action root q next ≤ thunk root q (.act point) :=
  source_action_le_with root q (current root q) (compile_le root q) (resolve_le root q) point next found

/-- A delayed scoped fork reserves only descendants of its existing source point.
Consumer: native action interpreter debit. -/
theorem fork_scoped_le_with (root : NativeEff) (q : List Nat) (weight : NCode → Nat)
    (resolveBound : ∀ point, weight (resolve root point) ≤ below q point.path) (point : Point) (scope : Nat) (next : NAction)
    (found : forkScopedAt root point scope = some next) : actionWeight weight next ≤ thunk root q (.forkInAt point scope) := by
  unfold forkScopedAt at found
  split at found
  · cases found
    have bound := resolveBound ((point.child 0).child 0)
    exact Nat.le_trans bound (Nat.le_trans (child_le q (point.child 0).path 0) (child_le q point.path 0))
  · cases found

/-- The original scoped fork uses the common resolution bound. -/
theorem fork_scoped_le (root : NativeEff) (q : List Nat) (point : Point) (scope : Nat) (next : NAction)
    (found : forkScopedAt root point scope = some next) : action root q next ≤ thunk root q (.forkInAt point scope) :=
  fork_scoped_le_with root q (current root q) (resolve_le root q) point scope next found

/-- Action accounting follows the same actual source, stored and masked program slots.
Consumer: the lexical and full finalizer source ledgers. -/
structure ActionBounds (root : NativeEff) (weight : NCode → Nat) (reserve : EffThunk → Nat)
    (T : EffThunk → Prop) : Prop where
  source : ∀ point next, T (.act point) → actionAt root point = some next →
    actionWeight weight next ≤ reserve (.act point)
  scopedFork : ∀ point scope next, T (.forkInAt point scope) → forkScopedAt root point scope = some next →
    actionWeight weight next ≤ reserve (.forkInAt point scope)
  stored : ∀ callback, T (.store (.act callback)) →
    actionWeight weight (embedAction (actionOf callback)) ≤ reserve (.store (.act callback))
  acquire : ∀ point context, T (.acquireMasked point context) →
    weight (.onSuccess (.withFiber (.store (.act .ambientScope))) (.acquireIn point context)) ≤ reserve (.acquireMasked point context)
  release : ∀ point previous, T (.releaseMasked point previous) →
    weight (.onExit (resolve root point) (.restoreCtx previous) false) ≤ reserve (.releaseMasked point previous)
  layer : ∀ point memo scope, T (.forkLayer point memo scope) →
    weight (resolveLayer root point memo scope) ≤ reserve (.forkLayer point memo scope)
  provide : ∀ update body flag, T (.provideMasked update body flag) →
    weight (.onSuccess (.withFiber .getCtx) (.updateThen update body flag)) ≤ reserve (.provideMasked update body flag)
  restore : ∀ body flag, T (.restoreRegion body flag) →
    weight (regionCode root body) ≤ reserve (.restoreRegion body flag)

/-- One native action interpreter walk supplies every program-slot accounting instance. -/
theorem interp_action_bound (root : NativeEff) (completed) (table : RowTable)
    (weight : NCode → Nat) (reserve : EffThunk → Nat) (T : EffThunk → Prop)
    (bounds : ActionBounds root weight reserve T) (suspended : EffThunk) (next : NAction)
    (owned : T suspended) (found : (interpAt root completed table).withFiberOf suspended = some next) :
    actionWeight weight next ≤ reserve suspended := by
  cases suspended
  case act point => exact bounds.source point next owned found
  case forkInAt point scope => exact bounds.scopedFork point scope next owned found
  case store stored =>
    cases stored
    case act callback => cases found; exact bounds.stored callback owned
    all_goals cases found
  case acquireMasked point context => cases found; exact bounds.acquire point context owned
  case releaseMasked point previous => cases found; exact bounds.release point previous owned
  case forkLayer point memo scope => cases found; exact bounds.layer point memo scope owned
  case provideMasked update body flag => cases found; exact bounds.provide update body flag owned
  case restoreRegion body flag => cases found; exact bounds.restore body flag owned
  all_goals aesop (add norm simp [interpAt, interpOf, actionWeight]) (add safe apply [Nat.zero_le])

/-- The original lexical ledger supplies the common action accounting contract. -/
theorem sourceActionBounds (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q) :
    ActionBounds root (current root q) (thunk root q) (ThunkAt root) where
  source := fun point next _ found => source_action_le root q point next found
  scopedFork := fun point scope next _ found => fork_scoped_le root q point scope next found
  stored := fun callback owned => Nat.le_of_eq (store_action_zero root q clear callback owned)
  acquire := by
    intro point context _
    simp only [current, cata_prim, thunk, name, push, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  release := by
    intro point previous _
    simpa only [current, cata_prim, name, push, Nat.add_zero, thunk] using resolve_le root q point
  layer := fun _ _ _ owned => owned.elim
  provide := by
    intro update body flag owned
    cases body
    case program point =>
      simp only [current, cata_prim, thunk, name, push, Nat.zero_add, Nat.add_zero, Nat.le_refl]
    all_goals exact owned.elim
  restore := by
    intro body flag owned
    cases body
    case program point => simpa only [regionCode, thunk] using resolve_le root q point
    all_goals exact owned.elim

/-- The actual native action interpreter retains only its existing source reservation.
Consumer: native evaluator installation and application registration uniqueness. -/
theorem interp_action_le (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (completed) (table : RowTable) (suspended : EffThunk) (next : NAction)
    (owned : ThunkAt root suspended)
    (found : (interpAt root completed table).withFiberOf suspended = some next) :
    action root q next ≤ thunk root q suspended :=
  interp_action_bound root completed table (current root q) (thunk root q) (ThunkAt root)
    (sourceActionBounds root q clear) suspended next owned found

end Effect4.Program.SourceScope.Opportunities
