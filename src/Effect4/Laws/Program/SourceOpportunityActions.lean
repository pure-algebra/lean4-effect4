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
def action (root : NativeEff) (q : List Nat) : NAction → Nat
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ => current root q body
  | .raceAll bodies _ | .raceAllFirst bodies _ | .closePar bodies => (bodies.map (current root q)).sum
  | _ => 0

/-- A source race's distinct entrant addresses share its parent reservation.
Consumer: native race action debit. -/
theorem entrants_le (root : NativeEff) (q : List Nat) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) :
    ((actionAt.entrants bodies p).map (current root q)).sum ≤ below q p.path := by
  revert found
  fun_induction actionAt.entrants bodies p
  case case1 point => intro found; exact Nat.zero_le _
  case case2 head rest point ih =>
    intro found
    have first : Node.at_ (.eff root) (point.child 0).path = some (.eff head) := by
      change Node.at_ (.eff root) (point.path ++ [0]) = some (.eff head)
      rw [Agreement.Node.at_append, found]
      rfl
    have tail : Node.at_ (.eff root) (point.child 1).path = some (.effs rest) := by
      change Node.at_ (.eff root) (point.path ++ [1]) = some (.effs rest)
      rw [Agreement.Node.at_append, found]
      rfl
    have left := compile_le root q head (point.child 0) first
    have right := ih tail
    have combined := siblings_le q point.path 0 1 (by decide)
    change current root q (compileEff head (point.child 0)) +
      ((actionAt.entrants rest (point.child 1)).map (current root q)).sum ≤ below q point.path
    change current root q (compileEff head (point.child 0)) ≤ below q (point.path ++ [0]) at left
    change ((actionAt.entrants rest (point.child 1)).map (current root q)).sum ≤ below q (point.path ++ [1]) at right
    omega

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
    all_goals aesop (add norm simp [actionOf, embedAction, action, raceEntrants, current, cata_prim, thunk, name, push, embed, StoreActionAt]) (add safe apply [(prog_zero root q clear)])
  all_goals rfl

/-- A source action reserves only descendants of its existing suspension point.
Consumer: actual fork and race evaluator accounting. -/
theorem source_action_le (root : NativeEff) (q : List Nat) (point : Point) (next : NAction)
    (found : actionAt root point = some next) :
    action root q next ≤ thunk root q (.act point) := by
  fun_cases actionAt root point
  case case1 body source =>
    simp only [actionAt, source] at found
    cases found
    simpa only [action, thunk, source] using
      Nat.le_trans (resolve_le root q (point.child 0)) (child_le q point.path 0)
  case case2 body source =>
    simp only [actionAt, source] at found
    cases found
    simpa only [action, thunk, source] using
      Nat.le_trans (resolve_le root q (point.child 0)) (child_le q point.path 0)
  case case3 saved body source =>
    simp only [actionAt, source] at found
    cases found
    simpa only [action, thunk, source] using
      Nat.le_trans (resolve_le root q (point.child 0)) (child_le q point.path 0)
  case case4 a source child refusal handles =>
    have forkBound : current root q (resolve root ((point.child 0).child 0)) ≤ below q point.path := by
      have body := resolve_le root q ((point.child 0).child 0)
      have inner := child_le q (point.child 0).path 0
      exact Nat.le_trans body (Nat.le_trans inner (child_le q point.path 0))
    have raceBound (bodies : Effs NativeOp)
        (node : (.action a : Node NativeOp).child 0 = some (.effs bodies)) :
        ((actionAt.entrants bodies ((point.child 0).child 0)).map (current root q)).sum ≤ below q point.path := by
      have location : Node.at_ (.eff root) ((point.child 0).child 0).path = some (.effs bodies) := by
        change Node.at_ (.eff root) (point.path ++ [0] ++ [0]) = some (.effs bodies)
        rw [Agreement.Node.at_append, Agreement.Node.at_append, source]
        exact node
      have entered := entrants_le root q bodies ((point.child 0).child 0) location
      exact Nat.le_trans entered (Nat.le_trans (child_le q (point.child 0).path 0) (child_le q point.path 0))
    simp only [actionAt, source] at found
    cases a
    all_goals repeat' split at found
    all_goals aesop (add norm simp [action, thunk, source, Node.child]) (add safe apply [raceBound, forkBound])
  case case5 noMask noInterrupt noRestore noAction =>
    unfold actionAt at found
    repeat' split at found
    all_goals aesop

/-- A delayed scoped fork reserves only descendants of its existing source point.
Consumer: native action interpreter debit. -/
theorem fork_scoped_le (root : NativeEff) (q : List Nat) (point : Point) (scope : Nat) (next : NAction)
    (found : forkScopedAt root point scope = some next) : action root q next ≤ thunk root q (.forkInAt point scope) := by
  unfold forkScopedAt at found
  split at found
  · cases found
    have bound := resolve_le root q ((point.child 0).child 0)
    exact Nat.le_trans bound (Nat.le_trans (child_le q (point.child 0).path 0) (child_le q point.path 0))
  · cases found

/-- The actual native action interpreter retains only its existing source reservation.
Consumer: native evaluator installation and application registration uniqueness. -/
theorem interp_action_le (root : NativeEff) (q : List Nat) (clear : ClearFinalizers root q)
    (completed) (table : RowTable) (suspended : EffThunk) (next : NAction)
    (owned : ThunkAt root suspended)
    (found : (interpAt root completed table).withFiberOf suspended = some next) :
    action root q next ≤ thunk root q suspended := by
  cases suspended
  case act point => exact source_action_le root q point next found
  case forkInAt point scope => exact fork_scoped_le root q point scope next found
  case store stored =>
    cases stored
    case act callback =>
      cases found
      have zero := store_action_zero root q clear callback owned
      exact Nat.le_of_eq zero
    all_goals cases found
  case acquireMasked point context =>
    cases found
    simp only [action, current, cata_prim, thunk, name, push, Nat.zero_add, Nat.add_zero, Nat.le_refl]
  case releaseMasked point previous =>
    cases found
    simpa only [action, current, cata_prim, name, push, Nat.add_zero, thunk] using resolve_le root q point
  case forkLayer => exact owned.elim
  -- a masked provider's update holds its region's point; a restore resolves it
  case provideMasked update body flag =>
    cases found
    cases body
    case program point =>
      simp only [action, current, cata_prim, thunk, name, push, Nat.zero_add, Nat.add_zero,
        Nat.le_refl]
    all_goals exact owned.elim
  case restoreRegion body flag =>
    cases found
    cases body
    case program point => simpa only [action, regionCode, thunk] using resolve_le root q point
    all_goals exact owned.elim
  all_goals aesop (add norm simp [interpAt, interpOf, action, thunk])

end Effect4.Program.SourceScope.Opportunities
