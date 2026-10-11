import Effect4.Laws.Program.NativeInterpScope

/-!
# Source scope of forked and raced native programs

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The laws inspect actual native fiber actions and their existing program slots.
Race entrants retain the source spine's child addresses and lexical lengths.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- Native fiber actions retain every program they can launch. -/
def ActionAt (root : NativeEff) : NAction → Prop
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ => CodeAt root body
  | .raceAll bodies _ | .raceAllFirst bodies _ => (∀ body ∈ bodies, CodeAt root body) ∧ RaceAllowed root
  | .closePar bodies => (∀ body ∈ bodies, CodeAt root body) ∧ ParallelAllowed root
  | _ => True

/-- A zero-binder child retains both its actual node and lexical scope. -/
theorem node_child_at (root : NativeEff) (p : Point) (node child : Node NativeOp) (i : Nat)
    (found : Node.at_ (.eff root) p.path = some node) (owned : At root p)
    (lookup : node.child i = some child) (level : node.childLevel p.env.length i = p.env.length) :
    Node.at_ (.eff root) (p.child i).path = some child ∧ At root (p.child i) := by
  refine ⟨?_, ?_⟩
  · change Node.at_ (.eff root) (p.path ++ [i]) = some child
    rw [Agreement.Node.at_append, found]
    exact lookup
  · unfold At
    change levelAt (.eff root) 0 (p.path ++ [i]) = some p.env.length
    rw [levelAt_suffix _ _ p.path [i] 0 found, owned]
    simp only [Option.bind_some, levelAt, lookup, level]

/-- Every compiled entrant retains the actual child address of its source spine. -/
theorem entrants_at (root : NativeEff) (fragment : Fragment root) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) (owned : At root p) :
    ∀ body ∈ actionAt.entrants bodies p, CodeAt root body := by
  revert found owned
  fun_induction actionAt.entrants bodies p
  case case1 p => intro found owned body member; cases member
  case case2 head rest p ih =>
    intro found owned
    have first := node_child_at root p (.effs (.cons head rest)) (.eff head) 0 found owned rfl rfl
    have tail := node_child_at root p (.effs (.cons head rest)) (.effs rest) 1 found owned rfl rfl
    intro body member
    rcases List.mem_cons.mp member with eq | later
    · rw [eq]
      exact compile_at root fragment head (p.child 0) first.1 first.2
    · exact ih tail.1 tail.2 body later

/-- Stored named actions retain every program hidden beneath their existing wrappers. -/
theorem store_action_at (root : NativeEff) (name : ActionName) (owned : StoreActionAt root name) :
    ActionAt root (embedAction (actionOf name)) := by
  cases name
  case fork | forkIn | forkScoped | setInterruptible => exact progOf_at root _ owned
  case closePar order exit =>
    refine ⟨?_, owned.2⟩
    change ∀ body ∈ (order.map (fun fin => finProgram fin exit)).map embed, CodeAt root body
    rw [List.map_map]
    intro body member
    obtain ⟨fin, present, eq⟩ := List.mem_map.mp member
    rw [← eq]
    exact finProgram_at root fin exit (owned.1 fin present)
  case raceAll race =>
    cases race <;> aesop (add norm simp [actionOf, embedAction, ActionAt, raceEntrants,
      List.mem_cons, CodeAt, embed, ThunkAt, StoreThunkAt, ProgAt, NameAt, StoreNameAt]) (add safe apply [progOf_at])
  all_goals trivial

/-- Resolving a mask body retains its actual source scope. -/
theorem mask_action_at (root : NativeEff) (fragment : Fragment root) (p : Point) (e : NativeEff)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (owned : At root p)
    (level : levelAt (.eff e) p.env.length [0] = some p.env.length) :
    CodeAt root (resolve root (p.child 0)) :=
  resolve_child_at root fragment p 0 (next_of_at root p e 0 0 found owned level)

set_option maxHeartbeats 2000000 in
/-- Reading a source action retains every forked, masked and raced entrant. -/
theorem source_action_at (root : NativeEff) (fragment : Fragment root) (p : Point) (action : NAction)
    (owned : At root p) (found : actionAt root p = some action) : ActionAt root action := by
  fun_cases actionAt root p
  case case1 body source =>
    simp only [actionAt, source] at found
    cases found
    exact mask_action_at root fragment p _ source owned rfl
  case case2 body source =>
    simp only [actionAt, source] at found
    cases found
    exact mask_action_at root fragment p _ source owned rfl
  case case3 saved body source =>
    simp only [actionAt, source] at found
    cases found
    exact mask_action_at root fragment p _ source owned rfl
  case case4 a source qPoint refusal handles =>
    have q := node_child_at root p (.eff (.withFiber a)) (.action a) 0 source owned rfl rfl
    have bodyScope (body : NativeEff) (h : (.action a : Node NativeOp).child 0 = some (.eff body)) :
        CodeAt root (resolve root ((p.child 0).child 0)) := by
      have child := node_child_at root (p.child 0) (.action a) (.eff body) 0 q.1 q.2 h rfl
      exact resolve_scoped root fragment _ child.2
    have raceScope (bodies : Effs NativeOp) (h : (.action a : Node NativeOp).child 0 = some (.effs bodies)) :
        ∀ body ∈ actionAt.entrants bodies ((p.child 0).child 0), CodeAt root body := by
      have child := node_child_at root (p.child 0) (.action a) (.effs bodies) 0 q.1 q.2 h rfl
      exact entrants_at root fragment bodies _ child.1 child.2
    simp only [actionAt, source] at found
    have allowed : match a with
      | .raceAll _ | .raceAllFirst _ => RaceAllowed root
      | _ => True := by
      cases a with
      | raceAll bodies => exact raceAllowed_firstSuccess root _ bodies q.1
      | raceAllFirst bodies => exact raceAllowed_firstExit root _ bodies q.1
      | _ => trivial
    cases a
    all_goals repeat' split at found
    all_goals aesop (add norm simp [ActionAt, Node.child]) (add safe apply [bodyScope, raceScope])
  case case5 noMask noInterrupt noRestore noAction =>
    unfold actionAt at found
    repeat' split at found
    all_goals aesop

/-- The second scoped-fork command retains its actual source program child. -/
theorem scoped_fork_at (root : NativeEff) (fragment : Fragment root) (p : Point) (scope : Nat)
    (action : NAction) (owned : At root p) (found : forkScopedAt root p scope = some action) :
    ActionAt root action := by
  unfold forkScopedAt at found
  split at found
  · rename_i body options source
    cases found
    have first := node_child_at root p (.eff (.withFiber (.forkScoped body options)))
      (.action (.forkScoped body options)) 0 source owned rfl rfl
    have second := node_child_at root (p.child 0) (.action (.forkScoped body options))
      (.eff body) 0 first.1 first.2 rfl rfl
    exact resolve_scoped root fragment _ second.2
  · cases found

/-- The native action interpreter retains the programs that its action can launch. -/
theorem interp_action_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (thunk : EffThunk) (action : NAction) (owned : ThunkAt root thunk)
    (found : (interpAt root completed table).withFiberOf thunk = some action) : ActionAt root action := by
  cases thunk
  case act p => exact source_action_at root fragment p action owned found
  case forkInAt p scope => exact scoped_fork_at root fragment p scope action owned found
  case store thunk =>
    cases thunk
    case act name =>
      cases found
      exact store_action_at root name owned
    all_goals cases found
  case acquireMasked p ctx =>
    cases found
    refine ⟨trivial, owned, ?_⟩
    intro _ _ wrong
    cases wrong
  case releaseMasked p previous =>
    cases found
    exact ⟨resolve_scoped root fragment p owned, trivial⟩
  case forkLayer => exact owned.elim
  all_goals aesop (add norm simp [interpAt, interpOf, ActionAt])

end Effect4.Program.SourceScope
