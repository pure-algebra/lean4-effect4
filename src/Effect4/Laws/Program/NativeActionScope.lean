import Effect4.Laws.Program.NativeInterpScope

/-!
# Source scope of forked and raced native programs

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The exact child producer also serves Timeout.cleanup_keeps and Timeout.retries_declared.
It retains constructor roles and captured points; it issues no active generation permission.
The laws inspect actual native fiber actions and their existing program slots.
Race entrants retain the source spine's child addresses and lexical lengths.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The existing action program slots distinguish their actual launch roles. -/
inductive ProgramRole
  | forkBody
  | maskBody
  | entrantBody

/-- The existing action predicate varies only the contract for its program slots. -/
def ActionProgramsAt (root : NativeEff) (program : ProgramRole → NCode → Prop) : NAction → Prop
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ => program .forkBody body
  | .setInterruptible body _ => program .maskBody body
  | .raceAll bodies _ | .raceAllFirst bodies _ => (∀ body ∈ bodies, program .entrantBody body) ∧ RaceAllowed root
  | .closePar bodies => (∀ body ∈ bodies, program .entrantBody body) ∧ ParallelAllowed root
  | _ => True

/-- Native fiber actions retain every program they can launch. -/
def ActionAt (root : NativeEff) : NAction → Prop := ActionProgramsAt root (fun _ => CodeAt root)

/-- A program-slot implication transports the existing action contract. -/
theorem ActionProgramsAt.mono (root : NativeEff) {P Q : ProgramRole → NCode → Prop} (action : NAction)
    (held : ActionProgramsAt root P action) (map : ∀ role program, P role program → Q role program) :
    ActionProgramsAt root Q action := by
  fun_cases ActionProgramsAt root P action
  all_goals aesop (add norm simp [ActionProgramsAt]) (add safe apply [map])

/-- Child steps use the existing point operation and list fold. -/
def childPoint (parent : Point) (indices : List Nat) : Point := indices.foldl Point.child parent

/-- The list fold retains captured fields and records the actual child address and fuel debit. -/
theorem childPoint_spec (parent : Point) (indices : List Nat) :
    (childPoint parent indices).path = parent.path ++ indices ∧
    (childPoint parent indices).fuel = parent.fuel - indices.length ∧
    {childPoint parent indices with path := parent.path, fuel := parent.fuel} = parent := by
  induction indices generalizing parent with
  | nil => exact ⟨(List.append_nil parent.path).symm, rfl, rfl⟩
  | cons index rest ih =>
    have previous := ih (parent.child index)
    refine ⟨?_, ?_, ?_⟩
    · change (childPoint (parent.child index) rest).path = parent.path ++ (index :: rest)
      rw [previous.1]
      change (parent.path ++ [index]) ++ rest = parent.path ++ (index :: rest)
      rw [List.append_assoc]
      rfl
    · change (childPoint (parent.child index) rest).fuel = parent.fuel - (rest.length + 1)
      rw [previous.2.1]
      change (parent.fuel - 1) - rest.length = parent.fuel - (rest.length + 1)
      rw [Nat.sub_sub, Nat.add_comm 1 rest.length]
    · exact congrArg (fun q : Point => {q with path := parent.path, fuel := parent.fuel}) previous.2.2

/-- Every source program slot retains its exact point, node, scope, and resolution. -/
def ChildProgramAt (root : NativeEff) (parent : Point) (indices : List Nat) (program : NCode) : Prop :=
  ∃ effect, Node.at_ (.eff root) (childPoint parent indices).path = some (.eff effect) ∧
    At root (childPoint parent indices) ∧ program = resolve root (childPoint parent indices)

/-- A child's program retains the original parent's exact child-step sequence. -/
theorem ChildProgramAt.parent (root : NativeEff) (parent : Point) (index : Nat)
    (indices : List Nat) (program : NCode)
    (held : ChildProgramAt root (parent.child index) indices program) :
    ChildProgramAt root parent (index :: indices) program := by
  obtain ⟨effect, node, scopeHeld, code⟩ := held
  exact ⟨effect, node, scopeHeld, code⟩

/-- Exact child provenance supplies the old source-fragment scope contract. -/
theorem ChildProgramAt.scope (root : NativeEff) (fragment : Fragment root) (parent : Point)
    (indices : List Nat) (program : NCode) (held : ChildProgramAt root parent indices program) : CodeAt root program := by
  obtain ⟨effect, node, scopeHeld, code⟩ := held
  rw [code]
  exact resolve_scoped root fragment _ scopeHeld

/-- The source action retains each constructor's exact program address and entrant position. -/
def SourceProgramAt (root : NativeEff) (parent : Point) : ProgramRole → NCode → Prop
  | .forkBody, program => ChildProgramAt root parent [0,0] program
  | .maskBody, program => ChildProgramAt root parent [0] program
  | .entrantBody, program => ∃ index, ChildProgramAt root parent ([0,0] ++ List.replicate index 1 ++ [0]) program

/-- The constructor-specific source witness supplies the existing scope contract. -/
theorem SourceProgramAt.scope (root : NativeEff) (fragment : Fragment root) (parent : Point)
    (role : ProgramRole) (program : NCode) (held : SourceProgramAt root parent role program) : CodeAt root program := by
  cases role with
  | forkBody => exact ChildProgramAt.scope root fragment parent [0,0] program held
  | maskBody => exact ChildProgramAt.scope root fragment parent [0] program held
  | entrantBody =>
    obtain ⟨index, held⟩ := held
    exact ChildProgramAt.scope root fragment parent _ program held

/-- A zero-binder child retains both its actual node and lexical scope. -/
theorem node_child_at (root : NativeEff) (p : Point) (node child : Node NativeOp) (i : Nat)
    (found : Node.at_ (.eff root) p.path = some node) (owned : At root p)
    (lookup : node.child i = some child) (level : node.childLevel p.env.length i = p.env.length) :
    Node.at_ (.eff root) (p.child i).path = some child ∧ At root (p.child i) := by
  refine ⟨?_, ?_⟩
  · change Node.at_ (.eff root) (p.path ++ [i]) = some child
    rw [Node.at_snoc, found]
    exact lookup
  · unfold At
    change levelAt (.eff root) 0 (p.path ++ [i]) = some p.env.length
    rw [levelAt_suffix _ _ p.path [i] 0 found, owned]
    simp only [Option.bind_some, levelAt, lookup, level]

/-- Every compiled entrant retains its actual child point and captured source metadata. -/
theorem entrants_children (root : NativeEff) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) (owned : At root p) :
    ∀ body ∈ actionAt.entrants bodies p, ∃ index, ChildProgramAt root p (List.replicate index 1 ++ [0]) body := by
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
      exact ⟨0, head, first.1, first.2, (Agreement.resolve_of_at first.1).symm⟩
    · obtain ⟨index, held⟩ := ih tail.1 tail.2 body later
      refine ⟨index + 1, ?_⟩
      have prefixed := ChildProgramAt.parent root p 1 (List.replicate index 1 ++ [0]) body held
      simpa only [List.replicate_succ, List.cons_append] using prefixed

/-- Every compiled entrant retains the actual child address of its source spine. -/
theorem entrants_at (root : NativeEff) (fragment : Fragment root) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) (owned : At root p) :
    ∀ body ∈ actionAt.entrants bodies p, CodeAt root body := by
  intro body member
  obtain ⟨index, held⟩ := entrants_children root bodies p found owned body member
  exact ChildProgramAt.scope root fragment p _ body held

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
    cases race <;> aesop (add norm simp [actionOf, embedAction, ActionAt, ActionProgramsAt, raceEntrants,
      List.mem_cons, CodeAt, embed, ThunkAt, StoreThunkAt, ProgAt, NameAt, StoreNameAt]) (add safe apply [progOf_at])
  all_goals trivial

/-- Resolving a mask body retains its actual source scope. -/
theorem mask_action_at (root : NativeEff) (fragment : Fragment root) (p : Point) (e : NativeEff)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (owned : At root p)
    (level : levelAt (.eff e) p.env.length [0] = some p.env.length) :
    CodeAt root (resolve root (p.child 0)) :=
  resolve_child_at root fragment p 0 (next_of_at root p e 0 0 found owned level)

set_option maxHeartbeats 2000000 in
/-- Reading a source action retains every exact program child point. -/
theorem source_action_children (root : NativeEff) (p : Point) (action : NAction)
    (owned : At root p) (found : actionAt root p = some action) : ActionProgramsAt root (SourceProgramAt root p) action := by
  fun_cases actionAt root p
  case case1 body source =>
    simp only [actionAt, source] at found
    cases found
    have child := node_child_at root p _ (.eff body) 0 source owned rfl rfl
    exact ⟨body, child.1, child.2, rfl⟩
  case case2 body source =>
    simp only [actionAt, source] at found
    cases found
    have child := node_child_at root p _ (.eff body) 0 source owned rfl rfl
    exact ⟨body, child.1, child.2, rfl⟩
  case case3 saved body source =>
    simp only [actionAt, source] at found
    cases found
    have child := node_child_at root p _ (.eff body) 0 source owned rfl rfl
    exact ⟨body, child.1, child.2, rfl⟩
  case case4 a source qPoint refusal handles =>
    have q := node_child_at root p (.eff (.withFiber a)) (.action a) 0 source owned rfl rfl
    have bodyScope (body : NativeEff) (h : (.action a : Node NativeOp).child 0 = some (.eff body)) :
        ChildProgramAt root p [0,0] (resolve root ((p.child 0).child 0)) := by
      have child := node_child_at root (p.child 0) (.action a) (.eff body) 0 q.1 q.2 h rfl
      exact ⟨body, child.1, child.2, rfl⟩
    have raceScope (bodies : Effs NativeOp) (h : (.action a : Node NativeOp).child 0 = some (.effs bodies)) :
        ∀ body ∈ actionAt.entrants bodies ((p.child 0).child 0), SourceProgramAt root p .entrantBody body := by
      have child := node_child_at root (p.child 0) (.action a) (.effs bodies) 0 q.1 q.2 h rfl
      intro body member
      obtain ⟨index, held⟩ := entrants_children root bodies _ child.1 child.2 body member
      exact ⟨index, ChildProgramAt.parent root p 0 _ body
        (ChildProgramAt.parent root (p.child 0) 0 _ body held)⟩
    simp only [actionAt, source] at found
    have allowed : match a with
      | .raceAll _ | .raceAllFirst _ => RaceAllowed root
      | _ => True := by
      cases a with
      | raceAll bodies => exact raceAllowed_firstSuccess root _ bodies q.1
      | raceAllFirst bodies => exact raceAllowed_firstExit root _ bodies q.1
      | _ => trivial
    cases a
    case fork body options =>
      cases found
      exact bodyScope body rfl
    case forkIn body options scope =>
      repeat' split at found
      all_goals cases found
      all_goals aesop (add norm simp [ActionProgramsAt, SourceProgramAt, Node.child]) (add safe apply [(bodyScope body)])
    case raceAll bodies =>
      cases found
      exact ⟨raceScope bodies rfl, allowed⟩
    case raceAllFirst bodies =>
      cases found
      exact ⟨raceScope bodies rfl, allowed⟩
    all_goals repeat' split at found
    all_goals cases found
    all_goals trivial
  case case5 noMask noInterrupt noRestore noAction =>
    unfold actionAt at found
    repeat' split at found
    all_goals aesop

/-- Reading a source action retains every forked, masked and raced entrant. -/
theorem source_action_at (root : NativeEff) (fragment : Fragment root) (p : Point) (action : NAction)
    (owned : At root p) (found : actionAt root p = some action) : ActionAt root action := by
  exact ActionProgramsAt.mono root action (source_action_children root p action owned found)
    (SourceProgramAt.scope root fragment p)

/-- The scoped fork answer retains the same captured source point as its parent. -/
theorem scoped_fork_children (root : NativeEff) (p : Point) (scope : Nat)
    (action : NAction) (owned : At root p) (found : forkScopedAt root p scope = some action) :
    ActionProgramsAt root (SourceProgramAt root p) action := by
  unfold forkScopedAt at found
  split at found
  · rename_i body options source
    cases found
    have first := node_child_at root p (.eff (.withFiber (.forkScoped body options)))
      (.action (.forkScoped body options)) 0 source owned rfl rfl
    have second := node_child_at root (p.child 0) (.action (.forkScoped body options))
      (.eff body) 0 first.1 first.2 rfl rfl
    exact ⟨body, second.1, second.2, rfl⟩
  · cases found

/-- The second scoped-fork command retains its actual source program child. -/
theorem scoped_fork_at (root : NativeEff) (fragment : Fragment root) (p : Point) (scope : Nat)
    (action : NAction) (owned : At root p) (found : forkScopedAt root p scope = some action) :
    ActionAt root action := by
  exact ActionProgramsAt.mono root action (scoped_fork_children root p scope action owned found)
    (SourceProgramAt.scope root fragment p)

/-- The actual source thunk producer retains its exact compiled child points. -/
theorem interp_source_children (root : NativeEff) (completed) (table : RowTable)
    (p : Point) (action : NAction) (owned : At root p)
    (found : (interpAt root completed table).withFiberOf (.act p) = some action) :
    ActionProgramsAt root (SourceProgramAt root p) action :=
  source_action_children root p action owned found

/-- The native action interpreter retains the programs that its action can launch. -/
theorem interp_action_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (thunk : EffThunk) (action : NAction) (owned : ThunkAt root thunk)
    (found : (interpAt root completed table).withFiberOf thunk = some action) : ActionAt root action := by
  cases thunk
  case act p =>
    exact ActionProgramsAt.mono root action (interp_source_children root completed table p action owned found)
      (SourceProgramAt.scope root fragment p)
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
  -- a masked provider runs its update under the region it owns; a restore runs the region
  case provideMasked update body flag =>
    cases found
    exact (⟨trivial, owned, fun _ _ wrong => nomatch wrong⟩ :
      CodeAt root (Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (.updateThen update body flag)))
  case restoreRegion body flag =>
    cases found
    exact (region_at root fragment body owned : CodeAt root (regionCode root body))
  all_goals aesop (add norm simp [interpAt, interpOf, ActionAt, ActionProgramsAt])

end Effect4.Program.SourceScope
