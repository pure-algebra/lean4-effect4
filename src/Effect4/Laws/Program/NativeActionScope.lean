import Effect4.Laws.Program.NativeInterpScope

/-!
# Source scope of forked and raced native programs

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The exact child producer also serves Timeout.cleanup_keeps, Timeout.retries_declared and FinalizerRun.once_placed_outside_census.
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
def ActionProgramsWith (races parallel : Prop) (program : ProgramRole → NCode → Prop) : NAction → Prop
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ => program .forkBody body
  | .setInterruptible body _ => program .maskBody body
  | .raceAll bodies _ | .raceAllFirst bodies _ => (∀ body ∈ bodies, program .entrantBody body) ∧ races
  | .closePar bodies => (∀ body ∈ bodies, program .entrantBody body) ∧ parallel
  | _ => True

/-- The lexical source instance also retains the permissions for race and parallel actions. -/
abbrev ActionProgramsAt (root : NativeEff) := ActionProgramsWith (RaceAllowed root) (ParallelAllowed root)

/-- Program-slot implications and action permissions transport the common assertion. -/
theorem ActionProgramsWith.mono {R S R' S' : Prop} {P Q : ProgramRole → NCode → Prop}
    (action : NAction) (held : ActionProgramsWith R S P action)
    (races : R → R') (parallel : S → S') (map : ∀ role program, P role program → Q role program) :
    ActionProgramsWith R' S' Q action := by
  fun_cases ActionProgramsWith R S P action
  all_goals aesop (add norm simp [ActionProgramsWith]) (add safe apply [map, races, parallel])

/-- Native fiber actions retain every program they can launch. -/
def ActionAt (root : NativeEff) : NAction → Prop := ActionProgramsAt root (fun _ => CodeAt root)

/-- A program-slot implication transports the existing action contract. -/
theorem ActionProgramsAt.mono (root : NativeEff) {P Q : ProgramRole → NCode → Prop} (action : NAction)
    (held : ActionProgramsAt root P action) (map : ∀ role program, P role program → Q role program) :
    ActionProgramsAt root Q action := by
  exact ActionProgramsWith.mono action held id id map

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
def ChildProgramUnder (root : NativeEff) (P : Point → Prop) (parent : Point) (indices : List Nat) (program : NCode) : Prop :=
  ∃ effect, Node.at_ (.eff root) (childPoint parent indices).path = some (.eff effect) ∧
    P (childPoint parent indices) ∧ program = resolve root (childPoint parent indices)

/-- The original lexical scope is one instance of exact child provenance. -/
abbrev ChildProgramAt (root : NativeEff) := ChildProgramUnder root (At root)

/-- Exact child provenance composes its actual parent path. -/
theorem ChildProgramUnder.parent (root : NativeEff) (P : Point → Prop) (parent : Point) (index : Nat)
    (indices : List Nat) (program : NCode)
    (held : ChildProgramUnder root P (parent.child index) indices program) :
    ChildProgramUnder root P parent (index :: indices) program := held

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
def SourceProgramUnder (root : NativeEff) (P : Point → Prop) (parent : Point) : ProgramRole → NCode → Prop
  | .forkBody, program => ChildProgramUnder root P parent [0,0] program
  | .maskBody, program => ChildProgramUnder root P parent [0] program
  | .entrantBody, program => ∃ index, ChildProgramUnder root P parent ([0,0] ++ List.replicate index 1 ++ [0]) program

/-- The original action provenance retains lexical scope as its point assertion. -/
abbrev SourceProgramAt (root : NativeEff) := SourceProgramUnder root (At root)

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

/-- The point assertion follows actual zero-binder children of source actions. -/
def ChildClosure (root : NativeEff) (P : Point → Prop) : Prop :=
  ∀ (p : Point) (node child : Node NativeOp) (i : Nat),
    Node.at_ (.eff root) p.path = some node → P p → node.child i = some child →
    node.childLevel p.env.length i = p.env.length → P (p.child i)

/-- Lexical scope supplies the existing action-child assertion. -/
theorem scopeChildClosure (root : NativeEff) : ChildClosure root (At root) :=
  fun p node child i found owned lookup level => (node_child_at root p node child i found owned lookup level).2

/-- An actual child lookup carries the supplied point assertion. -/
theorem node_child_under (root : NativeEff) (P : Point → Prop) (closed : ChildClosure root P)
    (p : Point) (node child : Node NativeOp) (i : Nat)
    (found : Node.at_ (.eff root) p.path = some node) (owned : P p)
    (lookup : node.child i = some child) (level : node.childLevel p.env.length i = p.env.length) :
    Node.at_ (.eff root) (p.child i).path = some child ∧ P (p.child i) := by
  refine ⟨?_, closed p node child i found owned lookup level⟩
  change Node.at_ (.eff root) (p.path ++ [i]) = some child
  rw [Node.at_snoc, found]
  exact lookup

/-- Every compiled entrant retains its actual child point and captured source metadata. -/
theorem entrants_children_under (root : NativeEff) (P : Point → Prop) (closed : ChildClosure root P) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) (owned : P p) :
    ∀ body ∈ actionAt.entrants bodies p, ∃ index, ChildProgramUnder root P p (List.replicate index 1 ++ [0]) body := by
  revert found owned
  fun_induction actionAt.entrants bodies p
  case case1 p => intro found owned body member; cases member
  case case2 head rest p ih =>
    intro found owned
    have first := node_child_under root P closed p (.effs (.cons head rest)) (.eff head) 0 found owned rfl rfl
    have tail := node_child_under root P closed p (.effs (.cons head rest)) (.effs rest) 1 found owned rfl rfl
    intro body member
    rcases List.mem_cons.mp member with eq | later
    · rw [eq]
      exact ⟨0, head, first.1, first.2, (Agreement.resolve_of_at first.1).symm⟩
    · obtain ⟨index, held⟩ := ih tail.1 tail.2 body later
      refine ⟨index + 1, ?_⟩
      have prefixed := ChildProgramUnder.parent root P p 1 (List.replicate index 1 ++ [0]) body held
      simpa only [List.replicate_succ, List.cons_append] using prefixed

/-- The original entrant caller uses lexical scope in the common child producer. -/
theorem entrants_children (root : NativeEff) (bodies : Effs NativeOp) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.effs bodies)) (owned : At root p) :
    ∀ body ∈ actionAt.entrants bodies p, ∃ index, ChildProgramAt root p (List.replicate index 1 ++ [0]) body :=
  entrants_children_under root (At root) (scopeChildClosure root) bodies p found owned

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
    cases race <;> aesop (add norm simp [actionOf, embedAction, ActionAt, ActionProgramsAt, ActionProgramsWith, raceEntrants,
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
theorem source_action_children_with (root : NativeEff) (P : Point → Prop) (closed : ChildClosure root P)
    (parallel : Prop) (p : Point) (action : NAction)
    (owned : P p) (found : actionAt root p = some action) :
    ActionProgramsWith (RaceAllowed root) parallel (SourceProgramUnder root P p) action := by
  fun_cases actionAt root p
  case case1 body source =>
    simp only [actionAt, source] at found
    cases found
    have child := node_child_under root P closed p _ (.eff body) 0 source owned rfl rfl
    exact ⟨body, child.1, child.2, rfl⟩
  case case2 body source =>
    simp only [actionAt, source] at found
    cases found
    have child := node_child_under root P closed p _ (.eff body) 0 source owned rfl rfl
    exact ⟨body, child.1, child.2, rfl⟩
  case case3 saved body source =>
    simp only [actionAt, source] at found
    cases found
    have child := node_child_under root P closed p _ (.eff body) 0 source owned rfl rfl
    exact ⟨body, child.1, child.2, rfl⟩
  case case4 a source qPoint refusal handles =>
    have q := node_child_under root P closed p (.eff (.withFiber a)) (.action a) 0 source owned rfl rfl
    have bodyScope (body : NativeEff) (h : (.action a : Node NativeOp).child 0 = some (.eff body)) :
        ChildProgramUnder root P p [0,0] (resolve root ((p.child 0).child 0)) := by
      have child := node_child_under root P closed (p.child 0) (.action a) (.eff body) 0 q.1 q.2 h rfl
      exact ⟨body, child.1, child.2, rfl⟩
    have raceScope (bodies : Effs NativeOp) (h : (.action a : Node NativeOp).child 0 = some (.effs bodies)) :
        ∀ body ∈ actionAt.entrants bodies ((p.child 0).child 0), SourceProgramUnder root P p .entrantBody body := by
      have child := node_child_under root P closed (p.child 0) (.action a) (.effs bodies) 0 q.1 q.2 h rfl
      intro body member
      obtain ⟨index, held⟩ := entrants_children_under root P closed bodies _ child.1 child.2 body member
      exact ⟨index, ChildProgramUnder.parent root P p 0 _ body
        (ChildProgramUnder.parent root P (p.child 0) 0 _ body held)⟩
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
      all_goals aesop (add norm simp [ActionProgramsAt, ActionProgramsWith, SourceProgramUnder, Node.child]) (add safe apply [(bodyScope body)])
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

/-- Source actions satisfy the original parallel permission through the common producer. -/
theorem source_action_children_under (root : NativeEff) (P : Point → Prop) (closed : ChildClosure root P)
    (p : Point) (action : NAction) (owned : P p) (found : actionAt root p = some action) :
    ActionProgramsAt root (SourceProgramUnder root P p) action :=
  source_action_children_with root P closed (ParallelAllowed root) p action owned found

/-- The original source caller uses lexical scope in the common action producer. -/
theorem source_action_children (root : NativeEff) (p : Point) (action : NAction)
    (owned : At root p) (found : actionAt root p = some action) : ActionProgramsAt root (SourceProgramAt root p) action :=
  source_action_children_under root (At root) (scopeChildClosure root) p action owned found

/-- Reading a source action retains every forked, masked and raced entrant. -/
theorem source_action_at (root : NativeEff) (fragment : Fragment root) (p : Point) (action : NAction)
    (owned : At root p) (found : actionAt root p = some action) : ActionAt root action := by
  exact ActionProgramsAt.mono root action (source_action_children root p action owned found)
    (SourceProgramAt.scope root fragment p)

/-- The scoped fork answer retains the same captured source point as its parent. -/
theorem scoped_fork_children_with (root : NativeEff) (P : Point → Prop) (closed : ChildClosure root P)
    (parallel : Prop) (p : Point) (scope : Nat) (action : NAction) (owned : P p)
    (found : forkScopedAt root p scope = some action) :
    ActionProgramsWith (RaceAllowed root) parallel (SourceProgramUnder root P p) action := by
  unfold forkScopedAt at found
  split at found
  · rename_i body options source
    cases found
    have first := node_child_under root P closed p (.eff (.withFiber (.forkScoped body options)))
      (.action (.forkScoped body options)) 0 source owned rfl rfl
    have second := node_child_under root P closed (p.child 0) (.action (.forkScoped body options))
      (.eff body) 0 first.1 first.2 rfl rfl
    exact ⟨body, second.1, second.2, rfl⟩
  · cases found

/-- The scoped-fork producer supplies the original action permissions. -/
theorem scoped_fork_children_under (root : NativeEff) (P : Point → Prop) (closed : ChildClosure root P)
    (p : Point) (scope : Nat) (action : NAction) (owned : P p)
    (found : forkScopedAt root p scope = some action) :
    ActionProgramsAt root (SourceProgramUnder root P p) action :=
  scoped_fork_children_with root P closed (ParallelAllowed root) p scope action owned found

/-- The original scoped-fork caller uses the common child producer. -/
theorem scoped_fork_children (root : NativeEff) (p : Point) (scope : Nat)
    (action : NAction) (owned : At root p) (found : forkScopedAt root p scope = some action) :
    ActionProgramsAt root (SourceProgramAt root p) action :=
  scoped_fork_children_under root (At root) (scopeChildClosure root) p scope action owned found

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

/-- The native interpreter requests closure only for program slots it actually constructs.
Consumer: lexical source ownership and the full finalizer source annotation. -/
structure ActionClosure (root : NativeEff) (R S : Prop) (T : EffThunk → Prop) (P : NCode → Prop) : Prop where
  source : ∀ point action, T (.act point) → actionAt root point = some action →
    ActionProgramsWith R S (fun _ => P) action
  scopedFork : ∀ point scope action, T (.forkInAt point scope) → forkScopedAt root point scope = some action →
    ActionProgramsWith R S (fun _ => P) action
  stored : ∀ name, T (.store (.act name)) → ActionProgramsWith R S (fun _ => P) (embedAction (actionOf name))
  acquire : ∀ point context, T (.acquireMasked point context) →
    P (.onSuccess (.withFiber (.store (.act .ambientScope))) (.acquireIn point context))
  release : ∀ point previous, T (.releaseMasked point previous) →
    P (.onExit (resolve root point) (.restoreCtx previous) false)
  layer : ∀ point memo scope, T (.forkLayer point memo scope) → P (resolveLayer root point memo scope)
  provide : ∀ update body flag, T (.provideMasked update body flag) →
    P (.onSuccess (.withFiber .getCtx) (.updateThen update body flag))
  restore : ∀ body flag, T (.restoreRegion body flag) → P (regionCode root body)

/-- The actual action result has one supplied assertion for every interpreter leaf.
Consumer: program closure and the parallel-close source debit. -/
structure ActionResults (root : NativeEff) (T : EffThunk → Prop) (A : NAction → Prop) : Prop where
  source : ∀ point action, T (.act point) → actionAt root point = some action → A action
  scopedFork : ∀ point scope action, T (.forkInAt point scope) → forkScopedAt root point scope = some action → A action
  stored : ∀ name, T (.store (.act name)) → A (embedAction (actionOf name))
  acquire : ∀ point context, T (.acquireMasked point context) →
    A (.setInterruptible (.onSuccess (.withFiber (.store (.act .ambientScope))) (.acquireIn point context)) false)
  release : ∀ point previous, T (.releaseMasked point previous) →
    A (.setInterruptible (.onExit (resolve root point) (.restoreCtx previous) false) false)
  layer : ∀ point memo scope, T (.forkLayer point memo scope) →
    A (.fork (resolveLayer root point memo scope) ⟨true, true, .inherit⟩ point.path)
  provide : ∀ update body flag, T (.provideMasked update body flag) →
    A (.setInterruptible (.onSuccess (.withFiber .getCtx) (.updateThen update body flag)) false)
  restore : ∀ body flag, T (.restoreRegion body flag) → A (.setInterruptible (regionCode root body) flag)
  context : T .getCtx → A .getContext
  captureMask : T .captureMask → A .getInterruptible
  setContext : ∀ context, T (.setCtx context) → A (.setContext context)
  closeScope : ∀ scope exit, T (.closeScope scope exit) → A (.closeScope scope exit)
  awaitAllFailFast : ∀ targets, T (.awaitAllFailFast targets) → A (.awaitAllFailFast targets)

/-- One actual interpreter walk serves every supplied action-result assertion. -/
theorem interp_action_result (root : NativeEff) (completed) (table : RowTable)
    (T : EffThunk → Prop) (A : NAction → Prop) (closed : ActionResults root T A)
    (thunk : EffThunk) (action : NAction) (owned : T thunk)
    (found : (interpAt root completed table).withFiberOf thunk = some action) : A action := by
  cases thunk
  case act p => exact closed.source p action owned found
  case forkInAt p scope => exact closed.scopedFork p scope action owned found
  case store thunk =>
    cases thunk
    case act name => cases found; exact closed.stored name owned
    all_goals cases found
  case acquireMasked p ctx => cases found; exact closed.acquire p ctx owned
  case releaseMasked p previous => cases found; exact closed.release p previous owned
  case forkLayer p memo scope => cases found; exact closed.layer p memo scope owned
  case provideMasked update body flag => cases found; exact closed.provide update body flag owned
  case restoreRegion body flag => cases found; exact closed.restore body flag owned
  case getCtx => cases found; exact closed.context owned
  case captureMask => cases found; exact closed.captureMask owned
  case setCtx context => cases found; exact closed.setContext context owned
  case closeScope scope exit => cases found; exact closed.closeScope scope exit owned
  case awaitAllFailFast targets => cases found; exact closed.awaitAllFailFast targets owned
  all_goals cases found

/-- Program-slot closure supplies the same actual action-result contract. -/
theorem ActionClosure.results (root : NativeEff) (R S : Prop) (T : EffThunk → Prop) (P : NCode → Prop)
    (closed : ActionClosure root R S T P) : ActionResults root T (ActionProgramsWith R S (fun _ => P)) where
  source := closed.source
  scopedFork := closed.scopedFork
  stored := closed.stored
  acquire := closed.acquire
  release := closed.release
  layer := closed.layer
  provide := closed.provide
  restore := closed.restore
  context := fun _ => trivial
  captureMask := fun _ => trivial
  setContext := fun _ _ => trivial
  closeScope := fun _ _ _ => trivial
  awaitAllFailFast := fun _ _ => trivial

/-- Program-slot assertions use the common actual action-result producer. -/
theorem interp_action_closed (root : NativeEff) (completed) (table : RowTable)
    (R S : Prop) (T : EffThunk → Prop) (P : NCode → Prop) (closed : ActionClosure root R S T P)
    (thunk : EffThunk) (action : NAction) (owned : T thunk)
    (found : (interpAt root completed table).withFiberOf thunk = some action) :
    ActionProgramsWith R S (fun _ => P) action :=
  interp_action_result root completed table T _ (closed.results root R S T P) thunk action owned found

/-- The original lexical source contract supplies the common action interpreter producer. -/
theorem sourceActionClosure (root : NativeEff) (fragment : Fragment root) :
    ActionClosure root (RaceAllowed root) (ParallelAllowed root) (ThunkAt root) (CodeAt root) where
  source := fun point action owned found => source_action_at root fragment point action owned found
  scopedFork := fun point scope action owned found => scoped_fork_at root fragment point scope action owned found
  stored := fun name owned => store_action_at root name owned
  acquire := by
    intro point context owned
    exact ⟨trivial, owned, fun _ _ wrong => nomatch wrong⟩
  release := fun point previous owned => ⟨resolve_scoped root fragment point owned, trivial⟩
  layer := fun _ _ _ owned => owned.elim
  provide := fun update body flag owned => ⟨trivial, owned, fun _ _ wrong => nomatch wrong⟩
  restore := fun body flag owned => region_at root fragment body owned

/-- The native action interpreter retains the programs that its action can launch. -/
theorem interp_action_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (thunk : EffThunk) (action : NAction) (owned : ThunkAt root thunk)
    (found : (interpAt root completed table).withFiberOf thunk = some action) : ActionAt root action :=
  interp_action_closed root completed table (RaceAllowed root) (ParallelAllowed root) (ThunkAt root) (CodeAt root)
    (sourceActionClosure root fragment) thunk action owned found

end Effect4.Program.SourceScope
