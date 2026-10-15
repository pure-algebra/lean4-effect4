import Effect4.Laws.Program.AnswerSlots.TypedSuspend

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: source fiber actions retain the protected source graph in every launched program.
Reach: actual source action child witnesses, scoped forks and represented race entrants.
Limit: stored action wrappers and command history require their respective producers.
Consumer: the protected native action evaluation and initialized crew driver.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- Child sequences ending in zero cannot enter a selected acquisition release. -/
theorem childPoint_ordinary (spec : Spec) (parent : Point) (indices : List Nat) :
    Ordinary spec.acquisitions (SourceScope.childPoint parent (indices ++ [0])) := by
  change Ordinary spec.acquisitions ((indices ++ [0]).foldl Point.child parent)
  rw [List.foldl_append]
  exact ordinary_zero spec (indices.foldl Point.child parent)

/-- Actual launched source programs retain the original parent's initialized leading slots. -/
theorem child_program_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (parent : Point) (indices : List Nat) (program : NCode)
    (slots : Prefix spec.bindings parent.env)
    (held : SourceScope.ChildProgramAt spec.root parent (indices ++ [0]) program) :
    CodeAt spec .root program := by
  obtain ⟨effect, node, lexical, code⟩ := held
  rw [code]
  apply resolve_source spec fragment
  refine ⟨lexical, ?_, .inl (childPoint_ordinary spec parent indices)⟩
  have env := congrArg (fun point : Point => point.env)
    (SourceScope.childPoint_spec parent (indices ++ [0])).2.2
  rw [env]
  exact slots

/-- Every actual source program role ends at a child-zero source point. -/
theorem source_program_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (parent : Point) (slots : Prefix spec.bindings parent.env)
    (role : SourceScope.ProgramRole) (program : NCode)
    (held : SourceScope.SourceProgramAt spec.root parent role program) : CodeAt spec .root program := by
  cases role with
  | forkBody => exact child_program_at spec fragment parent [0] program slots held
  | maskBody => exact child_program_at spec fragment parent [] program slots held
  | entrantBody =>
    obtain ⟨index, held⟩ := held
    exact child_program_at spec fragment parent ([0,0] ++ List.replicate index 1) program slots held

/-- Source action programs carry their actual broad answer class and source action permissions. -/
def ActionAt (spec : Spec) : NAction → Prop :=
  SourceScope.ActionProgramsAt spec.root (fun _ => CodeAt spec .root)

/-- Every native source action retains its protected launched programs. -/
theorem source_action_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (point : Point) (action : NAction) (source : SourcePoint spec point)
    (found : actionAt spec.root point = some action) : ActionAt spec action :=
  SourceScope.ActionProgramsAt.mono spec.root action
    (SourceScope.source_action_children spec.root point action source.1 found)
    (source_program_at spec fragment point source.2.1)

/-- Scoped forks retain the same protected source program class as direct source forks. -/
theorem scoped_fork_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (point : Point) (scope : Nat) (action : NAction) (source : SourcePoint spec point)
    (found : forkScopedAt spec.root point scope = some action) : ActionAt spec action :=
  SourceScope.ActionProgramsAt.mono spec.root action
    (SourceScope.scoped_fork_children spec.root point scope action source.1 found)
    (source_program_at spec fragment point source.2.1)
/-- Stored actions retain the certified captures of every launched existing program. -/
theorem store_action_at (spec : Spec) (name : ActionName)
    (lexical : SourceScope.StoreActionAt spec.root name)
    (leading : AnswerSlots.StoreActionAt spec.bindings name) (owned : StoreActionAt spec name) :
    ActionAt spec (embedAction (actionOf name)) := by
  cases name
  case fork | forkIn | forkScoped | setInterruptible => exact progOf_at spec _ lexical leading owned
  case closePar order exit =>
    refine ⟨?_, lexical.2⟩
    change ∀ body ∈ (order.map (fun fin => finProgram fin exit)).map embed, CodeAt spec .root body
    rw [List.map_map]
    intro body member
    obtain ⟨fin, present, same⟩ := List.mem_map.mp member
    rw [← same]
    exact finProgram_at spec fin exit (owned fin present)
  case raceAll race =>
    cases race <;> aesop (add norm simp [actionOf, embedAction, ActionAt, SourceScope.ActionProgramsAt,
      raceEntrants, List.mem_cons, CodeAt, ValueAt, embed, ThunkAt, StoreThunkAt, ProgAt,
      NameAt, OrdinaryName, ProtectedName, StoreNameAt, StoreActionAt,
      SourceScope.StoreActionAt, SourceScope.ProgAt, SourceScope.StoreThunkAt,
      SourceScope.OpAt, SourceScope.NameAt, SourceScope.ThunkAt,
      AnswerSlots.StoreActionAt, AnswerSlots.ProgAt, AnswerSlots.StoreThunkAt,
      AnswerSlots.OpAt, AnswerSlots.NameAt, AnswerSlots.ThunkAt]) (add safe apply [progOf_at])
  all_goals trivial

/-- Actual interpreted source and stored actions retain their protected launched programs. -/
theorem interp_action_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (thunk : EffThunk) (action : NAction)
    (owned : ThunkAt spec thunk)
    (found : (interpAt spec.root completed spec.table).withFiberOf thunk = some action) : ActionAt spec action := by
  cases thunk
  case act point => exact source_action_at spec fragment point action owned.2.2 found
  case forkInAt point scope => exact scoped_fork_at spec fragment point scope action owned.2.2 found
  case store thunk =>
    cases thunk
    case act name => cases found; exact store_action_at spec name owned.1 owned.2.1 owned.2.2
    all_goals cases found
  case acquireMasked point ctx =>
    cases found
    refine ⟨.root, ⟨rfl, trivial, trivial, trivial⟩, owned.1, owned.2.1, owned.2.2, ?_⟩
    exact spec.complete point.path owned.1.2.2
  case releaseMasked point previous =>
    cases found
    exact ⟨rfl, resolve_source spec fragment point
      ⟨owned.2.2.1, owned.2.2.2.1, .inr owned.2.2.2.2⟩, trivial, trivial, trivial⟩
  case forkLayer => exact owned.1.elim
  case provideMasked update region flag =>
    cases found
    exact ⟨.root, ⟨rfl, trivial, trivial, trivial⟩, owned.1, owned.2.1, owned.2.2⟩
  case restoreRegion region flag =>
    cases found
    exact region_at spec fragment region owned.2.2
  all_goals aesop (add norm simp [interpAt, interpOf, ActionAt, SourceScope.ActionProgramsAt])
end Effect4.Program.AnswerSlots.Typed
