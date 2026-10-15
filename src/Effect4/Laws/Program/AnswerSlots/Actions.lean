import Effect4.Laws.Program.AnswerSlots.Interp
import Effect4.Laws.Program.NativeActionScope

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: spawned and masked code retains the bindings used by the crew log proofs.
Reach: actual direct-fragment source actions and existing stored action wrappers.
Limit: source ownership and initialized leading bindings remain premises.
Consumer: the stable answer-flow action and fork clauses.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- Every launched program retains its initialized leading environment. -/
def ActionAt (bindings : List Val) : NAction → Prop
  | .fork body _ _ | .forkIn body _ _ _ | .forkScoped body _ _ | .setInterruptible body _ => CodeAt bindings body
  | .raceAll bodies _ | .raceAllFirst bodies _ | .closePar bodies => ∀ body ∈ bodies, CodeAt bindings body
  | _ => True

/-- Source ownership's exact child witness retains its parent's leading bindings. -/
theorem child_program_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (parent : Point) (indices : List Nat) (program : NCode)
    (slots : Prefix bindings parent.env) (held : SourceScope.ChildProgramAt root parent indices program) :
    CodeAt bindings program := by
  obtain ⟨effect, node, lexical, code⟩ := held
  have env := congrArg (fun point : Point => point.env) (SourceScope.childPoint_spec parent indices).2.2
  rw [code]
  apply resolve_at root fragment bindings
  rw [env]
  exact slots

/-- Exact source program roles retain the parent's immutable leading slots. -/
theorem source_program_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (parent : Point) (slots : Prefix bindings parent.env)
    (role : SourceScope.ProgramRole) (program : NCode)
    (held : SourceScope.SourceProgramAt root parent role program) : CodeAt bindings program := by
  cases role with
  | forkBody => exact child_program_at root fragment bindings parent _ program slots held
  | maskBody => exact child_program_at root fragment bindings parent _ program slots held
  | entrantBody =>
    obtain ⟨index, held⟩ := held
    exact child_program_at root fragment bindings parent _ program slots held

/-- The existing source role annotation supplies every action program's leading bindings. -/
theorem action_programs_at (root : NativeEff) (bindings : List Val) (action : NAction)
    (held : SourceScope.ActionProgramsAt root (fun _ => CodeAt bindings) action) :
    ActionAt bindings action := by
  cases action <;> aesop (add norm simp [ActionAt, SourceScope.ActionProgramsAt])

/-- A source action retains initialized leading bindings in every launched program. -/
theorem source_action_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (action : NAction) (source : SourceScope.At root p)
    (slots : Prefix bindings p.env) (found : actionAt root p = some action) : ActionAt bindings action :=
  action_programs_at root bindings action (SourceScope.ActionProgramsAt.mono root action
    (SourceScope.source_action_children root p action source found)
    (source_program_at root fragment bindings p slots))

/-- A scoped fork retains initialized leading bindings in its actual child program. -/
theorem scoped_fork_at (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (p : Point) (scope : Nat) (action : NAction) (source : SourceScope.At root p)
    (slots : Prefix bindings p.env) (found : forkScopedAt root p scope = some action) : ActionAt bindings action :=
  action_programs_at root bindings action (SourceScope.ActionProgramsAt.mono root action
    (SourceScope.scoped_fork_children root p scope action source found)
    (source_program_at root fragment bindings p slots))

/-- Stored action wrappers retain the immutable bindings of every captured finalizer. -/
theorem store_action_at (bindings : List Val) (name : ActionName) (held : StoreActionAt bindings name) :
    ActionAt bindings (embedAction (actionOf name)) := by
  cases name
  case fork | forkIn | forkScoped | setInterruptible => exact progOf_at bindings _ held
  case closePar order exit =>
    change ∀ body ∈ (order.map (fun fin => finProgram fin exit)).map embed, CodeAt bindings body
    rw [List.map_map]
    intro body member
    obtain ⟨fin, present, eq⟩ := List.mem_map.mp member
    rw [← eq]
    exact finProgram_at bindings fin exit (held fin present)
  case raceAll race =>
    cases race <;> aesop (add norm simp [actionOf, embedAction, ActionAt, raceEntrants,
      List.mem_cons, CodeAt, embed, ThunkAt, StoreThunkAt, ProgAt, NameAt, StoreNameAt]) (add safe apply [progOf_at])
  all_goals trivial

/-- The actual thunk interpreter retains initialized leading bindings in every action program. -/
theorem interp_action_at (root : NativeEff) (fragment : SourceScope.Fragment root) (bindings : List Val)
    (completed) (table : RowTable) (thunk : EffThunk) (action : NAction)
    (source : SourceScope.ThunkAt root thunk) (held : ThunkAt bindings thunk)
    (found : (interpAt root completed table).withFiberOf thunk = some action) : ActionAt bindings action := by
  cases thunk
  case act p => exact source_action_at root fragment bindings p action source held found
  case forkInAt p scope => exact scoped_fork_at root fragment bindings p scope action source held found
  case store thunk =>
    cases thunk
    case act name => cases found; exact store_action_at bindings name held
    all_goals cases found
  case acquireMasked p ctx => cases found; exact ⟨trivial, held⟩
  case releaseMasked p previous => cases found; exact ⟨resolve_at root fragment bindings p held, trivial⟩
  case forkLayer => exact held.elim
  case provideMasked update body flag => cases found; exact ⟨trivial, held⟩
  case restoreRegion body flag => cases found; exact region_at root fragment bindings body held
  all_goals aesop (add norm simp [interpAt, interpOf, ActionAt])
end Effect4.Program.AnswerSlots
