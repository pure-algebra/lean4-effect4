import Effect4.Laws.Program.ReleaseCustody.PopSequencing

/-!
Concept: scope-lifetime-finalization, R11.
Question: all primitive sequencing cases serve Execution.history and Workers.Assertions.releases_step.
Reach: native FrameFiber.step under the existing source predicate's exact registration-body field.
Limit: primitive closure alone proves no scheduler command closure, history closure or progress.
Unlock: parked-stack stability and evaluator sequencing reuse the same actual frame list.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.FrameSequencing
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.ReleaseCustody.PopSequencing
open Effect4.Program.ReleaseCustody.Pop (Frame)

/-- All eighteen native primitive cases retain the callback sequence.
The template premise is the existing CodeAt registration-body projection.
Consumer: native evaluator and admitted command histories. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem step (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable)
    (fiber : Frame) (held : Kept fiber.current fiber.stack)
    (template : ∀ body a fin, fiber.current = .onSuccess body (.afterScopeAdd a fin) →
      ∃ scope, body = .sync (.op (.scopeAdd scope fin))) :
    match (fiber.step (interpAt root completed table).toPrimInterp).1 with
    | .running next => Kept next.current next.stack
    | .finished _ => True := by
  have absent {code : NCode} (same : fiber.current = code)
      (notAdd : ∀ fin, ¬ AddPhase fin code) (notYield : ¬ YieldPhase code) : NoAdd fiber.stack :=
    opaque_noAdd (same ▸ held) notAdd notYield
  cases current : fiber.current
  case success value =>
    simp only [FrameFiber.step, current]
    exact resumeValue_kept root completed table fiber value (some (.success value)) held
  case failure cause =>
    simp only [FrameFiber.step, current]
    exact resumeCause_kept root completed table fiber cause (some (.failure cause)) held
  case sync thunk =>
    simp only [FrameFiber.step, current]
    exact resumeValue_kept root completed table fiber ((interpAt root completed table).syncValue thunk) none held
  case suspend thunk =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    exact .clean _ _ missing
  case withFiber thunk =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    exact .clean _ _ missing
  case yieldableError error =>
    simp only [FrameFiber.step, current]
    exact interrupt held (.fail error)
  case setInterruptible flag =>
    simp only [FrameFiber.step, current]
    exact interrupt held (.die (interpAt root completed table).notImplemented)
  case asyncFinalizer name =>
    simp only [FrameFiber.step, current]
    exact interrupt held (.die (interpAt root completed table).notImplemented)
  case yieldNowWith priority =>
    simp only [FrameFiber.step, current]
    exact current ▸ held
  case async =>
    simp only [FrameFiber.step, current]
    exact current ▸ held
  case onSuccess body name =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    cases name
    case afterScopeAdd a fin =>
      obtain ⟨scope, same⟩ := template body a fin current
      subst body
      exact .add _ scope a fin fiber.stack missing (.operation scope)
    all_goals exact .clean _ _ (noAdd_cons _ (by intro body' a fin same; cases same) missing)
  case onSuccessConst body next =>
    simp only [FrameFiber.step, current]
    exact constant_push_kept body next (current ▸ held)
  case onFailure body name =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    exact .clean _ _ (noAdd_cons _ (by intro body a fin same; cases same) missing)
  case onSuccessAndFailure body a e =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    exact .clean _ _ (noAdd_cons _ (by intro body a fin same; cases same) missing)
  case exitFrame body =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    exact .clean _ _ (noAdd_cons _ (by intro body a fin same; cases same) missing)
  case onExit body name flag =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    exact .clean _ _ (noAdd_cons _ (by intro body a fin same; cases same) missing)
  case iterator generator cursor =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    generalize found : (.iterator generator cursor : NCode).armA
      (interpAt root completed table).toPrimInterp cursor none = answer
    cases answer with
    | none => trivial
    | some pair =>
      obtain ⟨next, pushed⟩ := pair
      have extra := armA_noAdd root completed table (.iterator generator cursor) cursor none next pushed found
      exact .clean _ _ (noAdd_append _ _ extra missing)
  case whileLoop loop cursor =>
    have missing := absent current (by intro fin phase; cases phase) (by intro phase; cases phase)
    simp only [FrameFiber.step, current]
    generalize entered : (interpAt root completed table).loopEnter loop cursor = entry
    cases entry with
    | «continue» next body =>
      exact .clean _ _ (noAdd_cons _ (by intro body a fin same; cases same) missing)
    | finish code => exact .clean _ _ missing

end Effect4.Program.ReleaseCustody.FrameSequencing
