import Effect4.Laws.Machine.AnswerFlowConstructors
import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: recursive saved loops and iterators compose with the existing semantic saved frames.
Reach: arbitrary worlds and answer classes, with a named broad class and actual interpreter hooks.
Limit: source ownership, initialization and command preservation remain instance obligations.
Consumer: the initialized Workers and QueueWorkers native answer graph.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4 Effect4.Contracts
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α) (broad : Kind)
variable (Loop Iter : World → ν → Prop)

/-- Existing semantic saved frames coexist with recursive hook names, without finite loop unrolling. -/
inductive RecursiveEdge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop
  | saved {world input output frame} (held : SavedAt model interp world input output frame) :
      RecursiveEdge world input output frame
  | loop {world name} (cursor : β) (held : Loop world name) :
      RecursiveEdge world broad broad (.whileLoop name cursor)
  | iterator {world name} (cursor : β) (held : Iter world name) :
      RecursiveEdge world broad broad (.iterator name cursor)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Each recursive loop hook supplies the actual next program at the broad answer class. -/
def RecursiveLoopResult (world : World) : LoopNext β (Prim ν σ β ε δ ι α) → Prop
  | .continue _ body | .finish body => model.code world broad body

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Each recursive iterator hook supplies its next program and retained iterator name. -/
def RecursiveIterResult (world : World) : IterStep ν σ β ε δ ι α (Prim ν σ β ε δ ι α) → Prop
  | .done value => model.value world broad value
  | .halt cause => model.cause world broad cause
  | .resume body next => model.code world broad body ∧ Iter world next

/-- Hook producers retain actual recursive names across permitted future worlds. -/
structure RecursiveHooks : Prop where
  loop_future : ∀ world nextWorld, model.future world nextWorld → ∀ name,
    Loop world name → Loop nextWorld name
  iter_future : ∀ world nextWorld, model.future world nextWorld → ∀ name,
    Iter world name → Iter nextWorld name
  loop_resume : ∀ world name cursor answer, Loop world name →
    RecursiveLoopResult model broad world (interp.loopResume name cursor answer)
  iter_next : ∀ world name answer, Iter world name →
    RecursiveIterResult model broad Iter world ((interp.iterNext name answer).2)

/-- The semantic saved path embeds directly in the common recursive saved path. -/
theorem recursive_result (world : World) (output : Kind) (next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α))
    (held : FamilyResult model (SavedAt model interp) world output next pushed) :
    FamilyResult model (RecursiveEdge model interp broad Loop Iter) world output next pushed := by
  obtain ⟨input, code, path⟩ := held
  exact ⟨input, code, path.map (fun _ _ _ saved => .saved saved)⟩

/-- One common saved family handles semantic frames and recursive interpreter hooks. -/
theorem recursive_family (hooks : RecursiveHooks model interp broad Loop Iter) :
    SavedFamily model interp (RecursiveEdge model interp broad Loop Iter) := by
  have semantic := saved_family model interp
  constructor
  · intro world input output frame edge nextWorld future value good absent
    cases edge with
    | saved held => exact semantic.skip world input output frame held nextWorld future value good absent
    | loop => cases absent
    | iterator => cases absent
  · intro world input output frame edge nextWorld future cause good absent
    cases edge with
    | saved held => exact semantic.skipCause world input output frame held nextWorld future cause good absent
    | loop => exact good
    | iterator => exact good
  · intro world input output frame edge nextWorld future value provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      exact recursive_result model interp broad Loop Iter nextWorld output next pushed
        (semantic.answer world input output frame held nextWorld future value provided next pushed good supplied absent arm)
    | loop cursor held =>
      have later := hooks.loop_future world nextWorld future _ held
      have code := hooks.loop_resume nextWorld _ cursor value later
      change (match interp.loopResume _ cursor value with
        | .continue next body => some (body, [Prim.whileLoop _ next])
        | .finish body => some (body, [])) = some (next, pushed) at arm
      cases actual : interp.loopResume _ cursor value with
      | «continue» cursor body =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, code, .cons (.loop cursor later) (.nil broad)⟩
      | finish body =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, code, .nil broad⟩
    | iterator cursor held =>
      have later := hooks.iter_future world nextWorld future _ held
      have code := hooks.iter_next nextWorld _ value later
      change (match (interp.iterNext _ value).2 with
        | .done result => some (Prim.success result, [])
        | .halt reason => some (Prim.failure reason, [])
        | .resume body continueAs => some (body, [Prim.iterator continueAs cursor])) = some (next, pushed) at arm
      cases actual : (interp.iterNext _ value).2 with
      | done result =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, model.success nextWorld broad result code, .nil broad⟩
      | halt reason =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, model.failure nextWorld broad reason code, .nil broad⟩
      | resume body continueAs =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, code.1, .cons (.iterator cursor code.2) (.nil broad)⟩
  · intro world input output frame edge nextWorld future cause provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      exact recursive_result model interp broad Loop Iter nextWorld output next pushed
        (semantic.cause world input output frame held nextWorld future cause provided next pushed good supplied absent arm)
    | loop => cases arm
    | iterator => cases arm
  · intro world input output frame edge nextWorld future exit next good program
    cases edge with
    | saved held => exact semantic.program world input output frame held nextWorld future exit next good program
    | loop => cases program
    | iterator => cases program
  · intro world input output frame edge nextWorld future fiber cause delivered good selected interrupted skipped
    cases edge with
    | saved held => exact semantic.discard world input output frame held nextWorld future fiber cause delivered good selected interrupted skipped
    | loop => cases selected
    | iterator => cases selected
end Effect4.Machine.AnswerFlow
