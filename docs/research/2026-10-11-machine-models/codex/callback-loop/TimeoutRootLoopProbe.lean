import TimeoutJointGenerationProbe
import Effect4.Laws.Machine.AnswerFlowFamily

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the actual root cursor permission for Timeout's numeric history goals.
Consumer: shared loop_step and actual source child allocation.
The returned form and heap premises remain local producers, not a reached-history assertion.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutRootLoop
open Effect4 Effect4.Machine Effect4.Program Effect4.Contracts
open HostTimeoutSlots HostTimeoutSource HostTimeoutNumberState HostTimeoutNumberFlow
open HostTimeoutJointGeneration

/-- The root loop captures exactly the allocated cells, before any cursor binder. -/
def RootAt (point : Point) : Prop :=
  point.path = [1,1,1,0] ∧ point.env = cells (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩)

/-- The real outer binder holds the same cells beneath the loop. -/
def FinishAt (point : Point) : Prop :=
  point.path = [1,1,1] ∧ point.env = cells (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩)

/-- The source body receives this cursor only after the previous form completes. -/
structure Complete (image : Image) (n : Nat) (plain : Bool) : Prop where
  cursor : image.count = n
  cleanups : image.cleanups.length = image.count
  forms : image.exits.length = image.count
  declared : plain = true → image.exits.all HostTimeoutNumberLedger.exitRetries = true

/-- The instance retains a stopped root or an actual generation's body return. -/
inductive Kind
  | root
  | body (n : Fin 4) (delay : Nat) (previous : Val)

/-- A completed body either answers or supplies the declared returned failure before retry. -/
inductive BodyValue (plain : Bool) (state : Stores) (n : Fin 4) : Val → Prop
  | answered (image : Image) (body error : Val) (heap : ImageAt image state)
      (cursor : image.count = n.val + 1) : BodyValue plain state n (.list [.some body, error])
  | retry (image : Image) (error : Val) (heap : ImageAt image state)
      (complete : Complete image (n.val + 1) plain) (declared : Retryable error) :
      BodyValue plain state n (.list [.none, .some error])

/-- Every delivered root value still reads an actual numeric heap. -/
def ValueAt (plain : Bool) (state : Stores) : Kind → Val → Prop
  | .root, _ => ∃ image, ImageAt image state
  | .body n _ _, value => BodyValue plain state n value

/-- A skipped loop failure retains the actual numeric heap without granting another retry. -/
def CauseAt (state : Stores) (_kind : Kind) (_cause : CauseV) : Prop :=
  ∃ image, ImageAt image state

/-- The permitted source body retains its generation, captured cells and completed predecessor form. -/
inductive CodeAt (plain : Bool) (state : Stores) : Kind → NCode → Prop
  | success (kind : Kind) (value : Val) (good : ValueAt plain state kind value) :
      CodeAt plain state kind (.success value)
  | failure (kind : Kind) (cause : CauseV) (good : CauseAt state kind cause) :
      CodeAt plain state kind (.failure cause)
  | iteration (point : Point) (root : RootAt point) (n : Fin 4) (delay : Nat) (previous : Val)
      (image : Image) (heap : ImageAt image state) (complete : Complete image n.val plain) :
      CodeAt plain state (.body n delay previous)
        (resolve HostTimeoutSource.program (point.childWith 0 (cursor n delay .none previous)))

  | finish (point : Point) (source : FinishAt point) (view : HostTimeoutFlow.View)
      (value : Val) (image : Image) (heap : ImageAt image state) :
      CodeAt plain state .root
        (resolve HostTimeoutSource.program ({point with completed := view}.childWith 1 value))

/-- The numeric root instance uses the existing state-indexed callback contract. -/
def model (plain : Bool) : AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val)
    (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Stores Kind where
  future := HostTimeoutNumberFlow.Future
  future_refl := fun _ => ⟨Nat.le_refl _, Nat.le_refl _⟩
  future_trans := fun _ _ _ first second =>
    ⟨Nat.le_trans first.1 second.1, Nat.le_trans first.2 second.2⟩
  value := ValueAt plain
  cause := CauseAt
  code := CodeAt plain
  finalizer := fun _ _ _ => none
  success := fun _ => CodeAt.success
  failure := fun _ => CodeAt.failure

/-- Saved loop edges retain the captured root and the exact generation that will return to it. -/
inductive Edge (plain : Bool) (_state : Stores) : Kind → Kind → NCode → Prop
  | loop (point : Point) (root : RootAt point) (n : Fin 4) (delay : Nat) (previous : Val) :
      Edge plain _state (.body n delay previous) .root
        (.whileLoop (.loop point) (cursor n delay .none previous))
  | finish (point : Point) (source : FinishAt point) (body : NCode) :
      Edge plain _state .root .root (.onSuccess body (.cont point))
  | mask (kind : Kind) (flag : Bool) : Edge plain _state kind kind (.setInterruptible flag)

/-- Refreshing completed exits keeps the allocated cells and source address. -/
theorem RootAt.completed {point : Point} (held : RootAt point) (view : HostTimeoutFlow.View) :
    RootAt {point with completed := view} := held

/-- The concrete source guard supplies Fin4 before entering a new attempt. -/
theorem enter (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View) (point : Point) (root : RootAt point)
    (image : Image) (heap : ImageAt image state) (n delay : Nat) (previous : Val)
    (complete : Complete image n plain) :
    match (HostTimeoutFlow.interpreter view).loopEnter (.loop point) (cursor n delay .none previous) with
    | .continue next body =>
        AnswerFlow.FamilyResult (model plain) (Edge plain) state .root body [.whileLoop (.loop point) next]
    | .finish body => AnswerFlow.FamilyResult (model plain) (Edge plain) state .root body [] := by
  have slots : EnvAt [] point.path point.env := by
    rw [root.1, root.2]
    exact .loop _ _ _
  have equation := loop_waiting [] {point with completed := view} slots n delay previous root.1
  change (match loopNextAt HostTimeoutSource.program {point with completed := view}
      (cursor n delay .none previous) with
    | .continue next body => AnswerFlow.FamilyResult (model plain) (Edge plain) state .root body [.whileLoop (.loop point) next]
    | .finish body => AnswerFlow.FamilyResult (model plain) (Edge plain) state .root body [])
  rw [equation]
  by_cases allowed : n = 0 ∨ n < 4
  · rw [if_pos allowed]
    have bounded : n < 4 := by rcases allowed with zero | bounded; omega; exact bounded
    let next : Fin 4 := ⟨n, bounded⟩
    refine ⟨.body next delay previous, CodeAt.iteration _ (root.completed view) next delay previous image heap complete, ?_⟩
    exact .cons (.loop point root next delay previous) (.nil Kind.root)
  · rw [if_neg allowed]
    exact ⟨Kind.root, CodeAt.success Kind.root _ ⟨image, heap⟩, .nil Kind.root⟩

/-- A completed retry form grants Ready at the source's actual successor cursor. -/
theorem returned_complete (image : Image) (n : Fin 4) (active : Active image n)
    (attemptExit : ExitV) (delay : Nat) (previous : Val) (tag message : String)
    (selected : evalTerm
      (HostTimeoutSource.cellEnv (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) ++
        [cursor n delay .none previous, .unit, .list [.str tag, .str message]])
      HostTimeoutSource.retryTest = some (.bool true)) :
    Complete (image.afterForm active.own attemptExit (Exit.failure (Cause.fail (Err.tagged tag message))))
      (n.val + 1) true := by
  have finished := form_committed image active.own n active.cursor attemptExit
    (Exit.failure (Cause.fail (Err.tagged tag message)))
  refine ⟨active.cursor, finished.2.2.1, finished.2.2.2, ?_⟩
  intro _
  have declared := source_test_retries n delay previous tag message selected
  change (image.exits ++ [Exit.failure (Cause.fail (Err.tagged tag message))]).all
    HostTimeoutNumberLedger.exitRetries = true
  rw [List.all_append, active.declared]
  simp only [List.all_cons, declared, List.all_nil, Bool.and_self]

/-- The shared loop step consumes this exact Ready permission and retains the actual older suffix. -/
theorem ready_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View) (point : Point) (root : RootAt point)
    (image : Image) (heap : ImageAt image state) (n delay : Nat) (previous : Val)
    (complete : Complete image n plain) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (current : fiber.current = .whileLoop (.loop point) (cursor n delay .none previous))
    (output : Kind) (stack : Path (Edge plain state) .root output fiber.stack) :
    ∃ after, (fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp).1 = .running after ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack :=
  AnswerFlow.loop_step (model plain) (HostTimeoutFlow.interpreter view).toPrimInterp (Edge plain)
    state .root output fiber (.loop point) (cursor n delay .none previous) current stack
    (by intro next body found
        have result := enter plain state view point root image heap n delay previous complete
        rw [found] at result
        exact result)
    (by intro body found
        have result := enter plain state view point root image heap n delay previous complete
        rw [found] at result
        exact result)

/-- The actual loop value arm consumes the completed form at its matching generation.
The returned edge keeps the next generation instead of assuming a future heap. -/
theorem resume (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (point : Point) (root : RootAt point) (n : Fin 4) (delay : Nat) (previous value : Val)
    (good : BodyValue plain state n value) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (arm : (Prim.whileLoop (.loop point) (cursor n delay .none previous)).armA
      (HostTimeoutFlow.interpreter view).toPrimInterp value provided = some (next, pushed)) :
    AnswerFlow.FamilyResult (model plain) (Edge plain) state .root next pushed := by
  have slots : EnvAt [] point.path point.env := by
    rw [root.1, root.2]
    exact .loop _ _ _
  have equation := loop_step_value [] {point with completed := view} slots n delay
    (.list [.none, previous]) value root.1
  simp only [Prim.armA] at arm
  have hook : (HostTimeoutFlow.interpreter view).loopResume (.loop point)
      (cursor n delay .none previous) value =
      loopNextAt HostTimeoutSource.program {point with completed := view}
        (.list [.nat (n.val + 1), .list [.nat (if 0 < n.val then delay * 2 else delay), value]]) := equation
  rw [hook] at arm
  cases good with
  | answered image body error heap count =>
    have stopped := loop_answer_stops [] {point with completed := view} slots (n.val + 1)
      (if 0 < n.val then delay * 2 else delay) body error root.1
    change loopNextAt HostTimeoutSource.program {point with completed := view}
      (.list [.nat (n.val + 1), .list [.nat (if 0 < n.val then delay * 2 else delay),
        .list [.some body, error]]]) = _ at stopped
    rw [stopped] at arm
    cases arm
    exact ⟨.root, CodeAt.success Kind.root _ ⟨image, heap⟩, .nil Kind.root⟩
  | retry image error heap complete declared =>
    have result := enter plain state view point root image heap (n.val + 1)
      (if 0 < n.val then delay * 2 else delay) (.some error) complete
    have hook : (HostTimeoutFlow.interpreter view).loopEnter (.loop point)
        (cursor (n.val + 1) (if 0 < n.val then delay * 2 else delay) .none (.some error)) =
        loopNextAt HostTimeoutSource.program {point with completed := view}
          (cursor (n.val + 1) (if 0 < n.val then delay * 2 else delay) .none (.some error)) := rfl
    rw [hook] at result
    simp only [HostTimeoutSource.cursor] at result
    cases actual : loopNextAt HostTimeoutSource.program {point with completed := view}
      (cursor (n.val + 1) (if 0 < n.val then delay * 2 else delay) .none (.some error)) with
    | «continue» cursor body =>
      simp only [HostTimeoutSource.cursor] at actual
      rw [actual] at arm result
      cases arm
      exact result
    | finish body =>
      simp only [HostTimeoutSource.cursor] at actual
      rw [actual] at arm result
      cases arm
      exact result

/-- This recursive source family has finite local obligations, without an inductive callback cycle. -/
theorem family (plain : Bool) (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily (model plain) (HostTimeoutFlow.interpreter view).toPrimInterp (Edge plain) where
  skip := by
    intro state input output frame edge next future value good missing
    cases edge with
    | loop point root n delay previous => cases missing
    | finish point source body => cases missing
    | mask kind flag => exact good
  skipCause := by
    intro state input output frame edge next future cause good missing
    cases edge with
    | loop point root n delay previous => exact good
    | finish point source body => exact good
    | mask kind flag => exact good
  answer := by
    intro state input output frame edge nextState future value provided next pushed good supplied absent arm
    cases edge with
    | loop point root n delay previous => exact resume plain nextState view point root n delay previous value good provided next pushed arm
    | finish point source body =>
      obtain ⟨image, heap⟩ := good
      have callback : (.onSuccess body (.cont point) : NCode).armA
          (HostTimeoutFlow.interpreter view).toPrimInterp value provided =
          some (resolve HostTimeoutSource.program ({point with completed := view}.childWith 1 value), []) := rfl
      rw [callback] at arm
      cases arm
      exact ⟨Kind.root, CodeAt.finish point source view value image heap, .nil Kind.root⟩
    | mask kind flag => cases arm
  cause := by
    intro state input output frame edge nextState future cause provided next pushed good supplied absent arm
    cases edge with
    | loop point root n delay previous => cases arm
    | finish point source body => cases arm
    | mask kind flag => cases arm
  program := by
    intro state input output frame edge nextState future exit next good found
    rw [AnswerFlow.programOf_none (model plain) nextState frame exit (fun _ => rfl)] at found
    cases found
  discard := by
    intro state input output frame edge nextState future fiber cause delivered good armed interrupted skipped
    cases edge with
    | loop point root n delay previous => cases armed
    | finish point source body => cases armed
    | mask kind flag => cases armed

/-- The exact source continuation assigns a finite generation and retains its allocated capture.
Consumer: the existing source-action child producer and actual entrant allocation. -/
theorem continue_generation (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (point : Point) (root : RootAt point) (image : Image) (heap : ImageAt image state)
    (generation delay : Nat) (previous next : Val)
    (complete : Complete image generation plain) (body : NCode)
    (actual : (HostTimeoutFlow.interpreter view).loopEnter (.loop point)
      (cursor generation delay .none previous) = .continue next body) :
    ∃ bounded : Fin 4, bounded.val = generation ∧
      CodeAt plain state (.body bounded delay previous) body ∧
      Capture bounded delay previous
        ({point with completed := view}.childWith 0 (cursor bounded delay .none previous)) := by
  have slots : EnvAt [] point.path point.env := by
    rw [root.1, root.2]
    exact .loop _ _ _
  have equation := loop_waiting [] {point with completed := view} slots generation delay previous root.1
  change loopNextAt HostTimeoutSource.program {point with completed := view}
    (cursor generation delay .none previous) = .continue next body at actual
  rw [equation] at actual
  by_cases allowed : generation = 0 ∨ generation < 4
  · rw [if_pos allowed] at actual
    cases actual
    have bounded : generation < 4 := by rcases allowed with zero | bounded; omega; exact bounded
    let own : Fin 4 := ⟨generation, bounded⟩
    refine ⟨own, rfl, CodeAt.iteration _ (root.completed view) own delay previous image heap complete, ?_⟩
    change running (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) own delay previous <+:
      point.env ++ [cursor own delay .none previous]
    rw [root.2]
    exact List.prefix_refl _
  · rw [if_neg allowed] at actual
    cases actual

/-- A body return cannot reuse the ready heap before its matching generation is counted. -/
theorem uncounted_refuses (plain : Bool) (state : Stores) (image : Image) (n : Fin 4)
    (heap : ImageAt image state) (uncounted : image.count = n.val) (value : Val)
    (returned : BodyValue plain state n value) : False := by
  have distinct (after : Image) (post : ImageAt after state) (counted : after.count = n.val + 1) : False := by
    have cells := congrArg (fun refs : RefHeap => refs[0]?) (heap.symm.trans post)
    change some (Val.nat image.count) = some (Val.nat after.count) at cells
    have count := congrArg (Env.natOfVal 0) (Option.some.inj cells)
    change image.count = after.count at count
    omega
  cases returned with
  | answered after body error post counted => exact distinct after post counted
  | retry after error post complete declared => exact distinct after post complete.cursor

/-- The actual outer finish binder inhabits the numeric suffix required by ready_step. -/
theorem finish_stack (plain : Bool) (state : Stores) (point : Point)
    (source : FinishAt point) (body : NCode) :
    Path (Edge plain state) .root .root [.onSuccess body (.cont point)] :=
  .cons (.finish point source body) (.nil Kind.root)

end Test.Dogfood.Proofs.HostTimeoutRootLoop
