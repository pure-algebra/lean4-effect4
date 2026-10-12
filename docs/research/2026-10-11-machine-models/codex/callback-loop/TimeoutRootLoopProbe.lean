import TimeoutJointGenerationProbe
import Effect4.Laws.Machine.AnswerFlowFamilyPop

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

/-- The actual retry test point retains the allocated cells and generation cursor. -/
def catchPoint (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous
    fuel := fuel + 1}

def iterationPoint (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) : Point :=
  {captured with
    path := [1,1,1,0,0]
    env := running (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay previous
    fuel := fuel + 2}

theorem iteration_bind (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
    resolve HostTimeoutSource.program (iterationPoint captured fuel n delay previous) =
      .onSuccess (.suspend (.body ((iterationPoint captured fuel n delay previous).child 0)))
        (.cont (iterationPoint captured fuel n delay previous)) := by kernel_rfl

theorem delay_callback (view : HostTimeoutFlow.View) (captured : Point)
    (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
    (HostTimeoutFlow.interpreter view).contA
      (.cont (iterationPoint captured fuel n delay previous)) .unit =
      resolve HostTimeoutSource.program (catchPoint {captured with completed := view} fuel n delay previous) := by
  kernel_rfl


/-- The saved answer callback retains the allocated cells and exact generation capture. -/
def answerBinderPoint (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0]
    env := ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay previous
    fuel := fuel + 4}

/-- The answer binder's actual body is the numeric form-finalizer source point. -/
theorem answer_bind (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
    resolve HostTimeoutSource.program (answerBinderPoint captured fuel n delay previous) =
      .onSuccess (resolve HostTimeoutSource.program
        (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous))
        (.cont (answerBinderPoint captured fuel n delay previous)) := by kernel_rfl

/-- The answer callback wraps the actual returned form value and retains its success column. -/
theorem answer_callback (view : HostTimeoutFlow.View) (captured : Point) (fuel : Nat)
    (n : Fin 4) (delay : Nat) (previous body : Val) :
    (HostTimeoutFlow.interpreter view).contA (.cont (answerBinderPoint captured fuel n delay previous)) body =
      .success (HostTimeoutSource.answered body) := by kernel_rfl

/-- The callback reads the actual retry test and its existing body and handler. -/
theorem catch_node (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
    Node.at_ (.eff HostTimeoutSource.program) (catchPoint captured fuel n delay previous).path =
      some (.eff (.catchIf HostTimeoutSource.retryTest
        (HostTimeoutSlots.sourceAt [1,1,1,0,0,1,0])
        (HostTimeoutSlots.sourceAt [1,1,1,0,0,1,1]))) := by kernel_rfl

/-- The actual handled source leaf supplies the loop's failure option pair. -/
theorem catch_handler (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous error : Val) :
    resolve HostTimeoutSource.program ((catchPoint captured (fuel + 1) n delay previous).childWith 1 error) =
      Prim.success (.list [.none, .some error]) := by kernel_rfl

/-- The native catch uses its actual source test before returning that pair. -/
theorem catch_callback (view : HostTimeoutFlow.View) (captured : Point) (fuel : Nat)
    (n : Fin 4) (delay : Nat) (previous : Val) (cause : CauseV) :
    (HostTimeoutFlow.interpreter view).contE (.caughtError (catchPoint captured (fuel + 1) n delay previous)) cause =
      match caughtErrorValue?
        (ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay previous) HostTimeoutSource.retryTest cause with
      | some error => .success (.list [.none, .some error])
      | none => .failure cause := by
  change Effect4.Program.contEOf HostTimeoutSource.program
    (.caughtError {catchPoint captured (fuel + 1) n delay previous with completed := view}) cause = _
  rw [Effect4.Program.contEOf, catch_node]
  change (match caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous) HostTimeoutSource.retryTest cause with
    | some error => resolve HostTimeoutSource.program
      ((catchPoint {captured with completed := view} (fuel + 1) n delay previous).childWith 1 error)
    | none => .failure cause) = _
  cases handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous) HostTimeoutSource.retryTest cause with
  | none => rfl
  | some error => exact catch_handler _ _ _ _ _ _

/-- The source body receives this cursor only after the previous form completes. -/
structure Complete (image : Image) (n : Nat) (plain : Bool) : Prop where
  cursor : image.count = n
  cleanups : image.cleanups.length = image.count
  forms : image.exits.length = image.count
  declared : plain = true → image.exits.all HostTimeoutNumberLedger.exitRetries = true

/-- The instance retains a stopped root or an actual generation's body return. -/
inductive Kind
  | root
  | delay (n : Fin 4) (delay : Nat) (previous : Val)
  | body (n : Fin 4) (delay : Nat) (previous : Val)
  | formReturn (image : Image) (own : image.count = image.cleanups.length + 1)
      (n : Fin 4) (delay : Nat) (previous : Val)
  | published (image : Image) (own : image.count = image.cleanups.length + 1)
      (n : Fin 4) (delay : Nat) (previous : Val)

/-- A completed body either answers or supplies the declared returned failure before retry. -/
inductive BodyValue (plain : Bool) (state : Stores) (n : Fin 4) : Val → Prop
  | answered (image : Image) (body error : Val) (heap : ImageAt image state)
      (cursor : image.count = n.val + 1) : BodyValue plain state n (.list [.some body, error])
  | retry (image : Image) (error : Val) (heap : ImageAt image state)
      (complete : Complete image (n.val + 1) plain) (declared : Retryable error) :
      BodyValue plain state n (.list [.none, .some error])

/-- A catch receives an actual published form and the plain script's failure shape.
No arbitrary interrupted cause gains the permission to retry. -/
structure Published (plain : Bool) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (n : Fin 4) (cause : CauseV) : Prop where
  heap : HostTimeoutNumberFlow.CauseAt state (.formAfterCleanup image own) cause
  count : image.count = n.val + 1
  prior : plain = true → image.exits.all HostTimeoutNumberLedger.exitRetries = true
  shape : plain = true →
    (∃ tag message annotations, cause = {reasons := [Reason.fail (.tagged tag message) annotations]}) ∨
      HostTimeoutNumberFlow.NoTypedFailure cause

/-- Published input retains the concrete post-form heap even when its cause is discarded. -/
theorem Published.image {plain state image own n cause} (good : Published plain state image own n cause) :
    ∃ after, ImageAt after state := by
  obtain ⟨attemptExit, selected, heap, _⟩ := good.heap
  exact ⟨image.afterForm own attemptExit selected, heap⟩

/-- Every delivered root value still reads an actual numeric heap. -/
def ValueAt (plain : Bool) (state : Stores) : Kind → Val → Prop
  | .root, _ => ∃ image, ImageAt image state
  | .delay n _ _, value => ∃ image, ImageAt image state ∧ Complete image n.val plain ∧ value = .unit
  | .formReturn image own _ _ _, value => HostTimeoutNumberFlow.ValueAt state (.formAfterCleanup image own) value
  | .body n _ _, value | .published _ _ n _ _, value => BodyValue plain state n value

/-- A skipped loop failure retains the actual numeric heap without granting another retry. -/
def CauseAt (plain : Bool) (state : Stores) : Kind → CauseV → Prop
  | .published image own n _ _, cause | .formReturn image own n _ _, cause => Published plain state image own n cause
  | _, _ => ∃ image, ImageAt image state

/-- The permitted source body retains its generation, captured cells and completed predecessor form. -/
inductive CodeAt (plain : Bool) (state : Stores) : Kind → NCode → Prop
  | success (kind : Kind) (value : Val) (good : ValueAt plain state kind value) :
      CodeAt plain state kind (.success value)
  | failure (kind : Kind) (cause : CauseV) (good : CauseAt plain state kind cause) :
      CodeAt plain state kind (.failure cause)
  | iteration (point : Point) (root : RootAt point) (n : Fin 4) (delay : Nat) (previous : Val)
      (image : Image) (heap : ImageAt image state) (complete : Complete image n.val plain) :
      CodeAt plain state (.body n delay previous)
        (resolve HostTimeoutSource.program (point.childWith 0 (cursor n delay .none previous)))

  | delay (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
      (image : Image) (heap : ImageAt image state) (complete : Complete image n.val plain) :
      CodeAt plain state (.delay n delay previous)
        (.suspend (.body ((iterationPoint captured fuel n delay previous).child 0)))
  | catchEntry (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
      (image : Image) (heap : ImageAt image state) (complete : Complete image n.val plain) :
      CodeAt plain state (.body n delay previous)
        (resolve HostTimeoutSource.program (catchPoint captured fuel n delay previous))

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
  cause := CauseAt plain
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
  | caught (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
      (image : Image) (own : image.count = image.cleanups.length + 1) (body : NCode) :
      Edge plain _state (.published image own n delay previous) (.body n delay previous)
        (.onFailure body (.caughtError (catchPoint captured (fuel + 1) n delay previous)))
  | delay (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val) :
      Edge plain _state (.delay n delay previous) (.body n delay previous)
        (.onSuccess (.suspend (.body ((iterationPoint captured fuel n delay previous).child 0)))
          (.cont (iterationPoint captured fuel n delay previous)))

  | answer (captured : Point) (fuel : Nat) (image : Image)
      (own : image.count = image.cleanups.length + 1) (n : Fin 4) (delay : Nat) (previous : Val)
      (count : image.count = n.val + 1) (body : NCode) :
      Edge plain _state (.formReturn image own n delay previous) (.published image own n delay previous)
        (.onSuccess body (.cont (answerBinderPoint captured fuel n delay previous)))

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

/-- The actual catch test creates the body pair only after the matching form is published. -/
theorem published_retry (plain : Bool) (state : Stores) (captured : Point) (fuel : Nat)
    (image : Image) (own : image.count = image.cleanups.length + 1) (n : Fin 4)
    (delay : Nat) (previous : Val) (cause : CauseV) (error : Val)
    (good : Published plain state image own n cause)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest cause = some error) :
    BodyValue plain state n (.list [.none, .some error]) := by
  obtain ⟨attemptExit, heap⟩ := HostTimeoutNumberFormFamily.caught_is_published state image own cause good.heap _ _ error handled
  have finished := form_committed image own n good.count attemptExit (.failure cause)
  have prior : Complete (image.afterForm own attemptExit (.failure cause)) (n.val + 1) plain := by
    refine ⟨good.count, finished.2.2.1, finished.2.2.2, ?_⟩
    intro onlyPlain
    have declared : HostTimeoutNumberLedger.exitRetries (.failure cause) = true := by
      rcases good.shape onlyPlain with ⟨tag, message, annotations, singleton⟩ | interrupted
      · subst cause
        exact HostTimeoutNumberFormFamily.caught_singleton_declared n delay previous tag message annotations error handled
      · rw [HostTimeoutNumberFlow.no_typed_test _ _ cause interrupted] at handled
        cases handled
    change (image.exits ++ [Exit.failure cause]).all HostTimeoutNumberLedger.exitRetries = true
    rw [List.all_append, good.prior onlyPlain]
    simp only [List.all_cons, declared, List.all_nil, Bool.and_self]
  let point := catchPoint captured (fuel + 1) n delay previous
  have slots : EnvAt [] point.path point.env :=
    EnvAt.catch (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous
  have declared : Retryable error := caught_retryable point slots _ _ _ rfl (catch_node _ _ _ _ _) cause error handled
  exact .retry _ error heap prior declared

/-- This recursive source family has finite local obligations, without an inductive callback cycle. -/
theorem family (plain : Bool) (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily (model plain) (HostTimeoutFlow.interpreter view).toPrimInterp (Edge plain) where
  skip := by
    intro state input output frame edge next future value good missing
    cases edge with
    | loop point root n delay previous => cases missing
    | finish point source body => cases missing
    | caught captured fuel n delay previous image own body => exact good
    | delay captured fuel n delay previous => cases missing
    | answer captured fuel image own n delay previous count body => cases missing
    | mask kind flag => exact good
  skipCause := by
    intro state input output frame edge next future cause good missing
    cases edge with
    | loop point root n delay previous => exact good
    | finish point source body => exact good
    | caught captured fuel n delay previous image own body => cases missing
    | delay captured fuel n delay previous => exact good
    | answer captured fuel image own n delay previous count body => exact good
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
    | caught captured fuel n delay previous image own body => cases arm
    | delay captured fuel n delay previous =>
      obtain ⟨image, heap, complete, same⟩ := good
      rw [same] at arm
      change some ((HostTimeoutFlow.interpreter view).contA
        (.cont (iterationPoint captured fuel n delay previous)) .unit, []) = some (next, pushed) at arm
      cases arm
      rw [delay_callback]
      exact ⟨.body n delay previous, CodeAt.catchEntry _ _ _ _ _ image heap complete, .nil _⟩
    | answer captured fuel image own n delay previous count body =>
      obtain ⟨attemptExit, selected, heap, same⟩ := good
      rw [same] at heap
      change some ((HostTimeoutFlow.interpreter view).contA
        (.cont (answerBinderPoint captured fuel n delay previous)) value, []) = some (next, pushed) at arm
      cases arm
      rw [answer_callback]
      exact ⟨.published image own n delay previous,
        CodeAt.success _ _ (BodyValue.answered (image.afterForm own attemptExit (.success value))
          value .none heap count), .nil _⟩
    | mask kind flag => cases arm
  cause := by
    intro state input output frame edge nextState future cause provided next pushed good supplied absent arm
    cases edge with
    | loop point root n delay previous => cases arm
    | finish point source body => cases arm
    | caught captured fuel n delay previous image own body =>
      have equation := catch_callback view captured fuel n delay previous cause
      simp only [Prim.armE] at arm
      rw [equation] at arm
      cases handled : caughtErrorValue?
          (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
          HostTimeoutSource.retryTest cause with
      | none =>
        rw [handled] at arm
        cases arm
        exact ⟨.body n delay previous, CodeAt.failure _ cause good.image, .nil _⟩
      | some error =>
        rw [handled] at arm
        cases arm
        exact ⟨.body n delay previous,
          CodeAt.success _ _ (published_retry plain nextState captured fuel image own n delay previous cause error good handled), .nil _⟩
    | delay captured fuel n delay previous => cases arm
    | answer captured fuel image own n delay previous count body => cases arm
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
    | caught captured fuel n delay previous image own body => exact good.image
    | delay captured fuel n delay previous => cases armed
    | answer captured fuel image own n delay previous count body => cases armed
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

/-- The actual current failure supplies its carried exit to the admitted declared catch.
Consumer: the native step producer, before the root loop can advance. -/
theorem failure_selected_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (current : fiber.current = .failure cause) (output : Kind)
    (input : Kind) (good : CauseAt plain state input cause)
    (stack : Path (Edge plain state) input output fiber.stack)
    (body : NCode)
    (selected : (fiber.getCont .contE true (some cause)).answer =
      .frame (.onFailure body (.caughtError (catchPoint captured (fuel + 1) n delay previous))))
    (error : Val)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) = some error) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack := by
  have callback : (.onFailure body (.caughtError (catchPoint captured (fuel + 1) n delay previous)) : NCode).armE
      (HostTimeoutFlow.interpreter view).toPrimInterp
      ((fiber.getCont .contE true (some cause)).carriedCause.getD cause)
      ((some (Exit.failure cause)).map (fiber.getCont .contE true (some cause)).deliveredExit) =
      some (.success (.list [.none, .some error]), []) := by
    simp only [Prim.armE]
    rw [catch_callback, handled]
  obtain ⟨events, resumed, incoming, code, suffix⟩ :=
    AnswerFlow.External.resumeCause_provided_selected (model plain)
      (HostTimeoutFlow.interpreter view).toPrimInterp (Edge plain) (family plain view)
      (fun _ _ => Edge.mask _ true) state input output
      fiber cause (some (.failure cause)) _ (.success (.list [.none, .some error])) []
      good stack selected
      (by intro incoming delivered carried admitted exit member
          have image : (some (Exit.failure cause)).map (fiber.getCont .contE true (some cause)).deliveredExit =
              some (.failure delivered) := by
            simp only [Option.map_some, FramePop.deliveredExit, carried, Option.getD_some]
          rw [image] at member
          cases member
          exact admitted)
      (by intro delivered carried
          exact AnswerFlow.programOf_none (model plain) state _ _ (fun _ => rfl))
      callback
  refine ⟨{(fiber.getCont .contE true (some cause)).fiber with
    current := .success (.list [.none, .some error]),
    stack := [] ++ (fiber.getCont .contE true (some cause)).fiber.stack},
    events, ?_, incoming, code, suffix⟩
  rw [FrameFiber.step, current]
  exact resumed

theorem catch_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
    (image : Image) (own : image.count = image.cleanups.length + 1)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (current : fiber.current = .failure cause) (output : Kind)
    (good : Published plain state image own n cause)
    (stack : Path (Edge plain state) (.published image own n delay previous) output fiber.stack)
    (body : NCode)
    (selected : (fiber.getCont .contE true (some cause)).answer =
      .frame (.onFailure body (.caughtError (catchPoint captured (fuel + 1) n delay previous))))
    (error : Val)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) = some error) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack :=
  failure_selected_step plain state view captured fuel n delay previous fiber cause current output
    (.published image own n delay previous) good stack body selected error handled

/-- The real catch, loop, and outer binder form one inhabited ordered saved suffix. -/
theorem caught_stack (plain : Bool) (state : Stores) (captured : Point) (fuel : Nat)
    (n : Fin 4) (delay : Nat) (previous : Val) (image : Image)
    (own : image.count = image.cleanups.length + 1) (body : NCode)
    (loopPoint : Point) (root : RootAt loopPoint) (finishPoint : Point)
    (source : FinishAt finishPoint) (finishBody : NCode) :
    Path (Edge plain state) (.published image own n delay previous) .root
      [.onFailure body (.caughtError (catchPoint captured (fuel + 1) n delay previous)),
       .whileLoop (.loop loopPoint) (cursor n delay .none previous),
       .onSuccess finishBody (.cont finishPoint)] :=
  .cons (.caught captured fuel n delay previous image own body)
    (.cons (.loop loopPoint root n delay previous)
      (finish_stack plain state finishPoint source finishBody))

/-- An interruption-only carried cause cannot enter the declared source handler. -/
theorem interruption_refuses (n : Fin 4) (delay : Nat) (previous : Val) (cause : CauseV)
    (interrupted : HostTimeoutNumberFlow.NoTypedFailure cause) :
    caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest cause = none :=
  HostTimeoutNumberFlow.no_typed_test _ _ cause interrupted

/-- The actual loop child has the generation's captured cells and the stated remaining source fuel. -/
theorem root_child (point : Point) (root : RootAt point) (fuel : Nat)
    (budget : point.fuel = fuel + 3) (n : Fin 4) (delay : Nat) (previous : Val) :
    point.childWith 0 (cursor n delay .none previous) = iterationPoint point fuel n delay previous := by
  cases point with
  | mk path env actualFuel tape completed rootName params call =>
    dsimp only [RootAt] at root
    rcases root with ⟨source, cells⟩
    subst path
    subst env
    dsimp only at budget
    subst actualFuel
    rfl

/-- The actual source bind enters the retry delay above its real loop and finish suffix.
Consumer: the native producer's ordinary step branch at the generation's entry. -/
theorem iteration_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
    (image : Image) (heap : ImageAt image state) (complete : Complete image n.val plain)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (output : Kind)
    (current : fiber.current = resolve HostTimeoutSource.program (iterationPoint captured fuel n delay previous))
    (stack : Path (Edge plain state) (.body n delay previous) output fiber.stack) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack := by
  rw [iteration_bind] at current
  obtain ⟨after, events, ran, code, suffix⟩ := AnswerFlow.push_success_path (model plain)
    (HostTimeoutFlow.interpreter view).toPrimInterp state (.delay n delay previous) (.body n delay previous)
    output (Edge plain) fiber _ _ current (CodeAt.delay captured fuel n delay previous image heap complete)
    (Edge.delay captured fuel n delay previous) stack
  exact ⟨after, events, ran, .delay n delay previous, code, suffix⟩

/-- The delay's actual delivered success preserves Complete before entering the catch source child.
Consumer: the token-matched delay resume producer, before form or entrant allocation. -/
theorem delay_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
    (image : Image) (heap : ImageAt image state) (complete : Complete image n.val plain)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (output : Kind)
    (current : fiber.current = .success .unit)
    (stack : Path (Edge plain state) (.delay n delay previous) output fiber.stack)
    (selected : (fiber.getCont .contA false).answer =
      .frame (.onSuccess (.suspend (.body ((iterationPoint captured fuel n delay previous).child 0)))
        (.cont (iterationPoint captured fuel n delay previous)))) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack := by
  have callback : (.onSuccess (.suspend (.body ((iterationPoint captured fuel n delay previous).child 0)))
      (.cont (iterationPoint captured fuel n delay previous)) : NCode).armA
      (HostTimeoutFlow.interpreter view).toPrimInterp .unit (some (.success .unit)) =
      some (resolve HostTimeoutSource.program (catchPoint {captured with completed := view} fuel n delay previous), []) := by
    simp only [Prim.armA]
    rw [delay_callback]
  obtain ⟨events, resumed, incoming, code, suffix⟩ := AnswerFlow.External.resumeValue_selected (model plain)
    (HostTimeoutFlow.interpreter view).toPrimInterp (Edge plain) (family plain view)
    (fun _ _ => Edge.mask _ true) state (.delay n delay previous) output fiber .unit _ _ []
    (some (.success .unit)) ⟨image, heap, complete, rfl⟩ stack selected
    (by intro incoming good exit member; cases member; exact good)
    (AnswerFlow.programOf_none (model plain) state _ _ (fun _ => rfl)) callback
  refine ⟨{(fiber.getCont .contA false).fiber with
    current := resolve HostTimeoutSource.program (catchPoint {captured with completed := view} fuel n delay previous),
    stack := [] ++ (fiber.getCont .contA false).fiber.stack}, events, ?_, incoming, code, suffix⟩
  rw [FrameFiber.step, current]
  exact resumed

/-- Ready reaches the actual delay bind through the source loop, preserving its older suffix.
This attaches iteration_step to the real root cursor instead of assuming an unrelated source head. -/
theorem ready_iteration (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (point : Point) (root : RootAt point) (fuel : Nat) (sourceBudget : point.fuel = fuel + 3)
    (image : Image) (heap : ImageAt image state) (n : Fin 4) (delay : Nat) (previous : Val)
    (complete : Complete image n.val plain) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (current : fiber.current = .whileLoop (.loop point) (cursor n delay .none previous))
    (output : Kind) (stack : Path (Edge plain state) .root output fiber.stack) :
    ∃ entered after events,
      (fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp).1 = .running entered ∧
      entered.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack := by
  have slots : EnvAt [] point.path point.env := by
    rw [root.1, root.2]
    exact .loop _ _ _
  have hook := loop_waiting [] {point with completed := view} slots n delay previous root.1
  rw [if_pos (Or.inr n.isLt)] at hook
  obtain ⟨entered, first, _⟩ := ready_step plain state view point root image heap n delay previous complete fiber current output stack
  have concrete : (fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp).1 =
      .running {fiber with
        current := resolve HostTimeoutSource.program ({point with completed := view}.childWith 0 (cursor n delay .none previous)),
        stack := .whileLoop (.loop point) (cursor n delay .none previous) :: fiber.stack} := by
    have actualHook : (HostTimeoutFlow.interpreter view).loopEnter (EffName.loop point)
        (cursor n delay .none previous) = .continue (cursor n delay .none previous)
          (resolve HostTimeoutSource.program ({point with completed := view}.childWith 0 (cursor n delay .none previous))) := hook
    simp only [FrameFiber.step, current, actualHook]
  have same := FrameStep.running.inj (first.symm.trans concrete)
  subst entered
  obtain ⟨after, events, ran, result⟩ := iteration_step plain state view {point with completed := view}
    fuel n delay previous image heap complete
    {fiber with
      current := resolve HostTimeoutSource.program ({point with completed := view}.childWith 0 (cursor n delay .none previous)),
      stack := .whileLoop (.loop point) (cursor n delay .none previous) :: fiber.stack} output
    (by dsimp only; rw [root_child _ (root.completed view) fuel sourceBudget])
    (.cons (Edge.loop point root n delay previous) stack)
  exact ⟨_, after, events, concrete, ran, result⟩

/-- The actual delay, loop, and outer binder inhabit the ordered path consumed by delay_step. -/
theorem delay_stack (plain : Bool) (state : Stores) (captured : Point) (fuel : Nat)
    (n : Fin 4) (delay : Nat) (previous : Val) (loopPoint : Point) (root : RootAt loopPoint)
    (finishPoint : Point) (finish : FinishAt finishPoint) (outerBody : NCode) :
    Path (Edge plain state) (.delay n delay previous) .root
      [.onSuccess (.suspend (.body ((iterationPoint captured fuel n delay previous).child 0)))
        (.cont (iterationPoint captured fuel n delay previous)),
       .whileLoop (.loop loopPoint) (cursor n delay .none previous),
       .onSuccess outerBody (.cont finishPoint)] :=
  .cons (Edge.delay captured fuel n delay previous)
    (.cons (Edge.loop loopPoint root n delay previous) (finish_stack plain state finishPoint finish outerBody))

/-- A delayed callback cannot borrow a newer generation's heap as its Ready predecessor. -/
theorem delay_wrong_generation_refuses (plain : Bool) (state : Stores) (n : Fin 4)
    (delay : Nat) (previous : Val) (image : Image) (heap : ImageAt image state)
    (later : n.val < image.count) (good : ValueAt plain state (.delay n delay previous) .unit) : False := by
  obtain ⟨old, priorHeap, complete, _⟩ := good
  have cells := congrArg (fun refs : RefHeap => refs[0]?) (heap.symm.trans priorHeap)
  change some (Val.nat image.count) = some (Val.nat old.count) at cells
  have count := congrArg (Env.natOfVal 0) (Option.some.inj cells)
  change image.count = old.count at count
  have cursor := complete.cursor
  omega

/-- The actual published form value supplies the saved answer binder's input class.
Consumer: form_success_step after the existing native restore producer. -/
theorem restored_value (plain : Bool) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (n : Fin 4) (delay : Nat) (previous value : Val)
    (good : HostTimeoutNumberFlow.ValueAt state (.formAfterCleanup image own) value) :
    ValueAt plain state (.formReturn image own n delay previous) value := good

/-- The actual failed restore retains the same published-form permission through the answer binder.
The plain-script cause shape and predecessor declaration remain explicit local producer premises. -/
theorem restored_cause (plain : Bool) (state : Stores) (image : Image)
    (own : image.count = image.cleanups.length + 1) (n : Fin 4) (delay : Nat) (previous : Val) (cause : CauseV)
    (good : HostTimeoutNumberFlow.CauseAt state (.formAfterCleanup image own) cause)
    (count : image.count = n.val + 1)
    (prior : plain = true → image.exits.all HostTimeoutNumberLedger.exitRetries = true)
    (shape : plain = true →
      (∃ tag message annotations, cause = {reasons := [Reason.fail (.tagged tag message) annotations]}) ∨
        HostTimeoutNumberFlow.NoTypedFailure cause) :
    CauseAt plain state (.formReturn image own n delay previous) cause :=
  ⟨good, count, prior, shape⟩

/-- The actual restored success becomes the loop answer through the selected source binder.
Consumer: the reached owner/phase producer, after form publication and restore. -/
theorem form_success_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
    (image : Image) (own : image.count = image.cleanups.length + 1)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (output : Kind) (value : Val)
    (current : fiber.current = .success value)
    (good : HostTimeoutNumberFlow.ValueAt state (.formAfterCleanup image own) value)
    (stack : Path (Edge plain state) (.formReturn image own n delay previous) output fiber.stack)
    (body : NCode)
    (selected : (fiber.getCont .contA false).answer =
      .frame (.onSuccess body (.cont (answerBinderPoint captured fuel n delay previous)))) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack := by
  have callback : (.onSuccess body (.cont (answerBinderPoint captured fuel n delay previous)) : NCode).armA
      (HostTimeoutFlow.interpreter view).toPrimInterp value (some (.success value)) =
      some (.success (HostTimeoutSource.answered value), []) := by
    simp only [Prim.armA]
    rw [answer_callback]
  obtain ⟨events, resumed, incoming, code, suffix⟩ := AnswerFlow.External.resumeValue_selected (model plain)
    (HostTimeoutFlow.interpreter view).toPrimInterp (Edge plain) (family plain view)
    (fun _ _ => Edge.mask _ true) state (.formReturn image own n delay previous) output fiber value _ _ []
    (some (.success value)) (restored_value plain state image own n delay previous value good) stack selected
    (by intro incoming good exit member; cases member; exact good)
    (AnswerFlow.programOf_none (model plain) state _ _ (fun _ => rfl)) callback
  refine ⟨{(fiber.getCont .contA false).fiber with
    current := .success (HostTimeoutSource.answered value),
    stack := [] ++ (fiber.getCont .contA false).fiber.stack}, events, ?_, incoming, code, suffix⟩
  rw [FrameFiber.step, current]
  exact resumed

/-- The actual failed restore passes the answer binder and consumes the selected declared catch.
The shared pop retains the carried cause, including any real sanitize operation. -/
theorem form_failure_step (plain : Bool) (state : Stores) (view : HostTimeoutFlow.View)
    (captured : Point) (fuel : Nat) (n : Fin 4) (delay : Nat) (previous : Val)
    (image : Image) (own : image.count = image.cleanups.length + 1)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV)
    (current : fiber.current = .failure cause) (output : Kind)
    (good : HostTimeoutNumberFlow.CauseAt state (.formAfterCleanup image own) cause)
    (count : image.count = n.val + 1)
    (prior : plain = true → image.exits.all HostTimeoutNumberLedger.exitRetries = true)
    (shape : plain = true →
      (∃ tag message annotations, cause = {reasons := [Reason.fail (.tagged tag message) annotations]}) ∨
        HostTimeoutNumberFlow.NoTypedFailure cause)
    (stack : Path (Edge plain state) (.formReturn image own n delay previous) output fiber.stack)
    (body : NCode)
    (selected : (fiber.getCont .contE true (some cause)).answer =
      .frame (.onFailure body (.caughtError (catchPoint captured (fuel + 4) n delay previous))))
    (error : Val)
    (handled : caughtErrorValue?
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay previous)
      HostTimeoutSource.retryTest ((fiber.getCont .contE true (some cause)).carriedCause.getD cause) = some error) :
    ∃ after events, fiber.step (HostTimeoutFlow.interpreter view).toPrimInterp = (.running after, events) ∧
      AnswerFlow.FamilyResult (model plain) (Edge plain) state output after.current after.stack :=
  failure_selected_step plain state view captured (fuel + 3) n delay previous fiber cause current output
    (.formReturn image own n delay previous)
    (restored_cause plain state image own n delay previous cause good count prior shape)
    stack body selected error handled

/-- The actual answer, catch, loop and finish frames form one inhabited post-form return path. -/
theorem form_return_stack (plain : Bool) (state : Stores) (captured : Point) (fuel : Nat)
    (n : Fin 4) (delay : Nat) (previous : Val) (image : Image)
    (own : image.count = image.cleanups.length + 1) (count : image.count = n.val + 1)
    (catchBody : NCode) (loopPoint : Point) (root : RootAt loopPoint)
    (finishPoint : Point) (source : FinishAt finishPoint) (finishBody : NCode) :
    Path (Edge plain state) (.formReturn image own n delay previous) .root
      [.onSuccess (resolve HostTimeoutSource.program
         (HostTimeoutNumberFinalizers.formPoint captured fuel delay n previous))
         (.cont (answerBinderPoint captured fuel n delay previous)),
       .onFailure catchBody (.caughtError (catchPoint captured (fuel + 4) n delay previous)),
       .whileLoop (.loop loopPoint) (cursor n delay .none previous),
       .onSuccess finishBody (.cont finishPoint)] :=
  .cons (Edge.answer captured fuel image own n delay previous count _)
    (caught_stack plain state captured (fuel + 3) n delay previous image own catchBody
      loopPoint root finishPoint source finishBody)

end Test.Dogfood.Proofs.HostTimeoutRootLoop
