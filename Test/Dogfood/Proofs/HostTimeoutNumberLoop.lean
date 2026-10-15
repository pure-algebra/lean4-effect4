import Test.Dogfood.Proofs.HostTimeoutNumberResult

/-!
Concept: translation-simulation R10, with scope-lifetime-finalization R11.
Question: the root consumes its published result before entering another counted attempt.
Consumer: the between-attempt phase of Timeout.cleanup_keeps and Timeout.retries_declared.
Reach: the actual loop callback and the exact cleanup and form images.
Limit: the machine assertion must establish the result and its singleton failure shape.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
namespace Test.Dogfood.Proofs.HostTimeoutNumberLoop
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutNumberFlow HostTimeoutNumberState

/-- A published form closes the cleanup column before the root can enter another attempt. -/
theorem cleanup_complete (image : Image) (own : image.count = image.cleanups.length + 1)
    (attemptExit selected : ExitV) :
    (image.afterForm own attemptExit selected).cleanups.length =
      (image.afterForm own attemptExit selected).count :=
  image.cleanup_complete own attemptExit

/-- A published form closes the completed column at the same committed attempt count. -/
theorem form_complete (image : Image) (own : image.count = image.cleanups.length + 1)
    (attemptExit selected : ExitV) :
    (image.afterForm own attemptExit selected).exits.length =
      (image.afterForm own attemptExit selected).count := by
  change (image.exits ++ [selected]).length = image.count
  rw [List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
  exact image.form_gap own

/-- The actual retry cursor copies the encoded selected result and advances its own attempt number. -/
theorem result_step (point : Point) (n delay : Nat) (previous result : Val)
    (slots : HostTimeoutSlots.EnvAt [] point.path point.env)
    (path : point.path = [1,1,1,0]) :
    loopResumeAt HostTimeoutSource.program point (cursor n delay .none previous) result =
      loopNextAt HostTimeoutSource.program point
        (.list [.nat (n + 1), .list [.nat (if 0 < n then delay * 2 else delay), result]]) :=
  HostTimeoutSlots.loop_step_value [] point slots n delay (.list [.none, previous]) result path

/-- A successful selected result stops the actual retry loop before another count operation. -/
theorem success_stops (point : Point) (n delay : Nat) (previous body : Val)
    (slots : HostTimeoutSlots.EnvAt [] point.path point.env)
    (path : point.path = [1,1,1,0]) :
    loopResumeAt HostTimeoutSource.program point (cursor n delay .none previous)
        (.list [.some body, .none]) =
      .finish (Prim.success (.list [.some body, .none])) := by
  rw [result_step point n delay previous _ slots path]
  exact HostTimeoutSlots.loop_answer_stops [] point slots (n + 1)
    (if 0 < n then delay * 2 else delay) body .none path

/-- A tested failure continues only while the next cursor remains below four attempts. -/
theorem failure_next (point : Point) (n delay : Nat) (previous error : Val)
    (slots : HostTimeoutSlots.EnvAt [] point.path point.env)
    (path : point.path = [1,1,1,0]) :
    loopResumeAt HostTimeoutSource.program point (cursor n delay .none previous)
        (.list [.none, .some error]) =
      if n + 1 < 4 then
        .continue (cursor (n + 1) (if 0 < n then delay * 2 else delay) .none (.some error))
          (resolve HostTimeoutSource.program (point.childWith 0
            (cursor (n + 1) (if 0 < n then delay * 2 else delay) .none (.some error))))
      else .finish (Prim.success (.list [.none, .some error])) := by
  rw [result_step point n delay previous _ slots path]
  change loopNextAt HostTimeoutSource.program point
    (cursor (n + 1) (if 0 < n then delay * 2 else delay) .none (.some error)) = _
  rw [HostTimeoutSlots.loop_waiting [] point slots (n + 1)
    (if 0 < n then delay * 2 else delay) (.some error) path]
  simp only [Nat.add_one_ne_zero, false_or]

/-- The next counted image consumes both completed columns from the actual published form. -/
def nextImage (image : Image) (own : image.count = image.cleanups.length + 1)
    (attemptExit selected : ExitV) (n : Fin 4) (cursor : image.count = n.val) : Image :=
  (image.afterForm own attemptExit selected).enter n
    (cleanup_complete image own attemptExit selected)
    (form_complete image own attemptExit selected) (Nat.le_of_eq cursor)

end Test.Dogfood.Proofs.HostTimeoutNumberLoop
