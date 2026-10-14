import Effect4.Run
import Effect4.Api.Author

/-!
# Tools.View.Decision — a run's control decision in words

The words the run's frames (`Tools.View.Run`) write for a decision, in a module of their own so
that any picture of a run can share them without importing the frames.
-/

namespace Tools.View.Run

open Effect4

/-- A control decision in words. -/
def decisionText : Api.Decision → String
  | .fire owner => s!"fire the dispatcher of fiber {owner.value}"
  | .flush => "flush"
  | .evaluate f => s!"evaluate fiber {f.value}"
  | .yieldVerdict f v => s!"fiber {f.value} yields: {v}"
  | .answerAsync f _ _ => s!"answer fiber {f.value}"
  | .interruptFrom .. => "interrupt"
  | .installMiddleware => "install middleware"
  | .advance millis => s!"advance the clock {millis.toNat} ms"

end Tools.View.Run
