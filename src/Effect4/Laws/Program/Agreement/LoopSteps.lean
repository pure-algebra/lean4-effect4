import Effect4.Laws.Program.Agreement

/-!
# The loop's steps, as local steps

What the frame machine does with `Prim.whileLoop`, stated over the local step of
`Laws/Program/Agreement.lean`: entering a loop (`step_whileLoop_enter`), a value meeting the
loop's frame (`step_success_enter`, through `armA_whileLoop`), and a cause passing it
(`step_failure_pass_whileLoop`: the frame declares the value arm only). `enter` is where a
loop's next decision leaves the fiber: the body under the frame, or the finishing code with the
frame gone.

Both layers of the loop agreement read these: `Agreement/Loop.lean` (the local run against the
budgeted meaning) and `Agreement/Machine.lean` (the plain invariant of the real machine's
command loop).
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program

variable (root : NativeEff)

/-- The point a loop's hooks read: the loop's own point, with the local run's empty view of
completed fibers. -/
abbrev loopPoint (p : Point) : Point := { p with completed := [] }

/-- Entering a loop whose test holds: the body runs under the loop's frame. -/
theorem step_whileLoop_continue (p : Point) (c next : Val) (body : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (h : loopNextAt root (loopPoint p) c = .continue next body) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop p) c) K i) s =
      .running (fiberOf body (Prim.whileLoop (EffName.loop p) next :: K) i) s := by
  have hstep := FrameFiber.step_whileLoop_true (primOf root) (fiberOf (Prim.whileLoop (EffName.loop p) c) K i)
    (EffName.loop p) c next body h
  show ofFrameStep ((fiberOf (Prim.whileLoop (EffName.loop p) c) K i).step (primOf root)).1 s = _
  rw [show fiberOf (Prim.whileLoop (EffName.loop p) c) K i =
    FrameFiber.mk (Prim.whileLoop (EffName.loop p) c) K i none false from rfl] at hstep ⊢
  rw [hstep]
  rfl

/-- Entering a loop that finishes at once: the finishing code, no frame. -/
theorem step_whileLoop_finish (p : Point) (c : Val) (code : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (h : loopNextAt root (loopPoint p) c = .finish code) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop p) c) K i) s =
      .running (fiberOf code K i) s := by
  have hstep := FrameFiber.step_whileLoop_false (primOf root) (fiberOf (Prim.whileLoop (EffName.loop p) c) K i)
    (EffName.loop p) c code h
  show ofFrameStep ((fiberOf (Prim.whileLoop (EffName.loop p) c) K i).step (primOf root)).1 s = _
  rw [show fiberOf (Prim.whileLoop (EffName.loop p) c) K i =
    FrameFiber.mk (Prim.whileLoop (EffName.loop p) c) K i none false from rfl] at hstep ⊢
  rw [hstep]
  rfl

/-- The loop frame's value arm, read at the local interp. -/
theorem armA_whileLoop (p : Point) (c v : Val) (provided : Option ExitV) :
    (Prim.whileLoop (EffName.loop p) c : NCode).armA (primOf root) v provided =
      (match loopResumeAt root (loopPoint p) c v with
       | .continue next body => some (body, [Prim.whileLoop (EffName.loop p) next])
       | .finish code => some (code, [])) := by
  simp only [Prim.armA]
  have hres : PrimInterp.loopResume (primOf root) (EffName.loop p) c v =
      loopResumeAt root (loopPoint p) c v := rfl
  rw [hres]
  cases loopResumeAt root (loopPoint p) c v <;> rfl

/-- A value meets the loop's frame: the step, then the test, then the body under the frame at
the stepped cursor or the finishing code. -/
theorem step_success_whileLoop (p : Point) (c v : Val) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i) s =
      (match loopResumeAt root (loopPoint p) c v with
       | .continue next body =>
         .running (fiberOf body (Prim.whileLoop (EffName.loop p) next :: K) i) s
       | .finish code => .running (fiberOf code K i) s) := by
  let pop : NPop :=
    ⟨ContAnswer.frame (Prim.whileLoop (EffName.loop p) c), [], [], fiberOf (Prim.success v) K i, none⟩
  have hanswer : (popOf (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i)
      (Exit.success v)).answer = pop.answer := by cases i <;> rfl
  have hfiber : (popOf (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i)
      (Exit.success v)).fiber = pop.fiber := by cases i <;> rfl
  have h0 : localStep root
        (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i) s =
      exitFrom root (Exit.success v)
        (popOf (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop p) c :: K) i)
          (Exit.success v)) s := rfl
  rw [h0, exitFrom_ext root (Exit.success v) s hanswer hfiber]
  have h1 : exitFrom root (Exit.success v) pop s =
      ofFrameStep (resumeOf root (Exit.success v) pop) s := rfl
  rw [h1]
  simp only [resumeOf, pop, armA_whileLoop]
  cases loopResumeAt root (loopPoint p) c v <;> rfl

/-- A cause passes the loop's frame, which declares the value arm only. -/
theorem step_failure_pass_whileLoop (p : Point) (c : Val) (cause : CauseV) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.failure cause) (Prim.whileLoop (EffName.loop p) c :: K) i) s =
      localStep root (fiberOf (Prim.failure cause) K i) s := by
  have hpop := popFrom_pass Effect4.Arm.contE true (Prim.whileLoop (EffName.loop p) c) K
    (Prim.failure cause) i rfl rfl
  exact exitFrom_ext root _ s hpop.1 hpop.2


/-- Where a loop's next decision leaves the fiber: the body under the frame, or the finishing
code with the frame gone. -/
def enter (q : Point) (K : List NCode) (i : Bool) : LoopNext Val NCode → NFiber
  | .continue next body => fiberOf body (Prim.whileLoop (EffName.loop q) next :: K) i
  | .finish code => fiberOf code K i

theorem step_whileLoop_enter (q : Point) (hq : loopPoint q = q) (c : Val) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop q) c) K i) s =
      .running (enter q K i (loopNextAt root q c)) s := by
  cases h : loopNextAt root q c with
  | «continue» next body =>
    exact step_whileLoop_continue root q c next body K i s (by rw [hq]; exact h)
  | finish code => exact step_whileLoop_finish root q c code K i s (by rw [hq]; exact h)

theorem step_success_enter (q : Point) (hq : loopPoint q = q) (c v : Val) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop q) c :: K) i) s =
      .running (enter q K i (loopResumeAt root q c v)) s := by
  rw [step_success_whileLoop, hq]
  cases loopResumeAt root q c v <;> rfl

/-- Entering a loop, at any loop point: the hooks read the point with the empty view. -/
theorem step_whileLoop_enter_at (q : Point) (c : Val) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.whileLoop (EffName.loop q) c) K i) s =
      .running (enter q K i (loopNextAt root (loopPoint q) c)) s := by
  cases h : loopNextAt root (loopPoint q) c with
  | «continue» next body => exact step_whileLoop_continue root q c next body K i s h
  | finish code => exact step_whileLoop_finish root q c code K i s h

/-- A value meeting the loop's frame, at any loop point. -/
theorem step_success_enter_at (q : Point) (c v : Val) (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.success v) (Prim.whileLoop (EffName.loop q) c :: K) i) s =
      .running (enter q K i (loopResumeAt root (loopPoint q) c v)) s := by
  rw [step_success_whileLoop]
  cases loopResumeAt root (loopPoint q) c v <;> rfl

end Effect4.Program.Agreement
