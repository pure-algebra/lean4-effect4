import Effect4.Laws.Program.Typed.HostWalk

/-!
# Witness — the loop and generator hook contract at `ed83ea23`

Four kernel-checked controls on the frame contract for saved `loop` and `iter` slots
(`FrameAccepts.loop`/`.iter`, whose protocols are `LoopProtocol`/`IteratorProtocol`,
`Typed/Residual.lean:440-475`), and on the precondition of the loop operation (`fiberPre`'s `loop`
arm, `:224`). Codex's hook-view-support packet (2026-10-02) proposed the first and the third from
source reading; the second is the positive control it asked for; the fourth is G2's.

1. `Endless`: a checker-admitted loop whose test is always true has no loop protocol at any input
   type admitting `unit` (`no_protocol`, by the protocol's own recursion). Its entry pushes exactly
   such a frame over the body's typed code, so the fiber its entry leaves has no `CodeOk` at any
   world (`no_code_after_entry`).
2. `Finishing`: the same loop with a false test has a protocol.
3. `Cursor`: a checked Boolean-cursor loop entered with the cursor `unit` meets `fiberPre`'s loop arm
   (which reads only `PointTyped`) and its entry installs `badShapeExit`, typed at no type.
4. `View`: a loop whose point's own view holds a completed fiber has a loop protocol (it types the
   reference interpreter's step), but under the machine's interpreter with an empty view the walk
   installs an `await` of an undeclared fiber: the protocol does not give the machine's hook laws
   (`HookLawsAt`), and the ordinary walk's conclusion fails there. (The generator analogue was run
   by `#eval` only: `walkR` is defined by well-founded recursion and does not reduce by `rfl`.)
-/

set_option autoImplicit false

namespace Witness.LoopProtocols
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts

abbrev W := Effect4.Program.Typed.World

theorem unit_exit (w : W) : ExitOk w (EffTy.pure .unit) (.success Val.unit) :=
  ⟨by rw [fitsExit_success_iff]; exact trivial, trivial⟩

theorem bad_untyped {root : ProgramSource} (w : W) (ty : EffTy) :
    ¬ TypedProg root w ty (.pure badShapeExit) := by
  intro h
  exact ((TypedProg.pure_inv h).2 _ (List.mem_singleton_self _)).1 rfl

/-! ## 1. A safe endless loop -/

namespace Endless

def loop : NativeEff :=
  .iterate (some .unit) (.lit .unit) (.lit (.bool true)) (.lit .unit) (.lit .unit)
    (.succeed (.lit .unit))

def p : Point := rootPoint 2

/-- The checker admits it at `pure unit` from the root. -/
theorem admitted (w : W) : PointTyped (loop : ProgramSource) w p (EffTy.pure .unit) :=
  ⟨loop, [], rfl, by decide +kernel, ⟨rfl, fun _ _ _ h => nomatch h⟩, fun _ h => nomatch h⟩

theorem enter_eq : (interpR loop).loopEnter (.loop p) Val.unit =
    .continue Val.unit (.pure (.success Val.unit)) := rfl

/-- Every resume answers the same continue, the loop name unchanged. -/
theorem resume_eq (v : Val) : (interpR loop).loopResume (.loop p) Val.unit v =
    .continue Val.unit (.pure (.success Val.unit)) := rfl

/-- **No loop protocol**: a protocol must answer `unit`, the answer is the same continue, whose body
types `unit` at the tail's input type, and the tail is a smaller protocol of the same frame. -/
theorem no_protocol {w : W} {tin tout : EffTy} (fit : Fits w Val.unit tin.answer) :
    ¬ LoopProtocol (loop : ProgramSource) w tin tout (.loop p) Val.unit := fun h =>
  LoopProtocol.rec
    (motive_1 := fun w tin _ name cursor _ =>
      name = .loop p → cursor = Val.unit → Fits w Val.unit tin.answer → False)
    (motive_2 := fun _ _ name next _ =>
      name = .loop p → next = .continue Val.unit (.pure (.success Val.unit)) → False)
    (fun {w _ _ _ _} _ _ _ ih hn hc hfit => by
      subst hn
      subst hc
      exact ih w (leHost_refl w) Val.unit hfit rfl (resume_eq Val.unit))
    (fun {w _ _} _ _ _ typed _ ih hn hans => by
      cases hans
      exact ih hn rfl ((fitsExit_success_iff _ _ _).mp (TypedProg.pure_inv typed).1))
    (fun _ _ _ hans => nomatch hans)
    h rfl rfl fit

/-- The loop operation's entry pushes the loop frame over the body and installs the body. -/
theorem entry_eq (m : RState) (f : RFiber) (yielding : Bool) (next : ExitV → RProgram) :
    (evaluateFiberR (interpR loop) m f yielding (.loop p Val.unit) next).fiber.frame =
      { f.frame with
        current := .pure (.success Val.unit)
        stack := .loop (.loop p) Val.unit :: .answer next :: f.frame.stack } := rfl

/-- **The frame the entry leaves has no `CodeOk` at any world**: its body is typed only at types
admitting `unit`, and the loop slot's protocol is refused there. -/
theorem no_code_after_entry (w : W) (m : RState) (host : FiberId) (final : EffTy) (x : RSaved)
    (current : x.current = .pure (.success Val.unit))
    (stack : ∃ s, x.stack = .loop (.loop p) Val.unit :: s) :
    ¬ CodeOk (loop : ProgramSource) w m host final x := by
  rintro ⟨tin, typed, path, _⟩
  obtain ⟨s, hs⟩ := stack
  rw [current] at typed
  rw [hs] at path
  cases path with
  | cons edge _ =>
    rcases edge with frame | arrow
    · cases frame with
      | loop _ _ protocol =>
        exact no_protocol ((fitsExit_success_iff _ _ _).mp (TypedProg.pure_inv typed).1)
          (protocol w (leHost_refl w))
    · cases arrow

end Endless

/-! ## 2. The finishing loop (positive control) -/

namespace Finishing

def loop : NativeEff :=
  .iterate (some .unit) (.lit .unit) (.lit (.bool false)) (.lit .unit) (.lit .unit)
    (.succeed (.lit .unit))

def p : Point := rootPoint 2

theorem resume_eq (v : Val) : (interpR loop).loopResume (.loop p) Val.unit v =
    .finish (.pure (.success Val.unit)) := rfl

theorem protocol (w : W) :
    LoopProtocol (loop : ProgramSource) w (EffTy.pure .unit) (EffTy.pure .unit) (.loop p) Val.unit :=
  .step rfl (fun h => h) (fun w' _ _ _ => .finish _ (TypedProg.pure (unit_exit w')))

end Finishing

/-! ## 3. The loop operation's cursor -/

namespace Cursor

def loop : NativeEff :=
  .iterate (some .bool) (.lit (.bool false)) (.var 0) (.lit (.bool false)) (.lit .unit)
    (.succeed (.lit .unit))

def p : Point := rootPoint 2

theorem admitted (w : W) : PointTyped (loop : ProgramSource) w p (EffTy.pure .unit) :=
  ⟨loop, [], rfl, by decide +kernel, ⟨rfl, fun _ _ _ h => nomatch h⟩, fun _ h => nomatch h⟩

/-- `fiberPre`'s loop arm admits the operation with the cursor `unit`: it reads only the point. -/
theorem pre_admits (w : W) :
    fiberPre (loop : ProgramSource) w (.loop p Val.unit) (EffTy.pure .unit) := admitted w

/-- Its entry installs `badShapeExit`: the test does not evaluate to a Boolean at `unit`. -/
theorem entry_current (m : RState) (f : RFiber) (yielding : Bool) (next : ExitV → RProgram) :
    (evaluateFiberR (interpR loop) m f yielding (.loop p Val.unit) next).fiber.frame.current =
      .pure badShapeExit := rfl

end Cursor

/-! ## 4. A loop body's completed view (G2) -/

namespace View

def x : FiberId := ⟨5⟩

/-- The body awaits the fiber the point's environment names (`var 0`); the cursor is `var 1`. -/
def loop : NativeEff :=
  .iterate (some .bool) (.lit (.bool true)) (.var 1) (.lit (.bool true)) (.lit .unit)
    (.awaitFiber (.var 0) .joinEffect)

/-- The point's own view holds the fiber's failure. -/
def p : Point :=
  { rootPoint 3 with env := [Val.fiber x], completed := [(x, .failure Cause.empty)] }

def awaitCode : RProgram := .vis (.inr (.await x .joinEffect)) Effects.Program.pure

/-- Under the reference interpreter the body answers the recorded failure inline. -/
theorem own_view (v : Val) : (interpR loop).loopResume (.loop p) (.bool true) v =
    .continue (.bool true) (.pure (.failure Cause.empty)) := rfl

/-- Under the machine's interpreter at an empty view the body is an `await` operation. -/
theorem empty_view (v : Val) : (interpRAt loop []).loopResume (.loop p) (.bool true) v =
    .continue (.bool true) awaitCode := rfl

/-- The frame's protocol holds at every world: the inline failure is typed at `never`'s answer,
and the tail at that type has nothing to resume with. -/
theorem protocol (w : W) :
    LoopProtocol (loop : ProgramSource) w (EffTy.pure .unit) (EffTy.pure .unit) (.loop p)
      (.bool true) :=
  .step rfl (fun h => h) (fun w' _ v _ => by
    rw [own_view]
    exact .continue _ _ (EffTy.pure .never)
      (TypedProg.pure ⟨(fitsExit_failure_iff _ _ _).mpr ⟨(fun _ h => nomatch h), (fun _ h => nomatch h)⟩,
        fun _ h => nomatch h⟩)
      (.step rfl (fun h => h) (fun _ _ _ hv => nomatch hv)))

/-- An `await` of an undeclared fiber is typed at no type. -/
theorem await_untyped (w : W) (undeclared : w.Γ x = none) (ty : EffTy) :
    ¬ TypedProg (loop : ProgramSource) w ty awaitCode := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change (w.Γ x).isSome = true at pre
  rw [undeclared] at pre
  cases pre

/-- **The protocol does not give the machine's hook laws**: at a world where the fiber is
undeclared, `HookLawsAt` for the machine's interpreter at the empty view fails on this frame. -/
theorem no_hookLaws (w : W) (undeclared : w.Γ x = none) :
    ¬ HookLawsAt (loop : ProgramSource) (interpRAt loop []) (frameProtocols loop) w := by
  intro laws
  have step := (laws.loop _ _ (.loop p) (.bool true) (protocol w)).2 Val.unit trivial
  rw [empty_view] at step
  obtain ⟨tin', typed, _⟩ := step
  exact await_untyped w undeclared tin' typed

/-- **The ordinary walk's conclusion fails for the machine's interpreter**: the stack is accepted,
the exit typed, and the walk installs the untyped `await`. -/
theorem walk_untyped (w : W) (undeclared : w.Γ x = none) (frame : RSaved) :
    StackAccepts (TypedProg (loop : ProgramSource)) ExitOk (frameProtocols loop) w
        (EffTy.pure .unit) (EffTy.pure .unit) [.loop (.loop p) (.bool true)] ∧
      ExitOk w (EffTy.pure .unit) (.success Val.unit) ∧
      ¬ WalkTyped (loop : ProgramSource) (frameProtocols loop) w (EffTy.pure .unit)
        (popR (interpRAt loop []) (.success Val.unit) [.loop (.loop p) (.bool true)] frame) := by
  refine ⟨.cons (.loop (.loop p) (.bool true) fun w' _ => protocol w') (.nil _), unit_exit w, ?_⟩
  rintro (⟨tin, typed, _, _⟩ | ⟨_, _, _, _, callback, _⟩)
  · exact await_untyped w undeclared tin typed
  · cases callback

end View

end Witness.LoopProtocols

#print axioms Witness.LoopProtocols.Endless.no_protocol
#print axioms Witness.LoopProtocols.Endless.no_code_after_entry
#print axioms Witness.LoopProtocols.Finishing.protocol
#print axioms Witness.LoopProtocols.Cursor.entry_current
#print axioms Witness.LoopProtocols.View.no_hookLaws
#print axioms Witness.LoopProtocols.View.walk_untyped
