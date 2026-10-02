import Effect4.Laws.Program.Typed.HostWalk

/-!
# Test.Program.LoopProtocols — the hook protocols as greatest invariants (decisions row 190)

Placement: semantics Concept 2/4, the frame contract for saved `loop`/`iter` slots
(`IteratorProtocol`, `LoopProtocol`, `Typed/Residual.lean`) and the machine's hook laws
(`hookLawsAt_interpRAt`, `M5Hooks`), consumed by the walk (`popR_typed`, `popR_hostTyped`) on the way
to `M6Ledger.step_loop`/`.step_deliver`. The flips of `E4-TYPED-CE-036` and `-038`
(`docs/research/2026-10-02-claude-lead/witnesses/LoopProtocols.lean`):

* `Endless`: the checker-admitted always-true loop now has a protocol, by coinduction on the one
  state it revisits, and the frame its entry leaves is typed.
* `Finishing`: a loop that finishes keeps its protocol (folded once).
* `View`: a frame whose body awaits a fiber the point's own view holds is now refused at a world not
  declaring that fiber, since the step must answer at the empty view too.

Reach: concrete frames at one world; no whole step, no progress or termination claim.
-/

set_option autoImplicit false

namespace Test.Program.LoopProtocols
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed Effect4.Laws.Effects Contracts

abbrev W := Effect4.Program.Typed.World

theorem unit_exit (w : W) : ExitOk w (EffTy.pure .unit) (.success Val.unit) :=
  ⟨by rw [fitsExit_success_iff]; exact trivial, trivial⟩

namespace Endless

def loop : NativeEff :=
  .iterate (some .unit) (.lit .unit) (.lit (.bool true)) (.lit .unit) (.lit .unit)
    (.succeed (.lit .unit))

def p : Point := rootPoint 2

/-- At every completed view the loop resumes with the same continue. -/
theorem resume_eq (completed : List (FiberId × ExitV)) (v : Val) :
    (interpRAt loop completed).loopResume (.loop p) Val.unit v =
      .continue Val.unit (.pure (.success Val.unit)) := rfl

/-- The one state the loop revisits, at any world. -/
def Revisit : LoopState → Prop
  | (_, tin, tout, name, cursor) =>
    tin = EffTy.pure .unit ∧ tout = EffTy.pure .unit ∧ name = .loop p ∧ cursor = Val.unit

/-- **The endless loop's protocol** (the flip of `E4-TYPED-CE-036`): `Revisit` is closed under the
loop step, so it lies in the greatest invariant. -/
theorem protocol (w : W) :
    LoopProtocol (loop : ProgramSource) w (EffTy.pure .unit) (EffTy.pure .unit) (.loop p) Val.unit :=
  Greatest.coind (I := Revisit) (fun s member => by
    obtain ⟨w₀, tin, tout, name, cursor⟩ := s
    obtain ⟨rfl, rfl, rfl, rfl⟩ := member
    refine ⟨rfl, fun h => h, fun w' _ completed _ v _ => ?_⟩
    rw [resume_eq]
    exact ⟨EffTy.pure .unit, TypedProg.pure (unit_exit w'), rfl, rfl, rfl, rfl⟩)
    ⟨rfl, rfl, rfl, rfl⟩

/-- The frame the loop's entry leaves (its body over the loop slot) is typed. -/
theorem entry_saved (w : W) (x : RSaved) (current : x.current = .pure (.success Val.unit))
    (stack : x.stack = [.loop (.loop p) Val.unit]) (hp : InterruptProvenance x) :
    SavedOk (TypedProg (loop : ProgramSource)) ExitOk (frameProtocols loop) w (EffTy.pure .unit) x :=
  ⟨EffTy.pure .unit, current ▸ TypedProg.pure (unit_exit w),
    stack ▸ .cons (frameAccepts_loop (protocol w)) (.nil _), hp⟩

end Endless

namespace Finishing

def loop : NativeEff :=
  .iterate (some .unit) (.lit .unit) (.lit (.bool false)) (.lit .unit) (.lit .unit)
    (.succeed (.lit .unit))

def p : Point := rootPoint 2

theorem protocol (w : W) :
    LoopProtocol (loop : ProgramSource) w (EffTy.pure .unit) (EffTy.pure .unit) (.loop p) Val.unit :=
  LoopProtocol.fold ⟨rfl, fun h => h, fun w' _ _ _ _ _ => TypedProg.pure (unit_exit w')⟩

end Finishing

namespace View

def x : FiberId := ⟨5⟩

def loop : NativeEff :=
  .iterate (some .bool) (.lit (.bool true)) (.var 1) (.lit (.bool true)) (.lit .unit)
    (.awaitFiber (.var 0) .joinEffect)

def p : Point :=
  { rootPoint 3 with env := [Val.fiber x], completed := [(x, .failure Cause.empty)] }

def awaitCode : RProgram := .vis (.inr (.await x .joinEffect)) Effects.Program.pure

theorem empty_view (v : Val) : (interpRAt loop []).loopResume (.loop p) (.bool true) v =
    .continue (.bool true) awaitCode := rfl

theorem await_untyped (w : W) (undeclared : w.Γ x = none) (ty : EffTy) :
    ¬ TypedProg (loop : ProgramSource) w ty awaitCode := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change (w.Γ x).isSome = true at pre
  rw [undeclared] at pre
  cases pre

/-- **The view-dependent frame is refused** (the flip of `E4-TYPED-CE-038`): its step must answer
`unit` at the empty view, where the body awaits a fiber the world does not declare. -/
theorem refused (w : W) (undeclared : w.Γ x = none) (tout : EffTy) :
    ¬ LoopProtocol (loop : ProgramSource) w (EffTy.pure .unit) tout (.loop p) (.bool true) := by
  intro h
  obtain ⟨_, _, next⟩ := h.unfold
  have step := next w (leHost_refl w) [] (fun _ q => nomatch q) Val.unit trivial
  rw [empty_view] at step
  obtain ⟨tin', typed, _⟩ := step
  exact await_untyped w undeclared tin' typed

end View

/-! ## The `Effect4.Coind` bank's red control

`frameAccepts_iter`'s protocol premise (`Typed/Residual.lean`) closes with
`aesop (rule_sets := [Effect4.Coind])`: the bank projects the frame hook to the protocol and moves the
protocol to the later world. The identical goal without the bank fails. -/

/--
error: aesop: failed to prove the goal after exhaustive search.
---
error: unsolved goals
root : ProgramSource
w : W
tin tout : EffTy
name : EffName
h : IteratorProtocol root w tin tout name
w' : Typed.World
a : World.leHost w w'
⊢ (frameProtocols root).iterator w' tin tout name
-/
#guard_msgs (error) in
example {root : ProgramSource} {w : W} {tin tout : EffTy} {name : EffName}
    (h : IteratorProtocol root w tin tout name) :
    ∀ w', w.leHost w' → (frameProtocols root).iterator w' tin tout name := by
  aesop

end Test.Program.LoopProtocols
