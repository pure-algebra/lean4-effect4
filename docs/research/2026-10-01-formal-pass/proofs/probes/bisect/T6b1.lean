import Effect4.Laws.Program.Typed.Assembly

/-!
# Formal pass, seat PROOFS — red control: the stale code slot on a reachable, host-free run

Base `efd67af1`. Reading aid for `note.md` §3 (gap G1) and §5 (probe A). No tracked file
is changed and no production statement is amended here.

The program is `E4-SCHED-CE-008`'s preempted catch with a timer in place of the deferred
answer (so the tape has no host answer, as `RReachable` requires) and one pure bind (so that
a uniform command budget stops between the walk that finishes the root and its queued
`finish`). After the signed divergence `U-01` the root's *exit* is the recorded interrupt
with no `Fail` reason, which fits the checked type `⟨nat, never, ∅⟩`. Its *code slot* still
holds the escaped `Fail 42`: `popR` returns `(frame, some exit)` without writing `current`
(`Laws/Program/EvaluateR.lean:67,99`), and nothing after it clears `current`
(`RunFiber.publish`, `RunFiber.cleared`, `Machine/Fibers.lean:1747-1764`).

Claims, all at budget 6 or 7 on one tape:
* `reach6`, `reach7`: both machines are `RReachable` (no host answer on the tape).
* `window6`: at budget 6 the cut lands between the finishing walk and its `finish`; the root
  has not exited, its stack is empty, its code slot holds the `Fail`.
* `residue6_*`: the residue the cut drops is exactly `[finish root e, drainDue]` with `e`
  clean, recomputed from the decision's own pieces; its root projection agrees with `m6`.
* `untyped_of_stale`, `window_untyped`, `finished_untyped`: at every world, `TypedState`
  fails at both machines (the saved-state clause of the generated `RunFiberOk`).
* `capstone_false_finished`: the current `M6Ledger.typedState_reachable` proposition is false
  at budget 7, on a finished run with no host answer (a new host-free refutation; rows 95–107
  do not touch it; row 133's exited-fiber exemption does).
* `capstone_false_window`: the same proposition is false at budget 6, where the root has not
  exited and the machine carries no residue — so no exemption keyed on a queued `finish`
  (row 133) can be read off the machine that `RReachable` hands the capstone.
* Positive control `exitsTyped6`, `exitsTyped7`: the observation-level clause (every recorded
  exit fits its fiber's declared type) holds at both machines at the initial world.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FormalPass.Proofs.StaleCode
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

def n (i : Nat) : Term := .lit (.nat i)
def yes : Term := .lit (.bool true)
def sleepy : NativeEff := .perform .sleep (.lit (.nat 1))

/-- `catchAll(uninterruptible(sleep(1) >> succeed 0 >> fail 42), _ => succeed 0)`. -/
def prog : NativeEff :=
  .catchIf yes (.uninterruptible (.bind sleepy (.bind (.succeed (n 0)) (.fail (n 42)))))
    (.succeed (n 0))

def ty : EffTy := ⟨.nat, .never, .empty⟩

def interruptRoot : Api.Decision :=
  .interruptFrom (some Api.root) ReasonAnnotations.empty Api.root

/-- Run the root to its park, record an interrupt while it is masked, fire the timer. -/
def tape : List Api.Decision :=
  [Api.evaluate, Api.flush, interruptRoot, .advance (ClockMillis.ofNat 1), Api.flush]

def m6 : RState := (replayR prog 6 tape).machine
def m7 : RState := (replayR prog 7 tape).machine

/-- A pure failure that carries a typed `Fail` reason. -/
def staleFail : RProgram → Bool
  | .pure (.failure c) => c.reasons.any (fun r => r.tag == ReasonTag.fail)
  | _ => false

/-- An exit that is a failure with no `Fail` reason; `none` is vacuously fine. -/
def exitFailClean : Option ExitV → Bool
  | none => true
  | some (.failure c) => cleanExit (.failure c)
  | some (.success _) => false

theorem classify7 : classify (replayR prog 7 tape) = .finished := by decide +kernel
end FormalPass.Proofs.StaleCode
