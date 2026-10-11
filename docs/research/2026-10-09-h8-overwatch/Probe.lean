import Effect4.Laws.Program.Agreement.Calls
import Effect4.Laws.Program.Agreement.Machine
import Effect4.Laws.Api.SessionMeaning
import Test.Program.AgreementContract
import Test.Api.SessionMeaning

set_option autoImplicit false
set_option maxRecDepth 8192

namespace H8Overwatch

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Program.Agreement

-- Research controls of rows-denotation-session. Placement is in PLAN.md.
-- These declarations add no production claim or host-execution evidence.

def root : NativeEff := .succeed (.lit .unit)
def waiting (j : Nat) : NFiber :=
  fiberOf (.async (.external (.external j) (.nat j) []) false none) []
def otherStore : Stores := { Stores.empty with nextName := 9 }

-- The observation forgets distinct waiting calls and their retained stores.
theorem different_frontiers :
    ReachesC root 0 (waiting 0) Stores.empty [] (waiting 1) otherStore [] := by
  intro n
  cases n with
  | zero => rfl
  | succ n => rfl

#guard (waiting 0).current ≠ (waiting 1).current
#guard Stores.empty ≠ otherStore
#guard IsCall (waiting 0).current = true
#guard PlainCode (waiting 0).current = false

-- A positive control: one answer consumes one reply and retains the state.
#guard match localStepC root (waiting 0) otherStore
    [.success (.nat 7), .success (.nat 9)] with
  | some (.running fr s, remaining) =>
    decide (fr.current = Prim.success (.nat 7)) &&
    decide (s = otherStore) && decide (remaining = [.success (.nat 9)])
  | _ => false

-- The relation also forgets a repeated step that never reaches a host call.
def stalled : NFiber :=
  fiberOf (.async (.external (.external 0) (.nat 0) []) true none) []

#guard IsCall stalled.current = false

private theorem stalled_none (n : Nat) :
    localRunC root n stalled Stores.empty [] = none := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem stalled_observation :
    ReachesC root 0 stalled Stores.empty [] (waiting 1) otherStore [] := by
  intro n
  rw [Nat.add_zero, stalled_none]
  cases n with
  | zero => rfl
  | succ n => rfl

-- This is not a counterexample on StraightRows; it is a control of ReachesC's meaning.
#guard PlainCode stalled.current = false

def hostRow : Row := (Effect4.Program.Authoring.Row.host "H.wait" .nat .nat (.prod .string .string) "review").row
def table : RowTable := [hostRow]
def num (n : Nat) : Term := .lit (.nat n)
def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def call (n : Nat) : NativeEff := .perform (.external 0) (num n)
def bodyFailure : ExitV := .failure (.die (.user 3))

-- A cell is changed before failure. The finalizer calls the host, then writes again.
def stateful : NativeEff :=
  .bind (.perform .refMake (num 0))
    (.onExit
      (.bind (.perform .refSet (pair (.var 0) (num 7))) (call 1))
      (.bind (call 2) (.perform .refSet (pair (.var 0) (num 8)))))

#guard StraightRows table stateful = true

-- Reader of the landed law, including any outside continuation and mask.
example (K : List NCode) (i : Bool) (r : ReplyTape) :
    RunsTo stateful K i (fiberOf (compile stateful 128) K i) Stores.empty r
      (meaningRows table stateful [] Stores.empty r) :=
  localRunC_compile table stateful stateful (rootPoint 128) K i Stores.empty r
    (by rfl) (by rfl) (by decide)

-- A bounded inspection of local steps exposes the state at a waiting call.
def stoppedAt : Nat → NFiber → Stores → ReplyTape → Option (NFiber × Stores × ReplyTape)
  | 0, _, _, _ => none
  | n + 1, fr, s, r =>
    match localStepC stateful fr s r with
    | none => some (fr, s, r)
    | some (.running fr' s', r') => stoppedAt n fr' s' r'
    | some (.finished _ _, _) => none

#guard match stoppedAt 128 (fiberOf (compile stateful 128) []) Stores.empty [bodyFailure] with
  | some (fr, s, remaining) =>
    decide (s.refs = [.nat 7]) && decide (remaining = []) && !fr.interruptible &&
    (match fr.current with
      | .async (.external (.external 0) (.nat 2) _) false none => true
      | _ => false)
  | none => false

-- The declared meaning deliberately gives no frontier state in this observation.
#guard meaningRows table stateful [] Stores.empty [bodyFailure] = none
#guard localRunC stateful 128 (fiberOf (compile stateful 128) []) Stores.empty [bodyFailure] = none

-- After the finalizer's reply, both readers retain its write and the body failure.
#guard match localRunC stateful 128 (fiberOf (compile stateful 128) []) Stores.empty
    [bodyFailure, .success (.nat 11), .success (.nat 99)] with
  | some (ex, s, remaining) =>
    decide (ex = bodyFailure) && decide (s.refs = [.nat 8]) &&
    decide (remaining = [.success (.nat 99)])
  | none => false

#guard match meaningRows table stateful [] Stores.empty
    [bodyFailure, .success (.nat 11), .success (.nat 99)] with
  | some ((ex, s), remaining) =>
    decide (ex = bodyFailure) && decide (s.refs = [.nat 8]) &&
    decide (remaining = [.success (.nat 99)])
  | none => false

-- A successful session need not cover an untaken branch's syntactic depth.
def shallowPath (takeShort : Bool) : NativeEff :=
  .select (.lit (.bool takeShort)) .bool (.succeed (num 1))
    (Test.Program.AgreementContract.chain 8)

#guard 2 < Effect4.Program.Sched.depthRows (shallowPath true)
#guard Test.Api.SessionMeaning.raw (shallowPath true) table [.start]
    { fuel := 100, compileFuel := 2 } = some Test.Api.SessionMeaning.green
#guard match Test.Api.SessionMeaning.raw (shallowPath false) table [.start]
    { fuel := 100, compileFuel := 2 } with
  | some (_, funded, atRest, _, _) => !(funded && atRest)
  | none => false

-- Reader of the generalized drive theorem, at a nonempty table across two yields.
open Test.Program.AgreementContract in
example : ∃ fr k tr nt,
    replayEval (evaluator := evaluatorFor pLong table) (interpOf pLong table)
      fuelLong [Api.evaluate, Api.flush] (Api.load pLong fuelLong) =
    ReplayResult.finished
      (Mexit pLong (meaning pLong [] Stores.empty).1 fr
        (meaning pLong [] Stores.empty).2 k tr nt) :=
  replay_Mexit (table := table) pLong fuelLong
    (by unfold pLong; exact chain_straight 2100)
    (by unfold pLong fuelLong; rw [chain_depth]; omega)
    (by unfold pLong fuelLong; rw [chain_steps]; omega)

#print axioms different_frontiers
#print axioms stalled_observation
#print axioms localRunC_compile
#print axioms evaluateNative_plain
#print axioms evaluateNative_of_finished
#print axioms drive_localRun
#print axioms replay_Mexit
#print axioms run_eq_meaning
#print axioms Effect4.Run.denoteRows_eq_session

end H8Overwatch
