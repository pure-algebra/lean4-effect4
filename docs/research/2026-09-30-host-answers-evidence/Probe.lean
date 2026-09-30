import Effect4.Api.HostSession
import Effect4.Program.Profile

/-! Host answers and the typed guarantee: probes for the external-reply slice.
Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.HostAnswers
open Effect4 Effect4.Machine Effect4.Program Effect4.Api.HostSession

/-! ## 1. With no host table, the runtime's check refuses every host answer

This is what makes the in-scope M6 repair small: M6's reference runner has no table, and at
the empty table no `answerAsync` decision is ever admitted, whatever the machine holds. -/

theorem emptyTable_refuses_every_answer (m : NativeMachine) (fiber : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann) :
    admit [] m (.answerAsync fiber token answer) ≠ none := by
  intro h
  simp only [admit] at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · rename_i i _ _
          have hrow : externalRow [] i = none := rfl
          rw [hrow] at h
          simp only [reduceCtorEq] at h
        · cases h

#print axioms emptyTable_refuses_every_answer

/-! ## 2. A forged fiber handle passes the live host session

A host row that answers a fiber handle (`fiberOf nat never`). The program forks a fiber that
returns a string, asks the host for a fiber, and joins the fiber the host names. The host
names the string fiber. Every check on the certified live path passes: `start` admits the
program through `admitProgram`, `bindCall` binds the call, `submit` runs `preflight`
(`acceptReply`, `admit`, `Val.hasTy`), and `applyReply` applies it. The program, checked at
`nat`, finishes with a string. -/

def fiberRow : Row where
  name := "returnFiber"
  spelling := "Host.returnFiber"
  kind := .async
  registration := .external
  request := .unit
  answer := .fiberOf .nat .never
  error := .never
  cite := "research probe"

def table : RowTable := [fiberRow]
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

/-- `var 1` is the host's answer (binder levels count from the outside). -/
def program : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.str "wrong"))) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.awaitFiber (.var 1) .joinEffect))

#guard Api.typeOf program table = some (EffTy.pure .nat)
#guard (admitProgram program table).toOption.isSome

def header : Header := ⟨version, "probe", "probe", table⟩
def call : Call := ⟨version, "probe", table, 0, Api.root, .external 0, .unit⟩
def reply : Reply := ⟨version, "probe", 0, ⟨Api.root, 0⟩, .ofExit (.success (Value.fiber 1))⟩

/-- The phases of the live path, then the root's exit. -/
def livePath : Option (List Phase × Option ExitV) :=
  match start program table "probe" header 1000 with
  | .error _ => none
  | .ok s0 =>
    let r1 := advance s0 1000 Api.evaluate
    let r2 := bindCall r1.session call 0
    let r3 := submit r2.session reply
    let r4 := applyReply r3.session reply.key 1000
    let r5 := advance r4.session 1000 Api.flush
    some ([r1.phase, r2.phase, r3.phase, r4.phase, r5.phase],
      (r5.session.machine.fiber? Api.root).bind (·.exit))

#guard (livePath.map (·.1)) = some [.progressed, .bound, .preflight, .applied, .progressed]
#guard (livePath.map (·.2)) = some (some (.success (.str "wrong")))

-- The same answer through the checked tape replay.
#guard (match Api.replayChecked program 1000
    [Api.evaluate, .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1))), Api.flush]
    [] table with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.str "wrong")))

/-! ## 3. What the value check sees

`Val.hasTy` checks a handle by its kind only; what the fiber returns or the cell holds is
typed by the proof's world tables, which the runtime does not carry. -/

#guard Val.hasTy (Value.fiber 1) (.fiberOf .nat .never)
#guard Val.hasTy (Value.fiber 1) (.fiberOf .string .never)
-- in today's native subset cells and deferreds hold numbers, so a wrong cell handle still
-- delivers a number; the generic cells of decisions row 44 would open the same gap
#guard NativeOp.refTarget = "Ref.Ref<number>"
#guard NativeOp.deferredTarget = "Deferred.Deferred<number, number>"

/-! ## 4. Every host row in the tree answers data or an allocated external handle

So refusing internal handles in host answers breaks no package in the tree: the SQLite and
key-value packages, streams and the profile rows are checked by hand in the note. -/

#eval IO.println "Host-answer probes: all guards passed."

end Research.HostAnswers
