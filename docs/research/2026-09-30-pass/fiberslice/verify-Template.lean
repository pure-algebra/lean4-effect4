import Research.Pass.FiberSlice.Core

/-! Verifier probe (fiberslice): a host row whose answer column is a template (decisions row 42).
The checker instantiates a row's columns from the request's static type (`rowTy`,
`Program/Typing/Rules.lean:114-117`), for every row, host rows included, and the table admission
does not refuse template parameters (`checkTable`, `Program/Native.lean:345-352`). The answer
admission checks the value against the *uninstantiated* column (`admitAnswer`, `admit`,
`Program/Admit.lean:59-92`). Question: does the prototype still apply the honest reply there?
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSliceVerify.Template
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice

/-- Hand back a fiber: the request is a fiber handle, the answer a fiber of the same types. -/
def echoRow : Row where
  name := "echoFiber"
  spelling := "Host.echoFiber"
  kind := .async
  registration := .external
  request := .fiberOf (.var 0) (.var 1)
  answer := .fiberOf (.var 0) (.var 1)
  error := .never
  cite := "verifier probe"

def table : RowTable := [echoRow]
def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩

/-- Fork a child returning `child`, pass its handle to the host, join the fiber the host names. -/
def echoProgram (child : Term) : Api.Program :=
  .bind (.withFiber (.fork (.succeed child) opts))
    (.bind (.perform (.external 0) (.var 0)) (.awaitFiber (.var 1) .joinEffect))

def honest : Api.Program := echoProgram (.lit (.nat 7))

-- the checker instantiates the template from the request: the program checks at `nat`
#guard Api.typeOf honest table = some (EffTy.pure .nat)
-- and the table is admissible: the session starts
#guard (Api.HostSession.start honest table "probe"
  ⟨Api.HostSession.version, "probe", "probe", table⟩ 1000).toOption.isSome

/-- The root parked on the host call, the request being fiber 1's handle. -/
def parked : NativeMachine := (Api.replay honest 1000 [Api.evaluate] [] table).machine

#guard requestOf parked Api.root 0 == some (.external 0, Value.fiber 1)
-- fiber 1 is declared at `nat`, the type the program gave its handle
#guard (fiberDecl (nativeSignature table) honest parked ⟨1⟩).map (·.answer) = some .nat

def honestAnswer : NativeDecision := .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1)))

-- today's admission accepts the honest answer (it accepts any fiber at a `fiberOf` column)
#guard admit table parked honestAnswer = none
-- the prototype refuses it: the declaration `nat` is compared with the uninstantiated `var 0`
#guard admitD honest table parked honestAnswer =
  some (.handleDecl Api.root 0 ⟨[], .fiberDecl ⟨1⟩ (some (EffTy.pure .nat)) (.fiberOf (.var 0) (.var 1))⟩)

-- through the tape route: production finishes with 7, the prototype refuses the honest tape
#guard (match Api.replayChecked honest 1000 [Api.evaluate, honestAnswer, Api.flush] [] table with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.nat 7)))
#guard (match replayCheckedD honest 1000 [Api.evaluate, honestAnswer, Api.flush] [] table with
  | .inr (position, _, .handleDecl _ _ _, _) => position == 1
  | _ => false)

/-! The same row answered with a *forged* fiber: the program passes a `string` fiber, so its
answer is typed `fiberOf string never`, and the host names a `nat` fiber. Today's admission
accepts it (the same hole as the closed row); the prototype refuses it, as it refuses every
fiber at this row. -/

def forgedProgram : Api.Program :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 7))) opts))
    (.bind (.withFiber (.fork (.succeed (.lit (.str "s"))) opts))
      (.bind (.perform (.external 0) (.var 1)) (.awaitFiber (.var 2) .joinEffect)))

#guard Api.typeOf forgedProgram table = some (EffTy.pure .string)
def forgedAnswer : NativeDecision := .answerAsync Api.root 0 (.ofExit (.success (Value.fiber 1)))
#guard (match Api.replayChecked forgedProgram 1000 [Api.evaluate, forgedAnswer, Api.flush] [] table with
  | .inr _ => false
  | .inl r => r.exit == some (.success (.nat 7)))
#guard (match replayCheckedD forgedProgram 1000 [Api.evaluate, forgedAnswer, Api.flush] [] table with
  | .inr (position, _, .handleDecl _ _ _, _) => position == 1
  | _ => false)

/-! Context: a template *data* column is unanswerable today, before any slice. `Val.hasTy` at
`var` is `false` (`Program/Typed.lean:67`), so `admit` refuses even the value the checker
typed. -/

def idRow : Row where
  name := "echo"
  spelling := "Host.echo"
  kind := .async
  registration := .external
  request := .var 0
  answer := .var 0
  error := .never
  cite := "verifier probe"
def idProgram : Api.Program := .perform (.external 0) (.lit (.nat 3))

#guard Api.typeOf idProgram [idRow] = some (EffTy.pure .nat)
#guard admit [idRow] (Api.replay idProgram 1000 [Api.evaluate] [] [idRow]).machine
    (.answerAsync Api.root 0 (.ofExit (.success (.nat 3)))) =
  some (.answerType Api.root 0 (.var 0))

/-! Red control, pinned: the claim "the prototype applies the honest reply" fails at this row. -/

/-- error: Expression
  decide (admitD honest table parked honestAnswer = none)
did not evaluate to `true` -/
#guard_msgs in
#guard admitD honest table parked honestAnswer = none

end Research.Pass.FiberSliceVerify.Template
