import Research.Pass.FiberSlice.Core

/-! Verifier probe (fiberslice): nesting positions the seat's eight rows (`LivePath.lean` §2) do
not run: the error arm of `except`, a three-deep nesting, and a union whose members are two
fiber types. Same shape as the seat's rows: fiber 1 is a child the program forked first, returning
`"wrong"` (forged) or `7` (honest); the host answers at a type holding `fiberOf nat never`.
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSliceVerify.Nesting
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice

def opts : Supervision.ForkOptions := ⟨true, true, .interruptible⟩
def fNat : Ty := .fiberOf .nat .never

def rowAt (answer : Ty) : Row where
  name := "returnValue"
  spelling := "Host.returnValue"
  kind := .async
  registration := .external
  request := .unit
  answer := answer
  error := .never
  cite := "verifier probe"

/-- Fork a child, ask the host, return the answer. -/
def programOf (child : Term) : Api.Program :=
  .bind (.withFiber (.fork (.succeed child) opts))
    (.bind (.perform (.external 0) (.lit .unit)) (.succeed (.var 1)))

def parkedOf (answer : Ty) (child : Term) : NativeMachine :=
  (Api.replay (programOf child) 1000 [Api.evaluate] [] [rowAt answer]).machine

def verdict (answer : Ty) (child : Term) (value : Val) : Option RefusalD :=
  admitD (programOf child) [rowAt answer] (parkedOf answer child)
    (.answerAsync Api.root 0 (.ofExit (.success value)))

def oldVerdict (answer : Ty) (child : Term) (value : Val) : Option Refusal :=
  admit [rowAt answer] (parkedOf answer child) (.answerAsync Api.root 0 (.ofExit (.success value)))

def wrong : Term := .lit (.str "wrong")
def right : Term := .lit (.nat 7)

/-- (answer type, value, expected refusal path) -/
def cases : List (Ty × Val × List Nat) := [
  -- the error arm of a Result
  (.except fNat .unit, .ctor 0 [Value.fiber 1], [0]),
  -- three deep: list of options of pairs
  (.list (.option (.prod .unit fNat)), .list [.none, .some (.list [.unit, Value.fiber 1])], [1, 0, 1])]

#guard cases.all fun (ty, _, _) => (Api.typeOf (programOf wrong) [rowAt ty]).isSome
#guard cases.all fun (ty, _, _) => requestOf (parkedOf ty wrong) Api.root 0 == some (.external 0, .unit)
-- today's admission accepts every forged value
#guard cases.all fun (ty, v, _) => oldVerdict ty wrong v == none
-- the prototype refuses each at its path, and accepts the honest one
#guard cases.all fun (ty, v, path) =>
  verdict ty wrong v == some (.handleDecl Api.root 0 ⟨path, .fiberDecl ⟨1⟩ (some (EffTy.pure .string)) fNat⟩)
#guard cases.all fun (ty, v, _) => verdict ty right v == none

-- a union of two fiber types: the forged fiber (declared `string`) fits the second member, so it
-- is admitted, and the program sees exactly that union (no rule awaits a union: `fiberTy` is
-- syntactic, `Typing/Rules.lean:184-186`)
def twoFibers : Ty := .union fNat (.fiberOf .string .never)
#guard verdict twoFibers wrong (Value.fiber 1) == none
#guard (Api.typeOf (.bind (programOf wrong) (.awaitFiber (.var 2) .joinEffect)) [rowAt twoFibers]) == none

end Research.Pass.FiberSliceVerify.Nesting
