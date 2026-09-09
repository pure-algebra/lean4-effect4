import Effect4.Api
import Effect4.Laws.Program.Admit

namespace Test.Api.ExternalContract
open Effect4 Effect4.Program Effect4.Machine

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

def row (name : String) (answer : Ty) (error : Ty := .never) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request := .nat, answer, error, cite := "" }

def table : RowTable := [row "query" .nat, row "cell" NativeOp.refTy,
  row "flag" .bool, row "tagged" .nat .nat]

#guard LawfulTable table

def program (i : Nat := 0) : NativeEff := .callback (.external i) (.lit (.nat 1))

def accepted : Completion Val Err Defect FiberId Ann := .ofExit (.success (.nat 7))
def wrong : Completion Val Err Defect FiberId Ann := .ofExit (.success (.bool true))

def refusal (p : NativeEff) (tape : List Api.Decision)
    (answers : List (Completion Val Err Defect FiberId Ann) := []) : Option Refusal :=
  match Api.replayChecked p 1000 tape [] answers table with
  | .inl _ => none
  | .inr (_, _, why, _) => some why

#guard Api.typeOf (program 0) table = some (.pure .nat)
#guard Api.roundTrip (program 0) table = .ok (program 0)
#guard refusal (program 0) [Api.evaluate] [accepted] = none
#guard (Api.run (program 0) 1000 [] [accepted] table).exit = some (.success (.nat 7))
#guard refusal (program 0) [Api.evaluate] [wrong] = some (.oracleType 0 .nat)
-- E4-HOST-CE-001: the current decision's rejected oracle head is reported even at a fuel frontier.
#guard match Api.replayChecked (program 0) 2 [Api.evaluate] [] [wrong] table with
  | .inr (0, _, .oracleType 0 .nat, _) => true
  | _ => false
#guard match Api.replayChecked (program 0) 2 [Api.evaluate] [] [accepted] table with
  | .inl _ => true
  | _ => false
#guard refusal (program 0) [.answerAsync ⟨99⟩ 0 accepted] = some (.notParked ⟨99⟩)
#guard refusal (program 0) [.answerAsync Api.root 0 accepted] = some (.notParked Api.root)
#guard refusal (program 0) [Api.evaluate, .answerAsync Api.root 1 accepted] =
  some (.staleToken Api.root 0 1)
#guard refusal (.callback .sleep (.lit (.nat 5)))
  [Api.evaluate, .answerAsync Api.root 0 accepted] = some (.notExternal Api.root 0)
#guard refusal (program 0) [Api.evaluate, .answerAsync Api.root 0 wrong] =
  some (.answerType Api.root 0 .nat)
#guard refusal (program 0) [Api.evaluate,
  .answerAsync Api.root 0 (.ofExit (.failure (Cause.fail (.tag 1))))] =
  some (.errorType Api.root 0 .never)
#guard refusal (program 1) [Api.evaluate,
  .answerAsync Api.root 0 (.ofExit (.success (Val.cell ⟨0⟩)))] =
  some (.deadHandle Api.root 0)
#guard refusal (program 0) [Api.evaluate, .answerAsync Api.root 0 (.ofRefGet ⟨0⟩)] =
  some (.unknownCell ⟨0⟩)
#guard refusal (program 0) [Api.evaluate, .answerAsync Api.root 0 accepted,
  .answerAsync Api.root 0 accepted] = some (.notParked Api.root)
#guard (Api.replaySteps (program 0) 1000 [Api.evaluate] [] [] table).map (fun step => step.2.2) =
  [[(Api.root, 0, .external 0, Val.nat 1)]]

/-- A live cell alone is not enough: its value must inhabit the awaited type. -/
def boolAfterCell : NativeEff := .bind (.perform .refMake (.lit (.nat 7))) (program 2)
#guard refusal boolAfterCell [Api.evaluate, .answerAsync Api.root 0 (.ofRefGet ⟨0⟩)] =
  some (.answerType Api.root 0 .bool)

/-- E4-HOST-CE-002: an eager child rejects the head before the root accepts it at another row. -/
def twoRegistrations : NativeEff :=
  .bind (.withFiber (.fork (program 0) { daemon := false, startImmediately := true, maskMode := .inherit })) (program 2)
#guard refusal twoRegistrations [Api.evaluate] [wrong] = some (.oracleType 0 .nat)

/-- Receiver methods cover zero, one and two arguments, and explicit type arguments. -/
def methodTable : RowTable :=
  [ { row "stop" .nat with spelling := "stop", shape := .method, request := .prod .nat .unit }
  , { row "read" .nat with spelling := "read", shape := .method, request := .prod .nat .nat }
  , { row "write" .nat with spelling := "write", shape := .method, request := .prod .nat (.prod .nat .string) }
  , { row "lookup" .nat with spelling := "lookup", shape := .method, request := .prod .nat .nat, typeArgs := ["number"] } ]

#guard LawfulTable methodTable

def pair (a b : Term) : Term := .app "pair" (.cons a (.cons b .nil))
def methodProgram (i : Nat) (args : Term) : NativeEff :=
  .bind (.succeed (.lit (.nat 9))) (.callback (.external i) (pair (.var 0) args))
def methodPrograms : List NativeEff :=
  [methodProgram 0 (.lit .unit), methodProgram 1 (.lit (.nat 3)),
   methodProgram 2 (pair (.lit (.nat 3)) (.lit (.str "x"))), methodProgram 3 (.lit (.nat 3))]
#guard methodPrograms.all fun p => Api.typeOf p methodTable = some (.pure .nat)
#guard methodPrograms.all fun p => Api.roundTrip p methodTable = .ok p
#guard methodPrograms.all fun p =>
  (Api.run p 1000 [] [accepted] methodTable).exit = some (.success (.nat 7))

-- The finite table admits exactly its indexed rows; duplicates and built-in collisions fail.
#guard !(nativeSignature table).dom (.external table.length)
#guard !LawfulTable [row "query" .nat, row "query" .nat]
#guard !LawfulTable [{ row "query" .nat with spelling := "Ref.get" }]

#print axioms Effect4.Program.external_answer_typed
#print axioms Effect4.Program.external_oracle_typed
#print axioms Effect4.Program.mintedIn_iff_MintedIn
#print axioms Effect4.Program.replayCheckedFrom_answersValid

end Test.Api.ExternalContract
