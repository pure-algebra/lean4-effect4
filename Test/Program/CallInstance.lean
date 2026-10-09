import Effect4.Laws.Program.Typing.Call
import Test.Dogfood.Scenario.Todo

/-!
# The call instance at an address: the battery of slice H9

Each line is a finite evaluation or a control (decisions row 301).
-/

namespace Test.Program.CallInstance

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Test.Dogfood.P2HandlerLayers (built?)
open Test.Dogfood.Scenario.Todo

/-- The calls of a built program: address, position, request type, answer and error. -/
def callsOf (m : Module NativeOp) : Option (List (List Nat × Option Nat × Ty × Ty × Ty)) :=
  (built? m).map fun b =>
    (programCalls (nativeSignature b.table) [] b.program).map fun entry =>
      (entry.1, (match entry.2.op with | .external i => some i | _ => none),
        entry.2.request, entry.2.answer, entry.2.error)

-- finite evaluation: at a closed row the instance is the row's own columns, at the call's address
#guard callsOf (request (add (str "milk"))) =
  some [([1], some 0, .string, Todo.ty.normalize, SqlError.ty.normalize)]
#guard callsOf (request (complete (nat 1))) =
  some [([0], some 2, .prod .nat .bool, (Ty.option Todo.ty).normalize, SqlError.ty.normalize)]

/-- A template row, the witness of decisions row 183: `List<A>` to `Option<A>`. -/
def first : Row :=
  { name := "first", spelling := "L.first", kind := .async, registration := .external,
    request := .list (.var 0), answer := .option (.var 0), cite := "battery" }

/-- One program text: the call of the template row on the variable in scope. -/
def callFirst : NativeEff := .perform (.external 0) (.var 0)

-- control: one program text has two instances. The request's static type decides, so no function
-- of the request value (the empty list is a member of both) recovers the instance
#guard (callAt (nativeSignature [first]) [.list .nat] callFirst []).map (fun c => (c.request, c.answer)) =
    some (.list .nat, .option .nat) &&
  (callAt (nativeSignature [first]) [.list .string] callFirst []).map (fun c => (c.request, c.answer)) =
    some (.list .string, .option .string)
-- finite evaluation: the instance keeps the row's bindings, the template's parameter at the
-- request's element type
#guard (callAt (nativeSignature [first]) [.list .nat] callFirst []).map (·.bindings) =
  some [(0, .nat)]
-- control: the reply check reads the row's template column. It refuses a member of the instance,
-- and it admits the one value that is a member of every instance
#guard externalAdmits [first] 0 (.ofExit (.success (.some (.nat 1)))) = false
#guard externalAdmits [first] 0 (.ofExit (.success .none)) = true
-- control: no instance where the address holds no call, and none where the checker refuses the
-- request
#guard (callAt (nativeSignature [first]) [.list .nat] (.succeed (.var 0)) []).isNone
#guard (callAt (nativeSignature [first]) [.nat] callFirst []).isNone

end Test.Program.CallInstance
