import Tools.Query

/-! Finite controls for the S1 query integration.
The claim, existing proof consumers, and limits precede this probe in its review plan.
No new semantic theorem is stated here. -/

set_option autoImplicit false
namespace Research.S1Query
open Lean (Json)
open Effect4 Effect4.Program Effect4.Program.Wire
open Tools.Query

def sig : Signature NativeOp := ({} : SigApp).signature
def idDecl : DefDecl := { name := "identity", request := .nat, answer := .nat }
def idBody : NativeEff := .succeed (.var 0)
def plain : NativeEff := .succeed (.lit (.nat 5))
def callId : NativeEff := .perform (.call 0) (.lit (.nat 5))
def block : NativeEff := .defs [idDecl] (.cons idBody .nil) callId

-- Positive: the old structural focus supplies the query's root focus.
#guard (focusAt sig [] plain []).isSome
#guard (answer (ask "focus" plain)).laws == [``focusAt_typed]
#guard ((answer (ask "focus" plain)).result.getObjValAs? Bool "found").toOption == some true

-- The new root focus holds a whole admitted block.
#guard (Checker.checkModule sig block).toOption.isSome
#guard ((block : Sketch).focusAt {} []).isSome
#guard ((answer (ask "focus" block)).result.getObjValAs? Bool "found").toOption == some true

-- Challenged law claim: the query names a structural law whose premise fails.
#guard focusAt sig [] block [] == none
#guard (Checker.check sig [] [] block).toOption.isNone
#guard (answer (ask "focus" block)).laws == [``focusAt_typed]

-- Negative control: no answered focus or law at an invalid address.
#guard ((answer (ask "focus" block [9])).result.getObjValAs? Bool "found").toOption == some false
#guard (answer (ask "focus" block [9])).laws == []

-- Inside the block, the same call needs the part's definition signature.
#guard ((block : Sketch).focusAt {} [1]).isSome
#guard (focusAt (sig.withDefs [idDecl]) [] callId []).isSome
#guard focusAt sig [] block [1] == none

-- Existing limit: replacing a root block by itself keeps its check,
-- but the structural filling premise deliberately does not certify that case.
#guard ((answer { ask "fill" block with replacement := some (hexOf block) }).result.getObjValAs? Bool "matchedFocus").toOption == some false
#guard ((answer { ask "fill" block with replacement := some (hexOf block) }).result.getObjVal? "check").toOption ==
  some (checkJson ((block : Sketch).check {}))

def loop : NativeEff :=
  .iterate none (.lit (.nat 0)) (.lit (.bool true)) (.var 1) (.var 0) (.succeed (.var 0))
def inlineLoop : NativeEff := .bind plain loop
def definedLoop : NativeEff := .defs [idDecl] (.cons idBody .nil) (.bind callId loop)

-- Same slot-bearing program after a plain result or after an invocation.
#guard (Checker.checkModule sig inlineLoop).toOption.isSome
#guard (Checker.checkModule sig definedLoop).toOption.isSome
#guard ((definedLoop : Sketch).focusAt {} [1, 1]).isSome
#guard (slotsAt inlineLoop [1] allSlots).length == 3
#guard (answer (ask "slots" inlineLoop [1])).laws == [``hasTy_extSlotEnv]

-- The existing slot reader loses the context behind the definition call.
#guard slotsAt definedLoop [1, 1] allSlots == []
#guard (answer (ask "slots" definedLoop [1, 1])).result == Json.arr #[]
#guard (answer (ask "slots" definedLoop [1, 1])).laws == []

#eval IO.println "PASS S1 query controls: plain focus, block law mismatch, invalid address, part signature, root-fill limit, and slot extension gap"
end Research.S1Query
