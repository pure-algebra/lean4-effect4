import Effect4.Codegen.Tuple
import Effect4.Codegen.Read

/-! Finite controls for exact tuple index syntax, including indices outside the JavaScript number
profile. The universal laws are `Tuple.readAt_writeAt` and `Tuple.readAt_exact`
(`src/Effect4/Laws/Codegen/Tuple.lean`), on the raw scope-only domain. -/

namespace Effect4.Test.TupleCodegen
open Effect4.Program Effect4.Codegen TypeScript

#guard Data.NatDecimal.read "0" = some 0
#guard Data.NatDecimal.read "123456789012345678901234567890" = some 123456789012345678901234567890
#guard Data.NatDecimal.read "" = none
#guard Data.NatDecimal.read "00" = none
#guard Data.NatDecimal.read "01" = none
#guard Data.NatDecimal.read "+1" = none
#guard Data.NatDecimal.read "-0" = none
#guard Data.NatDecimal.read "1e3" = none
#guard Data.NatDecimal.read " 1" = none
#guard Data.NatDecimal.read "１" = none

#guard Tuple.readAt (Tuple.writeAt 0 (.ident "raw")) == some (0, .ident "raw")
#guard Tuple.readAt (Tuple.writeAt 123456789012345678901234567890 (.ident "raw")) ==
  some (123456789012345678901234567890, .ident "raw")

def marker (typeKey key : String) (targets : List Expr) : Expr :=
  .call (.call (.generic (.ident "tupleAt") [.literal typeKey]) [.str key]) targets

#guard (Tuple.readAt (marker "0" "0" [.int 7])).isSome
#guard (Tuple.readAt (marker "0" "1" [.int 7])).isNone
#guard (Tuple.readAt (marker "01" "01" [.int 7])).isNone
#guard (Tuple.readAt (marker "-1" "-1" [.int 7])).isNone
#guard (Tuple.readAt (marker "0" "0" [])).isNone
#guard (Tuple.readAt (marker "0" "0" [.int 7, .int 8])).isNone
#guard (Tuple.readAt (.call (.ident "tupleAt") [.int 0, .int 7])).isNone
#guard (Tuple.readAt (.index (.ident "raw") (.int 0))).isNone
#guard !exportNameSafe "tupleAt"
#guard TypeScript.Render.expr {} 0 (Tuple.writeAt 123456789012345678901234567890 (.ident "value")) ==
  "tupleAt<\"123456789012345678901234567890\">(\"123456789012345678901234567890\")(value)"

-- Empty, singleton, pair and larger construction keep the existing atom representation.
def empty : Term := .app "tuple" .nil
def singleton : Term := .app "tuple" (.cons (.lit (.nat 7)) .nil)
def pair : Term := .app "tuple" (.cons (.lit (.nat 7)) (.cons (.lit (.str "x")) .nil))
def larger : Term := .app "tuple" (.cons (.lit (.nat 7))
  (.cons (.lit (.str "x")) (.cons (.lit (.bool true)) .nil)))

#guard readTerm [] 0 (printTerm 0 empty) == .ok empty
#guard readTerm [] 0 (printTerm 0 singleton) == .ok singleton
#guard readTerm [] 0 (printTerm 0 pair) == .ok pair
#guard readTerm [] 0 (printTerm 0 larger) == .ok larger
#guard readTerm [] 0 (printTerm 0 (.tupleAt larger 2)) == .ok (.tupleAt larger 2)
#guard readTerm [] 1 (printTerm 1 (.tupleAt (.var 0) 123456789012345678901234567890)) ==
  .ok (.tupleAt (.var 0) 123456789012345678901234567890)
#guard readTerm [] 0 (printTerm 0 (.app "tupleAt" .nil)) == .ok (.app "tupleAt" .nil)

end Effect4.Test.TupleCodegen
