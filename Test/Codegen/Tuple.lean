import Effect4.Laws.Codegen.Tuple
import Effect4.Laws.Codegen.ReadLeaf

/-! Finite controls for exact tuple index syntax. The universal laws below retain the raw
scope-only domain, including indices outside the JavaScript number profile. -/

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

example (index : Nat) (target : Expr) :
    Tuple.readAt (Tuple.writeAt index target) = some (index, target) := Tuple.readAt_writeAt index target
example (e : Expr) (index : Nat) (target : Expr) (h : Tuple.readAt e = some (index, target)) :
    Tuple.writeAt index target = e := Tuple.readAt_exact e index target h
example (classes : Effect4.Codegen.Classes.Classes) (n index : Nat) (target : Term)
    (h : Term.scoped n target = true) (hc : target.covers classes = true)
    (hu : target.unannotated = true) :
    readTerm classes n (printTerm n (.tupleAt target index)) = .ok (.tupleAt target index) :=
  readTerm_printTerm _ h hc hu

end Effect4.Test.TupleCodegen

#print axioms Effect4.Data.NatDecimal.decodeBytes_repr
#print axioms Effect4.Data.NatDecimal.read_repr
#print axioms Effect4.Data.NatDecimal.read_exact
#print axioms Effect4.Codegen.Tuple.readAt_size
#print axioms Effect4.Codegen.Tuple.readAt_writeAt
#print axioms Effect4.Codegen.Tuple.readAt_exact
#print axioms Effect4.Program.readTerm_printTerm
#print axioms Effect4.Program.readTerm_exact
#print axioms Effect4.Program.keyFromText_print
#print axioms Effect4.Program.Var.name_inj
