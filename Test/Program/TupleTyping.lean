import Effect4.Laws.Program.Typed

/-! Tuple type and evaluation controls with the coarse membership judgment.
These controls make no target execution or whole-machine progress claim. -/
namespace Effect4.Test.TupleTyping
open Program Machine

#guard NativeAtom.typeOf .tuple [] = some (.tuple [])
#guard NativeAtom.typeOf .tuple [.nat] = some (.tuple [.nat])
#guard NativeAtom.typeOf .tuple [.nat, .string] = some (.prod .nat .string)
#guard NativeAtom.typeOf .tuple [.nat, .string, .bool] = some (.tuple [.nat, .string, .bool])
#guard termTy (nativeSignature []) []
  (.app "tuple" (.cons (.lit (.str "Tag")) (.cons (.lit (.nat 1)) .nil))) =
  some (.prod (.lit "Tag") .nat)
#guard Tuple.typeAt (.tuple [.nat, .string, .bool]) 1 = some .string
#guard Tuple.typeAt (.prod .nat .string) 0 = some .nat
#guard Tuple.typeAt (.prod .nat .string) 1 = some .string
#guard Tuple.typeAt (.tuple []) 0 = none
#guard Tuple.typeAt (.tuple [.nat]) 1 = none
#guard Tuple.typeAt (.prod .nat .string) 2 = none
#guard Tuple.typeAt (.list .nat) 0 = none
#guard Tuple.typeAt .unknown 0 = none
#guard Tuple.typeAt .never 999999999999999999999 = some .never
#guard Tuple.typeAt (.union (.prod .nat .string) (.tuple [.bool, .string, .nat])) 1 = some .string
#guard Tuple.typeAt (.union (.prod .nat .string) (.tuple [.bool, .string, .nat])) 2 = none
#guard Tuple.typeAt (.union (.tuple [.nat]) (.tuple [.string])) 0 = some (Ty.join .nat .string)
#guard Tuple.typeAt (.union (.tuple [.nat]) (.list .nat)) 0 = none
#guard Tuple.typeAt (.union (.tuple [.never]) (.tuple [.nat, .string, .bool])) 1 = none
#guard Val.tupleAt? (Val.fibers []) 0 = none
#guard Val.tupleAt? (Val.fibers [⟨0⟩]) 0 = none
#guard !Val.hasTy (Val.fibers []) (.tuple [])
#guard termTy (nativeSignature []) [.tuple [.nat, .string, .bool]] (.tupleAt (.var 0) 1) = some .string
#guard termTy (nativeSignature []) [.list .nat] (.tupleAt (.var 0) 0) = none

example : ∃ out, Val.tupleAt? (.list [.nat 1, .str "x", .bool true]) 1 = some out ∧
    Val.hasTy out .string = true := Tuple.typeAt_typed (input := .tuple [.nat, .string, .bool]) rfl rfl

#print axioms Tuple.project.eq_cata
#print axioms Fits.tuple
#print axioms tupleItem_typed
#print axioms Tuple.project_typed
#print axioms Tuple.typeAt_typed
#print axioms NativeAtom.sound
#print axioms evalTerm_hasTy
#print axioms evalTerm_isSome
end Effect4.Test.TupleTyping
