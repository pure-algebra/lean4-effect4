import Effect4.Program.Eff

/-! Finite controls for decisions rows 159 and 197.
They check raw tuple evaluation, exact indices and variable weakening.
Typing and target execution are separate obligations. -/

namespace Effect4.Test.TupleTerms
open Effect4.Program Effect4.Machine

private def triple : Term := .app "tuple"
  (.cons (.lit (.nat 1)) (.cons (.lit (.str "x")) (.cons (.lit (.bool true)) .nil)))

#guard NativeAtom.tuple.arity = none
#guard NativeAtom.tuple.constGeneric
#guard NativeAtom.ofName? "tuple" = some .tuple
#guard nativeAtom "tuple" [] = some (.list [])
#guard nativeAtom "tuple" [.nat 1] = some (.list [.nat 1])
#guard nativeAtom "tuple" [.nat 1, .str "x"] = some (.list [.nat 1, .str "x"])
#guard evalTerm [] triple = some (.list [.nat 1, .str "x", .bool true])
#guard evalTerm [] (.tupleAt triple 0) = some (.nat 1)
#guard evalTerm [] (.tupleAt triple 1) = some (.str "x")
#guard evalTerm [] (.tupleAt triple 2) = some (.bool true)
#guard evalTerm [] (.tupleAt triple 3) = none
#guard evalTerm [] (.tupleAt triple 100000000000000000000000) = none
#guard evalTerm [] (.tupleAt (.app "tuple" .nil) 0) = none
#guard evalTerm [] (.tupleAt (.lit (.nat 3)) 0) = none
#guard evalTerm [] (.tupleAt (.var 0) 0) = none
#guard evalTerm [.list [.list [.nat 1, .nat 2], .nat 3]] (.tupleAt (.var 0) 0) =
  some (.list [.nat 1, .nat 2])
#guard (Term.tupleAt triple 999999999999999999999).scoped 0
#guard !(Term.tupleAt (.var 0) 0).scoped 0
#guard (Term.tupleAt (.var 0) 0).scoped 1
#guard Term.weaken 0 (.tupleAt (.var 0) 999999999999999999999) =
  .tupleAt (.var 1) 999999999999999999999

#print axioms evalTerm
#print axioms Term.weaken_eq_lit
#print axioms NativeAtom.ofName?_name
#print axioms instDecidableEqTerm

end Effect4.Test.TupleTerms
