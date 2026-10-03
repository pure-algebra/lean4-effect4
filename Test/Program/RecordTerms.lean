import Effect4.Program.Eff

/-! Finite controls for the record term signature in decisions row 195.
The first stage checks raw evaluation, stored modes and variable weakening.
Typing and the semantic bridge are checked after the generated fold is restored. -/

namespace Effect4.Test.RecordTerms
open Effect4.Program Effect4.Machine

def personFields : List (String × Bool × Ty) :=
  [("name", false, .string), ("nickname", true, .string)]

def person : Term := .record personFields ["name"] (.cons (.lit (.str "Ada")) .nil)

#guard evalTerm [] person = some (Record.frame [("name", .str "Ada")])
#guard evalTerm [] (.field .required person "name") = some (.str "Ada")
#guard evalTerm [] (.field .optional person "name") = some (Store.Val.some (.str "Ada"))
#guard evalTerm [] (.field .optional person "nickname") = some Store.Val.none
#guard evalTerm [] (.field .required person "nickname") = none
#guard evalTerm [] (.record [] ["z", "a"]
  (.cons (.lit (.nat 7)) (.cons (.lit (.str "Ada")) .nil))) =
  some (Record.frame [("a", .str "Ada"), ("z", .nat 7)])
#guard evalTerm [] (.record [] ["name"] .nil) = none
#guard evalTerm [] (.record [] ["name", "name"]
  (.cons (.lit (.nat 1)) (.cons (.lit (.nat 2)) .nil))) = none
#guard evalTerm [] (.record [] [] (.cons (.lit .unit) .nil)) = none
#guard evalTerm [] (.recordSet person "nickname" (.lit (.str "A"))) =
  some (Record.frame [("name", .str "Ada"), ("nickname", .str "A")])
#guard evalTerm [] (.recordSet person "name" (.lit (.nat 4))) =
  some (Record.frame [("name", .nat 4)])
#guard evalTerm [Record.frame [("nickname", Store.Val.none)]]
  (.field .optional (.var 0) "nickname") = some (Store.Val.some Store.Val.none)
#guard evalTerm [Record.frame [("nickname", .unit)]]
  (.field .optional (.var 0) "nickname") = some (Store.Val.some .unit)

#guard person.scoped 0
#guard !(Term.record personFields ["name"] (.cons (.var 0) .nil)).scoped 0
#guard (Term.field .optional (.var 0) "name").scoped 1
#guard !(Term.recordSet (.var 0) "name" (.var 1)).scoped 1
#guard Term.weaken 0 (.record personFields ["name"] (.cons (.var 0) .nil)) =
  .record personFields ["name"] (.cons (.var 1) .nil)
#guard Term.weaken 1 (.recordSet (.var 0) "name" (.field .optional (.var 1) "nickname")) =
  .recordSet (.var 0) "name" (.field .optional (.var 2) "nickname")

#print axioms evalTerm
#print axioms Term.weaken_eq_lit
#print axioms instDecidableEqTerm

end Effect4.Test.RecordTerms
