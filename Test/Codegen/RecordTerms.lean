import Effect4.Laws.Codegen.ReadLeaf

/-!
Record term controls for the existing scope-only print/read judgment.
The finite cases include unsupported declarations, unequal input lists, and legacy atom names.
These controls concern structural TypeScript expressions, not target execution.
-/

namespace Effect4.Test.RecordTermsCodegen
open Effect4.Program

def person : Term := .record [("nickname", true, .option .undefined), ("id", false, .nat)]
  ["id"] (.cons (.lit (.nat 7)) .nil)

def raw : Term := .record [("open", true, .var 99), ("open", false, .nat)]
  ["supplied", "extra"] (.cons (.lit .unit) .nil)

def nested : Term := .recordSet
  (.record [("__proto__", true, .string), ("person", false,
    .record [("nickname", true, .option .undefined), ("id", false, .nat)])]
    ["person"] (.cons person .nil))
  "__proto__" (.lit (.str "owned"))

#guard readTerm 0 (printTerm person) == .ok person
#guard readTerm 0 (printTerm raw) == .ok raw
#guard readTerm 0 (printTerm nested) == .ok nested
#guard readTerm 0 (printTerm (.field .required person "id")) == .ok (.field .required person "id")
#guard readTerm 0 (printTerm (.field .optional person "nickname")) ==
  .ok (.field .optional person "nickname")
#guard readTerm 1 (printTerm (.recordSet (.var 0) "a-b" (.lit (.nat 9)))) ==
  .ok (.recordSet (.var 0) "a-b" (.lit (.nat 9)))
#guard (match readTerm 0 (printTerm (.field .optional (.var 0) "nickname")) with
  | .error _ => true
  | .ok _ => false)

-- Generic wrapper heads leave existing arbitrary atom calls recoverable.
#guard readTerm 0 (printTerm (.app "recordValue" .nil)) == .ok (.app "recordValue" .nil)
#guard readTerm 0 (printTerm (.app "recordRaw" .nil)) == .ok (.app "recordRaw" .nil)
#guard readTerm 0 (printTerm (.app "recordOptional" .nil)) == .ok (.app "recordOptional" .nil)
#guard readTerm 0 (printTerm (.app "recordSet" .nil)) == .ok (.app "recordSet" .nil)
#guard Effect4.Codegen.Record.helperNames.all fun name => !exportNameSafe name
#guard exportNameSafe "main"

def controlRow : Effect4.Program.Row :=
  { name := "control", spelling := "custom", kind := .program,
    request := .unit, answer := .unit, cite := "finite name control" }

#guard rowNamesSafe controlRow
#guard Effect4.Codegen.Record.helperNames.all fun name =>
  !rowNamesSafe { controlRow with spelling := name }
#guard Effect4.Codegen.Record.helperNames.all fun name =>
  !rowNamesSafe { controlRow with trailing := [name] }

example (n : Nat) (term : Term) (h : term.scoped n = true) :
    readTerm n (printTerm term) = .ok term := readTerm_printTerm term h

example (n : Nat) (x : TypeScript.Expr) (term : Term) (h : readTerm n x = .ok term) :
    printTerm term = x := readTerm_exact x h

end Effect4.Test.RecordTermsCodegen

#print axioms Effect4.Program.readTerm
#print axioms Effect4.Program.readTerm_printTerm
#print axioms Effect4.Program.readTerm_exact
#print axioms Effect4.Program.readTerms_printTerms
#print axioms Effect4.Program.readTerms_exact
