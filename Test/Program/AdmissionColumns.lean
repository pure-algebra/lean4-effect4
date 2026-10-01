import Effect4.Laws.Run
import Effect4.Laws.Program.CheckedTyping

/-!
# Admission's table check and column check (TY-05, rows 127 and 149)

**TY-05.** `Table.lawful` and `Table.checkLawful` decide one condition
(`Table.checkLawful_eq_none_iff`, proved in `Program/Admission.lean`), so admission takes its
refusal from the located check alone and no key is invented for a failure it does not explain.
The certificate theorems that unfold `admitProgram` (`admitProgram_eq_ok`,
`admitProgram_certificate`) read the same fact.
-/

set_option autoImplicit false

namespace Test.Program.AdmissionColumns

open Effect4 Effect4.Program

/-- A host row: `Host.<name>`, a `nat` request, the given answer and error columns. -/
def row (name : String) (answer : Ty) (error : Ty := .never) (request : Ty := .nat) : Row :=
  { name, spelling := "Host." ++ name, kind := .async, registration := .external,
    request, answer, error, cite := "" }

/-- Two rows under one key. -/
def dupTable : RowTable := [row "query" .nat, row "query" .string]

-- tested: the located refusal names the repeated key, and admission reports it
#guard Table.lawful dupTable == false
#guard Table.checkLawful dupTable == some (.duplicateKey (rowKey (row "query" .nat)))
#guard match admitProgram (.succeed (.lit (.nat 0))) dupTable with
  | .error (.duplicateKey k) => k == rowKey (row "query" .nat)
  | _ => false

/-- TY-05 on a table: `lawful` refuses and `checkLawful` locates (proved, by the theorem). -/
theorem dupTable_located : Table.checkLawful dupTable ≠ none :=
  Table.checkLawful_of_not_lawful dupTable (by decide)

#print axioms Effect4.Program.Table.findDup_eq_none_iff
#print axioms Effect4.Program.Table.lawful_eq_true_iff
#print axioms Effect4.Program.Table.checkLawful_eq_none_iff
#print axioms Effect4.Program.Table.checkLawful_of_not_lawful
#print axioms Effect4.Program.admitProgram
#print axioms Effect4.Program.admitProgram_eq_ok
#print axioms Effect4.Run.admitProgram_certificate
#print axioms dupTable_located

end Test.Program.AdmissionColumns
