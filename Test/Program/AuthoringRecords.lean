import Effect4.Laws.Program.Authoring.Records

/-! Finite reconstruction controls for the record scope-reader builders.
A successful builder resolves names; it does not certify formation or typing. -/

namespace Effect4.Test.AuthoringRecords
open Effect4.Program

def fields : List (String × Bool × Ty) :=
  [("name", false, .string), ("nickname", true, .string)]
def source : Authoring.TermSrc := Authoring.record fields [("name", Authoring.var "name")]

#guard source { names := ["trace", "name"] } [2] =
  .ok (.record fields ["name"] (.cons (.var 1) .nil))
#guard source { names := ["name"] } [2] =
  .ok (.record fields ["name"] (.cons (.var 0) .nil))
#guard source { names := ["name", "name"] } [2] =
  .ok (.record fields ["name"] (.cons (.var 1) .nil))
#guard source { names := [] } [2] = .error ⟨[2], .unbound "name"⟩
#guard Authoring.field (Authoring.var "person") "name" { names := ["person"] } [] =
  .ok (.field .required (.var 0) "name")
#guard Authoring.optionalField (Authoring.var "person") "nickname" { names := ["person"] } [] =
  .ok (.field .optional (.var 0) "nickname")
#guard Authoring.recordSet (Authoring.var "person") "nickname" (Authoring.var "alias")
  { names := ["person", "alias"] } [3] = .ok (.recordSet (.var 0) "nickname" (.var 1))
#guard Authoring.recordSet (Authoring.var "missingTarget") "nickname" (Authoring.var "missingValue") {} [3] =
  .error ⟨[3], .unbound "missingTarget"⟩
#guard Authoring.recordSet (Authoring.unit) "nickname" (Authoring.var "missingValue") {} [3] =
  .error ⟨[3], .unbound "missingValue"⟩

-- Scope-only reconstruction leaves malformed declarations for the ordinary checker.
#guard Authoring.record [("x", true, .nat), ("x", true, .string)] [] {} [] =
  .ok (.record [("x", true, .nat), ("x", true, .string)] [] .nil)

example : source.Scoped := by
  apply Authoring.record_scoped
  intro entry member
  simp only [List.mem_singleton] at member
  subst entry
  exact Authoring.var_scoped "name"

example : (Authoring.field (Authoring.var "person") "name").Scoped := Authoring.field_scoped (Authoring.var_scoped _) _
example : (Authoring.optionalField (Authoring.var "person") "nickname").Scoped :=
  Authoring.optionalField_scoped (Authoring.var_scoped _) _
example : (Authoring.recordSet (Authoring.var "person") "nickname" (Authoring.var "alias")).Scoped :=
  Authoring.recordSet_scoped (Authoring.var_scoped _) (Authoring.var_scoped _) _

end Effect4.Test.AuthoringRecords
