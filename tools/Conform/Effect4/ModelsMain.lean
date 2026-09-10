import Lean
import Conform.Effect4.Membership
import Conform.Layout.Check

/-!
# Conform.Effect4.ModelsMain — the composition and membership report

    lake env lean -M4096 --run tools/Conform/Effect4/ModelsMain.lean <outdir>

One `conform-report-v1` for the composed models: a row per plan (does it resolve against the
`Store.Image` library, and with which laws), a row per proved law of the four models, and the
obligations `Conform.Model.resolve` and `Conform.Effect4.Membership` raise.

The law rows are the only rows in this seat's reports whose evidence is `proved`: each names a
kernel-checked theorem in `Conform.Effect4.Models` or `.Membership` whose axioms the module
prints at elaboration. Nothing here re-derives them; the row is the receipt of a theorem that
exists, and a reader checks it by name.
-/

open Lean
open Conform Conform.Layout Conform.Effect4

namespace Conform.Effect4.ModelsReport

/-- The theorems this seat proved, as report rows. The pair `(subject, theorem name)` is the
whole content: a row that names a theorem that does not exist fails to elaborate this file. -/
def provedLaws : List (String × String × String) :=
  [ ("Effect4.Program.Ty", "ofVal_toVal", "Conform.Effect4.Models.tyImage_ofVal_toVal")
  , ("Effect4.Program.Ty", "ofVal_exact", "Conform.Effect4.Models.tyImage_ofVal_exact")
  , ("Effect4.Program.Ty", "HandleFree", "Conform.Effect4.Models.tyImage_handleFree")
  , ("Requirement", "ofVal_toVal", "Conform.Effect4.Models.requirementImage_ofVal_toVal")
  , ("Requirement", "ofVal_exact", "Conform.Effect4.Models.requirementImage_ofVal_exact")
  , ("Option (Option Nat)", "ofVal_toVal", "Conform.Effect4.Models.optOptNat_ofVal_toVal")
  , ("Option (Option Nat)", "ofVal_exact", "Conform.Effect4.Models.optOptNat_ofVal_exact")
  , ("Option (Option Nat)", "toVal = canonical",
      "Conform.Effect4.Models.optOptNat_toVal_eq_canonical")
  , ("Option (Option Nat)", "nested distinct", "Conform.Effect4.Models.optOptNat_nested_distinct")
  , ("Option (Option Nat)", "canonical nested distinct, via the model",
      "Conform.Effect4.Models.canonical_nested_distinct_via_model")
  , ("Option (Option Ty)", "nested distinct", "Conform.Effect4.Models.optOptTy_nested_distinct")
  , ("List (Option Ty)", "ofVal_toVal", "Conform.Effect4.Models.listOptTy_ofVal_toVal")
  , ("List (Option Ty)", "ofVal_exact", "Conform.Effect4.Models.listOptTy_ofVal_exact")
  , ("List (Option Ty)", "HandleFree", "Conform.Effect4.Models.listOptTy_handleFree")
  , ("GenTy", "ofVal_toVal", "Conform.Effect4.Models.genTy_ofVal_toVal")
  , ("GenTy", "ofVal_exact", "Conform.Effect4.Models.genTy_ofVal_exact")
  , ("GenTy", "joinAnswer none none = some none",
      "Conform.Effect4.Models.joinAnswer_none_none")
  , ("EffTy", "ofVal_toVal", "Conform.Effect4.Models.effTy_ofVal_toVal")
  , ("EffTy", "ofVal_exact", "Conform.Effect4.Models.effTy_ofVal_exact")
  , ("Image.nat", "hasTy .nat", "Conform.Effect4.Membership.hasTy_nat")
  , ("Image.bool", "hasTy .bool", "Conform.Effect4.Membership.hasTy_bool")
  , ("Image.string", "hasTy .string", "Conform.Effect4.Membership.hasTy_string")
  , ("Image.unit", "hasTy .unit", "Conform.Effect4.Membership.hasTy_unit")
  , ("Image.option", "hasTy .option, under the element's", "Conform.Effect4.Membership.hasTy_option")
  , ("Image.list", "hasTy .list, under the element's", "Conform.Effect4.Membership.hasTy_list")
  , ("Membership.pairTuple", "hasTy .prod, under both elements'",
      "Conform.Effect4.Membership.hasTy_pairTuple")
  , ("Option (Option Nat)", "hasTy .option (.option .nat)",
      "Conform.Effect4.Membership.hasTy_optOptNat")
  , ("Image.pair", "never inhabits .prod", "Conform.Effect4.Membership.pair_never_hasTy_prod")
  , ("Ty.never", "uninhabited by hasTy", "Conform.Effect4.Membership.hasTy_never_false")
  , ("Ty.int", "uninhabited by hasTy", "Conform.Effect4.Membership.hasTy_int_false")
  , ("Ty.except", "uninhabited by hasTy", "Conform.Effect4.Membership.hasTy_except_false")
  , ("Ty.causeOf", "uninhabited by hasTy", "Conform.Effect4.Membership.hasTy_causeOf_false") ]

/-- Every theorem named above exists in the environment with the type the module gave it; a
missing name is an `unresolved` row, never a silent pass. -/
def lawRows (env : Lean.Environment) : Array Row :=
  provedLaws.toArray.map fun (subject, law, thm) =>
    let subj : Subject := { kind := "model", path := ["Store.Image", subject, law] }
    match Lean.Environment.find? env thm.toName with
    | some _ => Row.pass "representation.law" subj .proved
        s!"{law}: {thm}" (Json.mkObj [("theorem", Json.str thm)])
    | none => Row.unresolved "representation.law" subj
        s!"the report names {thm}, and the environment has no such declaration"

def planRows : Array Row × Array Obligation := Id.run do
  let mut rows : Array Row := #[]
  let mut obs : Array Obligation := #[]
  for (label, plan) in Models.plans ++ [("negative control: a sum", Models.sumPlan)] do
    let subj : Subject := { kind := "plan", path := ["Store.Image", label] }
    let (res, os) := Conform.Model.resolve Models.imageLibrary Models.elementEnv
      ["Store.Image", label] plan
    obs := obs ++ os
    if os.isEmpty then
      rows := rows.push (Row.pass "representation.compose" subj .tested
        s!"{res.expression}, carrying {", ".intercalate res.laws}"
        (Json.mkObj [("expression", Json.str res.expression),
          ("laws", Json.arr (res.laws.toArray.map Json.str))]))
    else
      rows := rows.push (Row.refused "representation.compose" subj
        s!"{os.size} obligation(s): {"; ".intercalate (os.toList.map (·.statement))}"
        (Json.mkObj [("expression", Json.str res.expression)]))
  return (rows, obs)

end Conform.Effect4.ModelsReport

def main (argv : List String) : IO UInt32 := do
  Lean.initSearchPath (← Lean.findSysroot)
  let outDir : System.FilePath := System.FilePath.mk ((argv.drop 0).headD "/tmp/conform-layout")
  IO.FS.createDirAll outDir
  let env ← Lean.importModules #[{ module := `Conform.Effect4.Membership }] {} 0
  let (planR, planObs) := Conform.Effect4.ModelsReport.planRows
  let laws := Conform.Effect4.ModelsReport.lawRows env
  let obs := planObs ++ Conform.Effect4.Membership.obligations
  let report : Conform.Report :=
    { tool := "conform.model.compose"
      pins := [⟨"lean", "4.33.1"⟩, ⟨"library", "Store.Image"⟩]
      expected := planR.size + laws.size
      rows := planR ++ laws }
  let registry := Conform.Model.registry ++ Conform.Layout.registry
  match report.sorted.withObligations registry obs with
  | .ok j => IO.FS.writeFile (outDir / "models.json") (j.pretty ++ "\n")
  | .error e => IO.eprintln e
  IO.eprintln report.sorted.render
  IO.eprintln s!"obligations: {obs.size}"
  for o in obs do IO.eprintln s!"  {o.kind} {o.subject.render}: {o.statement}"
  return report.sorted.exitCode
