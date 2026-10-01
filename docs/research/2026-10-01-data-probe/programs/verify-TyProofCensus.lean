import Effect4
import Effect4.Laws

/-! Verifier of seat PROGRAMS (2026-10-01): the proof half of the bill of a `Ty` append, read
from the compiled environment rather than by a grep script (PROG-D6, PROG-D7). For every named
theorem of an `Effect4.*` module, it reports whether the proof term uses `Ty`'s recursor
(`Ty.rec`/`recOn`: the `induction` tactic; `Ty.brecOn`/`binductionOn`: structural recursion in a
theorem) and whether it cases on a `Ty` (`Ty.casesOn` directly, or through one of its own
matchers that does). Generated helpers (`.match_`, `._proof_`, `.eq_`, `.induct`, ...) are not
counted as theorems of their own. Scratch, not in the tree; prints only. -/

open Lean Elab Command

namespace Verify.TyProofCensus

def recNames : List Name :=
  [`Effect4.Program.Ty.rec, `Effect4.Program.Ty.recOn, `Effect4.Program.Ty.brecOn,
   `Effect4.Program.Ty.binductionOn]

def casesName : Name := `Effect4.Program.Ty.casesOn

def helperish (n : Name) : Bool :=
  let s := n.toString
  ["._", ".match_", ".proof_", ".eq_", ".induct", "_sunfold", ".splitter", "_unfold", ".mutual_induct",
   ".fun_cases", ".eq_def"].any (fun p => (s.splitOn p).length > 1)

/-- Does this constant's value case on `Ty`, directly or through a matcher it owns or calls? -/
def casesOnTy (env : Environment) (value : Expr) : Bool :=
  let used := value.getUsedConstants
  used.contains casesName ||
    used.any fun c =>
      ((c.toString.splitOn ".match_").length > 1) &&
        match env.find? c with
        | some ci => match ci.value? with
          | some v => v.getUsedConstants.contains casesName
          | none => false
        | none => false

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut rows : Array String := #[]
  let mut recCount : Nat := 0
  let mut casesCount : Nat := 0
  for (n, ci) in env.constants.toList do
    if let .thmInfo t := ci then
      let user := (privateToUserName? n).getD n
      if (`Effect4).isPrefixOf user && !helperish user then
        let modName := match env.getModuleIdxFor? n with
          | some i => (env.header.moduleNames[i.toNat]?).getD `unknown
          | none => `unknown
        let used := t.value.getUsedConstants
        let isRec := used.any (recNames.contains ·)
        let isCases := casesOnTy env t.value
        if isRec then recCount := recCount + 1
        if isCases && !isRec then casesCount := casesCount + 1
        if isRec || isCases then
          rows := rows.push s!"{modName}\t{user}{if user != n then " (private)" else ""}\t{if isRec then "rec" else "-"}\t{if isCases then "cases" else "-"}"
  logInfo m!"theorems over Ty: {recCount} by Ty's recursor (induction or structural recursion); {casesCount} more by case analysis only"
  for r in rows.qsort (· < ·) do
    logInfo r

end Verify.TyProofCensus
