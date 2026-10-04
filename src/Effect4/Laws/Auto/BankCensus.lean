import Aesop
import Effect4.Laws.Auto.RuleSets

/-!
# Laws.Auto.BankCensus — what each rule bank holds, and who names it

`#bank_census "src" "Test"` reports, for every declared `Effect4.*` aesop rule set: its aesop
rules (`BaseRuleSet.ruleNames`), its simp lemmas (the bank's `SimpTheorems`), and how many
`rule_sets := [...]` clauses under each directory name it. A bank with no rule is empty; a bank no
clause of the first directory names is unused by the library; the second count shows whether its
`Test` fixtures exist (decisions row 65: a bank lands with a fixture that omits its clause).

A measuring instrument, never a gate (decisions row 34): it changes nothing and fails on nothing.
Clauses are read from the source text, so a clause inside a comment is counted too. It answers the
reference scout's bank lint (`docs/research/2026-10-04-reference-scout/automation.md`,
recommendation 4, its sound half); `make bank-census` runs it.
-/

open Lean Elab Command

namespace Effect4.Laws.Auto

/-- The bank names a `rule_sets := [A, B]` clause lists, read from source text. -/
def ruleSetClauses (text : String) : Array Name := Id.run do
  let mut out : Array Name := #[]
  for part in (text.splitOn "rule_sets := [").drop 1 do
    let inside := (part.splitOn "]").headD ""
    for item in inside.splitOn "," do
      let n := item.trimAscii.toString
      unless n.isEmpty do out := out.push n.toName
  return out

/-- Every bank name the `.lean` files under `dir` name in a clause, with multiplicity. -/
def clausesUnder (dir : System.FilePath) : IO (Array Name) := do
  let mut out : Array Name := #[]
  for f in ← dir.walkDir do
    if f.extension == some "lean" then
      out := out ++ ruleSetClauses (← IO.FS.readFile f)
  return out

syntax (name := bankCensus) "#bank_census " str str : command

@[command_elab bankCensus] def elabBankCensus : CommandElab := fun stx => do
  let some library := stx[1].isStrLit? | throwError "bank census: expected a directory"
  let some tests := stx[2].isStrLit? | throwError "bank census: expected a directory"
  let inLibrary ← clausesUnder library
  let inTests ← clausesUnder tests
  let banks ← liftCoreM Aesop.Frontend.getDeclaredGlobalRuleSets
  let mut rows : Array String := #[]
  for (name, rs, _, _) in banks.qsort (fun a b => a.1.toString < b.1.toString) do
    unless (`Effect4).isPrefixOf name do continue
    let rules := rs.ruleNames.foldl (fun n _ v => n + v.size) 0
    let simps := rs.simpTheorems.lemmaNames.fold (fun n _ => n + 1) 0
    let named := (inLibrary.filter (· == name)).size
    let fixtures := (inTests.filter (· == name)).size
    let flag := if rules + simps == 0 then "  (empty)"
      else if named == 0 then "  (unused by the library)" else ""
    rows := rows.push s!"{name}\t{rules} rules\t{simps} simp lemmas\t{named} library clauses\t{fixtures} test clauses{flag}"
  logInfo m!"bank census\n{"\n".intercalate rows.toList}"

end Effect4.Laws.Auto
