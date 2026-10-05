import Effect4
import Effect4.Laws
import OCaml5
import Test.All
import Lean

open Lean Elab Command

/-- Every theorem of the environment whose declaration range meets a line the seat's commits own,
with its axioms. Input: `changed-lines.json` (module ↦ lines), from `git blame`. -/
elab "#axioms_of_changed " path:str : command => do
  let text ← IO.FS.readFile path.getString
  let json ← match Json.parse text with
    | .ok j => pure j
    | .error e => throwError e
  let obj ← match json.getObj? with
    | .ok o => pure o
    | .error e => throwError e
  let mut table : Std.HashMap Name (Std.HashSet Nat) := {}
  for (k, v) in obj.toList do
    let arr ← match v.getArr? with
      | .ok a => pure a
      | .error e => throwError e
    let mut set : Std.HashSet Nat := {}
    for x in arr do
      match x.getNat? with
      | .ok n => set := set.insert n
      | .error e => throwError e
    table := table.insert k.toName set
  let env ← getEnv
  let mut rows : Array (String × String × Nat × String) := #[]
  for (name, info) in env.constants.toList do
    unless info matches .thmInfo _ do continue
    let some idx := env.getModuleIdxFor? name | continue
    let modName := env.header.moduleNames[idx.toNat]!
    let some lines := table[modName]? | continue
    let some ranges ← liftCoreM (findDeclarationRanges? name) | continue
    let first := ranges.range.pos.line
    let last := ranges.range.endPos.line
    if (List.range (last - first + 1)).any (fun i => lines.contains (first + i)) then
      let axioms ← liftCoreM (collectAxioms name)
      let shown := (axioms.toList.map toString).mergeSort (· ≤ ·)
      rows := rows.push (toString modName, toString name, first, toString shown)
  let sorted := rows.qsort (fun a b => a.1 < b.1 || (a.1 == b.1 && a.2.2.1 < b.2.2.1))
  let mut out := ""
  for (m, n, l, a) in sorted do
    out := out ++ s!"{m}\t{l}\t{n}\t{a}\n"
  IO.FS.writeFile (path.getString ++ ".axioms.tsv") out
  let kinds := (sorted.toList.map (·.2.2.2)).eraseDups
  logInfo m!"{sorted.size} theorems; axiom sets: {kinds}"

#axioms_of_changed "docs/research/2026-10-04-seat-T3b/phase2/changed-lines.json"
