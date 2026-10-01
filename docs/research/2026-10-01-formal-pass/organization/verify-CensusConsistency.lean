import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
Verifier of seat ORGANIZATION (2026-10-01), probe for ORG-03/ORG-04: is the census consistent
about one-level matches?

`docs/core/traversal-census.md` §1 defines `structural` as "its own `match` or structural
recursion — a hand traversal", and §1's last sentence makes `structural + wf` the distance from
"every traversal is a fold or generated". On this toolchain a `match` compiles either through the
family's `casesOn` (the census sees it) or through a shared sparse `casesOn` helper named after
whichever definition first needed it (`Ty.infer._sparseCasesOn_13`), which the census's
`isFamilyRecursor` does not recognize (its prefix is not a family member).

For each family this probe recomputes the census's classes with the census's own helpers and
prints four counts over person-written takers:
  A  census `structural`/`wf` rows that recurse (a family `brecOn`/`rec`/`below` in the value);
  B  census `structural`/`wf` rows that do NOT recurse (one-level matches the census counts);
  C  rows the census prints `opaque`/`delegates` whose own matcher destructs the family through a
     sparse `casesOn` (one-level matches the census misses), outside generated modules;
  D  the same as C inside generated modules (would be `generated`).
B > 0 and C > 0 together mean the census counts some one-level matches and misses others,
depending only on how the compiler encoded the `match`.
-/

open Lean Elab Meta Command Effect4.Laws.Auto

def sparseFamilyCase (env : Environment) (family : Array Name) (matchers : Array Name) : Bool :=
  matchers.any fun m =>
    match env.find? m with
    | some (.defnInfo md) => md.value.getUsedConstants.any fun c =>
        "_sparseCasesOn".isPrefixOf c.getString! &&
          match env.find? c with
          | some (.defnInfo sd) => sd.value.getUsedConstants.any (isFamilyRecursor env family)
          | _ => false
    | _ => false

syntax (name := censusConsistency) "#census_consistency " ident : command

@[command_elab censusConsistency] def elabCensusConsistency : CommandElab := fun stx => do
  let root := stx[1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  let defs := definitionsUnder env `Effect4
  let folds := foldsOf family defs
  let generated ← generatedModules
  let mut takers : Array (Name × Name × Expr) := #[]
  for (n, m, type, value) in defs do
    if folds.contains n then continue
    if (← liftTermElabM (domainOf family type)).isSome then takers := takers.push (n, m, value)
  let mut a : Array Name := #[]
  let mut b : Array Name := #[]
  let mut c : Array Name := #[]
  let mut d : Nat := 0
  for (n, m, value) in takers do
    let used := value.getUsedConstants
    let algebras := algebrasIn env folds value #[]
    let recurses := used.any (isFamilyRecursor env family) || matchesFamily env family used
    let inst ← liftCoreM (do pure ((← isInstance n) || (← isInstance n.getPrefix)))
    if inst then continue
    if !algebras.isEmpty then continue
    if recurses then
      if generated.contains m then continue
      let recursive := used.any fun x => family.contains x.getPrefix &&
        ["brecOn", "rec", "below", "binductionOn"].any (fun s => s.isPrefixOf x.getString!)
      if recursive then a := a.push n else b := b.push n
    else
      let matchers := used.filter (fun x => isMatcherCore env x)
      if sparseFamilyCase env family matchers then
        if generated.contains m then d := d + 1 else c := c.push n
  logInfo m!"#census_consistency {root}: A (counted, recursive) {a.size}; B (counted, one-level) {b.size}; C (missed one-level, hand modules) {c.size}; D (missed, generated modules) {d}\nB: {(b.qsort (·.toString < ·.toString)).toList}\nC: {(c.qsort (·.toString < ·.toString)).toList}"

#census_consistency Effect4.Program.Ty
#census_consistency Effect4.Program.Eff
#census_consistency Effect4.Program.Term
#census_consistency Effect4.Representation
#census_consistency Effect4.Store.Val
