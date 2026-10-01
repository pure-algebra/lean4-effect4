import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
Verifier of seat ORGANIZATION (2026-10-01), follow-up to `verify-CensusDeep.lean`.

Why does the census miss the case analyses that probe found, and are they recursive traversals
or one-level matches? For each named definition: the constants its matcher's value uses (is it
`Ty.casesOn`, or a sparse `casesOn` helper the census's `isFamilyRecursor` does not recognize),
and whether the definition refers to itself through compiler-made helpers (recursion).

Red controls: `Ty.closed` (census `structural`) must show a matcher over `Ty.casesOn` or a
`Ty.brecOn`; `Ty.sub` must show recursion through `Ty.sub._unary`.
-/

open Lean Elab Command Effect4.Laws.Auto

def showMatchers (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  let some (.defnInfo d) := env.find? n | logInfo m!"{n}: not a definition"; return
  let used := d.value.getUsedConstants
  let matchers := used.filter (fun c => Lean.Meta.isMatcherCore env c)
  let mut lines : Array String := #[]
  for m in matchers do
    match env.find? m with
    | some (.defnInfo md) =>
      let mu := md.value.getUsedConstants
      let cases := mu.filter (fun c => c.toString.endsWith "casesOn" ||
        (c.components.getLast!.toString.startsWith "_sparseCasesOn"))
      lines := lines.push s!"    matcher {m}: case constants {cases.toList}"
    | _ => pure ()
  let selfRef := used.contains n ||
    (used.filter (fun c => c.isInternalDetail)).any (fun h =>
      match env.find? h with
      | some (.defnInfo hd) => hd.value.getUsedConstants.any (fun c => c == n || c == h)
      | _ => false)
  let brec := used.filter (fun c => c.toString.endsWith "brecOn" || c.toString.endsWith ".rec")
  logInfo m!"{n}: direct-recursor {brec.toList}; self-reference through helpers {selfRef}\n{"\n".intercalate lines.toList}"

#eval show CommandElabM Unit from do
  for n in [``Effect4.Program.Ty.closed, ``Effect4.Program.Ty.sub, ``Effect4.Program.Ty.isFactor,
      ``Effect4.Program.Ty.isTagged, ``Effect4.Program.Ty.payloadOf, ``Effect4.Program.Ty.factors,
      ``Effect4.Program.Ty.taggedColumn, ``Effect4.Program.Ty.litRule, ``Effect4.Program.Ty.sameHead,
      ``Effect4.Program.Ty.topRule, ``Effect4.Program.Typed.FlatFits, ``Effect4.Program.Checker.exitOf?,
      ``Effect4.Program.Checker.listOf?, ``Effect4.Program.causeInputError?, ``Effect4.Program.fiberTy,
      ``Effect4.Program.externalValue, ``Effect4.Program.Decision.arms, ``Effect4.Codegen.Types.ofTy,
      ``Effect4.Schema.Codec.isSupported, ``Effect4.Program.isTagTy] do
    showMatchers n
