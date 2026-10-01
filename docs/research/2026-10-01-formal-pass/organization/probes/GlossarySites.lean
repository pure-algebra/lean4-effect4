import Effect4
import Effect4.Laws

/-!
Seat ORGANIZATION probe (2026-10-01): definition sites for the formal glossary. For each short
name, every `Effect4.*` (and `ProofGraph.*`) declaration whose last name component is that name:
full name, kind, module, and declaration line. Nothing is asserted; a name with two or more
sites is a name a reader of the system map can resolve two ways.
-/

open Lean Elab Command

def shortNames : List String := [
  "Eff", "cataFam", "hom_eq_cata_eff", "Signature", "Ty", "Fits", "FitsExit", "FitsCause", "World",
  "TypedProg", "TypedState", "RReachable", "denote", "denoteR", "denoteB", "iter", "Beh", "Obs",
  "FairTape", "replay", "replayR", "replay_unique", "journal_replays", "RunMachine", "Cmd", "Command",
  "Projects", "Refines", "Canonical", "printT", "read", "read_print", "read_exact",
  "Representation", "RowTable", "Row", "HostSpec", "LawfulHostSpec", "HostSession", "Session",
  "ForkRecord", "ExitOk", "NoShapeDefect", "LayerTerm", "build", "Typed", "StepKeeps",
  "DecisionLift", "BookMeans", "GuardState", "Reachable", "Arena", "Image", "ProgramSource",
  "AdmittedProgram", "TypedProgram", "HasTy", "check", "explain", "Straight", "Looped",
  "run_eq_meaning", "run_eq_ref", "loopAgreement", "Obligation", "WorldOrder", "Agrees"]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mods := env.header.moduleNames
  let mut out : Array String := #[]
  for s in shortNames do
    let mut hits : Array String := #[]
    for (n, ci) in env.constants.toList do
      if n.isInternal then continue
      let top := n.getRoot.toString
      unless top == "Effect4" || top == "ProofGraph" do continue
      if n.components.getLast!.toString == s then
        let kind := match ci with
          | .defnInfo _ => "def" | .thmInfo _ => "theorem" | .inductInfo _ => "inductive"
          | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .opaqueInfo _ => "opaque"
          | .axiomInfo _ => "axiom" | .quotInfo _ => "quot"
        if kind == "ctor" || kind == "rec" then continue
        let m := match env.getModuleIdxFor? n with | some i => mods[i.toNat]!.toString | none => "?"
        let line := match (← findDeclarationRanges? n) with
          | some r => toString r.range.pos.line | none => "?"
        hits := hits.push s!"{kind} {n} @ {m}:{line}"
    out := out.push s!"{s} ({hits.size}): {"; ".intercalate (hits.qsort (· < ·)).toList}"
  logInfo m!"{"\n".intercalate out.toList}"
