import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Traversals

/-!
Seat F probe (2026-10-01, landing item 1): what does each census taker's *own code* do — its
value plus the compiler-made helpers it reaches (`_unary`, `_mutual`, `_f`, `match_n`,
`_sparseCasesOn_n`, `_proof_n`; never a person-written definition, never the family's own
recursors) — and where would two candidate recursion rules disagree?

  (i)  recursion over the family: a family `brecOn`/`binductionOn`/`below`, or a well-founded
       fixpoint whose measure reads a family member's `sizeOf`;
  (ii) any recursion: any `brecOn`, any well-founded fixpoint, or a self-reference.

Rows printed: every taker the unchanged census would print `opaque`/`delegates`/`structural`/`wf`
whose own code destructs the family, with both verdicts. Takers are read with the census's
own `definitionsUnder`, private definitions admitted under their user name.

Red controls: `Ty.sub` must show a wf fixpoint over a `Ty` measure; `Ty.isFactor` a family case
through a sparse helper and no recursion; `Ty.closed` a family `brecOn`; `ofNormalized`
(private) a family `brecOn`; `runStmts` a wf fixpoint whose measure is not the family's.
-/

open Lean Elab Meta Command Effect4.Laws.Auto

def userOf (n : Name) : Name := (privateToUserName? n).getD n

/-- A constant the compiler made for some definition (not a person-written one). -/
def isMadeHelper (env : Environment) (c : Name) : Bool :=
  isMatcherCore env c || (userOf c).isInternalDetail

/-- Follow compiler-made helpers from a value; stop at person-written definitions and at the
family's recursors. Returns every constant reached (helpers' own uses included). -/
def ownReach (env : Environment) (value : Expr) : NameSet := Id.run do
  let mut seen : NameSet := {}
  let mut stack := value.getUsedConstants.toList
  let mut steps := 0
  while steps < 100000 do
    steps := steps + 1
    match stack with
    | [] => break
    | c :: rest =>
      stack := rest
      if seen.contains c then continue
      seen := seen.insert c
      if isMadeHelper env c then
        match env.find? c with
        | some (.defnInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | some (.opaqueInfo d) => stack := d.value.getUsedConstants.toList ++ stack
        | _ => pure ()
  return seen

def isSizeOfOf (family : Array Name) (c : Name) : Bool :=
  family.contains c.getPrefix && "_sizeOf".isPrefixOf c.getString!

syntax (name := ownCode) "#own_code " ident : command

@[command_elab ownCode] def elabOwnCode : CommandElab := fun stx => do
  let root := stx[1].getId
  let family ← liftCoreM (familyOf root)
  let env ← getEnv
  -- takers, private definitions admitted under their user name
  let mut defs : Array (Name × Name × Expr × Expr) := #[]
  for (name, info) in env.constants.map₁.toList do
    let u := userOf name
    let ok := !(u.isInternalDetail || u.isInternal || isMatcherCore env name ||
      isAuxRecursor env name || isCompilerHelper u)
    if !ok then continue
    let tv : Option (Expr × Expr) := match info with
      | .defnInfo d => some (d.type, d.value)
      | .opaqueInfo d => some (d.type, d.value)
      | _ => none
    if let some (t, v) := tv then
      if let some m := moduleOf env name then
        if (`Effect4).isPrefixOf m then defs := defs.push (name, m, t, v)
  let folds := foldsOf family defs
  let mut lines : Array String := #[]
  let mut counts : Array (String × Nat) := #[]
  let bump (cs : Array (String × Nat)) (k : String) : Array (String × Nat) :=
    match cs.findIdx? (·.1 == k) with
    | some i => cs.modify i fun (a, b) => (a, b + 1)
    | none => cs.push (k, 1)
  for (n, m, type, value) in defs do
    if folds.contains n then continue
    if (← liftTermElabM (domainOf family type)).isNone then continue
    if !(algebrasIn env folds value #[]).isEmpty then continue
    let reach := ownReach env value
    let famCase := reach.toList.any (isFamilyRecursor env family)
    if !famCase then continue
    let famBrec := reach.toList.any fun c => family.contains c.getPrefix &&
      ["brecOn", "binductionOn", "below"].any (·.isPrefixOf c.getString!)
    let anyBrec := reach.toList.any fun c =>
      ["brecOn", "binductionOn"].any (·.isPrefixOf c.getString!)
    let wfFix := reach.contains ``WellFounded.fix || reach.contains ``WellFounded.Nat.fix ||
      reach.contains ``WellFounded.fixF
    let famMeasure := reach.toList.any (isSizeOfOf family)
    let selfRef := (value.getUsedConstants.contains n)
    let ruleI := if famBrec then "structural" else if wfFix && famMeasure then "wf" else "one-level"
    let ruleII := if famBrec || anyBrec || selfRef then "structural" else if wfFix then "wf" else "one-level"
    let priv := if isPrivateName n then " [private]" else ""
    counts := bump counts s!"{ruleI}/{ruleII}"
    if ruleI != ruleII || wfFix || isPrivateName n then
      lines := lines.push s!"{ruleI}\t{ruleII}\t{m}\t{userOf n}{priv}\tfamBrec={famBrec} anyBrec={anyBrec} wfFix={wfFix} famMeasure={famMeasure} self={selfRef}"
  let sorted := lines.qsort (· < ·)
  logInfo m!"#own_code {root}: rule (i)/(ii) counts over takers whose own code destructs the family (folds excluded): {counts.toList}\n{"\n".intercalate sorted.toList}"

#own_code Effect4.Program.Ty
#own_code Effect4.Program.Eff
#own_code Effect4.Program.Term
#own_code Effect4.Representation
#own_code Effect4.Store.Val
