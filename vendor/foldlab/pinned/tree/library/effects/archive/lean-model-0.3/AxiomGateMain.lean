import Lean
import Effects
import Effects.Conformance.Generate

/-!
# The axiom-profile gate

Turns the tree's axiom discipline from recorded prose into a build
failure. At elaboration of this module (so under every
`lake --wfail build`, with no extra task wiring):

- every constant whose module lives under `Effects.` may use only the
  allowed axioms — `propext`, `Quot.sound`, `Classical.choice` — and
  never a forbidden one (`sorryAx`, the `native_decide` axioms, the
  compiler-trust axiom);
- every carrier-discharge citation in the ledger's declared list
  resolves to a real constant, so a renamed or typo'd theorem cannot
  silently sit behind a green `discharged` row;
- the resolved discharge carriers are held to the strict base profile
  (`propext`/`Quot.sound` only), except carriers on the documented
  choice list, which are allowed `Classical.choice` as recorded at
  their ratification.

The quarantined mutant tree is deliberately outside the sweep: mutants
are non-load-bearing by construction and are never imported by the
model.
-/

open Lean

namespace AxiomGate

def allowedAxioms : List Name :=
  [``propext, ``Quot.sound, ``Classical.choice]

def strictAxioms : List Name :=
  [``propext, ``Quot.sound]

def forbiddenAxioms : List Name :=
  [``sorryAx, ``Lean.ofReduceBool, ``Lean.ofReduceNat, ``Lean.trustCompiler]

/-- Discharge carriers ratified with `Classical.choice` in their
profile (drawn through Std container lemmas; recorded at their
slices). Every other carrier is held to the strict base. -/
def choiceCarriers : List String :=
  []

structure CollectState where
  visited : NameSet := {}
  used : NameSet := {}

partial def visit (env : Environment) (n : Name) :
    StateM CollectState Unit := do
  if (← get).visited.contains n then return
  modify fun s => { s with visited := s.visited.insert n }
  match env.find? n with
  | none => return
  | some info =>
    if info matches .axiomInfo _ then
      modify fun s => { s with used := s.used.insert n }
    for u in info.type.getUsedConstants do
      visit env u
    if let some v := info.value? then
      for u in v.getUsedConstants do
        visit env u

/-- Axioms reachable from one constant. -/
def axiomsOf (env : Environment) (n : Name) : List Name :=
  ((visit env n).run {}).2.used.toList

/-- The module a constant was declared in, if known. -/
def moduleOf (env : Environment) (n : Name) : Option Name := do
  let idx ← env.getModuleIdxFor? n
  env.header.moduleNames[idx.toNat]?

def underEffects (m : Name) : Bool :=
  (`Effects).isPrefixOf m

end AxiomGate

open Lean Elab Command AxiomGate in
elab "#axiom_profile_gate" : command => do
  let env ← getEnv
  -- Roots: every non-internal constant declared under Effects.*.
  let mut roots : Array Name := #[]
  for (n, _) in env.constants.toList do
    if !n.isInternal then
      if let some m := moduleOf env n then
        if underEffects m then
          roots := roots.push n
  -- One shared-cache walk over all roots.
  let sweep : StateM CollectState Unit := do
    for n in roots do
      visit env n
  let used := ((sweep.run {}).2).used.toList
  for ax in used do
    if forbiddenAxioms.contains ax then
      throwError "axiom gate: forbidden axiom {ax} is reachable from the Effects tree"
    if !allowedAxioms.contains ax then
      throwError "axiom gate: unexpected axiom {ax} is reachable from the Effects tree (allowed: {allowedAxioms})"
  -- Citation resolution: every declared discharge names a real constant.
  let names := roots.map (·.toString)
  let mut resolved : List (String × Name) := []
  for (id, thm) in Effects.Conformance.carrierDischarges do
    let hit? := roots.find? fun n =>
      n.toString == thm || n.toString.endsWith ("." ++ thm)
    match hit? with
    | none =>
      throwError "axiom gate: carrier discharge {id} cites {thm}, which resolves to no constant in the Effects tree ({names.size} candidates searched)"
    | some n => resolved := (thm, n) :: resolved
  -- Strict profile on the resolved carriers.
  for (thm, n) in resolved do
    let axs := axiomsOf env n
    let bound := if choiceCarriers.contains thm then allowedAxioms else strictAxioms
    for ax in axs do
      if !bound.contains ax then
        throwError "axiom gate: discharge carrier {n} uses {ax}, outside its declared profile {bound}"

#axiom_profile_gate

def main : IO Unit :=
  IO.println "axiom profile enforced at build time"
