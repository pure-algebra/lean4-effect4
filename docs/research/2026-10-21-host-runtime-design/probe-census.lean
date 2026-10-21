import Lean
import ProofGraph.Registry
import Effect4.Laws
import Compiler.Run
import Test.Dogfood.Scenario.Todo.Typed

/-! Probe: what the run and host laws quantify over. For every registry claim of the concept
`host-session-protocol`, every claim of `translation-simulation` whose pointer is a run's law, and
the top nodes of R6 and R13 (`tools/ProofGraph/Registry.lean`), this reads the pointer's statement
from the environment and lists the carriers its binders range over. A finite evaluation over the
registry and the loaded environment; its helpers are metaprograms, so the audit runs it and does
not walk it (as the program-domain note's `probe-closure.lean`). -/

open Lean Meta Tools.Semantics

namespace Probe

/-- The carriers a run or host law can range over, each with a short label. -/
def carriers : List (Name × String) :=
  [(`Effect4.Run, "Run"), (`Effect4.Live, "Live"), (`Effect4.LiveRecord, "LiveRecord"),
   (`Effect4.Api.Built, "Built"), (`Effect4.Program.Object, "Object"),
   (`Effect4.Api.HostSession.Session, "Session"), (`Effect4.Api.Runner.Runner, "Runner"),
   (`Effect4.Run.Reactor, "Reactor"), (`Effects.Comodel, "Comodel"),
   (`Effect4.Run.Tree.Host, "Tree.Host"), (`Effect4.Program.HostSpec, "HostSpec"),
   (`Test.Dogfood.Scenario.Todo.Typed.Host, "typed host record"), (`Compiler.Hosted, "Hosted")]

/-- The laws `AGENTS.md`'s vocabulary and the plan note name, beside the registry's pointers. -/
def named : List Name :=
  [`Effect4.Run.drive_eq_play, `Effect4.Run.drive_envelope, `Effect4.Run.runWith_guarded_denotes,
   `Effect4.Run.runWith_host_denotes, `Effect4.Run.runWith_host_denotesB, `Effect4.Run.reactorHost_ofHost,
   `Effect4.Run.agrees_hostRun_blocks, `Effect4.Run.conforms_sat_blocks, `Effect4.Run.request_performed,
   `Effect4.Live.journal_replays, `Effect4.Api.Runner.replay_unique, `Effect4.Api.Runner.replay_append,
   `Effect4.Api.Runner.behaviour_unique]

/-- A role's word. -/
def roleWord : Role → String
  | .inversion => "inversion" | .canonicalForms => "canonical forms" | .weakening => "weakening"
  | .substitution => "substitution" | .progress => "progress" | .preservation => "preservation"
  | .monotonicity => "monotonicity" | .transitivity => "transitivity"
  | .antisymmetry => "antisymmetry" | .decidability => "decidability" | .adequacy => "adequacy"
  | .simulation => "simulation" | .compatibility => "compatibility"
  | .fundamentalProperty => "fundamental property"

/-- The selected claims: their id, concept and role, and pointer. -/
def selected : List (String × String × Name) :=
  let claims := registry.claims.filterMap fun c =>
    match c.pointer with
    | .witness n =>
      let runLaw := [`Effect4.Run, `Effect4.Live, `Effect4.LiveRecord].any (·.isPrefixOf n)
      if c.concept == "host-session-protocol" || (c.concept == "translation-simulation" && runLaw)
      then some (c.id, c.concept ++ ", " ++ roleWord c.role, n) else none
    | _ => none
  let tops := (registry.requirements.filter (fun r => r.id == "R6" || r.id == "R13")).flatMap
    fun r => r.top.map fun n => (r.id ++ " top", r.id, n)
  claims ++ tops ++ named.map fun n => ("named", "-", n)

/-- The selected concept's claims that point at no witness: an assumption or an absence. -/
def unwitnessed : List String :=
  registry.claims.filterMap fun c =>
    if c.concept == "host-session-protocol" then
      match c.pointer with
      | .witness _ => none
      | .refutedBy r _ => some s!"{c.id}: refuted by {r}"
      | .absent why => some s!"{c.id}: absent ({why})"
      | .assumed src why => some s!"{c.id}: assumed, {src} ({why})"
    else none

/-- The labels of the carriers that a binder of `n`'s statement ranges over, by the head of the
binder's type as written, with the number of such binders. -/
def bindersOf (n : Name) : MetaM (List (String × Nat)) := do
  let some info := (← getEnv).find? n | return [("missing", 1)]
  forallTelescopeReducing info.type fun xs _ => do
    let mut counts : List (String × Nat) := []
    for x in xs do
      let ty ← instantiateMVars (← inferType x)
      for (c, label) in carriers do
        if ty.getAppFn.constName? == some c then
          counts := match counts.find? (·.1 == label) with
            | some _ => counts.map fun (l, k) => if l == label then (l, k + 1) else (l, k)
            | none => counts ++ [(label, 1)]
    return counts

run_meta do
  let mut rows : Array String := #[]
  let mut tally : List (String × Nat) := []
  let mut twoRuns := 0
  let mut seen : List Name := []
  for (id, concept, n) in selected do
    let bs ← bindersOf n
    rows := rows.push s!"{id} | {concept} | {n} | {", ".intercalate (bs.map fun (l, k) => s!"{l}×{k}")}"
    if seen.contains n then continue
    seen := seen ++ [n]
    let runs := bs.foldl (fun acc (l, k) => if l == "Run" || l == "Live" then acc + k else acc) 0
    if runs ≥ 2 then twoRuns := twoRuns + 1
    for (l, _) in bs do
      tally := match tally.find? (·.1 == l) with
        | some _ => tally.map fun (m, k) => if m == l then (m, k + 1) else (m, k)
        | none => tally ++ [(l, 1)]
  logInfo m!"{rows.size} rows read, {seen.length} distinct statements\n{"\n".intercalate rows.toList}"
  logInfo m!"statements with two or more binders over a run (Run or Live): {twoRuns}"
  logInfo m!"host-session-protocol claims with no witness:\n{"\n".intercalate unwitnessed}"
  logInfo m!"distinct statements that range over each carrier:\n{"\n".intercalate (carriers.map fun (_, l) => s!"{l}: {(tally.find? (·.1 == l)).map (·.2) |>.getD 0}")}"

end Probe
