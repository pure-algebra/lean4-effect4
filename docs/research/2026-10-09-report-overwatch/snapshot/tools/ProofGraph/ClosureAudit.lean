import ProofGraph.Population

/-!
# `#closure_audit`: no table bound before a returned closure

Lean compiles a definition that returns a closure with the closure's argument as one more
parameter. So in `def f (x : A) : B → C := let table := build x; fun b => … table …` the table is
built again at every application `f x b`, not once per `f x`: a caller that keeps `f x` and
applies it to many `b` pays the build each time. The semantics report met this twice on
2026-10-09 (a module table and a name table), and it ran for minutes. The repair is to pass the
table as data: the caller builds it once and hands it to a definition that takes it as a
parameter.

`#closure_audit P₁ P₂ …` reads every computational definition of the modules that the prefixes
`Pᵢ` name (and of the current module, when a prefix names it), and refuses each one whose value,
after its parameters, binds a `let` or a `have` and then returns a `fun`. It reads the elaborated
values, so it sees the shape that the compiler sees. Propositions, type formers and the
elaborator's auxiliaries are skipped: they do not run.
-/

namespace ProofGraph
open Lean Elab Command

/-- The names a definition's value binds between its parameters and a closure it returns: empty
when it returns no closure there or binds nothing before it. -/
def letsBeforeClosure : Expr → Array Name
  | .lam _ _ body _ => letsBeforeClosure body
  | .mdata _ e => letsBeforeClosure e
  | e => bound e #[]
where
  bound : Expr → Array Name → Array Name
    | .letE name _ _ body _, acc => bound body (acc.push name)
    | .mdata _ e, acc => bound e acc
    | .lam .., acc => acc
    | _, _ => #[]

/-- `#closure_audit P₁ P₂ …`: the definitions of the modules under the prefixes that bind a table
before the closure they return. -/
syntax (name := closureAudit) "#closure_audit" (ppSpace ident)+ : command

@[command_elab closureAudit] def elabClosureAudit : CommandElab := fun stx => do
  let prefixes := stx[1].getArgs.map (·.getId)
  let env ← getEnv
  -- the module names, built once (`EnvironmentHeader.moduleNames` builds an array per call)
  let modules := env.header.moduleNames
  let mut names : Array Name := #[]
  for h : i in [0:modules.size] do
    if prefixes.any (·.isPrefixOf modules[i]) then
      names := names ++ env.header.moduleData[i]!.constNames
  if prefixes.any (·.isPrefixOf env.mainModule) then
    names := env.constants.map₂.foldl (fun acc name _ => acc.push name) names
  let offenders ← liftTermElabM do
    names.filterMapM fun name => do
      let some (.defnInfo d) := env.find? name | return none
      if isAuxiliary env name then return none
      if (← Meta.isProp d.type) || (← Meta.isTypeFormerType d.type) then return none
      let lets := letsBeforeClosure d.value
      if lets.isEmpty then return none
      return some (name, lets)
  if offenders.isEmpty then
    logInfo m!"#closure_audit: {names.size} declarations; none binds a table before a returned closure"
  else
    let lines := (offenders.qsort fun a b => a.1.toString < b.1.toString).toList.map fun (name, lets) =>
      m!"{name} binds {lets.toList} before the closure it returns"
    throwError m!"#closure_audit: {offenders.size} definitions bind a table before the closure \
      they return; pass the table as data:{indentD (MessageData.joinSep lines Format.line)}"

end ProofGraph
