import Effect4.Laws.Program.EvaluateR

/-! Probe Q3: which structure fields does a step definition write? Read off the constructor
applications in its body: an argument that is a projection of some source is copied, anything
else is written. -/

open Lean Meta Elab Command

namespace Probe

def owners : List Name :=
  [`Effect4.Machine.RunFiber, `Effect4.Machine.RunMachine, `Effect4.Program.Sched.RSaved,
   `Effect4.Machine.Race, `Effect4.Machine.Pending, `Effect4.Machine.Fibers.Race]

/-- Is `e` a projection of field `i` of some structure value? Both spellings. -/
def isProjOf (env : Environment) (s : Name) (i : Nat) (e : Expr) : Bool :=
  match e with
  | .proj s' i' _ => s' == s && i' == i
  | .mdata _ b => isProjOf env s i b
  | _ =>
    match e.getAppFn with
    | .const f _ =>
      match env.getProjectionFnInfo? f with
      | some info =>
        info.ctorName.getPrefix == s && info.i == i && e.getAppNumArgs == info.numParams + 1
      | none => false
    | _ => false

partial def collect (env : Environment) (e : Expr) (acc : Array (Name × Array String)) :
    Array (Name × Array String) := Id.run do
  let mut acc := acc
  match e with
  | .app .. =>
    let fn := e.getAppFn
    let args := e.getAppArgs
    if let .const c _ := fn then
      if let some (.ctorInfo ci) := env.find? c then
        if owners.contains ci.induct then
          let fields := (getStructureFields env ci.induct)
          let mut written : Array String := #[]
          for i in [:fields.size] do
            if let some a := args[ci.numParams + i]? then
              unless isProjOf env ci.induct i a do
                written := written.push fields[i]!.toString
          acc := acc.push (ci.induct, written)
    for a in args do acc := collect env a acc
    acc := collect env fn acc
    acc
  | .lam _ d b _ | .forallE _ d b _ => collect env b (collect env d acc)
  | .letE _ t v b _ => collect env b (collect env v (collect env t acc))
  | .mdata _ b | .proj _ _ b => collect env b acc
  | _ => acc

elab "#writes " id:ident : command => do
  let root := id.getId
  liftTermElabM do
    let env ← getEnv
    let ci ← getConstInfo root
    let some v := ci.value? | throwError "no value"
    -- the matcher alternatives live in the body as lambdas; unfold nothing
    let sites := collect env v #[]
    let mut report := m!"{root}: {sites.size} constructor sites"
    for (s, w) in sites do
      report := report ++ m!"\n  {s.getString!} writes {w}"
    logInfo report

end Probe

elab "#usedby " id:ident : command => do
  let ci ← getConstInfo id.getId
  let some v := ci.value? | throwError "no value"
  let used := v.getUsedConstants.filter fun c => (c.toString.splitOn "popR").length > 1
  logInfo m!"{id.getId} uses {used}"
/-- The write census of a step: every definition it reaches through the Effect4 modules,
each with the fields its own constructor sites write. Auxiliaries are reached the same way. -/
partial def closure (env : Environment) (root : Name) (seen : Array Name) : Array Name := Id.run do
  if seen.contains root then return seen
  let mut seen := seen.push root
  match env.find? root with
  | some ci =>
    if let some v := ci.value? then
      for c in v.getUsedConstants do
        if c.toString.startsWith "Effect4." then seen := closure env c seen
    return seen
  | none => return seen

elab "#writes_closure " id:ident : command => do
  liftTermElabM do
    let env ← getEnv
    let names := closure env id.getId #[]
    let mut report := m!"{id.getId}: {names.size} definitions reached"
    for n in names do
      if let some ci := env.find? n then
        if let some v := ci.value? then
          let sites := (Probe.collect env v #[]).filter fun (_, w) => !w.isEmpty
          unless sites.isEmpty do
            report := report ++ m!"\n  {n}"
            for (s, w) in sites do report := report ++ m!"\n      {s.getString!} <- {w}"
    logInfo report

#writes Effect4.Program.Sched.popR._f
#writes_closure Effect4.Program.Sched.popR
#writes_closure Effect4.Machine.driveStep
