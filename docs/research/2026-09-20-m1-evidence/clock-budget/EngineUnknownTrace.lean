import OCaml5.Lcnf.Translate
open Lean OCaml5 OCaml5.Lcnf
namespace OCaml5.Lcnf.ClockProfile
open Lean Compiler LCNF

/-- A finite dependency graph for the clock boundary. Edges point from a result to the
values it depends on; calls retain original argument positions, including erased slots. -/
structure Flow where
  name : Name
  params : Array FVarId
  clockResult : Bool := false
  deps : Array (FVarId × Array FVarId) := #[]
  calls : Array (Name × Array (Arg .pure) × Bool) := #[]
  globals : Std.HashMap FVarId (Name × Array (Arg .pure)) := {}
  locals : Std.HashMap FVarId (Array FVarId) := {}
  localCalls : Array (FVarId × Array (Arg .pure) × Option FVarId) := #[]
  localReturns : Std.HashMap FVarId (Array FVarId) := {}
  callResults : Array (Name × FVarId) := #[]
  returns : Array FVarId := #[]
  unknownResults : Std.HashSet FVarId := {}
  aliases : Std.HashMap FVarId FVarId := {}
  literals : Std.HashMap FVarId Nat := {}
  projections : Array (FVarId × FVarId × Option Name × Nat) := #[]

def clockIngress (n : Name) : Bool :=
  stripRedArg n == `Effect4.ClockMillis.ofNat || n == `Effect4.ClockMillis.positive

def clockArgIds (args : Array (Arg .pure)) : Array FVarId :=
  args.filterMap fun | .fvar id => some id | _ => none

/-- Read dependency data from mono LCNF, without executing or rewriting the program. -/
def ofDecl (decl : LCNF.Decl .pure) : Flow := Id.run do
  let initial : Flow := {
    name := decl.name, params := decl.params.map (·.fvarId),
    clockResult := decl.type.getForallBody.getAppFn.isConstOf `Effect4.ClockMillis }
  let .code body := decl.value | return initial
  let (_, flow) := (body.forM fun node => do
    match node with
    | .let d _ =>
      match d.value with
      | .lit (.nat n) => modify fun s => { s with literals := s.literals.insert d.fvarId n }
      | .fvar f args => modify fun s => { s with
          deps := s.deps.push (d.fvarId, #[f] ++ clockArgIds args),
          aliases := if args.isEmpty then s.aliases.insert d.fvarId f else s.aliases,
          localCalls := if args.isEmpty then s.localCalls else s.localCalls.push (f, args, some d.fvarId),
          calls := if !args.isEmpty && d.type.getAppFn.isConstOf `Effect4.ClockMillis then
            s.calls.push (`OCaml5.Lcnf.ClockFlow.higherOrderClockResult, args, false) else s.calls }
      | .const n _ args => modify fun s => { s with
          calls := s.calls.push (n, args, true),
          globals := s.globals.insert d.fvarId (n, args),
          callResults := if clockIngress n then s.callResults else s.callResults.push (n, d.fvarId),
          deps := if clockIngress n then s.deps else s.deps.push (d.fvarId, clockArgIds args) }
      | .proj _ index source => modify fun s => { s with
          deps := s.deps.push (d.fvarId, #[source]),
          projections := s.projections.push (d.fvarId, source, none, index) }
      | _ => pure ()
    | .fun d _ | .jp d _ =>
      let (_, returns) := (d.value.forM fun node => do
        if let .return value := node then modify (·.push value) : StateM (Array FVarId) Unit).run #[]
      modify fun s => { s with
        locals := s.locals.insert d.fvarId (d.params.map (·.fvarId)),
        localReturns := s.localReturns.insert d.fvarId returns }
    | .jmp f args => modify fun s => { s with localCalls := s.localCalls.push (f, args, none) }
    | .return value => modify fun s => { s with returns := s.returns.push value }
    | .cases cases =>
      for alt in cases.alts do
        if let .alt ctor params _ := alt then
          for index in [:params.size] do
            let param := params[index]!
            modify fun s => { s with
              deps := s.deps.push (param.fvarId, #[cases.discr]),
              projections := s.projections.push (param.fvarId, cases.discr, some ctor, index) }
    | _ => pure () : StateM Flow Unit).run initial
  let mut flow := flow
  -- Code.forM visits nested functions too; their return values do not belong to the
  -- enclosing function's return summary. Walk the same finite tree with explicit owners.
  let (_, count) := (body.forM fun _ => modify (· + 1) : StateM Nat Unit).run 0
  let mut work := [(body, none)]
  flow := { flow with returns := #[], localReturns := {} }
  for _ in [:count] do
    let (node, owner) :: rest := work | break
    work := rest
    match node with
    | .let _ next => work := (next, owner) :: work
    | .fun d next =>
      work := (d.value, some d.fvarId) :: (next, owner) :: work
    | .jp d next =>
      -- Join points return from their enclosing function, unlike local functions.
      work := (d.value, owner) :: (next, owner) :: work
    | .cases cs =>
      for alt in cs.alts do work := (alt.getCode, owner) :: work
    | .return value =>
      match owner with
      | none => flow := { flow with returns := flow.returns.push value }
      | some localId =>
        let values := (flow.localReturns.getD localId #[]).push value
        flow := { flow with localReturns := flow.localReturns.insert localId values }
    | _ => pure ()
  for (callee, args, result) in flow.localCalls do
    let mut target := callee
    for _ in [:flow.aliases.size + 1] do
      if let some source := flow.aliases[target]? then target := source else break
    if let some params := flow.locals[target]? then
      for param in params, arg in args do
        if let .fvar value := arg then
          flow := { flow with deps := flow.deps.push (param, #[value]) }
      if let some result := result then
        flow := { flow with deps := flow.deps.push (result, flow.localReturns.getD target #[]) }
    else if let some (name, bound) := flow.globals[target]? then
      flow := { flow with calls := flow.calls.push (name, bound ++ args, false) }
      if let some result := result then
        unless clockIngress name do
          flow := { flow with callResults := flow.callResults.push (name, result) }
    else if let some result := result then
      -- Unknown higher-order production has no scalar-bound certificate. Refuse it if
      -- its output reaches a clock, rather than inferring a bound from its target type.
      flow := { flow with unknownResults := flow.unknownResults.insert result }
  return flow

/-- FVar identifiers are local to a declaration; the owner is part of every graph key. -/
abbrev ValueKey := Name × FVarId

inductive Target where
  | global (name : Name)
  | localFn (owner : Name) (id : FVarId)
  deriving BEq, Hashable

/-- Constructor origins retain fields separately. Mixing a record's data and callback
fields would turn a known callback into an opaque value just because it captures input. -/
inductive Origin where
  | callable (target : Target) (supplied : Nat)
  | constructor (site : ValueKey)
  | unresolved
  deriving BEq, Hashable, Inhabited

structure CallableState where
  values : Std.HashMap ValueKey (Std.HashSet Origin) := {}
  facts : Nat := 0
  edges : Std.HashMap ValueKey (Array ValueKey) := {}
  pending : Array (ValueKey × Origin) := #[]

def addOrigins (s : CallableState) (key : ValueKey) (values : Array Origin) : CallableState :=
  values.foldl (fun s value =>
    let old := s.values.getD key {}
    if old.contains value then s else
      { s with
        values := s.values.insert key (old.insert value)
        facts := s.facts + 1
        pending := s.pending.push (key, value) }) s

def addEdge (s : CallableState) (source destination : ValueKey) : CallableState :=
  let destinations := s.edges.getD source #[]
  if destinations.contains destination then s else
    let s := { s with edges := s.edges.insert source (destinations.push destination) }
    addOrigins s destination (s.values.getD source {}).toArray

def globalArity (env : Environment) (byName : Std.HashMap Name Flow) (n : Name) : Nat :=
  match byName[n]? with
  | some f => f.params.size
  | none => match env.find? n with
    | some (.ctorInfo ci) => ci.numParams + ci.numFields
    | some ci => ci.type.getNumHeadForalls
    | none => 0

/-- Resolve internal calls in a finite closed-world value graph. Unknown root values and
unknown call results stay opaque; absence of a discovered target never establishes safety.
Only the unknown-production markers are refined here; scalar-narrowing checks remain. -/
def resolveCallables (env : Environment) (roots : Array Name) (flows : Array Flow) :
    Option (Array Flow) := Id.run do
  let mut byName : Std.HashMap Name Flow := {}
  let mut constructors : Std.HashMap ValueKey (Name × Array (Arg .pure)) := {}
  for flow in flows do
    byName := byName.insert flow.name flow
    for (id, name, args) in flow.globals.toArray do
      if let some (.ctorInfo _) := env.find? name then
        constructors := constructors.insert (flow.name, id) (name, args)
  let mut state : CallableState := {}
  for flow in flows do
    if roots.contains flow.name then
      for p in flow.params do state := addOrigins state (flow.name, p) #[.unresolved]
    for (id, _) in flow.locals.toArray do
      state := addOrigins state (flow.name, id) #[.callable (.localFn flow.name id) 0]
  let targetArity (target : Target) := match target with
    | .global n => globalArity env byName n
    | .localFn owner id => ((byName.getD owner flowDefault).locals.getD id #[]).size
  let targetParams (target : Target) : Array ValueKey := match target with
    | .global n => ((byName.getD n flowDefault).params.map (n, ·))
    | .localFn owner id => ((byName.getD owner flowDefault).locals.getD id #[]).map (owner, ·)
  let targetReturns (target : Target) : Array ValueKey := match target with
    | .global n => ((byName.getD n flowDefault).returns.map (n, ·))
    | .localFn owner id => ((byName.getD owner flowDefault).localReturns.getD id #[]).map (owner, ·)
  let applyTarget (s : CallableState) (owner : Name) (result : Option FVarId)
      (target : Target) (supplied : Nat) (args : Array (Arg .pure)) : CallableState := Id.run do
    let mut s := s
    let params := targetParams target
    for i in [:args.size] do
      if let some parameter := params[supplied + i]? then
        if let .fvar argument := args[i]! then s := addEdge s (owner, argument) parameter
    if let some result := result then
      let result := (owner, result)
      let arity := targetArity target
      if supplied + args.size < arity then
        s := addOrigins s result #[.callable target (supplied + args.size)]
      else
        let returns := targetReturns target
        if returns.isEmpty then s := addOrigins s result #[.unresolved]
        else for value in returns do s := addEdge s value result
    return s
  -- There are finitely many sites, constructor origins and (target, supplied-arity) pairs.
  -- Each productive pass adds a fact. The computed product bounds all such additions.
  let mut sites := 0
  let mut origins := constructors.size + 1
  for flow in flows do
    sites := sites + flow.params.size + flow.globals.size + flow.aliases.size +
      flow.projections.size + flow.localCalls.size + flow.locals.size + 1
    origins := origins + flow.params.size + 1
    for (_, name, _) in flow.globals.toArray do
      origins := origins + globalArity env byName name + 1
    for (_, params) in flow.locals.toArray do
      sites := sites + params.size
      origins := origins + params.size + 1
  -- Copy edges are installed once. Each newly discovered (value, origin) fact is
  -- queued once; projections and resolved callbacks add edges as their origins arrive.
  -- Installing an edge also copies existing facts, so discovery order loses no source.
  let mut projections : Std.HashMap ValueKey (Array (ValueKey × Option Name × Nat)) := {}
  let mut watchers : Std.HashMap ValueKey (Array (Name × Array (Arg .pure) × Option FVarId)) := {}
  for flow in flows do
    for (to, source) in flow.aliases.toArray do
      state := addEdge state (flow.name, source) (flow.name, to)
    for (result, source, expected, index) in flow.projections do
      let key := (flow.name, source)
      projections := projections.insert key
        ((projections.getD key #[]).push ((flow.name, result), expected, index))
    for (callee, args, result) in flow.localCalls do
      let key := (flow.name, callee)
      watchers := watchers.insert key ((watchers.getD key #[]).push (flow.name, args, result))
    for (id, name, args) in flow.globals.toArray do
      if let some (.ctorInfo ci) := env.find? name then
        if args.size ≥ ci.numParams + ci.numFields then
          state := addOrigins state (flow.name, id) #[.constructor (flow.name, id)]
        else
          state := addOrigins state (flow.name, id) #[.callable (.global name) args.size]
      else
        state := applyTarget state flow.name (some id) (.global name) 0 args
  let mut cursor := 0
  for _ in [:sites * origins + 1] do
    if cursor ≥ state.pending.size then break
    let (source, origin) := state.pending[cursor]!
    cursor := cursor + 1
    for destination in state.edges.getD source #[] do
      state := addOrigins state destination #[origin]
    for (destination, expected, index) in projections.getD source #[] do
      match origin with
      | .unresolved => state := addOrigins state destination #[.unresolved]
      | .constructor site =>
        if let some (ctor, args) := constructors[site]? then
          if expected.isNone || expected == some ctor then
            if let some (.ctorInfo ci) := env.find? ctor then
              if let some (.fvar field) := args[ci.numParams + index]? then
                state := addEdge state (site.1, field) destination
      | .callable .. => pure ()
    for (owner, args, result) in watchers.getD source #[] do
      match origin with
      | .callable target supplied =>
        state := applyTarget state owner result target supplied args
      | .unresolved =>
        if let some result := result then state := addOrigins state (owner, result) #[.unresolved]
      | .constructor _ => pure ()
  -- Exhausting the finite fact bound is a refusal, never an incomplete fixed point.
  unless cursor == state.pending.size do return none
  let localName (owner : Name) (id : FVarId) := owner ++ `_clockFlowLocal ++ id.name
  let mut out := #[]
  for flow in flows do
    let mut unknown : Std.HashSet FVarId := {}
    -- Partial application constructs a closure; it is not the callee's returned data.
    let mut results := flow.callResults.filter fun (name, result) =>
      match flow.globals[result]? with
      | some (_, args) => args.size ≥ globalArity env byName name
      | none => true
    let mut calls := flow.calls
    for (callee, args, result) in flow.localCalls do
      let choices := (state.values.getD (flow.name, callee) {}).toArray
      if let some result := result then
        let hasTarget := choices.any fun | .callable .. => true | _ => false
        if !hasTarget || choices.contains .unresolved then unknown := unknown.insert result
      for origin in choices do
        if let .callable target supplied := origin then
          let name := match target with
            | .global n => n
            | .localFn owner id => localName owner id
          -- Captured arguments were checked where the partial application was made;
          -- retain original positions for the arguments supplied at this invocation.
          calls := calls.push (name, (Array.replicate supplied .erased) ++ args, false)
          if let some result := result then
            if supplied + args.size ≥ targetArity target then
              results := results.push (name, result)
    let refined := { flow with unknownResults := unknown, callResults := results, calls := calls }
    out := out.push refined
    -- A local closure can escape to another helper. Its own scoped returns retain
    -- captured literal/unknown dependencies, independently of its creator's returns.
    for (id, params) in flow.locals.toArray do
      let localFlow := { refined with
        name := localName flow.name id
        params := params
        returns := flow.localReturns.getD id #[]
        clockResult := false }
      out := out.push localFlow
  return some out
where
  flowDefault : Flow := { name := .anonymous, params := #[] }

def clockCallSlots (summaries : Std.HashMap Name (Array Nat))
    (callee : Name) (args : Array (Arg .pure)) : Array Nat := Id.run do
  if clockIngress callee || callee == `OCaml5.Lcnf.ClockFlow.higherOrderClockResult then
    let mut slots := #[]
    for i in [:args.size] do
      if args[i]! matches .fvar _ then slots := slots.push i
    return slots
  return summaries.getD callee #[]

/-- Which parameters can reach clock ingress, including through another helper. -/
def clockInputSlots (flow : Flow) (summaries : Std.HashMap Name (Array Nat)) : Array Nat := Id.run do
  let mut needed : Std.HashSet FVarId := {}
  for (callee, args, _) in flow.calls do
    for i in clockCallSlots summaries callee args do
      if let some (.fvar value) := args[i]? then needed := needed.insert value
  for _ in [:flow.deps.size + 1] do
    let before := needed.size
    for (result, inputs) in flow.deps do
      if needed.contains result then
        for input in inputs do needed := needed.insert input
    if needed.size == before then break
  let mut slots := #[]
  for i in [:flow.params.size] do
    if needed.contains flow.params[i]! then slots := slots.push i
  return slots

/-- Propagate both known narrowing and unknown higher-order production through return values.
The two markers stay distinct so a refusal states which evidence is missing. -/
def clockRisks (flow : Flow) (narrowedReturns unknownReturns : Std.HashSet Name) :
    Std.HashSet FVarId × Std.HashSet FVarId := Id.run do
  let mut narrowed : Std.HashSet FVarId := {}
  let mut unknown := flow.unknownResults
  for (id, value) in flow.literals.toList do
    if value ≥ 4611686018427387904 then narrowed := narrowed.insert id
  for (callee, result) in flow.callResults do
    if narrowedReturns.contains callee then narrowed := narrowed.insert result
    if unknownReturns.contains callee then unknown := unknown.insert result
  for _ in [:flow.deps.size + 1] do
    let before := narrowed.size + unknown.size
    for (result, inputs) in flow.deps do
      if inputs.any narrowed.contains then narrowed := narrowed.insert result
      if inputs.any unknown.contains then unknown := unknown.insert result
    if narrowed.size + unknown.size == before then break
  return (narrowed, unknown)

/-- Only values reaching a clock boundary are refused. Parameter and returned-value summaries
reach fixed points bounded by the number of facts that can be added. Ordinary Nat arithmetic
and its deliberate saturation stay unchanged. -/
def refusals (env : Environment) (roots : Array Name) (input : Array Flow) : Array String := Id.run do
  let some flows := resolveCallables env roots input
    | return #["clock callable provenance did not reach a fixed point"]
  let mut summaries : Std.HashMap Name (Array Nat) := {}
  let bound := flows.foldl (fun n flow => n + flow.params.size) 0
  for _ in [:bound + 1] do
    let mut changed := false
    for flow in flows do
      let slots := clockInputSlots flow summaries
      if slots != summaries.getD flow.name #[] then
        summaries := summaries.insert flow.name slots
        changed := true
    unless changed do break
  let mut narrowedReturns : Std.HashSet Name := {}
  let mut unknownReturns : Std.HashSet Name := {}
  for _ in [:2 * flows.size + 1] do
    let before := narrowedReturns.size + unknownReturns.size
    for flow in flows do
      let (narrowed, unknown) := clockRisks flow narrowedReturns unknownReturns
      if flow.returns.any narrowed.contains then narrowedReturns := narrowedReturns.insert flow.name
      if flow.returns.any unknown.contains then unknownReturns := unknownReturns.insert flow.name
    if narrowedReturns.size + unknownReturns.size == before then break
  let mut refusals := #[]
  for flow in flows do
    let (narrowed, unknown) := clockRisks flow narrowedReturns unknownReturns
    -- Mono may erase a polymorphic helper's result type. Its caller's declared clock
    -- result still exposes a narrowed dependency, even without a named ingress call.
    if flow.clockResult && flow.returns.any narrowed.contains then
      refusals := refusals.push s!"{flow.name}: returned value reaches clock ingress after Nat saturation"
    for (callee, args, direct) in flow.calls do
      for i in clockCallSlots summaries callee args do
        if let some (.fvar value) := args[i]? then
          unless narrowed.contains value || unknown.contains value do continue
          -- The direct ingress already emits exact literals, including local aliases.
          let mut original := value
          for _ in [:flow.aliases.size + 1] do
            if let some source := flow.aliases[original]? then original := source else break
          if direct && clockIngress callee && flow.literals.contains original then continue
          let reason := if narrowed.contains value then "after Nat saturation"
            else "from unknown higher-order Nat production"
          refusals := refusals.push
            s!"{flow.name}: {callee} argument {i} reaches clock ingress {reason}"
  return refusals

end OCaml5.Lcnf.ClockProfile

namespace OCaml5.Lcnf
def profilePushNew (a : Array Name) (n : Name) : Array Name := if a.contains n then a else a.push n
def collectFlows (roots : Array Name) (cap : Nat := 60) (tn : TypeNames := {})
    (ex : Externs := {}) : CoreM (Closure × Array ClockProfile.Flow) := do
  let env ← getEnv
  let mono := Conform.Lcnf.persistedMonoIndex env
  let mut c : Closure := {}
  let mut clockFlows : Array ClockProfile.Flow := #[]
  let mut done : NameSet := {}
  let mut queue : Array Name := roots
  let mut i := 0
  while i < queue.size do
    let n := queue[i]!
    i := i + 1
    if done.contains n then continue
    let arity := (mono.findIn? env n).map (fun d => d.params.size)
    if ex.hasFn n arity then continue
    if (builtin? n).isSome then continue
    if env.find? n matches some (.ctorInfo _) then continue
    if c.decls.size ≥ cap then
      c := { c with frontier := profilePushNew c.frontier n }
      continue
    done := done.insert n
    let d? := mono.findIn? env n
    if d?.isNone then
      c := { c with missing := profilePushNew c.missing n }
      continue
    let d := d?.get!
    clockFlows := clockFlows.push (ClockProfile.ofDecl d)
    -- the wrapper folds onto its twin
    let mut d := d
    let mut userName := n
    match redArgTarget? d with
    | some twin =>
      done := done.insert twin
      if let some dt := mono.findIn? env twin then
        d := dt
        clockFlows := clockFlows.push (ClockProfile.ofDecl dt)
    | none =>
      -- a twin reached directly: its wrapper is the user-facing name
      userName := stripRedArg n
      if userName != n then
        done := done.insert userName
        if let some wrapper := mono.findIn? env userName then
          clockFlows := clockFlows.push (ClockProfile.ofDecl wrapper)
    let (t, st) := translateDecl env d userName (globalName userName) tn ex
    c := { c with
      decls := c.decls.push t,
      realTypes := st.realTypes.foldl profilePushNew c.realTypes,
      mentioned := st.mentioned.foldl profilePushNew c.mentioned,
      usedExterns := st.usedExterns.foldl profilePushNew c.usedExterns,
      usedOps := st.usedOps.foldl (fun a o => if a.contains o then a else a.push o) c.usedOps,
      usedCargs := st.usedCargs.foldl profilePushNew c.usedCargs,
      wantedCargs := st.wantedCargs.foldl (fun a w => if a.contains w then a else a.push w) c.wantedCargs,
      toLists := c.toLists ++ st.toLists,
      todos := c.todos ++ st.todos }
    for callee in st.calls do
      unless done.contains callee do
        -- a direct reference to a wrapper that has a twin: note it, translate the twin
        if stripRedArg callee == callee then
          if (mono.findIn? env (callee ++ `_redArg)).isSome then
            c := { c with wrapperRefs := profilePushNew c.wrapperRefs callee }
        queue := queue.push callee
  return (c, clockFlows)


end OCaml5.Lcnf

def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `Effect4.Api }] {} 0
  let ctx : Core.Context := { fileName := "<engine-origins>", fileMap := default }
  let .ok ex := Externs.parse (← IO.FS.readFile "ocaml/engine/externs.txt") | throw (IO.userError "externs parse")
  let act : MetaM Unit := do
    let roots := #[`Effect4.Api.run, `Effect4.Api.replay, `Effect4.Machine.stepDecisionState, `Effect4.Machine.driveState, `Effect4.Machine.settled, `Effect4.Machine.FnName.total, `Effect4.Machine.FnName.partialUpdate, `Effect4.Machine.FnName.modify, `Effect4.Machine.FnName.modifySome, `Effect4.Scope.make, `Effect4.Scope.fork, `Effect4.Machine.RunFiber.make, `Effect4.Machine.emptyCtx, `Effect4.Program.compile, `Effect4.Machine.stores, `Effect4.Program.Node.child]
    let mut ex := ex
    let (first, firstFlows) ← collectFlows roots 2000 {} ex
    let mut closure := first
    let mut flows := firstFlows
    for _ in [:64] do
      if closure.wantedCargs.isEmpty then break
      for (g, i, c) in closure.wantedCargs do
        let key := (ex.cargRowKey? g).getD g
        let prev := ex.cargs.getD key []
        unless prev.any (fun row => row.1 == CargParam.pos i) do
          ex := { ex with cargs := ex.cargs.insert key (prev ++ [(CargParam.pos i, [c])]) }
      let (next, nf) ← collectFlows roots 2000 {} ex
      closure := next
      flows := nf
    let some resolved := ClockProfile.resolveCallables env roots flows | throwError "unsettled"
    let mut returnPaths : Std.HashMap Name String := {}
    let unknownPaths (flow : ClockProfile.Flow) (returns : Std.HashMap Name String) := Id.run do
      let mut paths : Std.HashMap FVarId String := {}
      for (callee, _, result) in flow.localCalls do
        if let some result := result then
          if flow.unknownResults.contains result then
            paths := paths.insert result s!"unknown {flow.name} result {result.name} callback {callee.name}"
      for (callee, result) in flow.callResults do
        if let some path := returns[callee]? then
          unless paths.contains result do
            paths := paths.insert result s!"call {flow.name} result {result.name} <- {callee}\n{path}"
      for _ in [:flow.deps.size + 1] do
        let before := paths.size
        for (result, inputs) in flow.deps do
          unless paths.contains result do
            for input in inputs do
              if let some path := paths[input]? then
                paths := paths.insert result s!"dep {flow.name} {result.name} <- {input.name}\n{path}"
                break
        if paths.size == before then break
      return paths
    for _ in [:2 * resolved.size + 1] do
      let before := returnPaths.size
      for flow in resolved do
        unless returnPaths.contains flow.name do
          let paths := unknownPaths flow returnPaths
          for result in flow.returns do
            if let some path := paths[result]? then
              returnPaths := returnPaths.insert flow.name path
              break
      if returnPaths.size == before then break
    for flow in resolved do
      if flow.name.toString == "Effect4.Machine.replayEval._at_.Effect4.Program.replayCheckedFrom.spec_0" then
        let paths := unknownPaths flow returnPaths
        for (callee, args, _) in flow.calls do
          if callee == flow.name then
            if let some (Compiler.LCNF.Arg.fvar value) := args[5]? then
              if let some path := paths[value]? then IO.println s!"TRACE {value.name}\n{path}"

  let _ ← (act.run' {}).toIO ctx { env := env }
