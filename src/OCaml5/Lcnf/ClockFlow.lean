import Lean
import OCaml5.Lcnf.Index
import OCaml5.Lcnf.Externs

/-! Clock-boundary dependency analysis over mono LCNF.

Properties: original literals identify known scalar narrowing; helper-parameter and
returned-value summaries reach finite fixed points; unknown higher-order production is
refused when its result reaches a clock ingress. Direct known literals are left to the
exact decimal emitter. Other Nat consumers are unchanged. Finite controls live in
`Test/Audit/ClockLowering.lean`; this pass does not prove arbitrary arithmetic bounds.

* **Arity is mono arity.** A global's arity is the parameter count of its mono declaration
  (`Context.mono`), the count a mono call supplies. A compiler-made declaration has no
  kernel constant, and an instance's kernel type need not be a forall: read off the kernel, both
  had arity 0, so a builtin passed as a callback (`List.appendTR._redArg`, the program folds'
  `op`) read as a finished call of no flow, and every call through it as unknown production.
* **A host's reactor is host ingress** (decisions row 394 (1)). A root parameter whose mono type
  is a host reactor (`Context.reactor`, the type of `Effect4.Run.Reactor σ`) holds the
  `ingress` origin. A call whose origins are ingress answers checked host data, as the tape's
  answers are root data checked at the engine's ingress (EN8), and is not unknown production.
  A reactor inside other data, or reached by any other unknown, stays unknown. The obligation it
  leaves: the driver that supplies the reactor applies `E4_engine.check_answer` to every answer
  before the machine reads it. -/

namespace OCaml5.Lcnf.ClockFlow
open Lean Compiler LCNF

/-- A finite dependency graph for the clock boundary. Edges point from a result to the
values it depends on; calls retain original argument positions, including erased slots. -/
structure Flow where
  name : Name
  params : Array FVarId
  /-- The parameters' mono types, in order: what tells a host's reactor at a root. -/
  paramTypes : Array Lean.Expr := #[]
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

private def clockIngress (n : Name) : Bool :=
  stripRedArg n == `Effect4.ClockMillis.ofNat || n == `Effect4.ClockMillis.positive

private def clockArgIds (args : Array (Arg .pure)) : Array FVarId :=
  args.filterMap fun | .fvar id => some id | _ => none

/-- Read dependency data from mono LCNF, without executing or rewriting the program. -/
def ofDecl (decl : LCNF.Decl .pure) : Flow := Id.run do
  let initial : Flow := {
    name := decl.name, params := decl.params.map (·.fvarId),
    paramTypes := decl.params.map (·.type),
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
private abbrev ValueKey := Name × FVarId

private inductive Target where
  | global (name : Name)
  | localFn (owner : Name) (id : FVarId)
  deriving BEq, Hashable

/-- Constructor origins retain fields separately. Mixing a record's data and callback
fields would turn a known callback into an opaque value just because it captures input. -/
private inductive Origin where
  | callable (target : Target) (supplied : Nat)
  | constructor (site : ValueKey)
  | unresolved
  /-- A host's reactor, supplied at a root: its answers are host ingress (row 394 (1)). -/
  | ingress
  deriving BEq, Hashable, Inhabited

/-- What the analysis reads besides the flows, as data: the persisted mono declarations, whose
parameter counts are the globals' arities, and the mono type of a host reactor. -/
structure Context where
  /-- The persisted mono declarations (`OCaml5.Lcnf.persistedMonoIndex`). -/
  mono : MonoIndex
  /-- The mono type of `Effect4.Run.Reactor σ`, its state `σ` written `lcAny`; `none` when the
  environment has no reactor. -/
  reactor : Option Lean.Expr

/-- Whether a mono type is the reactor template at one state: equal to the template with every
`lcAny` of the template replaced by one type, the same at each position (`Reactor τ`, any `τ`).
The template's `lcAny` stand for its state alone: the compiler writes each free variable so. -/
partial def isReactorType (template ty : Lean.Expr) : Bool :=
  (go template ty none).isSome
where
  go (t e : Lean.Expr) (state : Option Lean.Expr) : Option (Option Lean.Expr) :=
    match t, e with
    | .mdata _ t, e => go t e state
    | t, .mdata _ e => go t e state
    | .const ``lcAny _, e =>
      match state with
      | none => some (some e)
      | some s => if s == e then some state else none
    | .forallE _ d₁ b₁ _, .forallE _ d₂ b₂ _ => go d₁ d₂ state >>= go b₁ b₂
    | .app f₁ a₁, .app f₂ a₂ => go f₁ f₂ state >>= go a₁ a₂
    | t, e => if t == e then some state else none

private structure CallableState where
  values : Std.HashMap ValueKey (Std.HashSet Origin) := {}
  facts : Nat := 0
  /-- Each source's destinations, in the order they were installed. -/
  edges : Std.HashMap ValueKey (Array ValueKey) := {}
  /-- The installed edges, for the membership test. -/
  installed : Std.HashSet (ValueKey × ValueKey) := {}
  pending : Array (ValueKey × Origin) := #[]
  /-- Each value that is a field of a saturated constructor application, with those
  applications. -/
  fieldOf : Std.HashMap ValueKey (Array ValueKey) := {}
  /-- The constructor applications whose origin is in the graph: a field of each holds a fact. -/
  live : Std.HashSet ValueKey := {}
  /-- The live applications, in the order they became live; the walk adds their origins. -/
  waking : Array ValueKey := #[]

/-- A key's set and a source's destinations are updated in place (`Std.HashMap.alter`): a copy of
the set or the array at every new fact made the walk quadratic in a key's facts (LC-4).

A constructor application's origin enters the graph once a field of it holds a fact. A field
with no fact makes no projection of the application carry a callable or an unknown value, so
the origin changes no answer before then. Before LC-4 every application's origin entered at once,
and they were 93 percent of the facts. -/
private def addOrigins (s : CallableState) (key : ValueKey) (values : Array Origin) : CallableState :=
  values.foldl (fun s value =>
    if (s.values.getD key {}).contains value then s else
      let s := { s with
        values := s.values.alter key fun old => some ((old.getD {}).insert value)
        facts := s.facts + 1
        pending := s.pending.push (key, value) }
      (s.fieldOf.getD key #[]).foldl (fun s site =>
        if s.live.contains site then s
        else { s with live := s.live.insert site, waking := s.waking.push site }) s) s

private def addEdge (s : CallableState) (source destination : ValueKey) : CallableState :=
  if s.installed.contains (source, destination) then s else
    let s := { s with
      edges := s.edges.alter source fun old => some ((old.getD #[]).push destination)
      installed := s.installed.insert (source, destination) }
    addOrigins s destination (s.values.getD source {}).toArray

/-- A global's arity in mono LCNF: its flow's parameters, else its mono declaration's (a builtin
or an extern row has no flow), else a constructor's parameters and fields, else the head foralls
of its kernel type. -/
private def globalArity (ctx : Context) (env : Environment) (byName : Std.HashMap Name Flow)
    (n : Name) : Nat :=
  match byName[n]? with
  | some f => f.params.size
  | none => match ctx.mono.findIn? env n with
    | some decl => decl.params.size
    | none => match env.find? n with
      | some (.ctorInfo ci) => ci.numParams + ci.numFields
      | some ci => ci.type.getNumHeadForalls
      | none => 0

/-- Resolve internal calls in a finite closed-world value graph. Unknown root values and
unknown call results stay opaque; absence of a discovered target never establishes safety.
Only the unknown-production markers are refined here; scalar-narrowing checks remain. -/
private def resolveCallables (ctx : Context) (env : Environment) (roots : Array Name)
    (flows : Array Flow) :
    Option (Array Flow) := Id.run do
  let mut byName : Std.HashMap Name Flow := {}
  let mut constructors : Std.HashMap ValueKey (Name × Array (Arg .pure)) := {}
  let mut fieldOf : Std.HashMap ValueKey (Array ValueKey) := {}
  for flow in flows do
    byName := byName.insert flow.name flow
    for (id, name, args) in flow.globals.toArray do
      if let some (.ctorInfo ci) := env.find? name then
        constructors := constructors.insert (flow.name, id) (name, args)
        if args.size ≥ ci.numParams + ci.numFields then
          for i in [ci.numParams:ci.numParams + ci.numFields] do
            if let some (.fvar field) := args[i]? then
              fieldOf := fieldOf.alter (flow.name, field) fun old =>
                some ((old.getD #[]).push (flow.name, id))
  let mut state : CallableState := { fieldOf }
  for flow in flows do
    if roots.contains flow.name then
      -- a root's parameter is unknown, unless it is a host's reactor: its answers are ingress
      for p in flow.params, ty in flow.paramTypes do
        let host := ctx.reactor.any (isReactorType · ty)
        state := addOrigins state (flow.name, p) #[if host then .ingress else .unresolved]
    for (id, _) in flow.locals.toArray do
      state := addOrigins state (flow.name, id) #[.callable (.localFn flow.name id) 0]
  let targetArity (target : Target) := match target with
    | .global n => globalArity ctx env byName n
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
  -- Each productive pass adds a fact. The computed product bounds all such additions. The two
  -- origins that name no site are `unresolved` and `ingress`.
  let mut sites := 0
  let mut origins := constructors.size + 2
  for flow in flows do
    sites := sites + flow.params.size + flow.globals.size + flow.aliases.size +
      flow.projections.size + flow.localCalls.size + flow.locals.size + 1
    origins := origins + flow.params.size + 1
    for (_, name, _) in flow.globals.toArray do
      origins := origins + globalArity ctx env byName name + 1
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
      projections := projections.alter (flow.name, source) fun old =>
        some ((old.getD #[]).push ((flow.name, result), expected, index))
    for (callee, args, result) in flow.localCalls do
      watchers := watchers.alter (flow.name, callee) fun old =>
        some ((old.getD #[]).push (flow.name, args, result))
    for (id, name, args) in flow.globals.toArray do
      if let some (.ctorInfo ci) := env.find? name then
        -- a saturated application's origin waits for a fact at one of its fields (`addOrigins`)
        unless args.size ≥ ci.numParams + ci.numFields do
          state := addOrigins state (flow.name, id) #[.callable (.global name) args.size]
      else
        state := applyTarget state flow.name (some id) (.global name) 0 args
  let mut cursor := 0
  let mut woken := 0
  for _ in [:sites * origins + constructors.size + 1] do
    if let some site := state.waking[woken]? then
      woken := woken + 1
      state := addOrigins state site #[.constructor site]
      continue
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
      | .callable .. | .ingress => pure ()
    for (owner, args, result) in watchers.getD source #[] do
      match origin with
      | .callable target supplied =>
        state := applyTarget state owner result target supplied args
      | .unresolved =>
        if let some result := result then state := addOrigins state (owner, result) #[.unresolved]
      -- a host's answer is data: a call of anything read out of it is unknown
      | .ingress =>
        if let some result := result then state := addOrigins state (owner, result) #[.unresolved]
      | .constructor _ => pure ()
  -- Exhausting the finite fact bound is a refusal, never an incomplete fixed point.
  unless cursor == state.pending.size && woken == state.waking.size do return none
  let mut out := #[]
  for flow in flows do
    let mut unknown : Std.HashSet FVarId := {}
    -- Partial application constructs a closure; it is not the callee's returned data.
    let mut results := flow.callResults.filter fun (name, result) =>
      match flow.globals[result]? with
      | some (_, args) => args.size ≥ globalArity ctx env byName name
      | none => true
    let mut calls := flow.calls
    for (callee, args, result) in flow.localCalls do
      let choices := state.values.getD (flow.name, callee) {}
      -- the call's targets in one order, by name and supplied count, whatever order the
      -- facts arrived in
      let targets := (choices.toArray.filterMap fun
          | .callable target supplied => some (targetName target, target, supplied)
          | _ => none).qsort fun (a, _, i) (b, _, j) =>
            Name.lt a b || (a == b && i < j)
      if let some result := result then
        -- an ingress origin answers checked host data; any other unresolved call is unknown
        if choices.contains .unresolved || (targets.isEmpty && !choices.contains .ingress) then
          unknown := unknown.insert result
      for (name, target, supplied) in targets do
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
        paramTypes := #[]
        returns := flow.localReturns.getD id #[]
        clockResult := false }
      out := out.push localFlow
  return some out
where
  flowDefault : Flow := { name := .anonymous, params := #[] }
  localName (owner : Name) (id : FVarId) : Name := owner ++ `_clockFlowLocal ++ id.name
  /-- The name a resolved call to `target` is recorded under. -/
  targetName : Target → Name
    | .global n => n
    | .localFn owner id => localName owner id

private def clockCallSlots (summaries : Std.HashMap Name (Array Nat))
    (callee : Name) (args : Array (Arg .pure)) : Array Nat := Id.run do
  if clockIngress callee || callee == `OCaml5.Lcnf.ClockFlow.higherOrderClockResult then
    let mut slots := #[]
    for i in [:args.size] do
      if args[i]! matches .fvar _ then slots := slots.push i
    return slots
  return summaries.getD callee #[]

/-- A flow's dependencies indexed both ways, built once per flow: each value's inputs and each
value's results. The closures below walk them, each value once, where a pass over every
dependency until nothing changed cost one pass per link of the longest chain (LC-4). -/
private structure DepIndex where
  inputsOf : Std.HashMap FVarId (Array FVarId) := {}
  resultsOf : Std.HashMap FVarId (Array FVarId) := {}
  /-- The number of input entries: no closure adds more values than this. -/
  edges : Nat := 0

private def DepIndex.of (flow : Flow) : DepIndex :=
  flow.deps.foldl (fun ix (result, inputs) =>
    { inputsOf := ix.inputsOf.alter result fun old => some ((old.getD #[]) ++ inputs)
      resultsOf := inputs.foldl (fun m input =>
        m.alter input fun old => some ((old.getD #[]).push result)) ix.resultsOf
      edges := ix.edges + inputs.size }) {}

/-- The least set that holds `seeds` and every value `next` gives of a member. Each value is
expanded once; a value enters the set at most once, so the seeds and the index's edges bound
the walk. -/
private def closeUnder (next : Std.HashMap FVarId (Array FVarId)) (edges : Nat)
    (seeds : Std.HashSet FVarId) : Std.HashSet FVarId := Id.run do
  let mut out := seeds
  let mut work := seeds.toArray
  let mut cursor := 0
  for _ in [:work.size + edges + 1] do
    let some value := work[cursor]? | break
    cursor := cursor + 1
    for other in next.getD value #[] do
      unless out.contains other do
        out := out.insert other
        work := work.push other
  return out

/-- Which parameters can reach clock ingress, including through another helper. -/
private def clockInputSlots (flow : Flow) (ix : DepIndex)
    (summaries : Std.HashMap Name (Array Nat)) : Array Nat := Id.run do
  let mut seeds : Std.HashSet FVarId := {}
  for (callee, args, _) in flow.calls do
    for i in clockCallSlots summaries callee args do
      if let some (.fvar value) := args[i]? then seeds := seeds.insert value
  let needed := closeUnder ix.inputsOf ix.edges seeds
  let mut slots := #[]
  for i in [:flow.params.size] do
    if needed.contains flow.params[i]! then slots := slots.push i
  return slots

/-- Propagate both known narrowing and unknown higher-order production through return values.
The two markers stay distinct so a refusal states which evidence is missing. -/
private def clockRisks (flow : Flow) (ix : DepIndex) (narrowedReturns unknownReturns : Std.HashSet Name) :
    Std.HashSet FVarId × Std.HashSet FVarId := Id.run do
  let mut narrowed : Std.HashSet FVarId := {}
  let mut unknown := flow.unknownResults
  for (id, value) in flow.literals.toList do
    if value ≥ 4611686018427387904 then narrowed := narrowed.insert id
  for (callee, result) in flow.callResults do
    if narrowedReturns.contains callee then narrowed := narrowed.insert result
    if unknownReturns.contains callee then unknown := unknown.insert result
  return (closeUnder ix.resultsOf ix.edges narrowed, closeUnder ix.resultsOf ix.edges unknown)

/-- The globals referenced by a root include partial applications and wrapper/redArg
links. Local calls stay within their owning flow; their global targets are among those
references. Retain the original input order when selecting the reachable flows. -/
private def rootFlows (input : Array Flow) (byName : Std.HashMap Name Flow) (root : Name) :
    Array Flow := Id.run do
  let mut reached : NameSet := ({} : NameSet).insert root
  let mut work := #[root]
  let mut cursor := 0
  -- Every queued name except the initial root is a distinct name from `input`.
  for _ in [:input.size + 1] do
    if cursor ≥ work.size then break
    let name := work[cursor]!
    cursor := cursor + 1
    if let some flow := byName[name]? then
      for (callee, _, _) in flow.calls do
        if byName.contains callee && !reached.contains callee then
          reached := reached.insert callee
          work := work.push callee
  return input.filter fun flow => reached.contains flow.name

/-- Independent exports without a reachable clock boundary do not seed opaque inputs
into another export's shared polymorphic helpers. The remaining roots are still analyzed
as a union: every clock-reaching root and all of its opaque inputs are retained. -/
private def clockRoots (roots : Array Name) (input : Array Flow) : Array Name × Array Flow := Id.run do
  let mut byName : Std.HashMap Name Flow := {}
  for flow in input do byName := byName.insert flow.name flow
  let mut active : Array Name := #[]
  let mut names : NameSet := {}
  for root in roots do
    let selected := rootFlows input byName root
    let relevant := selected.any fun flow => flow.clockResult || flow.calls.any fun (name, _, _) =>
      clockIngress name || name == `OCaml5.Lcnf.ClockFlow.higherOrderClockResult
    if relevant then
      active := active.push root
      for flow in selected do names := names.insert flow.name
  return (active, input.filter fun flow => names.contains flow.name)

/-- Only values reaching a clock boundary are refused. Parameter and returned-value summaries
reach fixed points bounded by the number of facts that can be added. Ordinary Nat arithmetic
and its deliberate saturation stay unchanged. -/
def refusals (ctx : Context) (env : Environment) (roots : Array Name) (input : Array Flow) :
    Array String := Id.run do
  let (roots, input) := clockRoots roots input
  let some flows := resolveCallables ctx env roots input
    | return #["clock callable provenance did not reach a fixed point"]
  let indexes := flows.map DepIndex.of
  let mut summaries : Std.HashMap Name (Array Nat) := {}
  let bound := flows.foldl (fun n flow => n + flow.params.size) 0
  for _ in [:bound + 1] do
    let mut changed := false
    for flow in flows, ix in indexes do
      let slots := clockInputSlots flow ix summaries
      if slots != summaries.getD flow.name #[] then
        summaries := summaries.insert flow.name slots
        changed := true
    unless changed do break
  let mut narrowedReturns : Std.HashSet Name := {}
  let mut unknownReturns : Std.HashSet Name := {}
  for _ in [:2 * flows.size + 1] do
    let before := narrowedReturns.size + unknownReturns.size
    for flow in flows, ix in indexes do
      let (narrowed, unknown) := clockRisks flow ix narrowedReturns unknownReturns
      if flow.returns.any narrowed.contains then narrowedReturns := narrowedReturns.insert flow.name
      if flow.returns.any unknown.contains then unknownReturns := unknownReturns.insert flow.name
    if narrowedReturns.size + unknownReturns.size == before then break
  let mut refusals := #[]
  for flow in flows, ix in indexes do
    let (narrowed, unknown) := clockRisks flow ix narrowedReturns unknownReturns
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

end OCaml5.Lcnf.ClockFlow
