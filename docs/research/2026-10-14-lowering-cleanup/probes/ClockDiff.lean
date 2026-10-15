import Lean
import OCaml5.Lcnf.Index
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.Translate

/-!
# LC-4's clock differential: the clock boundary's analysis at the base against the head

The base's analysis (`git:3a8eac840:src/OCaml5/Lcnf/ClockFlow.lean`) and the head's, copied with
their private steps, run on the same flows. The flows are the closure of each artifact of
`ocaml/gen/roots.json`, and the closure of each root set that `Test/Audit/ClockLowering.lean`
names. For each set the probe compares the resolved flows, the parameter summaries, the
return markers and the refusals, and the head's copy against the library. It prints AGREE or
DIFFER per set, with each analysis's time.

    lake build Test.Audit.ClockLiteralFixtures
    lake env lean -DwarningAsError=true -M4096 --run \
      docs/research/2026-10-14-lowering-cleanup/probes/ClockDiff.lean
-/

namespace Old
open Lean Compiler LCNF OCaml5.Lcnf OCaml5.Lcnf.ClockFlow

private def clockIngress (n : Name) : Bool :=
  stripRedArg n == `Effect4.ClockMillis.ofNat || n == `Effect4.ClockMillis.positive

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
  deriving BEq, Hashable, Inhabited

private structure CallableState where
  values : Std.HashMap ValueKey (Std.HashSet Origin) := {}
  facts : Nat := 0
  edges : Std.HashMap ValueKey (Array ValueKey) := {}
  pending : Array (ValueKey × Origin) := #[]

private def addOrigins (s : CallableState) (key : ValueKey) (values : Array Origin) : CallableState :=
  values.foldl (fun s value =>
    let old := s.values.getD key {}
    if old.contains value then s else
      { s with
        values := s.values.insert key (old.insert value)
        facts := s.facts + 1
        pending := s.pending.push (key, value) }) s

private def addEdge (s : CallableState) (source destination : ValueKey) : CallableState :=
  let destinations := s.edges.getD source #[]
  if destinations.contains destination then s else
    let s := { s with edges := s.edges.insert source (destinations.push destination) }
    addOrigins s destination (s.values.getD source {}).toArray

private def globalArity (env : Environment) (byName : Std.HashMap Name Flow) (n : Name) : Nat :=
  match byName[n]? with
  | some f => f.params.size
  | none => match env.find? n with
    | some (.ctorInfo ci) => ci.numParams + ci.numFields
    | some ci => ci.type.getNumHeadForalls
    | none => 0

/-- Resolve internal calls in a finite closed-world value graph. Unknown root values and
unknown call results stay opaque; absence of a discovered target never establishes safety.
Only the unknown-production markers are refined here; scalar-narrowing checks remain. -/
private def resolveCallables (env : Environment) (roots : Array Name) (flows : Array Flow) :
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

private def clockCallSlots (summaries : Std.HashMap Name (Array Nat))
    (callee : Name) (args : Array (Arg .pure)) : Array Nat := Id.run do
  if clockIngress callee || callee == `OCaml5.Lcnf.ClockFlow.higherOrderClockResult then
    let mut slots := #[]
    for i in [:args.size] do
      if args[i]! matches .fvar _ then slots := slots.push i
    return slots
  return summaries.getD callee #[]

/-- Which parameters can reach clock ingress, including through another helper. -/
private def clockInputSlots (flow : Flow) (summaries : Std.HashMap Name (Array Nat)) : Array Nat := Id.run do
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
private def clockRisks (flow : Flow) (narrowedReturns unknownReturns : Std.HashSet Name) :
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

/-- The globals referenced by a root include partial applications and wrapper/redArg
links. Local calls stay within their owning flow; their global targets are among those
references. Retain the original input order when selecting the reachable flows. -/
private def rootFlows (input : Array Flow) (root : Name) : Array Flow := Id.run do
  let mut byName : Std.HashMap Name Flow := {}
  for flow in input do byName := byName.insert flow.name flow
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
  let mut active : Array Name := #[]
  let mut names : NameSet := {}
  for root in roots do
    let selected := rootFlows input root
    let relevant := selected.any fun flow => flow.clockResult || flow.calls.any fun (name, _, _) =>
      clockIngress name || name == `OCaml5.Lcnf.ClockFlow.higherOrderClockResult
    if relevant then
      active := active.push root
      for flow in selected do names := names.insert flow.name
  return (active, input.filter fun flow => names.contains flow.name)

/-- Only values reaching a clock boundary are refused. Parameter and returned-value summaries
reach fixed points bounded by the number of facts that can be added. Ordinary Nat arithmetic
and its deliberate saturation stay unchanged. -/
def refusals (env : Environment) (roots : Array Name) (input : Array Flow) : Array String := Id.run do
  let (roots, input) := clockRoots roots input
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



/-- The intermediate results: the resolved flows, the summaries, the return markers. -/
def intermediates (env : Environment) (roots : Array Name) (input : Array Flow) :
    Option (Array Flow) × Array (Name × Array Nat) × Array Name × Array Name := Id.run do
  let (roots, input) := clockRoots roots input
  let some flows := resolveCallables env roots input | return (none, #[], #[], #[])
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
  return (some flows, summaries.toArray, narrowedReturns.toArray, unknownReturns.toArray)

end Old

namespace New
open Lean Compiler LCNF OCaml5.Lcnf OCaml5.Lcnf.ClockFlow

private def clockIngress (n : Name) : Bool :=
  stripRedArg n == `Effect4.ClockMillis.ofNat || n == `Effect4.ClockMillis.positive

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
  deriving BEq, Hashable, Inhabited

private structure CallableState where
  values : Std.HashMap ValueKey (Std.HashSet Origin) := {}
  facts : Nat := 0
  /-- Each source's destinations, in the order they were installed. -/
  edges : Std.HashMap ValueKey (Array ValueKey) := {}
  /-- The installed edges, for the membership test. -/
  installed : Std.HashSet (ValueKey × ValueKey) := {}
  pending : Array (ValueKey × Origin) := #[]

/-- A key's set and a source's destinations are updated in place (`Std.HashMap.alter`): a copy of
the set or the array at every new fact made the walk quadratic in a key's facts (LC-4). -/
private def addOrigins (s : CallableState) (key : ValueKey) (values : Array Origin) : CallableState :=
  values.foldl (fun s value =>
    if (s.values.getD key {}).contains value then s else
      { s with
        values := s.values.alter key fun old => some ((old.getD {}).insert value)
        facts := s.facts + 1
        pending := s.pending.push (key, value) }) s

private def addEdge (s : CallableState) (source destination : ValueKey) : CallableState :=
  if s.installed.contains (source, destination) then s else
    let s := { s with
      edges := s.edges.alter source fun old => some ((old.getD #[]).push destination)
      installed := s.installed.insert (source, destination) }
    addOrigins s destination (s.values.getD source {}).toArray

private def globalArity (env : Environment) (byName : Std.HashMap Name Flow) (n : Name) : Nat :=
  match byName[n]? with
  | some f => f.params.size
  | none => match env.find? n with
    | some (.ctorInfo ci) => ci.numParams + ci.numFields
    | some ci => ci.type.getNumHeadForalls
    | none => 0

/-- Resolve internal calls in a finite closed-world value graph. Unknown root values and
unknown call results stay opaque; absence of a discovered target never establishes safety.
Only the unknown-production markers are refined here; scalar-narrowing checks remain. -/
private def resolveCallables (env : Environment) (roots : Array Name) (flows : Array Flow) :
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
      projections := projections.alter (flow.name, source) fun old =>
        some ((old.getD #[]).push ((flow.name, result), expected, index))
    for (callee, args, result) in flow.localCalls do
      watchers := watchers.alter (flow.name, callee) fun old =>
        some ((old.getD #[]).push (flow.name, args, result))
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
def refusals (env : Environment) (roots : Array Name) (input : Array Flow) : Array String := Id.run do
  let (roots, input) := clockRoots roots input
  let some flows := resolveCallables env roots input
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



/-- The intermediate results: the resolved flows, the summaries, the return markers. -/
def intermediates (env : Environment) (roots : Array Name) (input : Array Flow) :
    Option (Array Flow) × Array (Name × Array Nat) × Array Name × Array Name := Id.run do
  let (roots, input) := clockRoots roots input
  let some flows := resolveCallables env roots input | return (none, #[], #[], #[])
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
  return (some flows, summaries.toArray, narrowedReturns.toArray, unknownReturns.toArray)

end New

open Lean OCaml5 OCaml5.Lcnf

def ms (a b : Nat) : String :=
  let tenths := (b - a) / 100000
  s!"{tenths / 10}.{tenths % 10} ms"

def sortNames (xs : Array Name) : Array Name := xs.qsort Name.lt

def sameFlow (a b : ClockFlow.Flow) : Bool :=
  a.name == b.name && a.params == b.params && a.calls == b.calls && a.callResults == b.callResults
    && a.unknownResults.size == b.unknownResults.size
    && a.unknownResults.toList.all b.unknownResults.contains && a.returns == b.returns

def sameSummaries (a b : Array (Name × Array Nat)) : Bool :=
  a.size == b.size && a.all fun (n, slots) => (b.find? (·.1 == n)).map (·.2) == some slots

/-- One input set, compared old against new: the intermediates and the refusals. -/
def compare (label : String) (env : Environment) (roots : Array Name) (flows : Array ClockFlow.Flow) :
    IO Bool := do
  let t0 ← IO.monoNanosNow
  let oldRefusals := Old.refusals env roots flows
  IO.println s!"{label}: old refusals {oldRefusals.size}"
  let t1 ← IO.monoNanosNow
  let newRefusals := New.refusals env roots flows
  IO.println s!"{label}: new refusals {newRefusals.size}"
  let t2 ← IO.monoNanosNow
  let library := ClockFlow.refusals env roots flows
  IO.println s!"{label}: library refusals {library.size}"
  let t3 ← IO.monoNanosNow
  let (of, os, on, ou) := Old.intermediates env roots flows
  let (nf, ns, nn, nu) := New.intermediates env roots flows
  let flowsAgree := match of, nf with
    | some a, some b => a.size == b.size && (a.zip b).all fun (x, y) => sameFlow x y
    | none, none => true
    | _, _ => false
  let ok := oldRefusals == newRefusals && newRefusals == library && flowsAgree
    && sameSummaries os ns && sortNames on == sortNames nn && sortNames ou == sortNames nu
  IO.println s!"{label}: {if ok then "AGREE" else "DIFFER"}; old {ms t0 t1}, new {ms t1 t2}, library {ms t2 t3}; \
    {(of.map (·.size)).getD 0} resolved flows, {os.size} summaries, {on.size} narrowed and {ou.size} unknown returns, \
    refusals {repr newRefusals}"
  return ok

def flowsOf (env : Environment) (closure : Closure) : Array ClockFlow.Flow := Id.run do
  let mono := OCaml5.Lcnf.persistedMonoIndex env
  let mut flows := #[]
  for t in closure.decls do
    if let some d := mono.findIn? env t.leanName then flows := flows.push (ClockFlow.ofDecl d)
  return flows

def fixtureRoots : List (List Name) :=
  [[`Test.ClockLiteralFixtures.direct], [`Test.ClockLiteralFixtures.numeral],
   [`Test.ClockLiteralFixtures.positive], [`Test.ClockLiteralFixtures.narrowed],
   [`Test.ClockLiteralFixtures.throughWrapper], [`Test.ClockLiteralFixtures.throughNestedWrapper],
   [`Test.ClockLiteralFixtures.throughFactory], [`Test.ClockLiteralFixtures.throughNestedFactory],
   [`Test.ClockLiteralFixtures.throughClockCallback],
   [`Test.ClockLiteralFixtures.throughGenericClockCallback],
   [`Test.ClockLiteralFixtures.throughValue], [`Test.ClockLiteralFixtures.throughKnownNatCallback],
   [`Test.ClockLiteralFixtures.throughUnknown], [`Test.ClockLiteralFixtures.unrelatedNat],
   [`Test.ClockLiteralFixtures.closedCallback], [`Test.ClockLiteralFixtures.closedRecordCallback],
   [`Test.ClockLiteralFixtures.unknownRecordCallback], [`Test.ClockLiteralFixtures.unknownContainer],
   [`Test.ClockLiteralFixtures.closedCallback, `Test.ClockLiteralFixtures.applyNat],
   [`Test.ClockLiteralFixtures.closedCallback, `Test.ClockLiteralFixtures.applyNat,
    `Test.ClockLiteralFixtures.throughUnknown]]

def main (argv : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let recipe ← IO.FS.readFile (argv.headD "ocaml/gen/roots.json")
  let json ← IO.ofExcept (Json.parse recipe)
  let artefacts ← IO.ofExcept (json.getObjValAs? (Array Json) "artefacts")
  let env ← importModules #[{ module := `Effect4.Api }, { module := `Test.Audit.ClockLiteralFixtures }] {} 0
  let ctx : Core.Context :=
    { fileName := "<clock-diff>", fileMap := default, maxHeartbeats := 1000000 * 1000 }
  let act : MetaM Bool := do
    let mut all := true
    for a in artefacts do
      let out ← IO.ofExcept (a.getObjValAs? String "out")
      let roots := (← IO.ofExcept (a.getObjValAs? (Array String) "roots")) ++
        ((a.getObjValAs? (Array String) "coverage").toOption.getD #[])
      let roots := roots.map String.toName
      let ex : Externs ← match a.getObjValAs? String "externs" with
        | .ok path => IO.ofExcept (Externs.parse (← IO.FS.readFile path))
        | .error _ => pure {}
      let (closure, _, _) ← translateClosureInferring roots 2000 {} ex
      all := (← compare out (← getEnv) roots (flowsOf (← getEnv) closure)) && all
    for roots in fixtureRoots do
      let roots := roots.toArray
      let closure ← translateClosure roots
      all := (← compare s!"{roots}" (← getEnv) roots (flowsOf (← getEnv) closure)) && all
    return all
  let (ok, _) ← (act.run' {}).toIO ctx { env := env }
  IO.println (if ok then "clock differential: every input set AGREES" else "clock differential: a DIFFERENCE")
  unless ok do throw (IO.userError "clock differential failed")
