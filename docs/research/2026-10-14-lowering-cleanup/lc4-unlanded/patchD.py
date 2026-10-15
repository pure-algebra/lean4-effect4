from pathlib import Path
p = Path('/Users/pooks/Dev/lean4-effect4-lowering/src/OCaml5/Lcnf/ClockFlow.lean'); s = p.read_text()
reps = [
("""private structure CallableState where
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
""",
"""private structure CallableState where
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
"""),
("""  let mut byName : Std.HashMap Name Flow := {}
  let mut constructors : Std.HashMap ValueKey (Name × Array (Arg .pure)) := {}
  for flow in flows do
    byName := byName.insert flow.name flow
    for (id, name, args) in flow.globals.toArray do
      if let some (.ctorInfo _) := env.find? name then
        constructors := constructors.insert (flow.name, id) (name, args)
  let mut state : CallableState := {}
""",
"""  let mut byName : Std.HashMap Name Flow := {}
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
"""),
("""    for (id, name, args) in flow.globals.toArray do
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
""",
"""    for (id, name, args) in flow.globals.toArray do
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
"""),
("""  -- Exhausting the finite fact bound is a refusal, never an incomplete fixed point.
  unless cursor == state.pending.size do return none
""",
"""  -- Exhausting the finite fact bound is a refusal, never an incomplete fixed point.
  unless cursor == state.pending.size && woken == state.waking.size do return none
"""),
("""    for (callee, args, result) in flow.localCalls do
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
""",
"""    for (callee, args, result) in flow.localCalls do
      let choices := state.values.getD (flow.name, callee) {}
      -- the call's targets in one order, by name and supplied count, whatever order the
      -- facts arrived in
      let targets := (choices.toArray.filterMap fun
          | .callable target supplied => some (targetName target, target, supplied)
          | _ => none).qsort fun (a, _, i) (b, _, j) =>
            Name.lt a b || (a == b && i < j)
      if let some result := result then
        if targets.isEmpty || choices.contains .unresolved then unknown := unknown.insert result
      for (name, target, supplied) in targets do
        -- Captured arguments were checked where the partial application was made;
        -- retain original positions for the arguments supplied at this invocation.
        calls := calls.push (name, (Array.replicate supplied .erased) ++ args, false)
        if let some result := result then
          if supplied + args.size ≥ targetArity target then
            results := results.push (name, result)
"""),
("""  return some out
where
  flowDefault : Flow := { name := .anonymous, params := #[] }
""",
"""  return some out
where
  flowDefault : Flow := { name := .anonymous, params := #[] }
  localName (owner : Name) (id : FVarId) : Name := owner ++ `_clockFlowLocal ++ id.name
  /-- The name a resolved call to `target` is recorded under. -/
  targetName : Target → Name
    | .global n => n
    | .localFn owner id => localName owner id
"""),
("""  unless cursor == state.pending.size && woken == state.waking.size do return none
  let localName (owner : Name) (id : FVarId) := owner ++ `_clockFlowLocal ++ id.name
  let mut out := #[]
""",
"""  unless cursor == state.pending.size && woken == state.waking.size do return none
  let mut out := #[]
"""),
]
for a, b in reps:
    assert s.count(a) == 1, a[:70]
    s = s.replace(a, b, 1)
p.write_text(s)
print("patched")
