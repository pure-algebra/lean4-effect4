import Lean

/-!
# Laws.Auto.Positions — the value-holding positions of a state, and who writes them

Three censuses over the environment, beside `#traversal_census` and `#auto_census`
(`docs/research/2026-09-18-position-census-design.md`):

- `#position_census R₁ R₂ …` walks the types reachable from each root (a type constant or an
  abbreviation of one) and lists every **position**: a field or constructor argument whose type,
  under the wrappers, is a **carrier** (`Val`, `Exit`, `Cause`, `Reason`, `Effects.Program`,
  `Machine.Program`, `Prim`). A function type is walked into its codomain and recorded as such
  (a continuation or a hook). A head that is neither an inductive, a wrapper, a carrier nor
  unfoldable, with a carrier in its arguments, is a **refusal**, as is a recursive inductive over
  a carrier: the walk never goes quiet on a container it does not know.
- `#write_census f` lists every constructor application of an owner type in `f`'s body and,
  per site, the potentially written fields. A field is omitted only when a caller identifies
  its exact source record. `#write_census f closure` follows every constant `f` uses under `Effect4.` (helpers,
  matchers, the auxiliaries structural recursion compiles a body into) and attributes each
  site to the definition that holds it.
- `#read_census f` lists the owner fields `f`'s body projects, with the same closure.

Commands print diagnostic rows. The structured Lean results are the analysis interface;
rendered output is not a proof ledger or an authoritative input.
-/

open Lean Meta Elab Command

namespace Effect4.Laws.Auto.Positions

/-- Where the type walk stops and reports. -/
def defaultCarriers : List Name :=
  [`Effect4.Store.Val, `Effect4.Machine.Val, `Effect4.Exit, `Effect4.Cause, `Effect4.Reason,
   `Effects.Program, `Effect4.Machine.Program, `Effect4.Prim,
   `Effect4.Program.EffName]

/-- Containers the walk sees through, recording them in the shape. -/
def defaultWrappers : List Name := [`List, `Option, `Prod, `Array, `Except, `Sum]

/-- Primitive types that hold no carrier; the walk does not enter them. -/
def stops : List Name :=
  [`Nat, `Bool, `String, `Unit, `PUnit, `Fin, `UInt8, `UInt32, `UInt64, `ByteArray, `BitVec, `Char, `Int]

/-- `parent.field` reaches the owner `child` (a structure or inductive the walk entered). -/
structure Edge where
  parent : Name
  field : String
  /-- The wrappers between the parent's field and the child, outermost first (`List`, `Option`,
  `Prod`, `fn`). -/
  wraps : List String
  child : Name
deriving Inhabited, BEq

structure Position where
  owner : Name
  /-- `field` of a structure, `ctor.arg` of an inductive with several constructors. -/
  field : String
  /-- The constructor and the argument's index, for an owner with several constructors. -/
  ctor : Option (Name × Nat)
  /-- The wrappers and function domains between the owner and the carrier, outermost first. -/
  shape : String
  /-- The same, as tokens: `List`, `Option`, `Prod`, `Except`, `Sum`, `fn`. -/
  wraps : List String
  carrier : Name
deriving Inhabited, BEq

def Position.key (p : Position) : String := s!"{p.owner}.{p.field}"

/-- Instantiate a constructor type's leading binders with the type's arguments. -/
def instArgs : Expr → List Expr → Option Expr
  | e, [] => some e
  | .forallE _ _ b _, a :: rest => instArgs (b.instantiate1 a) rest
  | _, _ => none

def mentionsCarrier (carriers : List Name) (e : Expr) : Bool :=
  carriers.any fun c => e.getUsedConstants.contains c

/-- A binder name a macro made carries scopes; print it by index instead. -/
def argLabel (name : Name) (i : Nat) : String :=
  if name.hasMacroScopes then s!"arg{i}" else name.toString

/-- The walk's accumulator: positions, containment edges, the instantiated types entered. -/
structure Walk where
  positions : Array Position := #[]
  edges : Array Edge := #[]
  seen : Array Expr := #[]

/-- The walk, bounded by a depth (`fuel`): a type nests a few dozen deep at most, and the trust
gate refuses unbounded recursion. Running out is a loud refusal, never silence. -/
def walkType (carriers wrappers : List Name) : Nat → Name → String → Option (Name × Nat) →
    String → List String → Expr → Walk → MetaM Walk
  | 0, owner, field, _, _, _, _, _ =>
    throwError "REFUSED {owner}.{field}: the type walk ran out of depth"
  | fuel + 1, owner, field, ctor, shape, wraps, ty, w => do
  let ty ← whnf (← instantiateMVars ty)
  if ← isProp ty then return w
  match ty with
  | .forallE n d b bi =>
    let dText ← ppExpr d
    withLocalDecl n bi d fun x =>
      walkType carriers wrappers fuel owner field ctor (shape ++ s!"({dText} → _) ")
        (wraps ++ ["fn"]) (b.instantiate1 x) w
  | _ =>
  let fn := ty.getAppFn
  let args := ty.getAppArgs
  match fn with
  | .const n _ =>
    if carriers.contains n then
      return { w with positions := w.positions.push { owner, field, ctor, shape, wraps, carrier := n } }
    if stops.contains n then return w
    if wrappers.contains n then
      let mut w := w
      let mut i := 0
      for a in args do
        -- a product or a sum records the side, so the emitter can read the component
        let tok := if n == `Prod || n == `Sum || n == `Except then s!"{n.getString!}.{i + 1}" else n.getString!
        w ← walkType carriers wrappers fuel owner field ctor (shape ++ s!"{tok} ") (wraps ++ [tok]) a w
        i := i + 1
      return w
    match (← getEnv).find? n with
    | some (.inductInfo iv) =>
      unless args.size == iv.numParams && iv.numIndices == 0 do
        throwError "REFUSED {owner}.{field}: {n} needs a closed, non-indexed instantiation"
      if iv.isRec then
        throwError "REFUSED {owner}.{field}: recursive type {n} needs an explicit carrier or wrapper"
      -- the edge is recorded from every parent; the child is entered once
      let edge : Edge := { parent := owner, field, wraps, child := n }
      let w := if w.edges.contains edge then w else { w with edges := w.edges.push edge }
      if w.seen.contains ty then return w
      let mut w := { w with seen := w.seen.push ty }
      for c in iv.ctors do
        let ci ← getConstInfoCtor c
        let cty := ci.type.instantiateLevelParams ci.levelParams fn.constLevels!
        let some cty := instArgs cty args.toList |
          throwError "REFUSED {owner}.{field}: {args.size} arguments do not fit {c}"
        w ← forallTelescope cty fun xs _ => do
          let mut w := w
          let mut i := 0
          for x in xs do
            let xty ← inferType x
            let name := (← x.fvarId!.getDecl).userName
            let single := iv.ctors.length == 1
            let label := if single then argLabel name i else s!"{c.getString!}.{argLabel name i}"
            w ← walkType carriers wrappers fuel n label (if single then none else some (c, i)) "" [] xty w
            i := i + 1
          return w
      return w
    | _ => throwError "REFUSED {owner}.{field}: cannot inspect type constructor {n}"
  | _ => throwError "REFUSED {owner}.{field}: cannot inspect type {ty}"

/-- The walk from a root: a type constant, or a definition whose value is one. -/
def walkOf (root : Name) (carriers := defaultCarriers) (wrappers := defaultWrappers) :
    MetaM Walk := do
  let ci ← getConstInfo root
  let v := match ci.value? with
    | some v => v
    | none => mkConst root (ci.levelParams.map mkLevelParam)
  walkType carriers wrappers 64 root "" none "" [] v {}

/-- The positions reachable from a root. -/
def positionsOf (root : Name) (carriers := defaultCarriers) (wrappers := defaultWrappers) :
    MetaM (Array Position) := do
  return (← walkOf root carriers wrappers).positions

syntax (name := positionCensus) "#position_census " ident+ : command

@[command_elab positionCensus] def elabPositionCensus : CommandElab := fun stx => do
  let roots := stx[1].getArgs.map (·.getId)
  liftTermElabM do
    let mut report := m!"root\towner\tfield\tshape\tcarrier"
    for root in roots do
      for p in ← positionsOf root do
        report := report ++ m!"\n{root}\t{p.owner}\t{p.field}\t{p.shape}\t{p.carrier}"
    logInfo report

syntax (name := edgeCensus) "#edge_census " ident+ : command

/-- The containment edges: which field of which owner reaches which structure or inductive,
under which wrappers. The skeleton emitter nests the `Ok` structures along them. -/
@[command_elab edgeCensus] def elabEdgeCensus : CommandElab := fun stx => do
  let roots := stx[1].getArgs.map (·.getId)
  liftTermElabM do
    let mut report := m!"root\tparent\tfield\twraps\tchild"
    for root in roots do
      for e in (← walkOf root).edges do
        report := report ++ m!"\n{root}\t{e.parent}\t{e.field}\t{e.wraps}\t{e.child}"
    logInfo report

/-! ## Writes and reads -/

/-- The value from which `e` projects a field. Equality of field numbers alone
never establishes that an update preserved a field: the source record matters. -/
def projectionSource? (env : Environment) (s : Name) (i : Nat) : Expr → Option Expr
  | .proj s' i' base => if s' == s && i' == i then some base else none
  | .mdata _ b => projectionSource? env s i b
  | e => do
    let .const f _ := e.getAppFn | none
    let info ← env.getProjectionFnInfo? f
    if info.ctorName.getPrefix == s && info.i == i && e.getAppNumArgs == info.numParams + 1
      then e.getAppArgs[info.numParams]?
      else none

/-- A frame is relative to this particular source value, never to any record of its type. -/
def isProjOf (env : Environment) (s : Name) (i : Nat) (source e : Expr) : Bool :=
  projectionSource? env s i e == some source

/-- The binder names of a constructor's fields, after its parameters. -/
def ctorArgNames (ty : Expr) (numParams : Nat) : Array String := Id.run do
  let mut ty := ty
  let mut i := 0
  let mut out := #[]
  while true do
    match ty with
    | .forallE n _ b _ =>
      if i ≥ numParams then out := out.push (argLabel n (i - numParams))
      ty := b; i := i + 1
    | _ => break
  return out

/-- Compiler matcher provenance is diagnostic data, never the stable identity of a goal. -/
structure Arm where
  matcher : Name
  alternative : Nat
deriving Inhabited, Repr, BEq

structure Site where
  holder : Name
  owner : Name
  fields : Array String
  arms : Array Arm := #[]
deriving Inhabited

/-- Every reconstructed field is a potential write unless it is copied from the
explicit source record. Callers without that source receive a conservative inventory. -/
def writeSites (env : Environment) (owners : List Name) (holder : Name)
    (fuel : Nat) (e : Expr) (acc : Array Site) (source? : Option Expr := none) :
    MetaM (Array Site) := go fuel e acc #[]
where
  go : Nat → Expr → Array Site → Array Arm → MetaM (Array Site)
    | 0, _, _, _ => throwError "position analysis: write scan ran out of depth"
    | fuel + 1, e, acc, arms => do
      let mut acc := acc
      match e with
      | .app .. =>
        let fn := e.getAppFn
        let args := e.getAppArgs
        if let .const c _ := fn then
          if let some (.ctorInfo ci) := env.find? c then
            if owners.contains ci.induct then
              let mut written : Array String := #[]
              if isStructure env ci.induct then
                let fields := getStructureFields env ci.induct
                for i in [:fields.size] do
                  let unchanged := (args[ci.numParams + i]?).any fun a =>
                    source?.any (fun source => isProjOf env ci.induct i source a)
                  unless unchanged do
                    written := written.push fields[i]!.toString
              else
                let names := ctorArgNames ci.type ci.numParams
                for i in [:ci.numFields] do
                  written := written.push s!"{c.getString!}.{(names[i]?).getD s!"arg{i}"}"
              acc := acc.push { holder, owner := ci.induct, fields := written, arms }
        let matcher? ← matchMatcherApp? e (alsoCasesOn := true)
        for j in [:args.size] do
          let path := match matcher? with
            | some app =>
              let first := app.toMatcherInfo.getFirstAltPos
              if first ≤ j && j < first + app.alts.size then
                arms.push ⟨app.matcherName, j - first⟩
              else arms
            | none => arms
          acc ← go fuel args[j]! acc path
        go fuel fn acc arms
      | .lam n d b bi | .forallE n d b bi =>
        withLocalDecl n bi d fun x => go fuel (b.instantiate1 x) acc arms
      | .letE n t v b _ =>
        acc ← go fuel v acc arms
        withLetDecl n t v fun x => go fuel (b.instantiate1 x) acc arms
      | .mdata _ b | .proj _ _ b => go fuel b acc arms
      | _ => return acc

/-- All fields of a value used opaquely. Pattern matchers and predicate parameters
consume whole values; a projection-only census must not treat those uses as independent. -/
private def wholeReads (owners : List Name) (e : Expr) (acc : Array (Name × String)) :
    MetaM (Array (Name × String)) := do
  let ty ← whnf (← inferType e)
  let .const owner _ := ty.getAppFn | return acc
  unless owners.contains owner do return acc
  let env ← getEnv
  if isStructure env owner then
    return acc ++ (getStructureFields env owner).map (fun f => (owner, f.toString))
  let .inductInfo info ← getConstInfo owner | return acc
  let mut acc := acc
  for c in info.ctors do
    let ci ← getConstInfoCtor c
    for f in ctorArgNames ci.type ci.numParams do
      acc := acc.push (owner, s!"{c.getString!}.{f}")
  return acc

/-- Conservative field dependencies, opening binders and tracking whole-value uses.
A projected record is visited without treating the projection as reading every field. -/
def readSites (env : Environment) (owners : List Name) (fuel : Nat) (e : Expr)
    (acc : Array (Name × String)) : MetaM (Array (Name × String)) := do
  return (← go fuel e acc true).foldl
    (fun out entry => if out.contains entry then out else out.push entry) #[]
where
  go : Nat → Expr → Array (Name × String) → Bool → MetaM (Array (Name × String))
    | 0, _, _, _ => throwError "position analysis: read scan ran out of depth"
    | fuel + 1, e, acc, whole => do
      let mut acc ← if whole then wholeReads owners e acc else pure acc
      match e with
      | .proj s i b =>
        if owners.contains s then
          let fields := getStructureFields env s
          acc := acc.push (s, (fields[i]?.map (·.toString)).getD s!"{i}")
        go fuel b acc false
      | .app .. =>
        if let .const f _ := e.getAppFn then
          if let some info := env.getProjectionFnInfo? f then
            if e.getAppNumArgs == info.numParams + 1 then
              let s := info.ctorName.getPrefix
              if owners.contains s then
                let fields := getStructureFields env s
                acc := acc.push (s, (fields[info.i]?.map (·.toString)).getD s!"{info.i}")
              return ← go fuel e.getAppArgs[info.numParams]! acc false
        for a in e.getAppArgs do acc ← go fuel a acc true
        go fuel e.getAppFn acc false
      | .lam n d b bi | .forallE n d b bi =>
        acc ← go fuel d acc true
        withLocalDecl n bi d fun x => go fuel (b.instantiate1 x) acc true
      | .letE n t v b _ =>
        acc ← go fuel v acc true
        withLetDecl n t v fun x => go fuel (b.instantiate1 x) acc whole
      | .mdata _ b => go fuel b acc whole
      | _ => return acc

/-- A caller-selected declaration boundary, with a loud work-budget failure. -/
def closure (env : Environment) (root : Name) (seen : Array Name)
    (namespaceRoot : Name := `Effect4) (budget : Nat := 200000) : MetaM (Array Name) := do
  let mut seen := seen
  let mut work : Array Name := #[root]
  for _ in [:budget] do
    if work.isEmpty then return seen
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.push n
    if let some ci := env.find? n then
      if let some v := ci.value? then
        for c in v.getUsedConstants do
          if namespaceRoot.isPrefixOf c && !seen.contains c then work := work.push c
  unless work.isEmpty do throwError "position analysis: closure scan ran out of work at {root}"
  return seen

/-- The owner types of a position list. -/
def ownersOf (ps : Array Position) : List Name :=
  ps.foldl (fun acc p => if acc.contains p.owner then acc else p.owner :: acc) []

syntax (name := writeCensus) "#write_census " ident (&" closure")? " over " ident+ : command

/-- `#write_census f [closure] over R₁ …`: the write sites of `f` (and, with `closure`, of every
definition it reaches) on the owner types of the roots' positions, one row per site. -/
@[command_elab writeCensus] def elabWriteCensus : CommandElab := fun stx => do
  let f := stx[1].getId
  let withClosure := !stx[2].isNone
  let roots := stx[4].getArgs.map (·.getId)
  liftTermElabM do
    let env ← getEnv
    let mut ps : Array Position := #[]
    for r in roots do ps := ps ++ (← positionsOf r)
    let owners := ownersOf ps
    let names ← if withClosure then closure env f #[] else pure #[f]
    let mut report := m!"step\tholder\towner\tfields"
    let mut count : Nat := 0
    for n in names do
      if let some ci := env.find? n then
        if let some v := ci.value? then
          for s in ← writeSites env owners n 100000 v #[] do
            unless s.fields.isEmpty do
              count := count + 1
              report := report ++ m!"\n{f}\t{s.holder}\t{s.owner}\t{s.fields}"
    logInfo (report ++ m!"\n# {f}: {names.size} definitions, {count} write sites")

syntax (name := readCensus) "#read_census " ident (&" closure")? " over " ident+ : command

@[command_elab readCensus] def elabReadCensus : CommandElab := fun stx => do
  let f := stx[1].getId
  let withClosure := !stx[2].isNone
  let roots := stx[4].getArgs.map (·.getId)
  liftTermElabM do
    let env ← getEnv
    let mut ps : Array Position := #[]
    for r in roots do ps := ps ++ (← positionsOf r)
    let owners := ownersOf ps
    let names ← if withClosure then closure env f #[] else pure #[f]
    let mut rows : Array (Name × Name × String) := #[]
    for n in names do
      if let some ci := env.find? n then
        if let some v := ci.value? then
          for (s, fld) in ← readSites env owners 100000 v #[] do
            unless rows.contains (n, s, fld) do rows := rows.push (n, s, fld)
    let mut report := m!"step\tholder\towner\tfield"
    for (n, s, fld) in rows do
      report := report ++ m!"\n{f}\t{n}\t{s}\t{fld}"
    logInfo (report ++ m!"\n# {f}: {names.size} definitions, {rows.size} read sites")

end Effect4.Laws.Auto.Positions
