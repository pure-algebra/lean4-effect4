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
  per site, the fields whose argument is not a projection of a source value: the fields `f`
  writes. `#write_census f closure` follows every constant `f` uses under `Effect4.` (helpers,
  matchers, the auxiliaries structural recursion compiles a body into) and attributes each
  site to the definition that holds it.
- `#read_census f` lists the owner fields `f`'s body projects, with the same closure.

Both are `tsv` on `logInfo`, one row per line, so a driver's output is the ledger. Nothing is
changed.
-/

open Lean Meta Elab Command

namespace Effect4.Laws.Auto.Positions

/-- Where the type walk stops and reports. -/
def defaultCarriers : List Name :=
  [`Effect4.Store.Val, `Effect4.Machine.Val, `Effect4.Exit, `Effect4.Cause, `Effect4.Reason,
   `Effects.Program, `Effect4.Machine.Program, `Effect4.Prim]

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

/-- The walk's accumulator: positions, containment edges, the type constants entered. -/
structure Walk where
  positions : Array Position := #[]
  edges : Array Edge := #[]
  seen : Array Name := #[]

/-- The walk, bounded by a depth (`fuel`): a type nests a few dozen deep at most, and the trust
gate refuses unbounded recursion. Running out is a loud refusal, never silence. -/
def walkType (carriers wrappers : List Name) : Nat → Name → String → Option (Name × Nat) →
    String → List String → Expr → Walk → MetaM Walk
  | 0, owner, field, _, _, _, _, w => do
    logWarning m!"REFUSED {owner}.{field}: the type walk ran out of depth"
    return w
  | fuel + 1, owner, field, ctor, shape, wraps, ty, w => do
  let ty ← whnf (← instantiateMVars ty)
  if ← isProp ty then return w
  match ty with
  | .forallE _ d b _ =>
    let dText ← ppExpr d
    walkType carriers wrappers fuel owner field ctor (shape ++ s!"({dText} → _) ") (wraps ++ ["fn"]) b w
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
      if iv.isRec then
        if args.any (mentionsCarrier carriers) then
          logWarning m!"REFUSED {owner}.{field}: recursive type {n} over a carrier"
        return w
      -- the edge is recorded from every parent; the child is entered once
      let edge : Edge := { parent := owner, field, wraps, child := n }
      let w := if w.edges.contains edge then w else { w with edges := w.edges.push edge }
      if w.seen.contains n then return w
      let mut w := { w with seen := w.seen.push n }
      for c in iv.ctors do
        let ci ← getConstInfoCtor c
        let cty := ci.type.instantiateLevelParams ci.levelParams fn.constLevels!
        let some cty := instArgs cty args.toList | do
          logWarning m!"REFUSED {owner}.{field}: {args.size} arguments do not fit {c}"
          return w
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
    | _ =>
      if args.any (mentionsCarrier carriers) then
        logWarning m!"REFUSED {owner}.{field}: unknown type constructor {n} over a carrier"
      return w
  | _ => return w

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

/-- Is `e` field `i` of structure `s` projected from some value? Both spellings: the primitive
projection, and the projection function applied to the structure's parameters and the value. -/
def isProjOf (env : Environment) (s : Name) (i : Nat) : Expr → Bool
  | .proj s' i' _ => s' == s && i' == i
  | .mdata _ b => isProjOf env s i b
  | e =>
    match e.getAppFn with
    | .const f _ =>
      match env.getProjectionFnInfo? f with
      | some info =>
        info.ctorName.getPrefix == s && info.i == i && e.getAppNumArgs == info.numParams + 1
      | none => false
    | _ => false

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

structure Site where
  holder : Name
  owner : Name
  fields : Array String
deriving Inhabited

/-- Every constructor application of an owner type in `e`, with the fields it writes. Bounded
by a depth, as the walk is. -/
def writeSites (env : Environment) (owners : List Name) (holder : Name) :
    Nat → Expr → Array Site → Array Site
  | 0, _, acc => acc
  | fuel + 1, e, acc => Id.run do
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
              if let some a := args[ci.numParams + i]? then
                unless isProjOf env ci.induct i a do
                  written := written.push fields[i]!.toString
          else
            -- a constructor of a sum: every argument is written; label by binder name
            let names := ctorArgNames ci.type ci.numParams
            for i in [:ci.numFields] do
              if (args[ci.numParams + i]?).isSome then
                written := written.push s!"{c.getString!}.{(names[i]?).getD s!"arg{i}"}"
          acc := acc.push { holder, owner := ci.induct, fields := written }
    for a in args do acc := writeSites env owners holder fuel a acc
    writeSites env owners holder fuel fn acc
  | .lam _ d b _ | .forallE _ d b _ =>
    writeSites env owners holder fuel b (writeSites env owners holder fuel d acc)
  | .letE _ t v b _ =>
    writeSites env owners holder fuel b
      (writeSites env owners holder fuel v (writeSites env owners holder fuel t acc))
  | .mdata _ b | .proj _ _ b => writeSites env owners holder fuel b acc
  | _ => acc

/-- Every owner field `e` reads: primitive projections and projection-function applications. -/
def readSites (env : Environment) (owners : List Name) :
    Nat → Expr → Array (Name × String) → Array (Name × String)
  | 0, _, acc => acc
  | fuel + 1, e, acc => Id.run do
  let mut acc := acc
  match e with
  | .proj s i b =>
    if owners.contains s then
      let fields := getStructureFields env s
      acc := acc.push (s, (fields[i]?.map (·.toString)).getD s!"{i}")
    readSites env owners fuel b acc
  | .app .. =>
    if let .const f _ := e.getAppFn then
      if let some info := env.getProjectionFnInfo? f then
        let s := info.ctorName.getPrefix
        if owners.contains s then
          let fields := getStructureFields env s
          acc := acc.push (s, (fields[info.i]?.map (·.toString)).getD s!"{info.i}")
    for a in e.getAppArgs do acc := readSites env owners fuel a acc
    readSites env owners fuel e.getAppFn acc
  | .lam _ d b _ | .forallE _ d b _ =>
    readSites env owners fuel b (readSites env owners fuel d acc)
  | .letE _ t v b _ =>
    readSites env owners fuel b (readSites env owners fuel v (readSites env owners fuel t acc))
  | .mdata _ b => readSites env owners fuel b acc
  | _ => acc

/-- The constants `root` reaches under `Effect4.`, `root` first; a worklist, bounded by the
number of steps it may take. -/
def closure (env : Environment) (root : Name) (seen : Array Name) : Array Name := Id.run do
  let mut seen := seen
  let mut work : Array Name := #[root]
  for _ in [:200000] do
    if work.isEmpty then break
    let n := work.back!
    work := work.pop
    if seen.contains n then continue
    seen := seen.push n
    if let some ci := env.find? n then
      if let some v := ci.value? then
        for c in v.getUsedConstants do
          if c.getRoot == `Effect4 && !seen.contains c then work := work.push c
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
    let names := if withClosure then closure env f #[] else #[f]
    let mut report := m!"step\tholder\towner\tfields"
    let mut count : Nat := 0
    for n in names do
      if let some ci := env.find? n then
        if let some v := ci.value? then
          for s in writeSites env owners n 100000 v #[] do
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
    let names := if withClosure then closure env f #[] else #[f]
    let mut rows : Array (Name × Name × String) := #[]
    for n in names do
      if let some ci := env.find? n then
        if let some v := ci.value? then
          for (s, fld) in readSites env owners 100000 v #[] do
            unless rows.contains (n, s, fld) do rows := rows.push (n, s, fld)
    let mut report := m!"step\tholder\towner\tfield"
    for (n, s, fld) in rows do
      report := report ++ m!"\n{f}\t{n}\t{s}\t{fld}"
    logInfo (report ++ m!"\n# {f}: {names.size} definitions, {rows.size} read sites")

end Effect4.Laws.Auto.Positions
