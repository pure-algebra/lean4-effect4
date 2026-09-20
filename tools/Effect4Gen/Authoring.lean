import Lean
import Tools.GeneratedStamp

/-!
# Effect4Gen.Authoring — the binder table's two projections

Reads `tools/Effect4Gen/binders.json`, the one statement of which argument of which
constructor is elaborated under which binders (review log B17), and the program family's
constructor declarations from the Lean environment, and emits:

* group `Binders` → `src/Effect4/Program/Binders.lean`: `Node.binders` (values bound at a
  child), `Node.closedChild` (children typed in the empty scope) and `Node.childLevel`, the
  table the hoisting proofs, the readers, the printer and the generator read instead of
  each spelling the discipline again; and the authoring profile's head lists (DI-84).
* group `Authoring` → `src/Effect4/Program/Authoring/Lifts.lean`: for every constructor an
  author may write, its lift through the scope reader of `Program/Authoring.lean`
  (DI-83): one definition per constructor, its slot names as `String` parameters, each
  argument elaborated under exactly the binders the table gives it, at the child path
  `Node.child` assigns it.
* group `Scoped` → `src/Effect4/Program/Scoped.lean`: the same table as an algebra of the
  program signature (`Fold.lean`) on the carrier `Nat → Bool`, so `Eff.scopedAt n e` (every
  variable below its level) is one `cata_eff`, with one `rfl` equation per constructor.
* group `ScopedLaws` → `src/Effect4/Laws/Program/Authoring/Lifts.lean`: for every lift, the
  theorem that it preserves scope, with one proof script for all of them.
* group `NodeLenses` → `src/Effect4/Program/NodeLenses.lean`: `Node.child` and
  `Node.setChild`, one arm per node-typed constructor argument, from the declarations alone.

Run by `tools/Effect4Gen/Driver.lean` like the other emitters:

    lake env lean -M 4096 --run tools/Effect4Gen/Authoring.lean --group Binders
      --imports Effect4.Program.Refs --out src/Effect4/Program/Binders.lean
      --append tools/Effect4Gen/guards/binders.lean -- Effect4.Program.Eff
-/

open Lean Meta Elab

namespace Effect4Gen.Authoring

def shortName (n : Name) : String := n.componentsRev.head!.toString

def srcOf (e : Expr) : MetaM String := do
  withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.universes false) do
    return toString (← ppExpr e)

/-! ## The table -/

structure Row where
  ctor : Name
  slots : List String
  args : List (List Nat)
  closed : List Nat
  whenHead : Option Name
  /-- The argument whose head `whenHead` names: `0` unless the row says otherwise. A row
  conditioned on a data argument (`select` on its `Decision`) is one of several for the
  constructor, one per head, and each gets its own lift (`lift`). -/
  whenArg : Nat
  /-- The lift's name for a head-conditioned row on a data argument. -/
  lift : Option String

structure Profile where
  families : List Name
  readerOnly : List Name
  machineOnly : List Name
  handWritten : List Name
  renames : List (Name × String)

structure Table where
  rows : List Row
  profile : Profile

def getArrD (j : Json) (key : String) : Except String (Array Json) :=
  match j.getObjVal? key with
  | .ok v => v.getArr?
  | .error _ => .ok #[]

def getNames (j : Json) (key : String) : Except String (List Name) := do
  let arr ← getArrD j key
  let strs ← arr.mapM Json.getStr?
  return (strs.map String.toName).toList

def parseRow (j : Json) : Except String Row := do
  let ctor ← (← j.getObjVal? "ctor").getStr?
  let slots ← (← (← j.getObjVal? "slots").getArr?).mapM Json.getStr?
  let args ← (← (← j.getObjVal? "args").getArr?).mapM fun a => do
    let ns ← (← a.getArr?).mapM Json.getNat?
    return ns.toList
  let closed ← (← getArrD j "closed").mapM Json.getNat?
  let whenHead ← match j.getObjVal? "whenHead" with
    | .ok v => do let s ← v.getStr?; pure (some s.toName)
    | .error _ => pure none
  let whenArg ← match j.getObjVal? "whenArg" with
    | .ok v => v.getNat?
    | .error _ => pure 0
  let lift ← match j.getObjVal? "lift" with
    | .ok v => do let s ← v.getStr?; pure (some s)
    | .error _ => pure none
  return { ctor := ctor.toName, slots := slots.toList, args := args.toList,
           closed := closed.toList, whenHead, whenArg, lift }

def parseTable (text : String) : Except String Table := do
  let j ← Json.parse text
  let rows ← (← (← j.getObjVal? "rows").getArr?).mapM parseRow
  let p ← j.getObjVal? "profile"
  let families ← getNames p "families"
  let readerOnly ← getNames p "readerOnly"
  let machineOnly ← getNames p "machineOnly"
  let handWritten ← getNames p "handWritten"
  let renames ← match p.getObjVal? "renames" with
    | .ok (.obj kvs) => pure (kvs.foldl (fun acc k v =>
        acc ++ [(k.toName, (Json.getStr? v).toOption.getD "")]) [])
    | _ => pure []
  return { rows := rows.toList,
           profile := { families, readerOnly, machineOnly, handWritten, renames } }

/-! ## The family, from the environment -/

inductive ArgKind
  | node (fam : Name)
  | term
  | optionTerm
  | cause
  | other
  deriving BEq, Repr

structure Arg where
  name : String
  tyText : String
  kind : ArgKind

structure Ctor where
  fam : Name
  name : Name
  short : String
  numFields : Nat
  args : List Arg

def famOfHead (members : List Name) (ty : Expr) : Option Name :=
  match ty.getAppFn with
  | .const n _ => if members.contains n then some n else none
  | _ => none

def readCtor (members : List Name) (c : Name) : MetaM Ctor := do
  let ci ← getConstInfoCtor c
  let args ← forallBoundedTelescope ci.type (ci.numParams + ci.numFields) fun xs _ => do
    let mut acc := []
    for x in xs[ci.numParams:] do
      let ty ← inferType x
      let name := (← x.fvarId!.getDecl).userName.toString
      let tyText ← srcOf ty
      let kind := match famOfHead members ty with
        | some f => ArgKind.node f
        | none =>
          if tyText == "Effect4.Program.Term" then ArgKind.term
          else if tyText == "Option Effect4.Program.Term" then ArgKind.optionTerm
          else if tyText == "Effect4.Program.CauseTerm" then ArgKind.cause
          else ArgKind.other
      acc := acc ++ [({ name, tyText, kind } : Arg)]
    return acc
  return { fam := ci.induct, name := c, short := shortName c, numFields := ci.numFields, args }

/-- Every constructor of every family named, each with its arguments. The program family
is the mutual block of `Eff`; `CauseTerm` stands alone. -/
def readFamilies (fams : List Name) : MetaM (List Ctor) := do
  let members := (← getConstInfoInduct `Effect4.Program.Eff).all
  let mut out := []
  for fam in fams do
    let fv ← getConstInfoInduct fam
    for c in fv.ctors do
      out := out ++ [← readCtor members c]
  return out

/-- `Node.child`'s index of a node-typed argument: its rank among the node-typed ones. -/
def nodeRank (c : Ctor) (j : Nat) : Option Nat :=
  let ranked := (c.args.zipIdx.filter fun (a, _) => match a.kind with | .node _ => true | _ => false)
  (ranked.zipIdx.find? fun ((_, k), _) => k == j).map (·.2)

def nodeCtorOf : Name → Option String
  | `Effect4.Program.Eff => some "eff"
  | `Effect4.Program.Stmts => some "stmts"
  | `Effect4.Program.Stmt => some "stmt"
  | `Effect4.Program.ActionTerm => some "action"
  | `Effect4.Program.Effs => some "effs"
  | `Effect4.Program.LayerTerm => some "layer"
  | `Effect4.Program.LayerTerms => some "layers"
  | _ => none

def wild (n : Nat) : String := String.join (List.replicate n " _")

def rowOf (t : Table) (c : Ctor) : Except String (Option Row) := do
  match t.rows.find? (·.ctor == c.name) with
  | none => return none
  | some r =>
    if r.args.length != c.args.length then
      throw s!"binders.json: {c.name} has {c.args.length} arguments, the row lists {r.args.length}"
    return some r

/-- The head-conditioned rows of a constructor whose conditioning argument is a data
argument (not a node): one per head, each with its own binder counts and lift. -/
def dataHeadRowsOf (t : Table) (c : Ctor) : Except String (List Row) := do
  let rs := t.rows.filter fun r =>
    r.ctor == c.name && r.whenHead.isSome && (c.args[r.whenArg]?).any (·.kind == .other)
  for r in rs do
    if r.args.length != c.args.length then
      throw s!"binders.json: {c.name} has {c.args.length} arguments, the row lists {r.args.length}"
    if r.lift.isNone then
      throw s!"binders.json: the head-conditioned row of {c.name} on argument {r.whenArg} names no lift"
  return rs

/-- The constructor of a data type applied to its fields, as a pattern (`(.tag _)`) or as a
term over named fields (`(.tag tag)`). -/
def headPattern (h : Name) (numFields : Nat) : String :=
  if numFields == 0 then s!".{shortName h}" else s!"(.{shortName h}{wild numFields})"

/-- The binder count each head of a data argument gives argument `j`, as a `match` over
every head of the data type (a head with no row binds nothing). -/
def headCountMatch (rows : List Row) (condArg : Nat) (j : Nat) : MetaM (Option String) := do
  let some r0 := rows.head? | return none
  let some h0 := r0.whenHead | return none
  let ci ← getConstInfoCtor h0
  let ind ← getConstInfoInduct ci.induct
  let counts ← ind.ctors.mapM fun h => do
    let hc ← getConstInfoCtor h
    let count := (rows.find? (·.whenHead == some h)).bind (fun r => r.args[j]?) |>.map (·.length) |>.getD 0
    return s!"| {headPattern h hc.numFields} => {count}"
  if counts.all (·.endsWith "=> 0") then return none
  return some s!"(n + match a{condArg} with {String.intercalate " " counts})"

/-! ## Group Binders -/

def emitBinders (t : Table) (ctors : List Ctor) : MetaM (String × List String) := do
  let mut binders : List String := []
  let mut closed : List String := []
  for r in t.rows do
    let some c := ctors.find? (·.name == r.ctor)
      | throwError "binders.json: no constructor {r.ctor} in the families read"
    if r.args.length != c.args.length then
      throwError "binders.json: {c.name} has {c.args.length} arguments, the row lists {r.args.length}"
    let some nodeCtor := nodeCtorOf c.fam
      | throwError "binders.json: {c.name} is not a node constructor"
    -- The pattern: the constructor with wildcards, or with its head constructor spelled out.
    let pat ← match r.whenHead with
      | none => pure s!".{nodeCtor} (.{c.short}{wild c.numFields})"
      | some h =>
        let hc ← getConstInfoCtor h
        pure s!".{nodeCtor} (.{c.short}{wild r.whenArg} (.{shortName h}{wild hc.numFields}){wild (c.numFields - r.whenArg - 1)})"
    for (scope, j) in r.args.zipIdx do
      match nodeRank c j with
      | some rank =>
        if scope.length > 0 then
          binders := binders ++ [s!"  | {pat}, {rank} => {scope.length}"]
        if r.closed.contains j then
          closed := closed ++ [s!"  | {pat}, {rank} => true"]
      | none =>
        if r.closed.contains j then
          throwError "binders.json: {c.name} argument {j} is closed but is not a node"
  let profile := t.profile
  let list (ns : List Name) : String :=
    "[" ++ String.intercalate ", " (ns.map fun n => s!"\"{shortName n}\"") ++ "]"
  let text := String.intercalate "\n" ([
    "namespace Node",
    "",
    "variable {Op : Type}",
    "",
    "/-- Values bound at child `i` beyond the ambient scope: the one binder table",
    "(`tools/Effect4Gen/binders.json`), which `effTy` follows with the types. -/",
    "def binders : Node Op → Nat → Nat"] ++ binders ++ [
    "  | _, _ => 0",
    "",
    "/-- Children elaborated and typed in the empty scope: a layer's body. -/",
    "def closedChild : Node Op → Nat → Bool"] ++ closed ++ [
    "  | _, _ => false",
    "",
    "/-- The level of child `i` of a node at level `n`. -/",
    "def childLevel (n : Nat) (node : Node Op) (i : Nat) : Nat :=",
    "  if node.closedChild i then 0 else n + node.binders i",
    "",
    "end Node",
    "",
    "/-! ## The authoring profile (DI-84): heads with no authoring lift -/",
    "",
    "/-- The reader's canonical forms for generator code and the retiring invocation forms. -/",
    s!"def readerOnlyHeads : List String := {list profile.readerOnly}",
    "",
    "/-- The fiber actions the printer refuses as internal. -/",
    s!"def machineOnlyHeads : List String := {list profile.machineOnly}",
    ""])
  return (text, ["Effect4.Program.Node.binders", "Effect4.Program.Node.closedChild",
                 "Effect4.Program.Node.childLevel"])

/-! ## Group Authoring -/

def srcTypeOf : ArgKind → Option String
  | .node `Effect4.Program.Eff => some "Src Op"
  | .node `Effect4.Program.ActionTerm => some "ActionSrc Op"
  | .node `Effect4.Program.LayerTerm => some "LayerSrc Op"
  | .node `Effect4.Program.Effs => some "List (Src Op)"
  | .node `Effect4.Program.LayerTerms => some "List (LayerSrc Op)"
  | .node _ => none
  | .term => some "TermSrc"
  | .optionTerm => some "Option TermSrc"
  | .cause => some "CauseSrc"
  | .other => none

def liftPrefix : Name → String
  | `Effect4.Program.Eff => ""
  | `Effect4.Program.ActionTerm => "Action."
  | `Effect4.Program.LayerTerm => "Layer."
  | `Effect4.Program.CauseTerm => "Cause."
  | _ => ""

def resultTypeOf : Name → String
  | `Effect4.Program.ActionTerm => "ActionSrc Op"
  | `Effect4.Program.LayerTerm => "LayerSrc Op"
  | `Effect4.Program.CauseTerm => "CauseSrc"
  | _ => "Src Op"

def quoteList (xs : List String) : String :=
  "[" ++ String.intercalate ", " (xs.map fun s => s!"\"{s}\"") ++ "]"

/-- Whether a constructor gets a lift at all: only the lifted families, and none of the
profile's reader-only, machine-only or hand-written heads. -/
def liftable (t : Table) (c : Ctor) : Bool :=
  t.profile.families.contains c.fam &&
    !(t.profile.readerOnly ++ t.profile.machineOnly ++ t.profile.handWritten).contains c.name

def liftDefName (t : Table) (c : Ctor) : String :=
  (t.profile.renames.find? (·.1 == c.name)).map (·.2) |>.getD c.short

/-- The head of a data argument applied to its fields, as a term over the field names. -/
def headTerm (hc : Ctor) : String :=
  if hc.args.isEmpty then s!".{hc.short}"
  else "(." ++ hc.short ++ " " ++ String.intercalate " " (hc.args.map (·.name)) ++ ")"

/-- One lift over a row. `none` when the constructor has an argument no lift can take.
`fixed?` names a data argument fixed to a head, whose fields become the lift's parameters:
the head-conditioned rows' lifts (`selectOption`, `selectTag`). -/
def emitLiftCore (_t : Table) (c : Ctor) (row? : Option Row) (fixed? : Option (Nat × Ctor))
    (defName : String) : MetaM (Option (String × String)) := do
  let slots := (row?.map (·.slots)).getD []
  let scopeOf (j : Nat) : String :=
    match row? with
    | none => "env"
    | some r =>
      if r.closed.contains j then "env.closed"
      else match r.args[j]? with
        | some ixs => if ixs.isEmpty then "env"
            else "(env.push [" ++ String.intercalate ", " (ixs.filterMap fun i => slots[i]?) ++ "])"
        | none => "env"
  let fullName := liftPrefix c.fam ++ defName
  let opParam := if c.fam == `Effect4.Program.CauseTerm then "" else "{Op : Type} "
  -- Parameters.
  let mut params : List String := slots.map fun s => s!"({s} : String)"
  let mut lines : List String := []
  let mut results : List String := []
  let mut usesEnv := false
  for (a, j) in c.args.zipIdx do
    if let some (k, hc) := fixed? then
      if j == k then
        params := params ++ hc.args.map fun f => s!"({f.name} : {f.tyText})"
        results := results ++ [headTerm hc]
        continue
    match a.kind with
    | .other =>
      params := params ++ [s!"({a.name} : {a.tyText})"]
      results := results ++ [a.name]
    | kind =>
      let some ty := srcTypeOf kind
        | return none
      params := params ++ [s!"({a.name} : {ty})"]
      usesEnv := true
      let x := s!"x{j}"
      match kind with
      | .node fam =>
        let some rank := nodeRank c j | return none
        if fam == `Effect4.Program.Effs then
          lines := lines ++ [s!"    let {x} ← elabEffs {a.name} {scopeOf j} (p ++ [{rank}])"]
          results := results ++ [x]
        else if fam == `Effect4.Program.LayerTerms then
          lines := lines ++ [s!"    let {x} ← elabLayers {a.name} {scopeOf j} (p ++ [{rank}])"]
          results := results ++ [x]
        else
          lines := lines ++ [s!"    let {x} ← {a.name} {scopeOf j} (p ++ [{rank}])"]
          results := results ++ [x]
      | .optionTerm =>
        lines := lines ++ [s!"    let {x} ← elabOption {a.name} {scopeOf j} p"]
        results := results ++ [x]
      | _ =>
        lines := lines ++ [s!"    let {x} ← {a.name} {scopeOf j} p"]
        results := results ++ [x]
  let ctorApp := if results.isEmpty then s!".{c.short}" else s!".{c.short} " ++ String.intercalate " " results
  let doc := match row? with
    | some r =>
      let sees := (r.args.zipIdx.filterMap fun (ixs, j) =>
        if ixs.isEmpty then none
        else (c.args[j]?).map fun a =>
          s!"`{a.name}` sees " ++ String.intercalate ", " (ixs.filterMap fun i => (slots[i]?).map fun s => s!"`{s}`"))
      let closed := (r.closed.filterMap fun j => (c.args[j]?).map fun a => s!"`{a.name}` is closed")
      "/-- `" ++ toString c.name ++ "`: " ++ String.intercalate "; " (sees ++ closed) ++ ". -/"
    | none => "/-- `" ++ toString c.name ++ "`. -/"
  let header := s!"def {fullName} {opParam}" ++ (if params.isEmpty then "" else String.intercalate " " params ++ " ") ++ s!": {resultTypeOf c.fam} :="
  let body := if usesEnv then
      String.intercalate "\n" (["  fun env p => do"] ++ lines ++ [s!"    .ok ({ctorApp})"])
    else s!"  fun _ _ => .ok ({ctorApp})"
  return some (doc ++ "\n" ++ header ++ "\n" ++ body ++ "\n", "Effect4.Program.Authoring." ++ fullName)

/-- The one lift of a constructor with a plain row (or no row). -/
def emitLift (t : Table) (c : Ctor) : MetaM (Option (String × String)) := do
  if !liftable t c then return none
  let row? ← match rowOf t c with
    | .ok r => pure r
    | .error e => throwError e
  let row? := row?.bind fun r => if r.whenHead.isSome then none else some r
  emitLiftCore t c row? none (liftDefName t c)

/-- The lift of one head-conditioned row on a data argument: the head's fields are
parameters and the argument is the head applied to them. -/
def emitLiftRow (t : Table) (c : Ctor) (r : Row) : MetaM (Option (String × String)) := do
  let some h := r.whenHead | return none
  let hc ← readCtor [] h
  emitLiftCore t c (some r) (some (r.whenArg, hc)) (r.lift.getD c.short)

def emitLifts (t : Table) (ctors : List Ctor) : MetaM (String × List String) := do
  let mut text := ""
  let mut receipts := []
  for c in ctors do
    let dataRows ← match dataHeadRowsOf t c with | .ok rs => pure rs | .error e => throwError e
    if !dataRows.isEmpty && liftable t c then
      for r in dataRows do
        if let some (d, name) ← emitLiftRow t c r then
          text := text ++ d ++ "\n"
          receipts := receipts ++ [name]
    else if let some (d, name) ← emitLift t c then
      text := text ++ d ++ "\n"
      receipts := receipts ++ [name]
  return (text, receipts)

/-! ## Group Scoped: the binder table as an algebra on the carrier `Nat → Bool`

The scope predicate is not a second recursion over the seven sorts: it is the program
signature's algebra (`Fold.lean`, `EffAlgebra`) on the carrier `Nat → Bool`, one field per
constructor, each argument checked at the level its row gives it, run by `cata_eff`. The one
head-dependent row (`whenHead`: a statement list's tail is one deeper after a `bindYield`)
is carried as a flag in that family's carrier. One equation lemma per constructor, `rfl`,
is what consumers rewrite with. -/

/-- The level an argument is checked at, from its row: `0` for a closed child, `n + k` under
`k` binders, `n` otherwise. -/
def levelText (row? : Option Row) (j : Nat) : String :=
  match row? with
  | none => "n"
  | some r =>
    if r.closed.contains j then "0"
    else match r.args[j]? with
      | some ixs => if ixs.isEmpty then "n" else s!"(n + {ixs.length})"
      | none => "n"

/-- The family whose carrier carries a flag, and the head the flag means. -/
structure Flag where
  fam : Name
  head : Name

def flagOf (t : Table) : MetaM (Option Flag) := do
  -- the flag is a node family's head (a statement list's tail after a `bindYield`); rows
  -- conditioned on a data argument's head (`select` on its `Decision`) are not flags
  let mut found : Option Flag := none
  for r in t.rows do
    if found.isSome then break
    let some h := r.whenHead | continue
    let ci ← getConstInfoCtor h
    if (nodeCtorOf ci.induct).isSome then
      found := some { fam := ci.induct, head := h }
  return found

def isLayerFam (fam : Name) : Bool :=
  fam == `Effect4.Program.LayerTerm || fam == `Effect4.Program.LayerTerms

def emitScoped (t : Table) (ctors : List Ctor) : MetaM (String × List String) := do
  let flag? ← flagOf t
  let flagged (fam : Name) : Bool := flag?.any (·.fam == fam)
  let mut fields : List String := []
  let mut eqns : List String := []
  for c in ctors do
    let some famKey := nodeCtorOf c.fam | continue
    let row? ← match rowOf t c with | .ok r => pure r | .error e => throwError e
    -- a table conditioned on a data argument: each argument's level is a `match` on the head
    let dataRows ← match dataHeadRowsOf t c with | .ok rs => pure rs | .error e => throwError e
    let condArg? : Option Nat := dataRows.head?.map (·.whenArg)
    let mut dataLevels : Array (Option String) := #[]
    for j in [0:c.args.length] do
      dataLevels := dataLevels.push (← match condArg? with
        | some k => headCountMatch dataRows k j
        | none => pure none)
    let row? := if dataRows.isEmpty then row? else none
    let headRow := row?.any (·.whenHead.isSome)
    -- the sibling whose head decides a `whenHead` row's binders: the flagged family's argument
    let headArg? : Option Nat :=
      if headRow then (c.args.zipIdx.find? fun (a, _) => match a.kind with
        | .node f => flagged f | _ => false).map (·.2) else none
    let plainRow? := if headRow then none else row?
    let lvl (j : Nat) (algebra : Bool) : String :=
      match dataLevels[j]? with
      | some (some s) => s
      | _ =>
      match row?, headArg? with
      | some r, some k =>
        match r.args[j]? with
        | some ixs =>
          if ixs.isEmpty then "n"
          else s!"(if a{k}{if algebra then ".2" else ".bindsNext"} then n + {ixs.length} else n)"
        | none => "n"
      | _, _ => levelText plainRow? j
    let parts (algebra : Bool) : List String := c.args.zipIdx.filterMap fun (a, j) =>
      let l := lvl j algebra
      match a.kind with
      | .term => some s!"a{j}.scoped {l}"
      | .optionTerm => some s!"a{j}.all (·.scoped {l})"
      | .cause => some s!"a{j}.scoped {l}"
      | .node fam =>
        if algebra then
          if isLayerFam fam then some s!"a{j} 0"
          else if flagged fam then some s!"a{j}.1 {l}"
          else some s!"a{j} {l}"
        else
          if isLayerFam fam then some s!"{shortName fam}.scoped a{j}"
          else some s!"{shortName fam}.scopedAt {l} a{j}"
      | .other => none
    let conj (algebra : Bool) : String :=
      let ps := parts algebra
      if ps.isEmpty then "true" else String.intercalate " && " ps
    let usesN (body : String) : Bool := (body.splitOn "n ").length > 1 || body.endsWith "n" || (body.splitOn "n)").length > 1
    let binders := String.intercalate " " (c.args.zipIdx.map fun (a, j) =>
      match a.kind with
      | .other => if condArg? == some j then s!"a{j}" else "_"
      | _ => s!"a{j}")
    let lam (body : String) : String :=
      let nb := if isLayerFam c.fam || !usesN body then "_" else "n"
      if binders.isEmpty then s!"fun {nb} => {body}" else s!"fun {binders} {nb} => {body}"
    let field := s!"{famKey}_{c.short}"
    if flagged c.fam then
      let body := conj true
      let inner := if usesN body then s!"fun n => {body}" else s!"fun _ => {body}"
      let pair := s!"({inner}, {if c.name == (flag?.map (·.head)).getD .anonymous then "true" else "false"})"
      fields := fields ++ [s!"  {field} := " ++ (if binders.isEmpty then pair else s!"fun {binders} => {pair}")]
    else
      fields := fields ++ [s!"  {field} := {lam (conj true)}"]
    -- the equation lemma
    let params := String.intercalate " " (c.args.zipIdx.map fun (a, j) => s!"(a{j} : {a.tyText})")
    let app := if c.args.isEmpty then s!".{c.short}" else s!".{c.short} " ++ String.intercalate " " (c.args.zipIdx.map fun (_, j) => s!"a{j}")
    let famShort := shortName c.fam
    let lhs := if isLayerFam c.fam then s!"{famShort}.scoped (({app} : {famShort} Op))" else s!"{famShort}.scopedAt n (({app} : {famShort} Op))"
    let nParam := if isLayerFam c.fam then "" else "(n : Nat) "
    let rhs := conj false
    let rhs := if rhs == "true" then rhs else s!"({rhs})"
    let lemma := if isLayerFam c.fam then "scoped" else "scopedAt"
    eqns := eqns ++ [s!"@[simp] theorem {famShort}.{lemma}_{c.short} \{Op : Type} {nParam}{params} :\n    {lhs} = {rhs} := rfl"]
    if flagged c.fam then
      let v := if c.name == (flag?.map (·.head)).getD .anonymous then "true" else "false"
      eqns := eqns ++ [s!"@[simp] theorem {famShort}.bindsNext_{c.short} \{Op : Type} {params} :\n    {famShort}.bindsNext (({app} : {famShort} Op)) = {v} := rfl"]
  let carrier := match flag? with
    | some f =>
      let key := (nodeCtorOf f.fam).getD "stmt"
      s!"abbrev ScopeCarrier : EffFam → Type\n  | .{key} => (Nat → Bool) × Bool\n  | _ => Nat → Bool"
    | none => "abbrev ScopeCarrier : EffFam → Type := fun _ => Nat → Bool"
  let flagDefs := match flag? with
    | some f =>
      let fs := shortName f.fam
      let key := (nodeCtorOf f.fam).getD "stmt"
      s!"def {fs}.scopedAt \{Op : Type} (n : Nat) (s : {fs} Op) : Bool := (cata_{key} (scopedAlgebra Op) s).1 n\n" ++
      s!"/-- Whether the statement binds the one after it: the head the table's `whenHead` row names. -/\n" ++
      s!"def {fs}.bindsNext \{Op : Type} (s : {fs} Op) : Bool := (cata_{key} (scopedAlgebra Op) s).2\n"
    | none => "def Stmt.scopedAt {Op : Type} (n : Nat) (s : Stmt Op) : Bool := cata_stmt (scopedAlgebra Op) s n\n"
  let text := String.intercalate "\n" ([
    "/-- The carrier: at every sort the scope test at a level; the flagged family also says",
    "whether it binds the sibling after it (the table's one `whenHead` row). -/",
    carrier,
    "",
    "/-- The binder table as an algebra: each argument checked at the level its row gives it. -/",
    "def scopedAlgebra (Op : Type) : EffAlgebra Op ScopeCarrier where"] ++ fields ++ [
    "",
    "/-- Every variable in scope at `n`, read off the tree by the one fold (`scoped` is the",
    "constructor, Effect's `scoped` combinator). -/",
    "def Eff.scopedAt {Op : Type} (n : Nat) (e : Eff Op) : Bool := cata_eff (scopedAlgebra Op) e n",
    flagDefs,
    "def Stmts.scopedAt {Op : Type} (n : Nat) (ss : Stmts Op) : Bool := cata_stmts (scopedAlgebra Op) ss n",
    "def Effs.scopedAt {Op : Type} (n : Nat) (es : Effs Op) : Bool := cata_effs (scopedAlgebra Op) es n",
    "def ActionTerm.scopedAt {Op : Type} (n : Nat) (a : ActionTerm Op) : Bool := cata_action (scopedAlgebra Op) a n",
    "/-- A layer is closed: its bodies are checked at level `0`. -/",
    "def LayerTerm.scoped {Op : Type} (l : LayerTerm Op) : Bool := cata_layer (scopedAlgebra Op) l 0",
    "def LayerTerms.scoped {Op : Type} (ls : LayerTerms Op) : Bool := cata_layers (scopedAlgebra Op) ls 0",
    "",
    "def Node.scopedAt {Op : Type} (n : Nat) : Node Op → Bool",
    "  | .eff e => e.scopedAt n",
    "  | .stmts ss => ss.scopedAt n",
    "  | .stmt s => s.scopedAt n",
    "  | .action a => a.scopedAt n",
    "  | .effs es => es.scopedAt n",
    "  | .layer l => l.scoped",
    "  | .layers ls => ls.scoped",
    "",
    "/-! ## The equations, one per constructor -/",
    ""] ++ eqns ++ [""])
  return (text, ["Effect4.Program.scopedAlgebra", "Effect4.Program.Eff.scopedAt",
                 "Effect4.Program.Node.scopedAt"])

/-! ## Group ScopedLaws: one preservation lemma per lift, from the same rows

Each lift elaborates its arguments under the binders its row gives it; its lemma says that
if every source argument is scoped, the result is scoped (`Laws/Program/Authoring.lean`
holds the predicates and the base). The proof is the same for every lift: open the `do`
chain (`bind_ok` once per elaborated argument), read each argument's scope at the depth the
row pushed, and close with the constructor's equation of the scope algebra
(`Program/Scoped.lean`). -/

def hypOf (kind : ArgKind) (name : String) : Option String :=
  match kind with
  | .node `Effect4.Program.Effs => some s!"∀ s ∈ {name}, s.Scoped"
  | .node `Effect4.Program.LayerTerms => some s!"∀ s ∈ {name}, s.Scoped"
  | .node _ => some s!"{name}.Scoped"
  | .term => some s!"{name}.Scoped"
  | .cause => some s!"{name}.Scoped"
  | .optionTerm => some s!"∀ t ∈ {name}, t.Scoped"
  | .other => none

def emitLiftLemmaCore (_t : Table) (c : Ctor) (row? : Option Row) (fixed? : Option (Nat × Ctor))
    (defName : String) : MetaM (Option (String × String)) := do
  let slots := (row?.map (·.slots)).getD []
  let closedArg (j : Nat) : Bool := match row? with
    | none => false
    | some r => r.closed.contains j
  let pushedArg (j : Nat) : Bool := match row? with
    | none => false
    | some r => (r.args[j]?).any (fun ixs => !ixs.isEmpty)
  let fullName := liftPrefix c.fam ++ defName
  let isCause := c.fam == `Effect4.Program.CauseTerm
  let mut params : List String :=
    (if isCause then [] else ["{Op : Type}"]) ++ slots.map fun s => s!"({s} : String)"
  let mut hyps : List String := []
  let mut appArgs : List String := slots
  let mut steps : List String := []
  let mut haves : List String := []
  let mut ss : List String := []
  let mut optionArg : Option Nat := none
  for (a, j) in c.args.zipIdx do
    if let some (k, hc) := fixed? then
      if j == k then
        params := params ++ hc.args.map fun f => s!"({f.name} : {f.tyText})"
        -- the lift takes the head's fields, not the head: the lemma applies it the same way
        appArgs := appArgs ++ hc.args.map (·.name)
        continue
    appArgs := appArgs ++ [a.name]
    match a.kind with
    | .other => params := params ++ [s!"({a.name} : {a.tyText})"]
    | kind =>
      let some ty := srcTypeOf kind | return none
      let some hyp := hypOf kind a.name | return none
      params := params ++ [s!"\{{a.name} : {ty}}"]
      hyps := hyps ++ [s!"(h{j} : {hyp})"]
      steps := steps ++ [s!"  obtain ⟨x{j}, hx{j}, h⟩ := bind_ok h"]
      let derive := match kind with
        | .node `Effect4.Program.Effs => s!"elabEffs_scoped h{j} hx{j}"
        | .node `Effect4.Program.LayerTerms => s!"elabLayers_scoped h{j} hx{j}"
        | .optionTerm => s!"elabOption_scoped h{j} hx{j}"
        | _ => s!"h{j}.holds _ _ _ hx{j}"
      haves := haves ++ [s!"  have s{j} := {derive}"]
      if kind == .optionTerm then optionArg := some j
      if closedArg j then
        haves := haves ++ [s!"  simp only [Env.closed_length] at s{j}"]
      else if pushedArg j then
        haves := haves ++ [s!"  simp only [Env.push_length, List.length_cons, List.length_nil] at s{j}"]
      ss := ss ++ [s!"s{j}"]
  let app := String.intercalate " " ([fullName] ++ appArgs)
  let finish :=
    if isCause then
      match optionArg with
      | some j => s!"  cases x{j} <;> simp_all [CauseTerm.scoped]"
      | none => "  simp [CauseTerm.scoped" ++ (if ss.isEmpty then "]" else ", " ++ String.intercalate ", " ss ++ "]")
    else if ss.isEmpty then "  simp" else "  simp [" ++ String.intercalate ", " ss ++ "]"
  let sig := String.intercalate " " (params ++ hyps)
  let text := String.intercalate "\n" ([
    s!"theorem {fullName}_scoped {sig} :",
    s!"    (({app}) : {resultTypeOf c.fam}).Scoped := by",
    "  refine ⟨fun env p e h => ?_⟩",
    s!"  unfold {fullName} at h"] ++ steps ++ ["  cases h"] ++ haves ++ [finish, ""])
  return some (text, s!"Effect4.Program.Authoring.{fullName}_scoped")

def emitLiftLemma (t : Table) (c : Ctor) : MetaM (Option (String × String)) := do
  if !liftable t c then return none
  let row? ← match rowOf t c with
    | .ok r => pure r
    | .error e => throwError e
  let row? := row?.bind fun r => if r.whenHead.isSome then none else some r
  emitLiftLemmaCore t c row? none (liftDefName t c)

def emitLiftLemmaRow (t : Table) (c : Ctor) (r : Row) : MetaM (Option (String × String)) := do
  let some h := r.whenHead | return none
  let hc ← readCtor [] h
  emitLiftLemmaCore t c (some r) (some (r.whenArg, hc)) (r.lift.getD c.short)

def emitLiftLemmas (t : Table) (ctors : List Ctor) : MetaM (String × List String) := do
  let mut text := ""
  let mut receipts := []
  for c in ctors do
    let dataRows ← match dataHeadRowsOf t c with | .ok rs => pure rs | .error e => throwError e
    if !dataRows.isEmpty && liftable t c then
      for r in dataRows do
        if let some (d, name) ← emitLiftLemmaRow t c r then
          text := text ++ d ++ "\n"
          receipts := receipts ++ [name]
    else if let some (d, name) ← emitLiftLemma t c then
      text := text ++ d ++ "\n"
      receipts := receipts ++ [name]
  return (text, receipts)

/-! ## Group NodeLenses: the child lenses from the constructor declarations

`Node.child` and `Node.setChild` address a node's node-typed arguments by their rank in
declaration order, the same rank the lifts elaborate at and the path folds thread. One arm
per (constructor, rank), from the reflection alone; no table. -/

def emitNodeLenses (ctors : List Ctor) : MetaM (String × List String) := do
  let mut childArms : List String := []
  let mut setArms : List String := []
  for c in ctors do
    let some famKey := nodeCtorOf c.fam | continue
    for (a, j) in c.args.zipIdx do
      let .node childFam := a.kind | continue
      let some childKey := nodeCtorOf childFam | continue
      let some rank := nodeRank c j | continue
      let childPat := String.intercalate " " (c.args.zipIdx.map fun (_, k) => if k == j then s!"a{j}" else "_")
      childArms := childArms ++ [s!"  | {famKey} (.{c.short} {childPat}), {rank} => some ({childKey} a{j})"]
      let setPat := String.intercalate " " (c.args.zipIdx.map fun (_, k) => if k == j then "_" else s!"a{k}")
      let result := String.intercalate " " (c.args.zipIdx.map fun (_, k) => if k == j then "x" else s!"a{k}")
      setArms := setArms ++ [s!"  | {famKey} (.{c.short} {setPat}), {rank}, {childKey} x => some ({famKey} (.{c.short} {result}))"]
  let text := String.intercalate "\n" ([
    "namespace Node",
    "",
    "variable {Op : Type}",
    "",
    "/-- The child at an index: the node-typed arguments of a constructor, in declaration order.",
    "Terms are not nodes: only programs, statements, actions, layers and the two spines are",
    "addressed. -/",
    "def child : Node Op → Nat → Option (Node Op)"] ++ childArms ++ [
    "  | _, _ => none",
    "",
    "/-- The node with the child at an index replaced by one of the same sort; `none` where",
    "`child` is `none` or the sorts differ. -/",
    "def setChild : Node Op → Nat → Node Op → Option (Node Op)"] ++ setArms ++ [
    "  | _, _, _ => none",
    "",
    "end Node",
    ""])
  return (text, ["Effect4.Program.Node.child", "Effect4.Program.Node.setChild"])

/-! ## The command line, as the driver spells it -/

structure Args where
  group : String := "Binders"
  imports : List String := []
  out : Option String := none
  headerOut : Option String := none
  append : Option String := none
  table : String := "tools/Effect4Gen/binders.json"
  kinds : List String := []
  types : List String := []

partial def parseArgs : List String → Args → Except String Args
  | [], a => .ok a
  | "--group" :: g :: rest, a => parseArgs rest { a with group := g }
  | "--imports" :: i :: rest, a =>
    parseArgs rest { a with imports := (i.splitOn ",").filter (· != "") }
  | "--out" :: o :: rest, a => parseArgs rest { a with out := some o }
  | "--header-out" :: o :: rest, a => parseArgs rest { a with headerOut := some o }
  | "--append" :: p :: rest, a => parseArgs rest { a with append := some p }
  | "--table" :: p :: rest, a => parseArgs rest { a with table := p }
  | "--kind" :: k :: rest, a => parseArgs rest { a with kinds := a.kinds ++ [k] }
  | "--" :: rest, a => parseArgs rest a
  | t :: rest, a =>
    if t.startsWith "--" then
      if rest.isEmpty then .error s!"{t} needs a value" else .error s!"unknown option {t}"
    else parseArgs rest { a with types := a.types ++ [t] }

def run (args : Args) : MetaM (Array String) := do
  let tableText ← IO.FS.readFile args.table
  let table ← match parseTable tableText with
    | .ok t => pure t
    | .error e => throwError "{args.table}: {e}"
  let outPath := (args.headerOut.orElse (fun _ => args.out) |>.getD "<stdout>").replace "\\" "/"
  let head := "lake env lean -M 4096 --run tools/Effect4Gen/Authoring.lean --group " ++ args.group
    ++ " --imports " ++ String.intercalate "," args.imports
    ++ " --out " ++ outPath
    ++ (match args.append with | some p => " --append " ++ p.replace "\\" "/" | none => "")
  let mut lines : Array String := #[
    "-- GENERATED by tools/Effect4Gen/Authoring.lean from tools/Effect4Gen/binders.json and the Lean environment. Do not edit.",
    "-- Regenerate (tools/Effect4Gen/Driver.lean runs this for every group; --verify refuses a diff):",
    "--   " ++ head ++ " -- " ++ String.intercalate " " args.types]
  if let some p := args.append then
    lines := lines.push s!"-- Acceptance guards appended verbatim from: {p.replace "\\" "/"}"
  lines := lines ++ (args.imports.map fun i => s!"import {i}").toArray
  lines := lines ++ #["", "set_option autoImplicit false", ""]
  let ctors ← readFamilies (table.profile.families ++
    [`Effect4.Program.Stmts, `Effect4.Program.Stmt, `Effect4.Program.Effs, `Effect4.Program.LayerTerms])
  let (text, receipts) ← match args.group with
    | "Binders" =>
      let (t, r) ← emitBinders table ctors
      pure ("namespace Effect4.Program\n\n" ++ t ++ "\n", r)
    | "Authoring" =>
      let (t, r) ← emitLifts table ctors
      pure ("namespace Effect4.Program.Authoring\n\nopen Effect4.Program\n\n" ++ t, r)
    | "Scoped" =>
      let (t, r) ← emitScoped table ctors
      pure ("namespace Effect4.Program\n\n" ++ t, r)
    | "ScopedLaws" =>
      let (t, r) ← emitLiftLemmas table ctors
      pure ("namespace Effect4.Program.Authoring\n\nopen Effect4.Program\n\n" ++ t, r)
    | "NodeLenses" =>
      let (t, r) ← emitNodeLenses ctors
      pure ("namespace Effect4.Program\n\n" ++ t, r)
    | g => throwError "unknown group {g}: Binders, Authoring, Scoped, ScopedLaws or NodeLenses"
  lines := lines.push text
  lines := lines ++ #["/-! ## Receipts -/", ""]
  for r in receipts do
    lines := lines.push s!"#print axioms {r}"
  let ns := if args.group == "Authoring" || args.group == "ScopedLaws" then "Effect4.Program.Authoring"
    else "Effect4.Program"
  lines := lines ++ #["", s!"end {ns}", ""]
  if let some p := args.append then
    let txt ← IO.FS.readFile p
    lines := lines ++ (txt.splitOn "\n").toArray.map (·.replace "\r" "")
  return lines

end Effect4Gen.Authoring

open Effect4Gen.Authoring in
def main (argv : List String) : IO Unit := do
  let args ← match parseArgs argv {} with
    | .ok a => pure a
    | .error e => throw (IO.userError e)
  if args.imports.isEmpty then
    throw (IO.userError "--imports names the modules the emitted file imports; none given")
  Lean.initSearchPath (← Lean.findSysroot)
  let env ← Lean.importModules (args.imports.map fun i => { module := i.toName }).toArray {} 0
  let ctx : Core.Context := { fileName := "<gen>", fileMap := default }
  let act : MetaM Unit := do
    let lines ← run args
    let stamp := Tools.GeneratedStamp.note "tools/Effect4Gen/Authoring.lean"
    let text := "-- " ++ stamp ++ "\n" ++ String.intercalate "\n" lines.toList ++ "\n"
    match args.out with
    | some p => IO.FS.writeFile p text
    | none => IO.println text
  let _ ← (act.run' {}).toIO ctx { env := env }
