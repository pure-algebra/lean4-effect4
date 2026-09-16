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
  return { ctor := ctor.toName, slots := slots.toList, args := args.toList,
           closed := closed.toList, whenHead }

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
        pure s!".{nodeCtor} (.{c.short} (.{shortName h}{wild hc.numFields}){wild (c.numFields - 1)})"
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

/-- One lift. `none` when the constructor has an argument no lift can take. -/
def emitLift (t : Table) (c : Ctor) : MetaM (Option (String × String)) := do
  -- Only the lifted families get lifts; the spines and statements are read for the table alone.
  if !t.profile.families.contains c.fam then return none
  if (t.profile.readerOnly ++ t.profile.machineOnly ++ t.profile.handWritten).contains c.name then
    return none
  let row? ← match rowOf t c with
    | .ok r => pure r
    | .error e => throwError e
  let row? := row?.bind fun r => if r.whenHead.isSome then none else some r
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
  let defName := (t.profile.renames.find? (·.1 == c.name)).map (·.2) |>.getD c.short
  let fullName := liftPrefix c.fam ++ defName
  let opParam := if c.fam == `Effect4.Program.CauseTerm then "" else "{Op : Type} "
  -- Parameters.
  let mut params : List String := slots.map fun s => s!"({s} : String)"
  let mut lines : List String := []
  let mut results : List String := []
  let mut usesEnv := false
  for (a, j) in c.args.zipIdx do
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
          lines := lines ++ [s!"    let {x} ← {a.name}.zipIdx.mapM fun (e, i) => e {scopeOf j} (p ++ [{rank}] ++ List.replicate i 1 ++ [0])"]
          results := results ++ [s!"(effsOfList {x})"]
        else if fam == `Effect4.Program.LayerTerms then
          lines := lines ++ [s!"    let {x} ← {a.name}.zipIdx.mapM fun (l, i) => l {scopeOf j} (p ++ [{rank}] ++ List.replicate i 1 ++ [0])"]
          results := results ++ [s!"(LayerTerms.ofList {x})"]
        else
          lines := lines ++ [s!"    let {x} ← {a.name} {scopeOf j} (p ++ [{rank}])"]
          results := results ++ [x]
      | .optionTerm =>
        lines := lines ++ [s!"    let {x} ← (match {a.name} with | none => pure none | some t => (some ·) <$> t {scopeOf j} p)"]
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

def emitLifts (t : Table) (ctors : List Ctor) : MetaM (String × List String) := do
  let mut text := ""
  let mut receipts := []
  for c in ctors do
    if let some (d, name) ← emitLift t c then
      text := text ++ d ++ "\n"
      receipts := receipts ++ [name]
  return (text, receipts)

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
    | g => throwError "unknown group {g}: Binders or Authoring"
  lines := lines.push text
  lines := lines ++ #["/-! ## Receipts -/", ""]
  for r in receipts do
    lines := lines.push s!"#print axioms {r}"
  let ns := if args.group == "Binders" then "Effect4.Program" else "Effect4.Program.Authoring"
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
