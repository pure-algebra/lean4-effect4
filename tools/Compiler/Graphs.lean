import Effect4.Api.Built
import Effect4.Program.LayerView
import Effect4.Program.Typing.Table
import Effect4.Program.Authoring
import Effect4.Store.Carrier.Utf8
import Tools.Document
import Tools.Document.Figure
import Tools.View.Glyph
import Tools.View.Flow

/-!
# Program relations and their graph queries

The four relations are the source of every figure and of the mapping table (row 443).
Their carrier is data: a node is its address, its scope, its sort, its constructor and what it
names; a definition, a host row and a call likewise (`Relations`). Keys are positions; names are
labels. Nodes retain stored reference occurrences. Calls use the checked expansion of
`HostSession.callTable`; their origin names the stored occurrence that produced them. Expansion
is not execution. The node relation is one generated fold, including `cata_layer` at layer
children.

The tables (`tables`), the figures (`boundary`, `boxes`, `calls`, `layers`) and the mapping are
folds of the carrier. No query reads a cell back. The JSON and the TSV are the document's folds
of the tables.

The boundary records incidence, not scheduling, handler composition, or layer evaluation.
Its wires identify namespaces and services. Its boxes are the contraction of those wires.
Cycles keep their edges and use `Flow.orderFor`'s stable fallback order.
-/

namespace Compiler.Graphs

open Effect4 Effect4.Program Tools.Document

/-! ## The carrier -/

/-- Where a node lies: a definition's body by its position, the main program, the module's
layers, the block's root node, or the definitions' spine. -/
inductive Scope where
  | def_ (k : Nat)
  | main
  | layers
  | block
  | defs
deriving DecidableEq, Repr

/-- A scope's key: the key of the drawn node that stands for it. -/
def Scope.key : Scope → String
  | .def_ k => "def:" ++ toString k
  | .main => "main"
  | .layers => "layers"
  | .block => "block"
  | .defs => "defs"

/-- What a node names beyond its children: a call of a definition, a host row, a service key,
or a reference's target. -/
inductive Named where
  | call (k : Nat)
  | row (i : Nat)
  | key (key : ServiceKey)
  | ref (target : List Nat)
deriving DecidableEq, Repr

/-- A node of the program term. -/
structure NodeRow where
  address : List Nat
  scope : Scope
  sort : EffFam
  ctor : String
  names : List Named
deriving Repr

/-- A definition of the block. -/
structure DefRow where
  k : Nat
  name : String
  role : DefRole
  /-- the address of its body -/
  body : List Nat
deriving Repr

/-- A row of a host. Its host is the part of its spelling before the dot. -/
structure HostRow where
  i : Nat
  spelling : String
  host : String
  request : Ty
  answer : Ty
deriving Repr

/-- A call's target: a definition or a host row, by position. -/
inductive Target where
  | def_ (k : Nat)
  | row (i : Nat)
deriving DecidableEq, Repr

/-- A target's key: the key of the drawn node that stands for it. -/
def Target.key : Target → String
  | .def_ k => "def:" ++ toString k
  | .row i => "row:" ++ toString i

/-- A call instance of the checked call table. -/
structure CallRow where
  address : List Nat
  scope : Scope
  target : Target
  /-- the stored call or reference occurrence that produced it -/
  origin : List Nat
deriving Repr

/-- The four relations. -/
structure Relations where
  nodes : List NodeRow
  defs : List DefRow
  rows : List HostRow
  calls : List CallRow

/-- The service a definition's role serves, if any. -/
def roleService : DefRole → Option String
  | .plain => none
  | .serviceInit s => some s
  | .serviceMethod s _ _ => some s

/-- The definition at a position. -/
def Relations.def? (r : Relations) (k : Nat) : Option DefRow := r.defs.find? (·.k == k)

/-- The row at a position. -/
def Relations.row? (r : Relations) (i : Nat) : Option HostRow := r.rows.find? (·.i == i)

/-- The node at an address. -/
def Relations.node? (r : Relations) (p : List Nat) : Option NodeRow := r.nodes.find? (·.address == p)

/-- A scope's label: a definition's name, or the scope's word. -/
def Relations.scopeLabel (r : Relations) : Scope → String
  | .def_ k => ((r.def? k).map (·.name)).getD "definition"
  | .main => "main"
  | .layers => "layers"
  | .block => "block"
  | .defs => "definitions"

/-- The key of the box a scope's calls belong to: its service when the scope is a definition
with a service role, else the scope itself. -/
def Relations.owner (r : Relations) : Scope → String
  | .def_ k => match (r.def? k).bind (roleService ·.role) with
    | some s => "service:" ++ s
    | none => (Scope.def_ k).key
  | s => s.key

/-- A path in the program's generated address alphabet. -/
def address (p : List Nat) : String := String.intercalate "." (p.map toString)

private def sortName : EffFam → String
  | .eff => "eff" | .effs => "effs" | .stmt => "stmt" | .stmts => "stmts"
  | .action => "action" | .layer => "layer" | .layers => "layers"

private def sortDecl : EffFam → Lean.Name
  | .eff => ``Eff | .effs => ``Effs | .stmt => ``Stmt | .stmts => ``Stmts
  | .action => ``ActionTerm | .layer => ``LayerTerm | .layers => ``LayerTerms

/-- The constructor's mark and word come from the shared glyph table. -/
def glyph (fam : EffFam) (ctor : String) : String × String :=
  match Tools.View.Glyph.table.find? (·.ctor == (sortDecl fam).str ctor) with
  | some row => (row.shape.glyph, row.word)
  | none => ("·", ctor)

/-- A node's mark and word. -/
def NodeRow.glyph (n : NodeRow) : String × String := Graphs.glyph n.sort n.ctor

/-- What a node names, in words. -/
def Relations.namesText (r : Relations) (ns : List Named) : String :=
  String.intercalate ", " (ns.map fun
    | .call k => "call " ++ (((r.def? k).map (·.name)).getD (toString k))
    | .row i => "row " ++ (((r.row? i).map (·.spelling)).getD (toString i))
    | .key key => "key " ++ toString key.name.value ++ ":" ++ toString key.service.value
    | .ref p => "ref " ++ address p)

/-! ## The read -/

/-- The scope of an address in the program. -/
private def scopeAt (program : Eff NativeOp) (p : List Nat) : Scope :=
  match program.scopeOf p with
  | some k => .def_ k
  | none =>
    if program.inModule p then .layers
    else if p.isEmpty && program.block?.isSome then .block
    else if program.block?.isSome && p.head? == some 0 then .defs
    else .main

/-- One constructor contributes one row, then its folded children at numbered addresses.
`EffAlgebra.ofLayer` supplies every constructor, including every layer constructor. -/
private def nodeAlgebra (program : Eff NativeOp) :
    EffAlgebra NativeOp (fun _ => List Nat → List NodeRow) :=
  EffAlgebra.ofLayer fun fam ctor args p =>
    let children := args.filterMap fun | .child _ f => some f | _ => none
    let names := args.filterMap fun
      | .op (.call k) => some (.call k)
      | .op (.external i) => some (.row i)
      | .key key => some (.key key)
      | .path q => some (.ref q)
      | _ => none
    { address := p, scope := scopeAt program p, sort := fam, ctor, names } ::
      children.zipIdx.flatMap (fun (f, i) => f (p ++ [i]))

/-- The original reference occurrence enclosing an expanded call, or the call itself. -/
private def origin (program : Eff NativeOp) (p : List Nat) : List Nat :=
  let refs := (program.refSites []).filter (fun (site, _) => site.isPrefixOf p)
  match refs with
  | [] => p
  | first :: rest => (rest.foldl (fun acc item => if acc.1.length < item.1.length then item else acc) first).1

/-- The host of a row: its spelling before the first dot. -/
private def hostOf (spelling : String) : String :=
  (Store.decodeString (spelling.toUTF8.data.toList.takeWhile (· != 46))).getD ""

/-- **Read all four relations.** The nodes retain source syntax; calls state both the checked
expanded address and their original occurrence. Definition positions survive expansion. -/
def read (b : Api.Built) : Relations :=
  let program := b.program
  let decls := program.defsOf
  { nodes := cata_eff (nodeAlgebra program) program []
    defs := decls.zipIdx.map fun (d, k) => { k, name := d.name, role := d.role, body := Authoring.bodyPath k }
    rows := b.app.rows.zipIdx.map fun (r, i) =>
      { i, spelling := r.spelling, host := hostOf r.spelling, request := r.request, answer := r.answer }
    calls := (Api.HostSession.callTable b.program b.app).filterMap fun (p, c) =>
      let row (target : Target) : CallRow :=
        { address := p, scope := scopeAt program p, target, origin := origin program p }
      match c.op with
      | .call k => if k < decls.length then some (row (.def_ k)) else none
      | .external i => if i < b.app.rows.length then some (row (.row i)) else none
      | _ => none }

/-! ## The tables: one fold each -/

private def cell (s : String) : Line := [.text s]
private def cells (ss : List String) : List Line := ss.map cell

/-- A relation row reaches its mark: the anchor of its node in the inside figure (`calls`), which
draws every definition, row, main and module layers in its form (`Tools.Document.Figure.anchorIn`). -/
private def anchor (key : String) : String := "#" ++ Tools.Document.Figure.anchorIn "calls" key

/-- A scope's cell: its key as code, then its label linked to its node. The block's root and the
definitions' spine are no node of a figure, so their labels link nowhere. -/
private def scopeCell (r : Relations) (s : Scope) : Line :=
  match s with
  | .block | .defs => [.code s.key, .text " ", .text (r.scopeLabel s)]
  | _ => [.code s.key, .text " ", .link (anchor s.key) (r.scopeLabel s)]

/-- A target's cell: its key as code, then its name linked to the drawn node. -/
private def targetCell (r : Relations) (t : Target) : Line :=
  let name := match t with
    | .def_ k => ((r.def? k).map (·.name)).getD (toString k)
    | .row i => ((r.row? i).map (·.spelling)).getD (toString i)
  [.code t.key, .text " ", .link (anchor t.key) name]

private def roleLine : DefRole → Line
  | .plain => [.text "plain"]
  | .serviceInit service => [.text "init of ", .code service]
  | .serviceMethod service method _ => [.text "method ", .code method, .text " of ", .code service]

/-- The nodes relation as a table. -/
def nodesTable (r : Relations) : Block :=
  .table ["address", "in", "sort", "mark", "word", "names", "constructor"] (r.nodes.map fun n =>
    cell (address n.address) :: scopeCell r n.scope ::
      cells [sortName n.sort, n.glyph.1, n.glyph.2, r.namesText n.names, n.ctor])

/-- The definitions relation as a table. -/
def defsTable (r : Relations) : Block :=
  .table ["k", "name", "role", "body"] (r.defs.map fun d =>
    [cell (toString d.k), cell d.name, roleLine d.role, cell (address d.body)])

/-- The rows relation as a table. -/
def rowsTable (r : Relations) : Block :=
  .table ["i", "spelling", "namespace", "request", "answer"] (r.rows.map fun h =>
    cells [toString h.i, h.spelling, h.host, h.request.render, h.answer.render])

/-- The calls relation as a table. A definition's target address is its body; a row's is its
position. -/
def callsTable (r : Relations) : Block :=
  .table ["address", "from", "targetSort", "target", "targetAddress", "origin"] (r.calls.map fun c =>
    let (sort, at_) := match c.target with
      | .def_ k => ("def", address (((r.def? k).map (·.body)).getD []))
      | .row i => ("row", toString i)
    [cell (address c.address), scopeCell r c.scope, cell sort, targetCell r c.target,
     cell at_, cell (address c.origin)])

/-! ## The figures: queries over the carrier -/

/-- Every graph uses the view's checked Kahn order. A cycle keeps the input order and all edges. -/
def ordered (ns : List GraphNode) (es : List (String × String)) : List GraphNode :=
  let edges := es.filterMap fun (a, b) => do
    return ({ fr := ← ns.findIdx? (·.key == a), to := ← ns.findIdx? (·.key == b) } : Tools.View.Flow.Edge)
  (Tools.View.Flow.orderFor ns.length edges edges).2.filterMap (ns[·]?)

private def figure (key caption : String) (ns : List GraphNode) (es : List (String × String)) : Block :=
  let edges := es.eraseDups
  .graph key caption (ordered ns edges) edges

/-- The relation a node that stands for a relation row opens, when the document holds the relations
(`opens`): a definition opens the definitions, a row the rows, main and the module layers the nodes. -/
private def opening (opens : Bool) (relation : String) : Option String :=
  if opens then some ("relation-" ++ relation) else none

/-- The mark and word of the node at an address. -/
private def constructor (r : Relations) (p : List Nat) : String × String :=
  ((r.node? p).map (·.glyph)).getD ("·", "")

/-- The address of the main program: the block's second child, or the root. -/
private def mainAddress (r : Relations) : List Nat :=
  if (r.nodes.head?.map (·.ctor)) == some "defs" then [1] else []

private def definitionNode (r : Relations) (opens : Bool) (d : DefRow) : GraphNode :=
  let g := constructor r d.body
  { key := (Scope.def_ d.k).key, label := d.name, status := "definition " ++ g.1, detail := g.2,
    ref := opening opens "defs" }

private def definitionNodes (r : Relations) (opens : Bool) : List GraphNode :=
  r.defs.map (definitionNode r opens)

private def mainNode (r : Relations) (opens : Bool) : GraphNode :=
  let g := constructor r (mainAddress r)
  { key := Scope.main.key, label := "main", status := "eff " ++ g.1, detail := g.2, ref := opening opens "nodes" }

private def moduleNodes (r : Relations) (opens : Bool) : List GraphNode :=
  if r.calls.any (·.scope == .layers) then
    let g := constructor r [2]
    [{ key := Scope.layers.key, label := "module layers", status := "layers " ++ g.1, detail := g.2,
       ref := opening opens "nodes" }]
  else []

/-- Definition and host-row calls, joined by positions, never by display names. With `opens`, each
node opens its relation. -/
def calls (r : Relations) (opens : Bool := false) : Block :=
  let ns := mainNode r opens :: definitionNodes r opens ++ moduleNodes r opens ++ r.rows.map fun h =>
    { key := (Target.row h.i).key, label := h.spelling, status := "row " ++ (glyph .eff "perform").1, form := .port,
      ref := opening opens "rows" }
  let es := r.calls.map fun c => (c.scope.key, c.target.key)
  figure "calls" "Calls from definitions and main to definitions and host rows." ns es

/-- The hosts, by their namespaces. -/
def hosts (r : Relations) : List String := (r.rows.map (·.host)).eraseDups

/-- The services, by the names the definitions' roles carry. -/
def services (r : Relations) : List String := (r.defs.filterMap (roleService ·.role)).eraseDups

private def hostKey (name : String) : String := "host:" ++ name
private def serviceKey (name : String) : String := "service:" ++ name

private def boundaryNodes (r : Relations) (opens : Bool) : List GraphNode :=
  (hosts r).map (fun name => { key := hostKey name, label := name, status := "host " ++ (glyph .eff "perform").1 }) ++
  (services r).map (fun name => { key := serviceKey name, label := name, status := "service " ++ (glyph .eff "defs").1 }) ++
  (r.defs.filter fun d => (roleService d.role).isNone).map (definitionNode r opens) ++
  moduleNodes r opens ++ [mainNode r opens]

/-- The provider-to-consumer pairs: a call's row gives its host; a call's definition gives its
owner; the call's own scope gives the consumer. A call inside its own provider gives none. -/
def dependencies (r : Relations) : List (String × String) :=
  (r.calls.filterMap fun c => do
    let dst := r.owner c.scope
    let src ← match c.target with
      | .row i => (r.row? i).map (fun h => hostKey h.host)
      | .def_ k => some (r.owner (.def_ k))
    if src == dst then none else some (src, dst)).eraseDups

/-- One wire per provider identity. Multiple consumers meet the same wire. -/
def boundary (r : Relations) (opens : Bool := false) : Block :=
  let ds := dependencies r
  let providers := (ds.map Prod.fst).eraseDups
  let boxes := boundaryNodes r opens
  let wires := providers.map fun key =>
    { key := "wire:" ++ key, label := (boxes.find? (·.key == key)).map (·.label) |>.getD key
      status := "wire " ++ (glyph .eff "service").1, form := .wire }
  let es := providers.map (fun key => (key, "wire:" ++ key)) ++ ds.map (fun (a, b) => ("wire:" ++ a, b))
  figure "boundary" "Boundary incidence: shared service wires join providers to consumers; no execution order is claimed." (boxes ++ wires) es

/-- Contract every wire in the boundary by joining each incoming edge to each outgoing edge. -/
def boxes (r : Relations) (opens : Bool := false) : Block :=
  match boundary r opens with
  | .graph _ _ ns es =>
    let wires := ns.filter (·.form == .wire)
    let contracted := wires.flatMap fun wire =>
      (es.filter (·.2 == wire.key)).flatMap fun (a, _) =>
        (es.filter (·.1 == wire.key)).map (fun (_, b) => (a, b))
    figure "boundary-boxes" "The boundary with each service wire contracted." (ns.filter (·.form != .wire)) contracted
  | _ => .graph "boundary-boxes" "The boundary with each service wire contracted." [] []

/-- Layer constructors and their nearest enclosing layer constructor, by address.
The node relation's generated fold enters layers through `cata_layer`; lists are transparent here. -/
def layers (r : Relations) (opens : Bool := false) : Block :=
  let rs := r.nodes.filter (·.sort == .layer)
  let key (n : NodeRow) : String := "layer:" ++ address n.address
  let ns := rs.map fun n =>
    { key := key n, label := n.glyph.2, status := "layer " ++ n.glyph.1, detail := r.namesText n.names,
      ref := opening opens "nodes" }
  let es := rs.filterMap fun n =>
    let ancestors := rs.filter fun a => a.address.length < n.address.length && a.address.isPrefixOf n.address
    match ancestors with
    | [] => none
    | first :: rest =>
      let parent := rest.foldl (fun acc a => if a.address.length > acc.address.length then a else acc) first
      some (key parent, key n)
  figure "layers" (if rs.isEmpty then "This program has no stored layer constructors."
    else "Stored layer constructor positions and reference targets; this picture states no merge commutativity.") ns es

/-- Each mapping row names an entity or dependency present in the same relations. -/
def mapping (r : Relations) : Block :=
  .table ["ours", "Effect TypeScript", "algebra"]
    ((hosts r).map (fun h => cells [h ++ " host namespace", "Layer<Tag> supplied by the host", "comodel of the row operation syntax signature"]) ++
     (services r).map (fun s => cells [s ++ " service block", "Layer.effect(Tag, map(init, closures))", "handler with one program per method"]) ++
     [cells ["main", "Effect.provide(program, layer)", "term over the handled methods"]] ++
     (dependencies r).map (fun (a, b) => cells [a ++ " to " ++ b, "Layer.provide", "provider-to-consumer incidence"]) ++
     (r.nodes.filter (·.sort == .layer)).map
       (fun n => cells ["layer at " ++ address n.address,
         if n.ctor == "ref" then "reference to a hoisted layer constant" else "Layer." ++ n.ctor,
         if n.ctor == "merge" || n.ctor == "mergeAll" then
           "incidence overlay; tensor only for disjoint services"
         else if n.ctor == "provide" || n.ctor == "provideMerge" then "shared-wire incidence overlay"
         else if n.ctor == "ref" then "reference to " ++ r.namesText n.names
         else "constructor of the layer signature"]))

/-- One document, selected by a command reading. All formats fold this value. -/
def document (b : Api.Built) (what : String) : Tools.Document.Document :=
  let r := read b
  let mappingPart := Block.part "mapping" "The program and its boundary" [mapping r]
  let opens := what == "relations"
  let figures := if what == "boundary" then [boundary r, boxes r]
    else if what == "calls" then [calls r]
    else if what == "layers" then [layers r]
    else [boundary r opens, boxes r opens, calls r opens, layers r opens]
  let tables := if what == "relations" then
    [Block.part "relation-nodes" "Nodes" [nodesTable r], .part "relation-defs" "Definitions" [defsTable r],
     .part "relation-rows" "Rows" [rowsTable r], .part "relation-calls" "Calls" [callsTable r]] else []
  { title := "The program as relations and graphs"
    producer := ["GENERATED by Compiler.Graphs; do not edit", "python3 scripts/generate.py --only graphs"]
    body := [.para [.text "Node addresses name stored syntax. Call addresses name the checked expansion; origin names the stored call or reference."]] ++ tables ++ [mappingPart] ++
      figures.map (fun | .graph _ caption [] [] => .para [.text caption] | block => block) }

end Compiler.Graphs
