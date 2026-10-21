import Effect4.Api.Built
import Effect4.Program.LayerView
import Effect4.Program.Typing.Table
import Effect4.Program.Authoring
import Effect4.Store.Carrier.Utf8
import Tools.Document
import Tools.View.Glyph
import Tools.View.Flow

/-!
# Program relations and their graph queries

The four tables are the source of every figure and of the mapping table (row 443).
Keys are positions; names are labels. Nodes retain stored reference occurrences.
Calls use the checked expansion of `HostSession.callTable`; their origin column names
the stored occurrence that produced them. Expansion is not execution.
The node relation is one generated fold, including `cata_layer` at layer children.
A drawing queries the tables; it never walks program syntax.

The boundary records incidence, not scheduling, handler composition, or layer evaluation.
Its wires identify namespaces and services. Its boxes are the contraction of those wires.
Cycles keep their edges and use `Flow.orderFor`'s stable fallback order.
-/

namespace Compiler.Graphs

open Effect4 Effect4.Program Tools.Document

/-- The four relations, each held in the document's existing table carrier. -/
structure Relations where
  nodes : Block
  defs : Block
  rows : Block
  calls : Block

/-- A path in the program's generated address alphabet. -/
def address (p : List Nat) : String := String.intercalate "." (p.map toString)

private def cell (s : String) : Line := [.text s]
private def cells (ss : List String) : List Line := ss.map cell

/-- A relation's rows. Every producer below returns a table. -/
def records : Block → List (List Line)
  | .table _ rs => rs
  | _ => []

/-- Literal cell text, independent of any output format. -/
def text (l : Line) : String := String.join (l.map fun
  | .text s | .code s | .status s => s
  | .ref _ s | .link _ s => s)

private def column (r : List Line) (i : Nat) : String := text (r[i]?.getD [])

/-- A scope cell keeps its position separately from its display name. -/
private def scopeCell (key label : String) : Line := [.code key, .text " ", .text label]
private def scopeKey (l : Line) : String :=
  match l with
  | .code key :: _ => key
  | _ => "main"

private def scope (program : Eff NativeOp) (p : List Nat) : Line :=
  match program.scopeOf p with
  | some k => scopeCell ("def:" ++ toString k) ((program.defsOf[k]?).map (·.name) |>.getD "definition")
  | none =>
    if program.inModule p then scopeCell "layers" "layers"
    else if p.isEmpty && program.block?.isSome then scopeCell "block" "block"
    else if program.block?.isSome && p.head? == some 0 then scopeCell "defs" "definitions"
    else scopeCell "main" "main"

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

private def names {R : EffFam → Type} (decls : List DefDecl) (rows : RowTable)
    (args : List (ArgF NativeOp R)) : String :=
  String.intercalate ", " (args.filterMap fun
    | .op (.call k) => some ("call " ++ ((decls[k]?).map (·.name)).getD (toString k))
    | .op (.external i) => some ("row " ++ ((rows[i]?).map (·.spelling)).getD (toString i))
    | .key key => some ("key " ++ toString key.name.value ++ ":" ++ toString key.service.value)
    | .path p => some ("ref " ++ address p)
    | _ => none)

/-- One constructor contributes one row, then its folded children at numbered addresses.
`EffAlgebra.ofLayer` supplies every constructor, including every layer constructor. -/
private def nodeAlgebra (program : Eff NativeOp) (rows : RowTable) :
    EffAlgebra NativeOp (fun _ => List Nat → List (List Line)) :=
  EffAlgebra.ofLayer fun fam ctor args p =>
    let g := glyph fam ctor
    let children := args.filterMap fun | .child _ f => some f | _ => none
    (cell (address p) :: scope program p :: cells [sortName fam, g.1, g.2, names program.defsOf rows args, ctor]) ::
      children.zipIdx.flatMap (fun (f, i) => f (p ++ [i]))

private def roleLine : DefRole → Line
  | .plain => [.text "plain"]
  | .serviceInit service => [.text "init of ", .code service]
  | .serviceMethod service method _ => [.text "method ", .code method, .text " of ", .code service]

/-- The original reference occurrence enclosing an expanded call, or the call itself. -/
private def origin (program : Eff NativeOp) (p : List Nat) : List Nat :=
  let refs := (program.refSites []).filter (fun (site, _) => site.isPrefixOf p)
  match refs with
  | [] => p
  | first :: rest => (rest.foldl (fun acc item => if acc.1.length < item.1.length then item else acc) first).1

/-- Read all four relations. The nodes retain source syntax; calls state both the checked
expanded address and its original occurrence. Definition positions survive expansion. -/
def read (b : Api.Built) : Relations :=
  let program := b.program
  let decls := program.defsOf
  { nodes := .table ["address", "in", "sort", "mark", "word", "names", "constructor"]
      (cata_eff (nodeAlgebra program b.app.rows) program [])
    defs := .table ["k", "name", "role", "body"] (decls.zipIdx.map fun (d, k) =>
      [cell (toString k), cell d.name, roleLine d.role, cell (address (Authoring.bodyPath k))])
    rows := .table ["i", "spelling", "namespace", "request", "answer"]
      (b.app.rows.zipIdx.map fun (r, i) => cells [toString i, r.spelling,
        ((Store.decodeString (r.spelling.toUTF8.data.toList.takeWhile (· != 46))).getD ""), r.request.render, r.answer.render])
    calls := .table ["address", "from", "targetSort", "target", "targetAddress", "origin"]
      ((Api.HostSession.callTable b.program b.app).filterMap fun (p, c) =>
        match c.op with
        | .call k => (decls[k]?).map fun d =>
          [cell (address p), scope program p, cell "def", cell d.name, cell (address (Authoring.bodyPath k)), cell (address (origin program p))]
        | .external i => (b.app.rows[i]?).map fun r =>
          [cell (address p), scope program p, cell "row", cell r.spelling, cell (toString i), cell (address (origin program p))]
        | _ => none) }

private def service (r : List Line) : Option String :=
  match (r[2]?.getD [] : Line) with
  | [.text "init of ", .code name] => some name
  | [.text "method ", .code _, .text " of ", .code name] => some name
  | _ => none

private def definitionKey (r : List Line) : String := "def:" ++ column r 0
private def rowKey (r : List Line) : String := "row:" ++ column r 0
private def hostKey (name : String) : String := "host:" ++ name
private def serviceKey (name : String) : String := "service:" ++ name

private def definition (r : Relations) (key : String) : Option (List Line) :=
  (records r.defs).find? (definitionKey · == key)

private def owner (r : Relations) (key : String) : String :=
  match (definition r key).bind service with
  | some s => serviceKey s
  | none => key

private def target (r : Relations) (call : List Line) : Option String :=
  if column call 2 == "row" then some ("row:" ++ column call 4)
  else ((records r.defs).find? (column · 3 == column call 4)).map definitionKey

private def source (call : List Line) : String := scopeKey (call[1]?.getD [])

/-- Every graph uses the view's checked Kahn order. A cycle keeps the input order and all edges. -/
def ordered (ns : List GraphNode) (es : List (String × String)) : List GraphNode :=
  let edges := es.filterMap fun (a, b) => do
    return ({ fr := ← ns.findIdx? (·.key == a), to := ← ns.findIdx? (·.key == b) } : Tools.View.Flow.Edge)
  (Tools.View.Flow.orderFor ns.length edges edges).2.filterMap (ns[·]?)

private def figure (key caption : String) (ns : List GraphNode) (es : List (String × String)) : Block :=
  let edges := es.eraseDups
  .graph key caption (ordered ns edges) edges

private def constructor (r : Relations) (p : String) : String × String :=
  match (records r.nodes).find? (column · 0 == p) with
  | some row => (column row 3, column row 4)
  | none => ("·", "")

private def definitionNodes (r : Relations) : List GraphNode :=
  (records r.defs).map fun d =>
    let g := constructor r (column d 3)
    { key := definitionKey d, label := column d 1, status := "definition " ++ g.1, detail := g.2 }

private def mainNode (r : Relations) : GraphNode :=
  let g := constructor r (if ((records r.nodes).head?.map (column · 6)).getD "" == "defs" then "1" else "")
  { key := "main", label := "main", status := "eff " ++ g.1, detail := g.2 }

private def moduleNodes (r : Relations) : List GraphNode :=
  if (records r.calls).any (fun call => source call == "layers") then
    let g := constructor r "2"
    [{ key := "layers", label := "module layers", status := "layers " ++ g.1, detail := g.2 }]
  else []

/-- Definition and host-row calls, joined by positions, never by display names. -/
def calls (r : Relations) : Block :=
  let ns := mainNode r :: definitionNodes r ++ moduleNodes r ++ (records r.rows).map fun row =>
    { key := rowKey row, label := column row 1, status := "row " ++ (glyph .eff "perform").1 }
  let es := (records r.calls).filterMap fun call => (target r call).map (source call, ·)
  figure "calls" "Calls from definitions and main to definitions and host rows." ns es

private def hosts (r : Relations) : List String := ((records r.rows).map (column · 2)).eraseDups
private def services (r : Relations) : List String := ((records r.defs).filterMap service).eraseDups

private def boundaryNodes (r : Relations) : List GraphNode :=
  (hosts r).map (fun name => { key := hostKey name, label := name, status := "host " ++ (glyph .eff "perform").1 }) ++
  (services r).map (fun name => { key := serviceKey name, label := name, status := "service " ++ (glyph .eff "defs").1 }) ++
  (definitionNodes r).filter (fun n => ((definition r n.key).bind service).isNone) ++ moduleNodes r ++ [mainNode r]

private def dependencies (r : Relations) : List (String × String) :=
  ((records r.calls).filterMap fun call => do
    let dst := owner r (source call)
    let key ← target r call
    let src ← if column call 2 == "row" then
      ((records r.rows).find? (rowKey · == key)).map (fun row => hostKey (column row 2))
      else some (owner r key)
    if src == dst then none else some (src, dst)).eraseDups

/-- One wire per provider identity. Multiple consumers meet the same wire. -/
def boundary (r : Relations) : Block :=
  let ds := dependencies r
  let providers := (ds.map Prod.fst).eraseDups
  let boxes := boundaryNodes r
  let wires := providers.map fun key =>
    { key := "wire:" ++ key, label := (boxes.find? (·.key == key)).map (·.label) |>.getD key
      status := "wire " ++ (glyph .eff "service").1 }
  let es := providers.map (fun key => (key, "wire:" ++ key)) ++ ds.map (fun (a, b) => ("wire:" ++ a, b))
  figure "boundary" "Boundary incidence: shared service wires join providers to consumers; no execution order is claimed." (boxes ++ wires) es

/-- Contract every wire in the boundary by joining each incoming edge to each outgoing edge. -/
def boxes (r : Relations) : Block :=
  match boundary r with
  | .graph _ _ ns es =>
    let wires := ns.filter (fun n => (n.key.toUTF8.data.toList.take 5) == "wire:".toUTF8.data.toList)
    let contracted := wires.flatMap fun wire =>
      (es.filter (·.2 == wire.key)).flatMap fun (a, _) =>
        (es.filter (·.1 == wire.key)).map (fun (_, b) => (a, b))
    figure "boundary-boxes" "The boundary with each service wire contracted." (ns.filter fun n => !(wires.any (·.key == n.key))) contracted
  | _ => .graph "boundary-boxes" "The boundary with each service wire contracted." [] []

private def path (s : String) : List Nat :=
  if s.isEmpty then [] else
    let parsed := s.toUTF8.data.toList.foldl (fun (parts, n) c =>
      if c == 46 then (parts ++ [n], 0)
      else (parts, n * 10 + (c.toNat - 48))) ([], 0)
    parsed.1 ++ [parsed.2]

/-- Layer constructors and their nearest enclosing layer constructor, queried from addresses.
The node relation's generated fold enters layers through `cata_layer`; lists are transparent here. -/
def layers (r : Relations) : Block :=
  let rs := (records r.nodes).filter (column · 2 == "layer")
  let ns := rs.map fun row =>
    { key := "layer:" ++ column row 0, label := column row 4, status := "layer " ++ column row 3, detail := column row 5 }
  let es := rs.filterMap fun row =>
    let p := path (column row 0)
    let ancestors := rs.filter fun a => let q := path (column a 0); q.length < p.length && q.isPrefixOf p
    let parent := ancestors.foldl (fun acc a => if (path (column a 0)).length > (path (column acc 0)).length then a else acc) []
    if parent.isEmpty then none else some ("layer:" ++ column parent 0, "layer:" ++ column row 0)
  figure "layers" (if rs.isEmpty then "This program has no stored layer constructors."
    else "Stored layer constructor positions and reference targets; this picture states no merge commutativity.") ns es

/-- Each mapping row names an entity or dependency present in the same relations. -/
def mapping (r : Relations) : Block :=
  .table ["ours", "Effect TypeScript", "algebra"]
    ((hosts r).map (fun h => cells [h ++ " host namespace", "Layer<Tag> supplied by the host", "comodel of the row operation syntax signature"]) ++
     (services r).map (fun s => cells [s ++ " service block", "Layer.effect(Tag, map(init, closures))", "handler with one program per method"]) ++
     [cells ["main", "Effect.provide(program, layer)", "term over the handled methods"]] ++
     (dependencies r).map (fun (a, b) => cells [a ++ " to " ++ b, "Layer.provide", "provider-to-consumer incidence"]) ++
     ((records r.nodes).filter (fun row => column row 2 == "layer")).map
       (fun row => cells ["layer at " ++ column row 0,
         if column row 6 == "ref" then "reference to a hoisted layer constant" else "Layer." ++ column row 6,
         if column row 6 == "merge" || column row 6 == "mergeAll" then
           "incidence overlay; tensor only for disjoint services"
         else if column row 6 == "provide" || column row 6 == "provideMerge" then "shared-wire incidence overlay"
         else if column row 6 == "ref" then "reference to " ++ column row 5
         else "constructor of the layer signature"]))

/-- One document, selected by a command reading. All formats fold this value. -/
def document (b : Api.Built) (what : String) : Tools.Document.Document :=
  let r := read b
  let mappingPart := Block.part "mapping" "The program and its boundary" [mapping r]
  let figures := if what == "boundary" then [boundary r, boxes r]
    else if what == "calls" then [calls r]
    else if what == "layers" then [layers r]
    else [boundary r, boxes r, calls r, layers r]
  let tables := if what == "relations" then
    [Block.part "relation-nodes" "Nodes" [r.nodes], .part "relation-defs" "Definitions" [r.defs],
     .part "relation-rows" "Rows" [r.rows], .part "relation-calls" "Calls" [r.calls]] else []
  { title := "The program as relations and graphs"
    producer := ["GENERATED by Compiler.Graphs; do not edit", "python3 scripts/generate.py --only graphs"]
    body := [.para [.text "Node addresses name stored syntax. Call addresses name the checked expansion; origin names the stored call or reference."]] ++ tables ++ [mappingPart] ++
      figures.map (fun | .graph _ caption [] [] => .para [.text caption] | block => block) }

end Compiler.Graphs
