import Test.Api.SessionContract
import Tools.Document.Html
import Tools.Document.Json
import Tools.Document.Figure
open Effect4 Effect4.Program Effect4.Machine Effect4.Api Test.Api.SessionFixtures
open Tools.Document Tools.View
open Effect4.Program.Authoring

/-! Prove-out: the to-do as graphs, every form a fold of one `Document` value. -/

/-- The namespace of a row's spelling: the part before the dot. -/
def nsOf (s : String) : String := ((s.splitOn ".").head?.getD s)

/-- G2, the inside of the box: the call edges of the block, by definition name and row. -/
def callEdges (b : Built) : List (String × String) :=
  let decls := b.program.defsOf
  (HostSession.callTable b.program b.app).filterMap fun (path, c) =>
    let source := match path with
      | 0 :: rest => (decls[((rest.takeWhile (· == 1)).length)]?.map fun (d : DefDecl) => d.name).getD "?"
      | 1 :: _ => "main"
      | _ => "?"
    let target := match c.op with
      | .call k => (decls[k]?.map fun (d : DefDecl) => d.name)
      | .external i => (externalRow b.app.rows i).map fun (r : Program.Row) => r.spelling
      | _ => none
    target.map fun t => (source, t)

def services (b : Built) : List String :=
  (b.program.defsOf.filterMap fun d => match d.role with
    | .serviceMethod s _ _ => some s | _ => none).eraseDups

def serviceOf (b : Built) (defName : String) : Option String :=
  b.program.defsOf.findSome? fun d => if d.name == defName then
    (match d.role with | .serviceMethod s _ _ => some s | .serviceInit s => some s | _ => none) else none

/-- D1, the boundary as Mokhov's graph: one box per host namespace, per service block and the main;
an edge for a dependency, `connect(that, self)`. -/
def boundary (b : Built) : List GraphNode × List (String × String) :=
  let hosts := (b.app.rows.map fun r => nsOf r.spelling).eraseDups
  let blocks := services b
  let es := callEdges b
  let hostToBlock := (es.filterMap fun (src, t) =>
    if hosts.contains (nsOf t) && src != "main" then (serviceOf b src).map fun s => (nsOf t, s) else none).eraseDups
  let blockToMain := (es.filterMap fun (src, t) =>
    if src == "main" then (serviceOf b t).map fun s => (s, "main") else none).eraseDups
  let hostToMain := (es.filterMap fun (src, t) =>
    if src == "main" && hosts.contains (nsOf t) then some (nsOf t, "main") else none).eraseDups
  let blockToBlock := (es.filterMap fun (src, t) =>
    match serviceOf b src, serviceOf b t with
    | some s1, some s2 => if s1 != s2 then some (s2, s1) else none
    | _, _ => none).eraseDups
  ((hosts.map fun h => { key := h, label := h ++ " host", status := "host", detail := "reactor, state σ" }) ++
   (blocks.map fun s => { key := s, label := s ++ " block", status := "handler", detail := "init once, bodies" }) ++
   [{ key := "main", label := "main program", status := "user code" }],
   hostToBlock ++ blockToBlock ++ blockToMain ++ hostToMain)

/-- D3, the boundary as a hypergraph (Fong, BSZ): a wire is a node of its own, typed by its tag. -/
def hypergraph (b : Built) : List GraphNode × List (String × String) :=
  let (ns, es) := boundary b
  (ns ++ (es.map fun (a, c) => { key := s!"{a}→{c}", label := if a == "main" || c == "main" then a else a, status := "wire", detail := "a service tag" }),
   (es.map fun (a, c) => (a, s!"{a}→{c}")) ++ (es.map fun (a, c) => (s!"{a}→{c}", c)))

/-- D2, a layer term as a term graph: one node per constructor occurrence, keyed by its path. -/
partial def termGraph : LayerTerm NativeOp → List Nat → List GraphNode × List (String × String)
  | t, p =>
    let key := String.intercalate "." (p.map toString)
    let node (l : String) (d : String := "") : GraphNode := { key := key, label := l, status := "layer", detail := d }
    let child (i : Nat) (c : LayerTerm NativeOp) :=
      let (ns, es) := termGraph c (p ++ [i])
      (ns, (key, String.intercalate "." ((p ++ [i]).map toString)) :: es)
    match t with
    | .effect k _ => ([node "effect" s!"tag {k.service.value}"], [])
    | .succeed k _ => ([node "succeed" s!"tag {k.service.value}"], [])
    | .effectDiscard _ => ([node "effectDiscard"], [])
    | .provide s r => let (a, ea) := child 0 s; let (c, ec) := child 1 r; (node "provide" :: a ++ c, ea ++ ec)
    | .provideMerge s r => let (a, ea) := child 0 s; let (c, ec) := child 1 r; (node "provideMerge" :: a ++ c, ea ++ ec)
    | .merge s r => let (a, ea) := child 0 s; let (c, ec) := child 1 r; (node "merge" :: a ++ c, ea ++ ec)
    | .fresh i => let (a, ea) := child 0 i; (node "fresh" :: a, ea)
    | .orDie i => let (a, ea) := child 0 i; (node "orDie" :: a, ea)
    | .ref q => ([node "ref" s!"{q}"], [])
    | .mergeAll _ => ([node "mergeAll"], [])

def k1 : ServiceKey := ⟨⟨30⟩, ⟨6⟩⟩
def k2 : ServiceKey := ⟨⟨30⟩, ⟨4⟩⟩
def composed : LayerSrc NativeOp :=
  Layer.provide (Layer.effect k1 (succeed unit)) (Layer.merge (Layer.effect k2 (succeed (nat 1))) (Layer.fresh (Layer.effect k2 (succeed (nat 2)))))

def callGraph (b : Built) : List GraphNode × List (String × String) :=
  let es := callEdges b
  let names := (es.flatMap fun (a, c) => [a, c]).eraseDups
  (names.map fun n => { key := n, label := n, status := if n == "main" then "user code" else if n.contains '.' then "row" else "definition" }, es)

/-- Kahn's order: a node follows every node an edge reaches it from. `Block.graph` takes its nodes in
the order the drawing ranks them (decisions row 365). -/
partial def topo (ns : List GraphNode) (es : List (String × String)) : List GraphNode :=
  let rec go (pending acc : List GraphNode) (fuel : Nat) : List GraphNode :=
    match fuel with
    | 0 => acc ++ pending
    | fuel + 1 =>
      let ready := pending.filter fun n => es.all fun (a, c) => c != n.key || !(pending.any (·.key == a))
      if ready.isEmpty then acc ++ pending
      else go (pending.filter fun n => !(ready.any (·.key == n.key))) (acc ++ ready) fuel
  go ns [] ns.length

def t (s : String) : Line := [.text s]
def mapping : Block := .table ["ours", "Effect TypeScript", "algebra"] [
  [t "a host namespace of rows", t "a Layer<Tag> the host supplies", t "a comodel of the row signature"],
  [t "a service block", t "Layer.effect(Tag, map(init, closures))", t "a handler, one program per method"],
  [t "the main program", t "Effect.provide(program, layer)", t "a term over the methods, handled"],
  [t "rows a block calls", t "Layer.provide(block, host)", t "composition: connect(host, block)"],
  [t "two blocks of disjoint services", t "Layer.merge", t "the tensor: overlay"],
  [t "a second block of one service", t "a second Layer of one Tag", t "a second handler; the same boundary"]]

def docOf (plain cached : Built) : Tools.Document.Document :=
  let (bn, be) := boundary plain
  let (cn, ce) := boundary cached
  let (hn, he) := hypergraph plain
  let (tn, te) := (composed {} [2]).toOption.map (termGraph · [2]) |>.getD ([], [])
  let (gn, ge) := callGraph plain
  { title := "The to-do as graphs", producer := ["walk-view.lean (prove-out)"], body := [
      mapping,
      .graph "boundary-plain" "D1 the boundary, Mokhov's graph: boxes and dependency edges" (topo bn be) be,
      .graph "boundary-cached" "D1 the cached block has the same boundary" (topo cn ce) ce,
      .graph "hypergraph" "D3 the boundary as a hypergraph: wires are nodes typed by a tag" (topo hn he) he,
      .graph "term" "D2 a layer term as a term graph: provide over merge over fresh" (topo tn te) te,
      .graph "calls" "G2 inside the box: the call graph of the session object, plain" (topo gn ge) ge] }

def svgOf (ns : List GraphNode) (es : List (String × String)) : String :=
  match SvgOut.fileText (Figure.picture (fun _ => none) ns es) with
  | .ok s => s | .error e => s!"<p>refused: {e}</p>"

def tsvOf (ns : List GraphNode) (es : List (String × String)) : String :=
  "nodes\nkey\tlabel\tstatus\tdetail\n" ++ String.intercalate "\n" (ns.map fun n => s!"{n.key}\t{n.label}\t{n.status}\t{n.detail}") ++
  "\n\nedges\nsrc\tdst\n" ++ String.intercalate "\n" (es.map fun (a, c) => s!"{a}\t{c}") ++ "\n"

def proveOut : IO Unit := do
  let some plain := todoSession | throw (IO.userError "no plain")
  let some cached := cachedSession | throw (IO.userError "no cached")
  let d := docOf plain cached
  let out := "tools/view/out/view-graph/"
  IO.FS.writeFile (out ++ "todo.gen.md") d.markdown
  IO.FS.writeFile (out ++ "todo.gen.json") (Tools.Document.Json.Document.json d).pretty
  let figures : List (String × String × List GraphNode × List (String × String)) :=
    d.body.filterMap fun b => match b with
    | .graph k c ns es => some (k, c, ns, es) | _ => none
  let mut html := "<!doctype html><html><head><meta charset=\"utf-8\"><link rel=\"stylesheet\" href=\"looks.css\"><link rel=\"stylesheet\" href=\"page.css\"><title>The to-do as graphs</title></head><body style=\"padding:16px\"><div style=\"display:flex;flex-wrap:wrap;gap:24px;align-items:flex-start\">"
  for (k, c, ns, es) in figures do
    IO.FS.writeFile (out ++ k ++ ".gen.svg") (svgOf ns es)
    IO.FS.writeFile (out ++ k ++ ".gen.tsv") (tsvOf ns es)
    html := html ++ s!"<figure style=\"margin:0\"><figcaption style=\"font:14px sans-serif;margin-bottom:6px\">{c}</figcaption>" ++ svgOf ns es ++ "</figure>"
  IO.FS.writeFile (out ++ "index.html") (html ++ "</div></body></html>")
  IO.println s!"wrote {figures.length} figures"
  for (k, _, ns, es) in figures do IO.println s!"{k}: {ns.length} nodes, {es.length} edges"

#eval proveOut
