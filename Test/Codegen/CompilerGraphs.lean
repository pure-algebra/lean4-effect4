import Compiler.Graphs
import Tools.View.LayerGraph
import Tools.View.Graph
import Test.Api.SessionContract

/-!
# Readers and finite controls for program graph queries

G3, G4 and G5 are finite checks on the to-do session and the controls below.
G4 states no general equivalence between row coverage and session admission.
The incidence readers apply G1 and G2; they state no agreement with the command's boundary query.
Every rendered value stays inside a command, so no battery declaration owns rendered bytes.
-/

set_option autoImplicit false
namespace Test.Codegen.CompilerGraphs
open Effect4 Effect4.Program Effect4.Api Tools.Document Tools.View
open Compiler.Graphs Test.Api.SessionFixtures

/-- One admitted external row, shared by two definitions in the controls. -/
def hostRow : Program.Row := (Authoring.Row.host "Host.get" .unit .nat).row

/-- Two definitions share a display name and a host, while keeping distinct positions. -/
def shared : Object :=
  { app := { rows := [hostRow] }
    program := .defs
      [{ name := "main", request := .unit, answer := .nat },
       { name := "main", request := .unit, answer := .nat }]
      (.cons (.perform (.external 0) (.lit .unit))
        (.cons (.perform (.external 0) (.lit .unit)) .nil)) unitProgram .nil }

/-- A stored module layer and a reference to it both contain a checked host call. -/
def referencedCall : Object :=
  { app := { rows := [hostRow] }
    program := .defs [] .nil
      (.provideLayer (.ref [2, 0]) false (.service natKey))
      (.cons (.effect natKey (.perform (.external 0) (.lit .unit))) .nil) }

/-- An empty declaration block still places its main at child one. -/
def emptyBlock : Object := { app := {}, program := .defs [] .nil unitProgram .nil }

/-- A self-call has no topological order; its graph must retain the edge. -/
def recursive : Object :=
  { app := {}, program := .defs [{ name := "loop", request := .unit, answer := .unit }]
      (.cons (.perform (.call 0) (.lit .unit)) .nil) unitProgram .nil }

-- Finite evaluation (row 443, the forms): in the boundary a wire is a wire and a box a box; in the
-- calls figure a row is a port. A row's target cell holds its node's key, so no name is joined.
#guard todoSession.any fun b =>
  let r := Compiler.Graphs.read b
  (match boundary r, calls r with
   | .graph _ _ bs _, .graph _ _ cs _ =>
     bs.all (fun n => (n.form == .wire) == n.key.startsWith "wire:") &&
     cs.all (fun n => (n.form == .port) == n.key.startsWith "row:")
   | _, _ => false) &&
  (records r.calls).all fun call => match (call[3]? : Option Tools.Document.Line) with
    | some (.code key :: _) => key.startsWith "def:" || key.startsWith "row:"
    | _ => false

-- Finite evaluation: the four to-do relations keep the probe's measured rows.
#guard todoSession.any fun b =>
  let r := Compiler.Graphs.read b
  [records r.nodes |>.length, records r.defs |>.length,
    records r.rows |>.length, records r.calls |>.length] == [70, 5, 9, 14] &&
  (document b "relations").check.isOk

-- G3, finite evaluation: the to-do's three shared wires contract to its three dependencies.
#guard todoSession.any fun b =>
  let r := Compiler.Graphs.read b
  match boundary r, boxes r with
  | .graph _ _ ns es, .graph _ _ contracted edges =>
    ns.length == 7 && es.length == 6 && contracted.length == 4 && edges.length == 3 &&
    edges.contains ("host:TodoRepo", "service:TodoApp") &&
    edges.contains ("host:Session", "main") && edges.contains ("service:TodoApp", "main")
  | _, _ => false

-- G3 control: one provider has one wire shared by two differently positioned consumers.
#guard match shared.open with
  | .error _ => false
  | .ok b =>
    let r := Compiler.Graphs.read b
    match boundary r, boxes r, calls r with
    | .graph _ _ ns es, .graph _ _ _ contracted, .graph _ _ cn ce =>
      (document b "relations").check.isOk &&
      (ns.filter (·.key == "wire:host:Host")).length == 1 && es.length == 3 &&
      es.contains ("wire:host:Host", "def:0") && es.contains ("wire:host:Host", "def:1") &&
      contracted.length == 2 && contracted.contains ("host:Host", "def:0") &&
      contracted.contains ("host:Host", "def:1") &&
      (cn.filter (·.label == "main")).length == 3 &&
      ce.contains ("def:0", "row:0") && ce.contains ("def:1", "row:0")
    | _, _, _ => false

-- G4, finite evaluation: each to-do row has its namespace host; no foreign key remains.
#guard todoSession.any fun b =>
  let r := Compiler.Graphs.read b
  match calls r, boundary r with
  | .graph _ _ cn _, .graph _ _ bn _ =>
    (ServiceSession.foreign b).isEmpty &&
    (records r.rows).all fun row =>
      cn.any (·.key == "row:" ++ text (row[0]?.getD [])) &&
      bn.any (·.key == "host:" ++ text (row[2]?.getD []))
  | _, _ => false

-- Reader: the session constructor's law, at the to-do source and its admitted lifetime.
#check fun (sourceExists : todoBuilt.isSome = true) (sessionExists : todoSession.isSome = true) =>
  Built.session_ok_iff (todoBuilt.get sourceExists) "TodoApp" (todoSession.get sessionExists)

-- G5, finite evaluation: every edge of each to-do figure goes forward in its Kahn order.
#guard todoSession.any fun b =>
  let r := Compiler.Graphs.read b
  [boundary r, boxes r, calls r, layers r].all fun block =>
    match block with
    | .graph _ _ ns es =>
      (ordered ns es).map (·.key) == ns.map (·.key) &&
      es.all fun (a, z) => match ns.findIdx? (·.key == a), ns.findIdx? (·.key == z) with
        | some i, some j => i < j
        | _, _ => false
    | _ => false

-- Reader: the existing rank law at the two positions of one forward edge.
#check Graph.ranks_forward
  { nodes := #[⟨"source", "source", "", false, .box⟩, ⟨"target", "target", "", false, .box⟩], edges := #[⟨"edge", 0, 1⟩] }
  ⟨"edge", 0, 1⟩ (List.mem_singleton_self _) (by decide) (by decide)

-- G5 control: the stable fallback retains a cycle; it cannot make the self-edge forward.
#guard match recursive.open with
  | .error _ => false
  | .ok b => match calls (Compiler.Graphs.read b) with
    | .graph _ _ ns es =>
      (document b "calls").check.isOk && ns.map (·.key) == ["main", "def:0"] &&
      es == [("def:0", "def:0")] && (ordered ns es).map (·.key) == ns.map (·.key)
    | _ => false

-- Control: the existing shadowed service keeps both definitions despite their equal names.
#guard shadowed.any fun o => match o.open with
  | .error _ => false
  | .ok b =>
    let r := Compiler.Graphs.read b
    let defs := records r.defs
    match calls r with
    | .graph _ _ ns _ =>
      (document b "relations").check.isOk && defs.length == 6 &&
      (ns.filter (·.label == "TodoApp_list")).length == 2 &&
      (ns.filter (fun n => (defs.map fun d => "def:" ++ text (d[0]?.getD [])).contains n.key)).length == 6
    | _ => false

-- Control: stored reference syntax stays visible, with its target as data.
#guard match moduleLayer.open with
  | .error _ => false
  | .ok b => match layers (Compiler.Graphs.read b) with
    | .graph _ _ ns _ =>
      ns.any (fun n => n.key == "layer:0.1.0.0" && n.detail == "ref 2.0") &&
      ns.any (·.key == "layer:2.0")
    | _ => false

-- Control: expanded addresses retain their source reference and module owner.
#guard match referencedCall.open with
  | .error _ => false
  | .ok b =>
    let r := Compiler.Graphs.read b
    let cs := (records r.calls).map (fun row => row.map text)
    match calls r, layers r with
    | .graph _ _ ns es, .graph _ _ ls _ =>
      (document b "relations").check.isOk && cs.length == 2 &&
      cs.any (fun row => row[0]? == some "1.0.0" && row[5]? == some "1.0") &&
      cs.any (fun row => row[0]? == some "2.0.0" && row[5]? == some "2.0.0") &&
      ns.any (·.key == "layers") && es.contains ("layers", "row:0") &&
      es.contains ("main", "row:0") &&
      ls.any (fun n => n.key == "layer:1.0" && n.detail == "ref 2.0")
    | _, _ => false

-- Control: neither an empty definition block nor a bare main displays the block's constructor.
#guard [emptyBlock, ({ app := {}, program := unitProgram } : Object)].all fun o =>
  match o.open with
  | .error _ => false
  | .ok b => match calls (Compiler.Graphs.read b) with
    | .graph _ _ ns _ => ns.any (fun n => n.key == "main" && n.detail == "succeed")
    | _ => false

-- Readers G1 and G2: relation names supply vertices, and real layer constructors supply composition.
#check fun (present : todoSession.isSome = true) =>
  let b := todoSession.get present
  let atoms : EffAlgebra NativeOp (fun _ => AGraph String) := EffAlgebra.ofLayer fun _ _ _ =>
    ((records (Compiler.Graphs.read b).rows).map fun row => text (row[2]?.getD [])).foldr
      (fun name rest => .overlay (.vertex name) rest) .empty
  LayerGraph.hypergraph_provide atoms (.succeed natKey (.nat 23)) (.ref [2, 0])

#check fun (present : todoSession.isSome = true) =>
  let b := todoSession.get present
  let atoms : EffAlgebra NativeOp (fun _ => AGraph String) := EffAlgebra.ofLayer fun _ _ _ =>
    ((records (Compiler.Graphs.read b).rows).map fun row => text (row[2]?.getD [])).foldr
      (fun name rest => .overlay (.vertex name) rest) .empty
  LayerGraph.hypergraph_merge_comm atoms (.succeed natKey (.nat 23)) (.ref [2, 0])

end Test.Codegen.CompilerGraphs
