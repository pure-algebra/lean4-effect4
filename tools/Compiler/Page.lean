import Compiler.Graphs
import Tools.View.Program
import Tools.View.Flow

/-!
# The page of a program object: its term, its relation rows and its flows, one key each

A program object (`Api.Built`) on the view's own page (`Tools.View.Page`): the program's lines
above, each with its type at the object's rows, and beside each line the node relation's row for
its address (`Compiler.Graphs.read`); below, the program's flows (`Tools.View.Flow`): each
definition's body as a region named by its definition, side by side, and the main program under
them. A line, its relation row and its mark share one key, the address, so a later motion from
the code through the rows to the graph is a keyed move (row 443).

Nothing new is drawn. The lines are `Program.sessionPage`, the flows are `Flow.flowLayer`'s fold
at each body's address and `Flow.ofProgram`, laid out by `Flow.layout` and joined by rigid moves
(`Laid.beside`, `Laid.below`).
-/

namespace Compiler.Page

open Effect4 Effect4.Program Tools.View

/-- The flow of a subtree at its address in the program: the fold's carrier takes the address in,
so the keys are the program's own. The waits are read on the whole program, whose keys are
absolute. The releases no scope of the subtree holds run as the scope around it closes. -/
def flowAt (program body : NativeEff) (p : List Nat) : Flow.Flow :=
  let ws := Flow.waits program
  let part := cata_eff (EffAlgebra.ofLayer (Flow.flowLayer fun k => (ws.lookup k).getD [])) body p
  part.flow.closing part.releases

/-- **The flows of a program object**: each definition's body as a region keyed by its body's
address and named by its definition, then the main program's flow (`Flow.ofProgram`, which
brackets main as the region `definitions`). A program with no block has its one flow. -/
def flows (program : NativeEff) : List Flow.Flow :=
  match program.block? with
  | some (decls, bodies, _, _) =>
    (bodies.toList.zipIdx.map fun (body, k) =>
      let p := Authoring.bodyPath k
      .region (((decls[k]?).map (·.name)).getD s!"definition {k}") (Program.bracket p) (flowAt program body p)) ++
      [Flow.ofProgram program]
  | none => [Flow.ofProgram program]

/-- The flows laid out and joined: the bodies side by side, and the main program below them. -/
def laid (program : NativeEff) (page : Page) : Laid :=
  let label (k : Key) : Option (String × String) :=
    (page.lines.toList.find? (·.key == k)).map fun l => (l.text, l.type)
  let ls := (flows program).map fun f => Flow.layout (f.relabel label)
  match ls.dropLast, ls.getLast? with
  | [], some main => main
  | b :: bs, some main => (bs.foldl Laid.beside b).below main
  | _, none => {}

/-- The relation row of a line, in words: where it lies, its sort, its mark and word, and what it
names. -/
def rowText (r : Graphs.Relations) (n : Graphs.NodeRow) : String :=
  n.scope.key ++ " " ++ r.scopeLabel n.scope ++ " · " ++ Graphs.sortName n.sort ++ " · " ++
    n.glyph.1 ++ " " ++ n.glyph.2 ++
    (if n.names.isEmpty then "" else " · " ++ r.namesText n.names)

/-- **The page of a program object.** Its lines are the program's, typed at the object's rows,
with the mark of each row it performs. Beside each line, under the line's key, the node relation's
row at its address. Below, the flows, keyed by address. The judgment line counts the relations. -/
def page (b : Api.Built) (title : String) : Page :=
  let session := EditSession.open b.app { program := b.program }
  let r := Graphs.read b
  let nodes := Program.lines b.program
  let judgment := s!"{r.nodes.length} nodes · {r.defs.length} definitions · {r.rows.length} rows · {r.calls.length} calls"
  let g := Program.sessionPage session none title judgment "" ""
  let rows := nodes.map fun n => ((r.node? n.path).map (rowText r)).getD ""
  let g := { g with code := some { head := "relation", lines := rows.toArray, keys := g.lines.map (fun (l : Tools.View.Line) => l.key) } }
  { g with graph := some { title := "flows", laid := laid b.program g } }

end Compiler.Page
