import Tools.View.FlowSpecimen

/-!
The placement and limits of this law reader are in PLAN.md.
The consumer combines existing lines and structural flow through their product algebra.
No new program traversal or terminal implementation appears here.
-/

namespace TerminalBoundary

open Effect4 Effect4.Program Tools.View

/-- The existing page readings, computed through one product of their algebras. -/
def readings (program : NativeEff) : List Program.Node × Flow.Flow :=
  let ws := Flow.waits program
  let both := Algebra.fold
    (Algebra.Layer.prod Program.layer (Flow.flowLayer fun k => (ws.lookup k).getD []))
    .eff program
  let part := both.2 []
  (both.1 [] 0, part.flow.closing part.releases)

/-- A reader of `cata_prod` at the proposed shared page builder.
It states equality with the existing readings, without a claim about program execution. -/
theorem readings_eq (program : NativeEff) :
    readings program = (Program.lines program, Flow.ofProgram program) := by
  exact congrArg
    (fun (both : Program.Lines .eff × Flow.FlowAt .eff) =>
      (both.1 [] 0, (both.2 []).flow.closing (both.2 []).releases))
    (Algebra.cata_prod Program.layer
      (Flow.flowLayer fun k => ((Flow.waits program).lookup k).getD []) .eff program)

#print axioms Algebra.cata_prod
#print axioms Program.layer
#print axioms Flow.flowLayer
#print axioms Flow.waits
#print axioms readings_eq

-- Finite execution of the actual consumers, in addition to the general law reader.
-- Rendering remains inside the guard, as the trust rules require for text controls.
#guard FlowSpecimen.programs.all fun (_, _, p) =>
  let both := readings p
  let nodeData := fun (ns : List Program.Node) =>
    ns.map fun n => (n.path, n.depth, n.text, n.op.map reprStr)
  nodeData both.1 == nodeData (Program.lines p) &&
    reprStr (Flow.layout both.2) == reprStr (Flow.layout (Flow.ofProgram p))

-- Changing a key changes the page data but not its text projection.
#guard
  let l : Line := { gutter := "[0]", depth := 0, text := "same", key := "first" }
  let a : Page := { title := "identity", lines := #[l] }
  let b : Page := { a with lines := #[{ l with key := "second" }] }
  a.lines[0].key != b.lines[0].key && pageText a == pageText b

-- An actual program graph can disappear without changing the text projection.
#guard FlowSpecimen.frames.all fun p =>
  p.graph.isSome && pageText p == pageText { p with graph := none }

-- A printable source label and a literal terminal control are different input data.
-- The control remains in the returned string. This guard never writes it to a terminal.
#guard
  let esc := String.singleton (Char.ofNat 27)
  let l : Line := { gutter := "[0]", depth := 0, text := "left" ++ esc ++ "[2Jright", key := "control" }
  let p : Page := { title := "control", lines := #[l] }
  (pageText p).any fun s => s.contains (Char.ofNat 27)

-- A line-state distinction does survive the current text projection.
#guard
  let l : Line := { gutter := "[0]", depth := 0, text := "same", key := "state" }
  let p : Page := { title := "state", lines := #[l] }
  pageText p != pageText { p with lines := #[{ l with state := .refused }] }

-- Terminal placement cannot recover an erased key from equal strings alone.
-- The same character count also says nothing about terminal glyph width.
#guard "A".length == "界".length && "界".utf8ByteSize != "A".utf8ByteSize

#eval FlowSpecimen.programs.length

end TerminalBoundary
