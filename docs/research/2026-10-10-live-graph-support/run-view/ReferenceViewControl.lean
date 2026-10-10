import Baseline
import Tools.View.Run

/-! Finite source/expansion control for `prepared-run-view-agrees`.
Concept `initial-algebras-folds`, serving `reference-expansion-complete` and the R14 address view.
This control checks the isolated ae80ada1 source, not the 3ef7aeb0 scope-rule landing. -/
namespace RunViewReferenceControl
open Effect4 Effect4.Program Tools.View

def key : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
-- One source reference to an earlier layer, with no definition body or host row.
def program : NativeEff :=
  .provideLayer (.merge (.succeed key (.nat 7)) (.ref [0, 0])) false (.service key)

#guard program.refSites [] = [([0, 1], [0, 0])]
#guard program.layerRefsWF
#guard (Api.Author.Internal.finishBuild program [] []).isOk
-- Source checking rejects the reference even though whole-program admission accepts it.
#guard match Api.Author.Internal.finishBuild program [] [] with
  | .error _ => false
  | .ok b =>
    let session := EditSession.open ⟨b.table, []⟩ { program := b.program }
    session.view.type.isNone && session.view.refusals.any fun r =>
      r.path == [0, 1] && r.reason.head == "layerReference"

-- Negative display control: the source refusal has no visible marker or note.
-- The non-Eff table entry has no result; the parent carries the refusal at its child's path.
#guard match Api.Author.Internal.finishBuild program [] [] with
  | .error _ => false
  | .ok b =>
    let prepared := Tools.View.Run.prepare b
    prepared.lines.any (fun (path, line) =>
      path == [0, 1] && line.state == .plain && line.type.isEmpty && line.note.isEmpty) &&
      !prepared.lines.any (fun (_, line) => line.state == .refused)

-- The actual frame retains this former output, while its printed module succeeds.
#guard match Api.Author.Internal.finishBuild program [] [] with
  | .error _ => false
  | .ok b =>
    let s := Effect4.Run.open b "view"
    let frame := Tools.View.Run.frame "one reference" none s "open"
    reprStr frame == reprStr (RunViewBaseline.frame "one reference" program none s "open") &&
      match frame.code with
      | none => false
      | some code => !code.lines.any (·.startsWith "no module:")

-- A reference-free control supplies its root's source type.
#guard match Api.Author.Internal.finishBuild
    (.provideLayer (.succeed key (.nat 7)) false (.service key)) [] [] with
  | .error _ => false
  | .ok b => (Tools.View.Run.prepare b).lines.any fun (path, line) =>
      path.isEmpty && line.type == "number" && line.state == .plain

#eval match Api.Author.Internal.finishBuild program [] [] with
  | .error _ => "admission refused"
  | .ok b =>
    let prepared := Tools.View.Run.prepare b
    reprStr (prepared.lines.toList.map fun (entry : List Nat × Line) =>
      (entry.1, entry.2.text, entry.2.type, entry.2.note, entry.2.state))
end RunViewReferenceControl
