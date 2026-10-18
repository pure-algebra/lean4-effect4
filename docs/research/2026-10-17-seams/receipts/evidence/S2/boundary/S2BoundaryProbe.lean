import S1DocControls
import Effect4.Laws.Program.FillSet

/-!
Finite controls for the exact S2 connector hypotheses.
They serve kept_eq_certified and publish_eq_materialize under initial-algebras-folds, R14.
These controls prove neither connector. They retain the old certification and materialization observations.
-/
set_option autoImplicit false
set_option maxRecDepth 20000
namespace SeamsS2BoundaryScout
open Effect4 Effect4.Program
open SeamsS1Scout
open SeamsS1Scout.FeedControls (n7 str)
open SeamsCheckScout (n1)

-- A reference-free base alone does not give kept_eq_certified when the filling adds a reference.
def keyA : ServiceKey := ⟨⟨127⟩, ⟨127⟩⟩
def appA : SigApp := { services := [(keyA, .string)] }
def base : Sketch := ⟨.bind (.provideLayer (.effect keyA str) false n1) n7, []⟩
def withRef : NativeEff := .provideLayer (.ref [0, 0]) false n7
def session : SeamsS1Scout.SourceSession := (SeamsS1Scout.SourceSession.open_ Oracle.uncached appA base).value
#guard base.program.refSites [] = []
#guard !(withRef.refSites []).isEmpty
#guard certifiedB base appA [1] withRef = false
#guard (session.feed Oracle.uncached .keepExact (.fill [1] withRef)).value.toOption.isSome
#guard (session.feed Oracle.uncached .keepExact (.fill [1] withRef)).value.toOption.map
  (fun p => decide (p.1.table = p.1.sketch.sourceTable appA)) = some true

-- Both fills certify separately through expansion, but their joint publication must refuse.
#guard (session.feed Oracle.uncached .keepExact (.fill [0] n7)).value.toOption.isSome
def doc : SeamsS1Scout.Doc := (SeamsS1Scout.Doc.open_ ⟨⟨"ref", 0⟩, appA, base⟩).value
def joint := doc.step Oracle.uncached doc.snap (.commit
  [(.at_ [0] (.provideLayer (.effect keyA str) false n1), .fill n7),
   (.at_ [1] n7, .fill withRef)] .keepExact)
#guard joint.value.toOption.isNone
#guard match materialize appA base [([0], n7), ([1], withRef)] with
  | .error (.refused _) => true
  | _ => false

-- Publication can accept a kept local fill on an already refused root.
-- The old materializer always checks the whole root, so it refuses this same resulting sketch.
def broken : Sketch := ⟨.bind n1 (.succeed (.var 2)), []⟩
def brokenDoc : SeamsS1Scout.Doc := (SeamsS1Scout.Doc.open_ ⟨⟨"broken", 0⟩, {}, broken⟩).value
#guard broken.program.refSites [] = []
#guard n7.refSites [] = []
#guard certifiedB broken {} [0] n7 = true
#guard brokenDoc.session.table = broken.sourceTable {}
#guard (brokenDoc.step Oracle.uncached brokenDoc.snap
  (.commit [(.at_ [0] n1, .fill n7)] .keepExact)).value.toOption.map
    (fun p => (p.1.session.view.type, decide (p.1.session.table = p.1.session.sketch.sourceTable {}))) =
      some (none, true)
#guard match materialize {} broken [([0], n7)] with
  | .error (.refused _) => true
  | _ => false

-- Root exclusion remains necessary even on reference-free programs.
#guard certifiedB ⟨n1, []⟩ {} [] n7 = false
#guard ((SeamsS1Scout.SourceSession.open_ Oracle.uncached {} ⟨n1, []⟩).value.feed
  Oracle.uncached .keepExact (.fill [] n7)).value.toOption.isSome
end SeamsS2BoundaryScout
#eval IO.println "S2 boundaries: filling references, positive-base materialization, joint refusal, and root exclusion pass"
