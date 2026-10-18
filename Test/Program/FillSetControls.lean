import Effect4.Program.Typing.FillSet
import Test.Program.SourceDocumentControls
import Effect4.Laws.Program.FillSet
import Effect4.Tool.Serve
set_option autoImplicit false
namespace Test.Program.SeamsS2
open Effect4 Effect4.Program Check
open Test.Program.SeamsV1 (n1)
open Test.Program.SeamsS1.FeedControls (n7 str)
def h : Row := Row.hole "nat" .nat
def base : Sketch := ⟨.bind (Sketch.hole {} 0)
  (.bind (Sketch.hole {} 1) (Sketch.hole {} 2)), [h,h,h]⟩
def doc : Doc := (Doc.open_ ⟨⟨"fills",0⟩,{},base⟩).value
def start : FillSet := FillSet.open_ doc
def added := start.add Oracle.uncached [([0],n1),([1,0],str),([1,1],n7)]
-- A refused fill carries the kept-exact feed's own refusal: the string's type is not the hole's.
#guard added.value.2 = [.applied [0],
  .refused [1,0] (.notCertified (.notKept ([.nat], .pure .nat) (.ok (.pure .string)))),
  .applied [1,1]]
def pending := added.value.1
#guard pending.pending = [([0],n1),([1,1],n7)]
#guard pending.anchor.revision = 0
#guard match pending.publication with
  | .ok (.commit items .keepExact) => items.length = 2
  | _ => false
def action : DocAction := pending.publication.toOption.getD (.commit [] .keepExact)
def published := doc.step Oracle.uncached pending.anchor action
def next : Doc := (published.value.toOption.map Prod.fst).getD doc
#guard next.snap.revision = 1
#guard next.history.length = 1
#guard (FillSet.open_ next).pending = []
#guard match next.check pending.anchor with | .error (.stale _) => true | _ => false
#guard (start.add Oracle.uncached [([],n1),([9],n1)]).value.2 =
  [.refused [] .root,.refused [9] .unknownAddress]
#guard (pending.add Oracle.uncached [([0],n1),([0],n7)]).value.2 =
  [.collapsed [0],.refused [0] .conflict]
#guard (pending.add Oracle.uncached [([1],.bind n1 n7)]).value.2 =
  [.refused [1] (.overlap [1,1])]
#guard match start.publication with | .error .empty => true | _ => false
#guard match doc.check ⟨⟨"foreign",0⟩,0⟩ with | .error (.foreign _) => true | _ => false
-- References certify at the whole anchor expansion; publication rechecks dependencies.
def key : ServiceKey := ⟨⟨127⟩,⟨127⟩⟩
def app : SigApp := { services := [(key,.string)] }
def referenceBase : Sketch := ⟨.bind (.provideLayer (.effect key str) false n1) n7,[]⟩
def referenceFill : NativeEff := .provideLayer (.ref [0,0]) false n7
def refDoc : Doc := (Doc.open_ ⟨⟨"refs",0⟩,app,referenceBase⟩).value
def refSet := (FillSet.open_ refDoc).add Oracle.uncached [([1],referenceFill),([0],n7)]
#guard refSet.value.2 = [.applied [1],.applied [0]]
def refAction := refSet.value.1.publication.toOption.getD (.commit [] .keepExact)
#guard (refDoc.step Oracle.uncached refSet.value.1.anchor refAction).value.toOption.isNone

#guard next.session.sketch.holes = base.holes
#guard (next.step Oracle.uncached next.snap (.revert 0)).value.toOption.map
  (fun result => decide (result.1.session.sketch.program = base.program)) = some true
#guard FillReference.certifiedB referenceBase app [1] referenceFill = false
#guard referenceBase.program.refSites [] = []
#guard (referenceFill.refSites []).isEmpty = false
#guard match FillReference.materialize {} base [([],n1)] with | .error .root => true | _ => false
#guard match FillReference.materialize {} base [([9],n1),([0],n1)] with
  | .error .unknownAddress => true | _ => false

def broken : Sketch := ⟨.bind n1 (.succeed (.var 2)),[]⟩
def brokenDoc : Doc := (Doc.open_ ⟨⟨"broken",0⟩,{},broken⟩).value
#guard FillReference.certifiedB broken {} [0] n7
-- A fill is certified through the kept-exact feed, which keeps only a typed root's observations:
-- beside the unrelated error the fill set refuses it, while the retired certification, which reads
-- only the focus, accepts it. This is `kept_eq_certified`'s typed-root premise.
#guard match ((FillSet.open_ brokenDoc).add Oracle.uncached [([0],n7)]).value.2 with
  | [.refused [0] (.notCertified (.rootRefused _))] => true
  | _ => false
#guard match FillReference.materialize {} broken [([0],n7)] with
  | .error (.refused _) => true | _ => false

-- Equal identities and revisions do not authorize an anchor against another base.
def otherBase : Sketch := ⟨.bind n1 (.bind n7 n1),[]⟩
def otherDoc : Doc := (Doc.open_ ⟨doc.origin.id,{},otherBase⟩).value
#guard otherDoc.snap.doc = pending.anchor.doc
#guard otherDoc.snap.revision = pending.anchor.revision
#guard (otherDoc.check pending.anchor).toOption.isSome
-- In the tool that pairing cannot arise: every open allocates a fresh generation and clears the
-- pending fills, so a fill at the earlier snapshot refuses as foreign and the state stays.
#guard
  let serve1 (st : Tool.State) (r : Tool.Request) := (Tool.serve Oracle.uncached st r).value
  let (s0, _) := serve1 Tool.empty (.act (.open_ "fills" {} base))
  let (s1, _) := serve1 s0 (.act (.fill ⟨⟨"fills", 0⟩, 0⟩ [([1,0], n1)]))
  let (s2, _) := serve1 s1 (.act (.open_ "fills" {} otherBase))
  let (s3, r3) := serve1 s2 (.act (.fill ⟨⟨"fills", 0⟩, 0⟩ [([1,0], n1)]))
  s2.raw.fills.isNone && s3.transcript.length == s2.transcript.length &&
    match r3.result with
    | .error (.doc (.foreign _)) => true
    | _ => false


namespace SuggestionKeyControls
open Effect4 Effect4.Program Effect4.Program.Check
def rootProgram : NativeEff := .succeed (.lit (.nat 0))
def rootCandidate : NativeEff := .succeed (.lit (.nat 1))
def rootDoc : Doc := (Doc.open_ ⟨⟨"root-key",0⟩,{},⟨rootProgram,[]⟩⟩).value
def rootFocus : Focus NativeOp := ⟨rootProgram,[],.pure .nat⟩
def rootSuggestion := Suggest.suggestOne Oracle.uncached rootDoc rootFocus [] none [] rootCandidate
#guard rootDoc.session.partKey [] rootCandidate = none
#guard match rootSuggestion.value with
  | .ok candidate => candidate.key == .module {} [] rootCandidate
  | .error _ => false
#guard (rootDoc.session.feed Oracle.uncached .keepExact (.fill [] rootCandidate)).value.isOk
#guard (rootDoc.session.feed Oracle.uncached .keepExact (.fill [] rootCandidate)).trace =
  (Checked.ask Oracle.uncached (.module {} [] rootCandidate)).trace
#guard rootSuggestion.trace = (Checked.ask Oracle.uncached (.module {} [] rootCandidate)).trace

def badChild : NativeEff := .succeed (.var 0)
def badProgram : NativeEff := .bind badChild (.succeed (.var 0))
def badDoc : Doc := (Doc.open_ ⟨⟨"missing-focus-key",0⟩,{},⟨badProgram,[]⟩⟩).value
#guard match Place.resolve {} ⟨badProgram,[]⟩ (.at_ [0] badChild) with
  | .ok (path, program) => path == [0] && program == badChild
  | .error _ => false
#guard (badDoc.session.focusAt [0]).isNone
#guard badDoc.session.partKey [0] rootCandidate = none
#guard match (badDoc.session.feed Oracle.uncached .keepExact (.fill [0] rootCandidate)).value with
  | .error (.noFocus [0]) => true
  | _ => false
#guard (badDoc.session.feed Oracle.uncached .keepExact (.fill [0] rootCandidate)).trace.isEmpty
#guard match (Suggest.page Oracle.uncached badDoc [0] [] 0 16).value with
  | .error (.noFocus [0]) => true
  | _ => false
#guard (Suggest.page Oracle.uncached badDoc [0] [] 0 16).trace.isEmpty
#guard match (Suggest.suggestOne Oracle.uncached badDoc
    ⟨badChild,[],.pure .nat⟩ [0] none [] rootCandidate).value with
  | .error (.noFocus [0]) => true
  | _ => false
#guard (Suggest.suggestOne Oracle.uncached badDoc
  ⟨badChild,[],.pure .nat⟩ [0] none [] rootCandidate).trace.isEmpty
end SuggestionKeyControls

end Test.Program.SeamsS2

/-! ## One located refusal on every route (Codex R1.1's red control)

The probe's step 7: fill hole 0 at `[1]` with `succeed (var 1)`, where the environment there holds
one variable. The edit route (`Doc.step`), the pending-fill route (`FillSet.add`) and the suggestion
route (`Suggest.page`) report one refusal: the unbound variable, at the program's own address `[1]`.
The feed places a part's refusal once (`Located.under`); placed twice it would read `[1, 1]`. -/
namespace Test.Program.SeamsS2.LocatedRoutes
open Effect4 Effect4.Program Effect4.Program.Check
open Test.Program.SeamsS1.DocControls (d0)

def wrong : NativeEff := .succeed (.var 1)
def located : TypeRefusal := ⟨[1], .unboundVariable [] 1 1⟩
def viaEdit := d0.step Oracle.uncached d0.snap (.commit [(.hole 0, .fill wrong)] .keepExact)
def viaFill := (FillSet.open_ d0).add Oracle.uncached [([1], wrong)]
def viaSuggest := Suggest.page Oracle.uncached d0 [1] [wrong] 0 1

#guard match viaEdit.value with
  | .error (.feed 0 (.notKept ([.nat], _) (.error r))) => r == located
  | _ => false
#guard match viaFill.value.2 with
  | [.refused [1] (.notCertified (.notKept ([.nat], _) (.error r)))] => r == located
  | _ => false
#guard match viaSuggest.value with
  | .ok ([s], _) => s.evidence == .refused located
  | _ => false
-- red: the refusal placed a second time is another address, which no route answers
#guard (Located.under [1] located).site = [1, 1]
#guard Located.under [1] located != located

/-- An application whose one row is synchronous: its signature is not lawful. -/
def syncApp : SigApp := { rows := [{ Row.hole "ask" .nat with kind := .sync }] }
-- Signature admission refuses first where the program does not type either.
#guard match admitProgram wrong syncApp with
  | .error (.signature _) => true
  | _ => false
-- At a lawful signature the same program is refused with its located typing refusal.
#guard match admitProgram wrong with
  | .error (.illTyped ⟨[], .unboundVariable [] 1 0⟩) => true
  | _ => false
end Test.Program.SeamsS2.LocatedRoutes
