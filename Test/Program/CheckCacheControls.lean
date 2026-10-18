import Effect4.Program.Typing.CheckCache
import Effect4.Laws.Program.CheckAgreement
import Tools.Session
import Effect4.Program.Scoped
import Effect4.Run.Kit
set_option autoImplicit false
namespace Test.Program.SeamsV1
open Effect4 Effect4.Program Check Check.Internal
deriving instance DecidableEq for Verdict
def composed (i : CheckInput) := combine i ((deps i).map fun d => run d.input)
def n1 : NativeEff := .succeed (.lit (.nat 1))
def bad : NativeEff := .succeed (.var 0)
def idDecl : DefDecl := { name := "id", request := .nat, answer := .nat }
def idBody : NativeEff := .succeed (.var 0)
def invokeId : NativeEff := .perform (.call 0) (.lit (.nat 5))
def checkedModule : NativeEff := .defs [idDecl] (.cons idBody .nil) invokeId .nil
def badLayers : LayerTerms NativeOp := .cons (.effectDiscard bad) .nil
def withLayers : NativeEff := .defs [] .nil n1 badLayers
def faultMismatch : NativeEff := .defs [idDecl] .nil
  (.provideLayer (.ref [9]) false n1) .nil
def besideRef : NativeEff := .provideLayer (.effectDiscard n1) false
  (.bind (.provideLayer (.ref [0]) false n1) n1)
def controls : List NativeEff :=
  [n1, bad, checkedModule, .defs [] .nil n1 .nil, withLayers,
    .defs [idDecl] .nil invokeId .nil,
    .defs [] (.cons n1 .nil) n1 .nil,
    .defs [{ idDecl with answer := .var 0 }] (.cons idBody .nil) invokeId .nil,
    .defs [idDecl] (.cons (.succeed (.lit (.str "a"))) .nil) invokeId .nil,
    faultMismatch, besideRef]

#guard controls.all fun p => decide (composed (.module {} [] p) = run (.module {} [] p))
#guard (deps (.module {} [] (.defs [] .nil n1 .nil))).length = 1
#guard (run (.part ⟨{}, [], .root⟩ [] (Part.layersProgram .nil))).result.toBool = false
#guard (run (.module {} [] (.defs [] .nil n1 .nil))).result.toBool = true
#guard ((run (.module {} [] withLayers)).result.toOption).isNone
#guard ((Checker.refusal (composed (.module {} [] withLayers)).result).map (·.path)) =
  some [2, 0, 0]
#guard ((Checker.refusal (composed (.module {} [] faultMismatch)).result).map (·.reason.head)) =
  some "referenceIllFormed"
#guard ((Checker.refusal (Checker.checkModule ({} : SigApp).signature faultMismatch.expandRefs)).map
  (·.reason.head)) = some "definitionsMismatch"
#guard combine (.module {} [] checkedModule) [] = run (.module {} [] checkedModule)

def oneRow : SigData := ⟨{ rows := [Row.hole "a" .nat] }, [], .root⟩
def twoRows : SigData := ⟨{ rows := [Row.hole "a" .nat, Row.hole "b" .string] }, [], .root⟩
def extCall : NativeEff := .perform (.external 0) (.lit .unit)
def nextCall : NativeEff := .perform (.external 1) (.lit .unit)
#guard oneRow.extendsB twoRows
#guard run (.part oneRow [] extCall) = run (.part twoRows [] extCall)
#guard run (.part oneRow [] nextCall) != run (.part twoRows [] nextCall)


#guard (Checked.ask Oracle.uncached (.part oneRow [] extCall)).trace.length = 1
#guard (Checked.ask Oracle.uncached (.module {} [] n1)).trace.length = 1
#guard (Checked.ask Oracle.uncached (.module {} [] (.defs [] .nil n1 .nil))).trace.length = 1
def moduleTrace := Checked.ask Oracle.uncached (.module {} [] checkedModule)
def learned := Memo.empty.learn moduleTrace
#guard learned.entries.length = (deps (.module {} [] checkedModule)).length
#guard (deps (.module {} [] checkedModule)).all fun d =>
  learned.entries.any (HitRule.exact.hit d.input)
def suggestionDoc : Doc := Doc.open {} ⟨.bind n1 (Sketch.hole {} 0), [Row.hole "n" .nat]⟩
def suggestion := CheckCache.suggest Oracle.uncached suggestionDoc [1] 8 0 [n1]
#guard suggestion.value.isSome
#guard suggestion.trace.length > 0
#guard suggestion.value.map (fun s => decide (s.doc = suggestionDoc.id)) = some true
#guard (Memo.empty.learn suggestion).entries.length = suggestion.trace.length
#guard match suggestion.value with
  | some result => result.suggestions.any fun item =>
    match item.evidence with | .exactFit _ => true | _ => false
  | none => false
#guard (extension.hit (.part twoRows [] extCall)
  (.part oneRow [] extCall,run (.part oneRow [] extCall)))
#guard !(extension.hit (.part twoRows [] nextCall)
  (.part oneRow [] nextCall,run (.part oneRow [] nextCall)))
#guard match (explain Oracle.uncached (.module {} [] bad)).value with
  | some e => decide (e.part = some (.part ⟨{},[],.root⟩ [] bad))
  | none => false
#guard match (explain Oracle.uncached (.module {} [] withLayers)).value with
  | some e => decide (e.refusal.path = [2,0,0]) && e.part.isSome
  | none => false
#guard match (explain Oracle.uncached (.module {} [] faultMismatch)).value with
  | some e => decide (e.refusal.reason.head = "referenceIllFormed") && e.part.isNone
  | none => false
def aggregateMismatch : NativeEff :=
  .defs [idDecl] (.cons (.succeed (.lit (.str "a"))) .nil) invokeId .nil
#guard (deps (.module {} [] aggregateMismatch)).all (fun d => (run d.input).result.toBool)
#guard match (explain Oracle.uncached (.module {} [] aggregateMismatch)).value with
  | some e => decide (e.refusal.reason.head = "bodyNotDeclared") && e.part.isNone
  | none => false
#guard (explain Oracle.uncached (.module {} [] n1)).value.isNone

-- Retained original controls: row identity, contextual evidence, placement, and lexical environments.
def natApp : SigApp := { rows := [Row.hole "external" .nat] }
def strApp : SigApp := { rows := [Row.hole "external" .string] }
def dataAt (app : SigApp) : SigData := ⟨app,[],.root⟩
#guard (run (.part (dataAt natApp) [] extCall)).result != (run (.part (dataAt strApp) [] extCall)).result
#guard !(dataAt natApp).extendsB (dataAt strApp)
#guard (.part (dataAt natApp) [] extCall : CheckInput) != .part (dataAt strApp) [] extCall

def catalogueSketch : Sketch := ⟨.bind n1 (Sketch.hole {} 0),[Row.hole "h" .nat]⟩
def catalogueDoc : Doc := Doc.open {} catalogueSketch ⟨"suggest-doc",0⟩
def catalogue := CheckCache.suggest Oracle.uncached catalogueDoc [1] 10 0 [nextCall]
#guard catalogue.value.map (·.revision) = some 0
#guard catalogue.value.map (·.cursor) = some 0
#guard catalogue.value.map (·.limit) = some 10
#guard catalogue.value.map (·.env) = some [.nat]
#guard catalogue.value.map (·.expected) = some (.pure .nat)
#guard catalogue.value.map (fun r => r.suggestions.any (fun s =>
  decide (s.program = .succeed (.var 0)) && decide (s.evidence = .exactFit (.pure .nat)))) = some true
#guard catalogue.value.map (fun r => r.suggestions.any (fun s =>
  decide (s.program = nextCall) && match s.evidence with
    | .refused why => decide (why.path = [1]) | _ => false)) = some true
#guard catalogue.value.map (fun r => r.suggestions.any (fun s =>
  decide (s.sourcePath = some [0]) && decide (s.evidence = .differentEnv [] [.nat]))) = some true

def catalogueMemo := Memo.empty.learn catalogue
def catalogueCached := CheckCache.suggest (catalogueMemo.oracle (HitRule.exact.or extension))
  catalogueDoc [1] 10 0 [nextCall]
#guard catalogueCached.value.map (·.suggestions) = catalogue.value.map (·.suggestions)
#guard catalogue.trace.all (fun e => catalogueMemo.entries.any (HitRule.exact.hit e.1))
#guard
  let opened := Tools.Session.answer {}
    { op := "open", program := some (Tools.JsonBridge.toHex catalogueSketch.program),
      holes := some (Tools.JsonBridge.toHex catalogueSketch.holes) }
  let answered := Tools.Session.answer opened.1
    { op := "suggest", path := [1], limit := 2, cursor := 0,
      candidates := some (Tools.JsonBridge.toHex [nextCall]) }
  answered.2.ok && decide (answered.2.result.getObjValAs? Nat "revision" = .ok 0) &&
    decide ((answered.2.result.getObjValD "bounds").getObjValAs? Nat "limit" = .ok 2) &&
    !answered.1.cache.entries.isEmpty

def badVar : NativeEff := .bind n1 (.succeed (.var 42))
def badKey : CheckInput := .part oneRow [] badVar
def badMemo := Memo.empty.learn (Checked.ask Oracle.uncached badKey)
#guard badMemo.entries.any (HitRule.exact.hit badKey)
#guard (place [8,4] ((badMemo.oracle HitRule.exact).ask badKey)).result =
  Checker.check oneRow.signature [] [8,4] badVar
#guard (place [8,4] ((badMemo.oracle HitRule.exact).ask badKey)).result !=
  Checker.check oneRow.signature [] [] badVar
#guard !twoRows.extendsB oneRow
#guard extension.hit (.part twoRows [] extCall) (.part oneRow [] extCall,run (.part oneRow [] extCall))
#guard !(extension.hit (.part twoRows [] nextCall) (.part oneRow [] nextCall,run (.part oneRow [] nextCall)))

def closedAtRoot : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
#guard closedAtRoot.scopedAt 0
#guard (run (.part (dataAt {}) [] closedAtRoot)).result = .ok (.pure .nat)
#guard (run (.part (dataAt {}) [.string] closedAtRoot)).result = .ok (.pure .string)
#guard !HitRule.exact.hit (.part (dataAt {}) [.string] closedAtRoot)
  (.part (dataAt {}) [] closedAtRoot,run (.part (dataAt {}) [] closedAtRoot))
#guard !(extension.hit (.part (dataAt {}) [.string] closedAtRoot)
  (.part (dataAt {}) [] closedAtRoot,run (.part (dataAt {}) [] closedAtRoot)))
#guard (run (.part (dataAt {}) [.string] (Eff.weaken 0 closedAtRoot))).result = .ok (.pure .nat)

def fDecl : DefDecl := { name := "f", request := .unit, answer := .nat }
def blockSketch : Sketch := ⟨.defs [fDecl] (.cons n1 .nil) n1 .nil,[]⟩
#guard partSigAt blockSketch.program [0,0] = .body [fDecl] []
#guard partSigAt blockSketch.program [0,1,0] = .root
#guard partSigAt blockSketch.program [1] = .block [fDecl]
#guard partSigAt blockSketch.program [] = .root
#guard (Effect4.Run.Kit.check {} checkedModule).toBool

end Test.Program.SeamsV1
