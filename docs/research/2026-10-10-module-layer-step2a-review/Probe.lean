import Effect4.Program.Edit
import Effect4.Api.HostSession

/-! Finite controls only. PLAN.md places each check before this probe. -/
namespace ModuleLayerStep2aReview
open Effect4 Effect4.Program

def unitP : NativeEff := .succeed (.lit .unit)
def badP : NativeEff := .succeed (.var 0)
def bindP : NativeEff := .bind (.succeed (.lit (.nat 7))) (.succeed (.var 0))
def callP : NativeEff := .perform .refMake (.lit (.nat 7))
def releaseP : NativeEff := .scoped (.acquireRelease (.succeed (.lit (.nat 7)))
  (.succeed (.var 0)))
def one (p : NativeEff) : LayerTerms NativeOp := .cons (.effectDiscard p) .nil

def block (layers : LayerTerms NativeOp) : NativeEff :=
  .defs [{ name := "identity", request := .unit, answer := .unit }]
    (.cons (.succeed (.var 0)) .nil) unitP layers

def sketch (layers : LayerTerms NativeOp) : Sketch := ⟨block layers, []⟩

def samples : List (LayerTerms NativeOp) :=
  [.nil, one unitP, one badP, one bindP, one callP, one releaseP,
   .cons (.effectDiscard badP) (one unitP),
   .cons (.merge (.effectDiscard unitP) (.effectDiscard bindP)) .nil,
   .cons (.ref [2, 0]) .nil]

-- The actual whole-module adapter now covers every source address.
#guard samples.all fun ls => (sketch ls).annotate {} == (sketch ls).table {}
#guard samples.all fun ls => ((sketch ls).annotate {}).map (·.path) ==
  Node.addresses (.eff (block ls))
#guard ((sketch .nil).annotate {}).find? (fun e => e.path == [2]) ==
  some ⟨[2], none, none⟩
#guard ((sketch (one badP)).annotate {}).any fun e =>
  match e.result with
  | some (.error r) => r.path == [2,0,0]
  | _ => false
#guard ((sketch (.cons (.effectDiscard badP) (one unitP))).annotate {}).any fun e =>
  e.path == [2,1,0,0] && e.result == some (.ok (EffTy.pure .unit))
#guard ((sketch (one releaseP)).annotate {}).any fun e =>
  e.path == [2,0,0,0,1] && e.env == some (.env [.nat, .exitOf .unknown .unknown])

-- A same-type fill chooses the real splice path, then undo restores the sketch.
def before : EditSession := EditSession.open {} (sketch (one bindP))
def replacement : NativeEff := .succeed (.lit (.nat 12))
def edited : EditSession × Edit.Step := before.feedStep (.fill [2,0,0] replacement)
def after : EditSession := edited.1
#guard before.view.refusals.isEmpty && before.view.type.isSome
#guard edited.2.delta == .spliced [[2,0,0]]
#guard after.table == after.sketch.table {}
#guard after.table == after.sketch.annotate {}
#guard after.view.type == before.view.type
#guard (Node.eff after.sketch.program).at_ [2,0,0] == some (.eff replacement)
#guard edited.2.replaced == some bindP
#guard match edited.2.replaced with
  | some old => ((after.feed (.fill [2,0,0] old)).1.sketch.program == before.sketch.program)
  | none => false
#guard match edited.2.replaced with
  | some old => let undone := (after.feed (.fill [2,0,0] old)).1
                undone.table == before.table && undone.sketch.holes == before.sketch.holes
  | none => false

-- A rejected replacement rechecks and keeps a located refusal at the source address.
def rejected : EditSession × Edit.Delta := before.feed (.fill [2,0,0] badP)
#guard rejected.2 == .rechecked
#guard rejected.1.table == rejected.1.sketch.table {}
#guard rejected.1.view.type.isNone && rejected.1.view.refusals.any (fun r => r.path == [2,0,0])
#guard (before.feed (.fill [2] unitP)).2 == .unchanged

-- The call instance and host call-table key retain source addresses.
def sig : Signature NativeOp := nativeSignature []
def callProgram : NativeEff := block (one callP)
#guard ((programCallAt sig [] callProgram [2,0,0]).map fun c => (c.request, c.answer)) ==
  some (.nat, .refOf .nat)
#guard (programCalls sig [] callProgram).map (·.1) == [[2,0,0]]
#guard (Api.HostSession.callTable callProgram []).map (·.1) == [[2,0,0]]
#guard (programCallAt sig [] callProgram [0,0,0,0]).isNone

#eval (samples.length, samples.foldl (fun n ls => n + ((sketch ls).annotate {}).length) 0)
#eval (edited.2.delta, rejected.2, (Api.HostSession.callTable callProgram []).map (·.1))
end ModuleLayerStep2aReview
