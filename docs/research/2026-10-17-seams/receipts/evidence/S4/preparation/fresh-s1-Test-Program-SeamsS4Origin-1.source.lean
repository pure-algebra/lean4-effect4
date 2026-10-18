import Effect4.Tool.Origin
import Effect4.Run.LiveRecord
import Test.Program.SeamsS4

/-! Finite controls using S1's actual Snap and replayed Doc.
Snapshot origins retain their source data; standalone restoration invents no document identity. -/
namespace Test.Program.SeamsS4Origin
open Effect4 Effect4.Program Effect4.Program.Check
open Test.Program.SeamsS4

def doc : Doc := (Doc.open_ ⟨⟨"demo", 0⟩, app, sketch⟩).value

def started : Option (Tool.Origin × Live) :=
  (Api.Built.ofSketch doc.session.app doc.session.sketch).toOption.map fun built =>
    (.snapshot doc.snap doc.session.app doc.session.sketch,
      (Live.open built "demo" budget).feedAll [.start])

#guard match started with
  | some (.snapshot at_ originApp originSketch, live) =>
    at_.doc.name == "demo" && at_.revision == 0 &&
      originApp.rows.map Row.spelling == ["ask"] && originSketch.program == program &&
      live.run.budget.fuel == 71 && live.run.budget.compileFuel == 109
  | _ => false

def changed : NativeEff :=
  .bind (.perform (.external 0) (.lit .unit)) (.succeed (.lit (.nat 1)))
def edited : Except DocRefusal (Doc × Receipt) :=
  (Doc.step Oracle.uncached doc doc.snap
    (.commit [(.at_ [] program, .fill changed)] .keepExact)).value

#guard match edited, started with
  | .ok (next, _), some (.snapshot at_ _ originSketch, _) =>
    next.snap.revision == 1 && at_.revision == 0 && originSketch.program == program
  | _, _ => false

def standalone : Option (Tool.Origin × Live) :=
  started.bind fun (_, live) => (LiveRecord.save live).restore.toOption.map fun restored =>
    (.standalone, restored)

#guard match standalone with
  | some (.standalone, live) => live.run.id == "demo" &&
      live.run.budget.fuel == 71 && live.run.budget.compileFuel == 109
  | _ => false
end Test.Program.SeamsS4Origin
