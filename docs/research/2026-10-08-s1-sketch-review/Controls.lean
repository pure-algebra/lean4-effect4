import Effect4.Laws.Program.Sketch

/-! Finite controls and readers of existing laws.
Placement: `scope.md` beside this file. No new general obligation is stated. -/

set_option autoImplicit false

namespace S1SketchReview

open Effect4 Effect4.Program
open Effect4.Machine.Env (Requirement)
open Conform.Effect4.Typing

def natTy : EffTy := ⟨.nat, .never, Requirement.empty⟩
def boolTy : EffTy := ⟨.bool, .never, Requirement.empty⟩
def host : Row := Row.hole "host" .string
def app : SigApp := ⟨[host], []⟩
def natDecl : DefDecl := ⟨"idNat", .nat, .nat, .never, []⟩
def boolDecl : DefDecl := ⟨"idBool", .bool, .bool, .never, []⟩
def idBody : NativeEff := .succeed (.var 0)
def invokeNat : NativeEff := .perform (.call 0) (.lit (.nat 7))
def invokeBool : NativeEff := .perform (.call 1) (.var 0)
def block : NativeEff := .defs [natDecl, boolDecl] (.cons idBody (.cons idBody .nil)) invokeNat
def sketch : Sketch := ⟨block, [Row.hole "old" .string]⟩
def mainFocus : Focus NativeOp := ⟨invokeNat, [], natTy⟩
def boolFocus : Focus NativeOp := ⟨idBody, [.bool], boolTy⟩

-- Positive controls: whole-program checking and root/part environments differ.
#guard sketch.check app = .ok natTy
#guard (Checker.check (app.withHoles sketch.holes).signature [] [] block).toOption.isNone
#guard sketch.focusAt app [] = some ⟨block, [], natTy⟩
#guard sketch.focusAt app [1] = some mainFocus
#guard sketch.focusAt app [0, 0] = some ⟨idBody, [.nat], natTy⟩
#guard sketch.focusAt app [0, 1, 0] = some boolFocus
#guard (sketch.focusAt app [0]).isNone
#guard (sketch.focusAt app [0, 1]).isNone
#guard (sketch.focusAt app [0, 1, 1]).isNone
#guard (sketch.focusAt app [2]).isNone

-- A filling may invoke either installed definition at a part signature.
#guard Checker.check (sketch.sigAt app [0, 1, 0]) [.bool] [] invokeBool = .ok boolTy
#guard (Checker.check (app.withHoles sketch.holes).signature [.bool] [] invokeBool).toOption.isNone
#guard (sketch.fillAt [0, 1, 0] invokeBool).map (·.check app) = some (.ok natTy)
#guard (sketch.fillAt [1] invokeNat).map (·.check app) = some (.ok natTy)

-- Readers: exact existing statements applied to actual checked parts.
example : ∃ s', sketch.fillAt [0, 1, 0] invokeBool = some s' ∧ s'.check app = .ok natTy := by
  have h := Sketch.check_fill_focusAt sketch app (T := natTy) (by decide +kernel)
    (f := boolFocus) (path := [0, 1, 0]) (by decide +kernel) []
    (q' := invokeBool) (pq := []) (by decide +kernel)
  simpa only [List.append_nil] using h

example : ∃ s', sketch.omitAt app [0, 1, 0] (Row.hole "new" .bool) = some s' ∧
    s'.check app = .ok natTy :=
  Sketch.check_omit_focusAt sketch app (by decide +kernel)
    (f := boolFocus) (path := [0, 1, 0]) (by decide +kernel) "new" rfl rfl
    (by decide +kernel) (by decide +kernel)
    ((Formation.check_eq_none_iff _).mp (by decide +kernel))

-- Hole order: one host row, one retained hole, then the newly omitted hole.
def omitted : Option Sketch := sketch.omitAt app [0, 1, 0] (Row.hole "new" .bool)
#guard omitted.map (·.holes) = some [Row.hole "old" .string, Row.hole "new" .bool]
#guard omitted.map (fun s => (Node.eff s.program).at_ [0, 1, 0]) =
  some (some (.eff (.perform (.external 2) (.lit .unit))))
#guard omitted.map (·.check app) = some (.ok natTy)
#guard omitted.map (fun s => ((s.sigAt app [0, 1, 0]).rowOf (.call 0)).answer) = some .nat
#guard omitted.map (fun s => ((s.sigAt app [0, 1, 0]).rowOf (.call 1)).answer) = some .bool
#guard omitted.map (fun s => ((s.sigAt app [0, 1, 0]).rowOf (.external 0)).answer) = some .string
#guard omitted.map (fun s => ((s.sigAt app [0, 1, 0]).rowOf (.external 1)).answer) = some .string
#guard omitted.map (fun s => ((s.sigAt app [0, 1, 0]).rowOf (.external 2)).answer) = some .bool
#guard ((omitted.bind fun s => s.fillAt [0, 1, 0] idBody).map (·.holes)) = omitted.map (·.holes)
#guard ((omitted.bind fun s => s.fillAt [0, 1, 0] idBody).map (·.check app)) = some (.ok natTy)

-- More holes: a filling at the second body's signature uses the newly appended row.
def extended : Sketch := { sketch with holes := sketch.holes ++ [Row.hole "next" .bool] }
def nextHole : NativeEff := Sketch.hole app sketch.holes.length
#guard Checker.check (extended.sigAt app [0, 1, 0]) [.bool] [] nextHole = .ok boolTy
#guard (extended.fillAt [0, 1, 0] nextHole).map (·.check app) = some (.ok natTy)
example : ∃ s', extended.fillAt [0, 1, 0] nextHole = some s' ∧ s'.check app = .ok natTy :=
  Sketch.check_fill_focusAt sketch app (by decide +kernel)
    (f := boolFocus) (path := [0, 1, 0]) (by decide +kernel) [Row.hole "next" .bool]
    (q' := nextHole) (pq := []) (by decide +kernel)

-- Wrong body type: the edit exists, but its checker premise fails and its declaration refuses.
def wrongBody : NativeEff := .succeed (.lit (.nat 1))
#guard Checker.check (sketch.sigAt app [0, 1, 0]) [.bool] [] wrongBody = .ok natTy
#guard ((sketch.fillAt [0, 1, 0] wrongBody).bind fun s => Checker.refusal (s.check app)).map
    (fun r => (r.path, r.reason.head)) = some ([0, 1, 0], "bodyNotDeclared")

-- Missing variable and invalid call: a body receives only its own declared request.
def badScope : NativeEff := .succeed (.var 1)
def scopedWrong : Sketch := ⟨.defs [natDecl, boolDecl]
  (.cons idBody (.cons badScope .nil)) invokeNat, sketch.holes⟩
#guard (scopedWrong.check app).toOption.isNone
#guard (scopedWrong.focusAt app [0, 1, 0]).isNone
#guard (scopedWrong.refusals app).head? = Checker.refusal (scopedWrong.check app)
#guard !(scopedWrong.refusals app).isEmpty
#guard (sketch.focusAt app [0, 1, 0]).map (·.env) = some [.bool]
#guard (Checker.check (sketch.sigAt app [0, 1, 0]) [.bool] []
  (.perform (.call 2) (.lit .unit))).toOption.isNone

-- Refusals: malformed declarations and body counts remain module-check errors.
def mismatch : Sketch := ⟨.defs [natDecl] .nil (.succeed (.lit .unit)), []⟩
#guard mismatch.check app = .error ⟨[], .definitionsMismatch 1 0⟩
#guard mismatch.refusals app = [⟨[], .definitionsMismatch 1 0⟩]
def badDecl : DefDecl := { natDecl with request := .var 0 }
def malformed : Sketch := ⟨.defs [badDecl] (.cons (.succeed (.lit (.nat 1))) .nil)
  (.succeed (.lit .unit)), []⟩
#guard malformed.check app = .error ⟨[0, 0], .definitionColumns "idNat"⟩
#guard (malformed.refusals app).head? = Checker.refusal (malformed.check app)

-- A nested block is refused and its children receive no focus.
def nested : Sketch := ⟨.suspend block, []⟩
#guard nested.check app = .error ⟨[0], .definitionBlock⟩
#guard (nested.focusAt app [0]).isNone
#guard (nested.focusAt app [0, 1]).isNone
#guard !(nested.refusals app).isEmpty

-- Root scope: ordinary fillings and omission keep the module type.
#guard (sketch.fillAt [] (.succeed (.lit (.nat 9)))).map (·.check app) = some (.ok natTy)
#guard (sketch.omitAt app [] (Row.hole "root" .nat)).map (·.check app) = some (.ok natTy)
-- A whole-block root filling is legal data, but lies outside the structural-check premise.
#guard (sketch.fillAt [] block).map (·.check app) = some (.ok natTy)
#guard (Checker.check (sketch.sigAt app []) [] [] block).toOption.isNone

-- Entry paths use whole-program addresses, not addresses relative to a body.
#guard sketch.tableEntry app [0, 1, 0] = ⟨[0, 1, 0], some (.env [.bool]), some (.ok boolTy)⟩
#guard sketch.tableEntry app [0, 1] = ⟨[0, 1], none, none⟩
#guard sketch.refusals app = []
example : sketch.refusals app = [] ↔ (sketch.check app).toOption.isSome = true :=
  Sketch.refusals_nil_iff sketch app
example : mismatch.refusals app = [] ↔ (mismatch.check app).toOption.isSome = true :=
  Sketch.refusals_nil_iff mismatch app

-- Off a block: finite entrywise equality with the pre-existing structural table.
def plain : NativeEff := .bind (.succeed (.lit (.nat 1))) (.succeed (.var 0))
#guard (Sketch.table (plain : Sketch) app) = table app.signature [] plain
#guard (Sketch.table (nested : Sketch) app) = table app.signature [] nested.program

end S1SketchReview
