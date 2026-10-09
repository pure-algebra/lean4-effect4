import Tools.Session

/-! Finite controls for the c4b6b795 MCP design, verified at 28ed6727. These exercise existing interfaces.
No declaration here states a new law or changes a production contract. -/

open Lean (Json toJson)
open Effect4.Program

namespace McpSupport

def value (n : Nat) : NativeEff := .succeed (.lit (.nat n))

def start : EditSession := EditSession.open {} { program := value 1 }

def changed : EditSession × Edit.Step := start.feedStep (.fill [] (value 2))

def warm : Tools.Session.State :=
  { session := some changed.1, journal := [changed.2] }

def cold : Tools.Session.State :=
  { session := some (EditSession.open {} changed.1.sketch) }

def appNat : SigApp := { rows := [Row.hole "same" .nat] }
def appBool : SigApp := { rows := [Row.hole "same" .bool] }
def externalSketch : Sketch := { program := .perform (.external 0) (.lit .unit) }

def row (name : String) (actual expected : Json) : String × Json × Json :=
  (name, actual, expected)

def admitted (s : Sketch) : Bool := (s.check {}).toOption.isSome

def pairStart : EditSession := EditSession.open {}
  { program := .bind (value 1) (.succeed (.var 0)) }
def changeInput : Edit := .fill [0] (.succeed (.lit (.str "text")))
def incrementResult : Edit := .fill [1] (.succeed (.app "succ" (.cons (.var 0) .nil)))
def keepInputType : Edit := .fill [0] (value 9)
def omitA : Edit := .omitAt [0] (Row.hole "ha" .nat)
def omitB : Edit := .omitAt [1] (Row.hole "hb" .nat)
def omissionsAB : EditSession := pairStart.run [omitA, omitB]
def omissionsBA : EditSession := pairStart.run [omitB, omitA]
def duplicateNames : EditSession := pairStart.run
  [.omitAt [0] (Row.hole "h0" .nat), .omitAt [1] (Row.hole "h0" .nat)]

def checks : List (String × Json × Json) :=
  let bad : Edit := .fill [999] (value 3)
  let before := (start.feed (.fill [] (value 2))).1
  let after := start.run [.fill [] (value 2), bad, .fill [] (value 4)]
  let natSession := EditSession.open appNat externalSketch
  let boolSession := EditSession.open appBool externalSketch
  [ row "same-sketch-same-context-same-view"
      (toJson (Tools.Session.viewJson changed.1 ==
        Tools.Session.viewJson (EditSession.open {} changed.1.sketch))) (toJson true),
    row "warm-undo-has-history" (toJson (Tools.Session.answer warm { op := "undo" }).2.ok)
      (toJson true),
    row "cold-undo-has-no-history" (toJson (Tools.Session.answer cold { op := "undo" }).2.ok)
      (toJson false),
    row "same-sketch-journals-differ"
      (toJson ((Tools.Session.answer warm { op := "journal" }).2.result ==
        (Tools.Session.answer cold { op := "journal" }).2.result)) (toJson false),
    row "both-application-signatures-admitted"
      (toJson ((admitSig appNat).toOption.isSome && (admitSig appBool).toOption.isSome)) (toJson true),
    row "same-program-different-signature-answer"
      (toJson [natSession.view.type.map (·.answer) == some .nat,
        boolSession.view.type.map (·.answer) == some .bool]) (toJson [true, true]),
    row "invalid-address-is-unchanged" (toJson ((before.feed bad).2 == .unchanged)) (toJson true),
    row "raw-fold-continues-after-invalid-address"
      (toJson (after.sketch.program == value 4)) (toJson true),
    row "raw-fold-keeps-prior-change-before-invalid-address"
      (toJson ((before.feed bad).1.sketch.program == value 2)) (toJson true),
    row "empty-word-keeps-program" (toJson ((start.run []).sketch.program == start.sketch.program))
      (toJson true),
    row "split-word-agrees-for-program"
      (toJson ((start.run [.fill [] (value 2), .fill [] (value 4)]).sketch.program ==
        ((start.run [.fill [] (value 2)]).run [.fill [] (value 4)]).sketch.program)) (toJson true),
    row "disjoint-edits-each-admitted-at-base"
      (toJson [admitted pairStart.sketch,
        admitted (pairStart.run [changeInput]).sketch,
        admitted (pairStart.run [incrementResult]).sketch]) (toJson [true, true, true]),
    row "disjoint-edits-combined-refused"
      (toJson (admitted (pairStart.run [changeInput, incrementResult]).sketch)) (toJson false),
    row "disjoint-edits-syntax-commutes"
      (toJson ((pairStart.run [changeInput, incrementResult]).sketch.program ==
        (pairStart.run [incrementResult, changeInput]).sketch.program)) (toJson true),
    row "type-preserving-disjoint-edits-combine"
      (toJson (admitted (pairStart.run [keepInputType, incrementResult]).sketch)) (toJson true),
    row "opposite-omissions-both-admitted"
      (toJson [admitted omissionsAB.sketch, admitted omissionsBA.sketch]) (toJson [true, true]),
    row "opposite-omissions-append-opposite-orders"
      (toJson [omissionsAB.sketch.holes.map (·.name), omissionsBA.sketch.holes.map (·.name)])
      (toJson [["ha", "hb"], ["hb", "ha"]]),
    row "opposite-omissions-have-different-programs"
      (toJson (omissionsAB.sketch.program == omissionsBA.sketch.program)) (toJson false),
    row "duplicate-labels-remain-two-distinct-rows"
      (toJson (duplicateNames.sketch.holes.map (·.name))) (toJson ["h0", "h0"]),
    row "duplicate-labels-program-uses-each-row-once"
      (toJson (duplicateNames.sketch.program == .bind (Sketch.hole {} 0) (Sketch.hole {} 1)))
      (toJson true) ]

end McpSupport

def main : IO Unit := do
  let checks := McpSupport.checks
  let rows := checks.map fun (name, actual, expected) =>
    Json.mkObj [("name", .str name), ("actual", actual), ("expected", expected),
      ("pass", .bool (actual == expected))]
  IO.println (Json.arr rows.toArray).compress
  unless checks.all (fun (_, actual, expected) => actual == expected) do
    throw (IO.userError "MCP session control failed")
