import Tools.View.GraphContent
import Tools.View.FlowSpecimen
import Tools.View.GraphBounds
import Tools.View.GraphCheck
import Tools.View.SvgOut
import Tools.View.Tokens

/-! Real program content projected into three graph-label treatments.
The source graph shows structural constraints, never recorded execution state.
SVG output passes the existing content and XML checks. -/

open Tools.View Effect4 Effect4.Program Lean

deriving instance Repr for GraphCheck.Site
deriving instance Repr for GraphCheck.Field
deriving instance Repr for GraphCheck.Reason
deriving instance Repr for GraphCheck.Refusal

namespace GraphLeafStudy

def programs : List (String × String × NativeEff) :=
  (FlowSpecimen.programs.zipIdx.filterMap fun (p, i) =>
    if [0, 8, 9, 12, 13, 14].contains i then some p else none) ++
  [("reference operations", "Declared operation rows name the Ref operations; arguments remain source expressions.",
    .bind (.perform .refMake (.lit (.nat 7))) (.perform .refGet (.var 0))),
   ("long operand expression", "Long operands remain fully available in the selected leaf's details.",
    .succeed (.lit (.str "A long source value with <markup> & punctuation, retained without interpreting it.")))]

/-- Inspector text retains absent optional arguments that the compact source printer omits. -/
def inspectorArg : GraphContent.Argument → Option String
  | .optTy none => some "none"
  | .optTerm none => some "none"
  | a => Program.argText a

def args (e : GraphContent.Entry) : List String := e.node.arguments.filterMap inspectorArg

/-- Names of source argument sorts, without inventing constructor-specific parameter names. -/
def argKind : GraphContent.Argument → String
  | .child .. => "child"
  | .term .. => "term"
  | .cause .. => "cause term"
  | .op .. => "operation"
  | .nat .. => "natural number"
  | .mode .. => "observer mode"
  | .bool .. => "Boolean"
  | .key .. => "service key"
  | .decision .. => "decision"
  | .optTy .. => "optional type"
  | .decls .. => "declarations"
  | .forkOptions .. => "fork options"
  | .optTerm .. => "optional term"
  | .keys .. => "service keys"
  | .lit .. => "literal"
  | .path .. => "source path"

def title (e : GraphContent.Entry) : String :=
  ((e.operation.bind (·.row)).map (·.spelling)).getD e.node.ctor

def requiresText (t : EffTy) : String :=
  if t.requires.elems.isEmpty then "∅" else " ".intercalate (t.requires.elems.map keyText)

def typeText (e : GraphContent.Entry) : String :=
  match e.typing.bind (·.result) with
  | some (.ok t) => "A " ++ t.answer.render ++ " · E " ++ t.error.render ++ " · R " ++ requiresText t
  | some (.error _) => "typing refused"
  | none => "type unavailable"

def typingStatus (e : GraphContent.Entry) : String :=
  match e.typing.bind (·.result) with
  | some (.ok _) => "Checked type at this source address"
  | some (.error r) => "Checker refusal at " ++ Program.bracket r.path
  | none => "No typing observation at this address"

def entryJson (e : GraphContent.Entry) : Lean.Json :=
  let t := (e.typing.bind (·.result)).bind fun r => match r with | .ok t => some t | .error _ => none
  let refusal := match e.typing.bind (·.result) with
    | some (.error r) => some (Program.bracket r.path ++ ": " ++ Program.reasonText r)
    | _ => none
  Lean.Json.mkObj [("key", toJson e.node.key), ("ctor", toJson (title e)),
    ("constructor", toJson e.node.ctor), ("args", toJson (args e)),
    ("argKinds", toJson (e.node.arguments.filterMap fun a => (inspectorArg a).map fun _ => argKind a)),
    ("source", toJson (Program.ownText e.node.ctor e.node.arguments)),
    ("typeText", toJson e.typeText), ("typeStatus", toJson (typingStatus e)),
    ("answer", toJson (t.map fun t => t.answer.render)),
    ("error", toJson (t.map fun t => t.error.render)),
    ("requires", toJson (t.map requiresText)), ("refusal", toJson refusal)]

def labels (mode : String) (e : GraphContent.Entry) : String × String :=
  let detailArgs := e.node.arguments.filterMap fun a =>
    match a with
    | .op _ => if (e.operation.bind (·.row)).isSome then none else Program.argText a
    | _ => Program.argText a
  (title e, if mode == "types" then typeText e else " ".intercalate detailArgs)

def writeMode (out : System.FilePath) (L : Look) (i : Nat) (name description : String)
    (p : NativeEff) (page : Page) (entries : List GraphContent.Entry) (mode : String) : IO Lean.Json := do
  let table := KeyMap.firstBy (fun e : GraphContent.Entry => e.node.key) entries
  let laid := if mode == "source" then Flow.ofPage p page
    else Flow.layout ((Flow.ofProgram p).relabel fun k => (table.get? k).map (labels mode))
  match GraphCheck.laid laid with
  | .error why => throw (IO.userError (reprStr why))
  | .ok _ => pure ()
  let style : GraphText.Style := if mode == "source" then {} else { first := some .name }
  let raw := laid.calls L 0 0 style
  let viewport := GraphBounds.viewport laid raw 18
  let width := viewport.size.1.toNat
  let height := viewport.size.2.toNat
  let calls := (⟨"", .fill .ground 1000 0 0 width height⟩ : Keyed Call) :: viewport.calls raw
  let svg := Whatwg.Html.Svg.Frame.titled { width, height, ratio := 1 }
    s!"leaf-{i}-{mode}" (name ++ " · " ++ mode)
    [.className "e4-view", .data "look" L.name]
    (SvgOut.marksOf L 1 (lowerAll 1 calls)) (some (description ++ " Static program structure."))
  let file := s!"{i}-{mode}.svg"
  match SvgOut.fileText svg with
  | .error why => throw (IO.userError why)
  | .ok text => IO.FS.writeFile (out / file) text
  let nodes := laid.placed.toList.filterMap fun p => p.node.map fun _ =>
    Lean.Json.mkObj [("key", toJson p.key), ("bounds", toJson
      ([p.x + viewport.shift.1, p.y + viewport.shift.2,
        p.x + p.w + viewport.shift.1, p.y + ROWH * BOXROWS + viewport.shift.2] : List Int))]
  return Lean.Json.mkObj [("file", toJson file), ("width", toJson width), ("height", toJson height), ("nodes", toJson nodes)]

end GraphLeafStudy

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "tools/view/out/graph-leaves"
  IO.FS.createDirAll out
  let base : Look := {}
  let L := { base with faces := { base.faces with name := { base.faces.data with weight := 650 } } }
  let paper ← Tokens.lookFile "paper"
  IO.FS.writeFile (out / "look.css") (Tokens.css L ++ Tokens.css paper ++ Tokens.rules)
  let mut cases : Array Lean.Json := #[]
  for ((name, description, p), i) in GraphLeafStudy.programs.zipIdx do
    let session := EditSession.open {} { program := p }
    let page := Program.sessionPage session none name description "" ""
    let entries := GraphContent.ofSessionPage session page
    let source := Flow.ofPage p page
    let visible := entries.filter fun e => source.placed.any fun p => p.key == e.node.key && p.node.isSome
    let mut modes : List (String × Lean.Json) := []
    for mode in ["source", "arguments", "types"] do
      modes := modes ++ [(mode, ← GraphLeafStudy.writeMode out L i name description p page entries mode)]
    cases := cases.push (Lean.Json.mkObj [("name", toJson name), ("description", toJson description),
      ("nodes", toJson (visible.map GraphLeafStudy.entryJson)), ("modes", Lean.Json.mkObj modes)])
    IO.println s!"leaf-study,{i},{visible.length},3"
  IO.FS.writeFile (out / "manifest.json") (Lean.Json.mkObj [("cases", toJson cases)]).pretty
