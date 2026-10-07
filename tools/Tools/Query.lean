import Effect4.Program.Sketch
import Effect4.Program.Typing.Table
import Effect4.Store.Domain.ProgramWire
import Effect4.Store.Carrier.Digest
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Program.Typing.Table
import Lean.Data.Json
import Tools.ProfileJson

/-!
# Tools.Query — one function that answers a request about a program (slice QUERY)

**What it is.** `answer` reads one request and gives one answer. A request names an operation
and carries a program as its canonical bytes in lowercase hex (`decodeProgram`,
`src/Effect4/Store/Domain/ProgramWire.lean`). Each operation is one library function. The
driver `tools/Drivers/Query.lean` reads one JSON object for each line of standard input and
prints one answer for each: it is `answerLine` and nothing more.

| Operation | Function | The law that an answer names |
| --- | --- | --- |
| `check` | `Sketch.check` | `Sketch.check_program` |
| `addresses` | `Node.addresses` | `mem_addresses_iff` |
| `focus` | `Sketch.focusAt` | `focusAt_typed`, where the focus is answered |
| `table` | `Sketch.table` | `mem_addresses_iff`, `table_head` |
| `refusals` | `Sketch.refusals` | `refusals_head`, `refusals_nil_iff` |
| `slots` | `Node.extSlotTerm`, `Node.extSlotEnv` | `hasTy_extSlotEnv`, where the node is typed and has a slot |
| `omit` | `Sketch.omitAt` | `Sketch.check_omit_focusAt`, where its premises hold |
| `fill` | `Sketch.fillAt` | `Sketch.check_fill_focusAt`, where its premises hold |

**A named law is a claim.** An answer names a law only where this function has decided the
law's premises (`omitPremises`, `fillPremises`, and a typed focus at `slots`). Elsewhere the
answer is a computed check, and it names no law. The names are checked when this file is
compiled: each is a name literal that must resolve.

**The application is the empty one**, and each answer says so. A request carries no hole table.
So the program that `omit` answers performs a hole row that its bytes do not carry: it cannot be
sent back as a request, and the answer says so (`needsHoleTable`). A sketch has no canonical
codec yet.

**What it is not.** It is no server, it stores no session, and it adds no theorem. A term is
answered as its canonical bytes, and a type in the JSON view of `Tools.ProfileJson`.
-/

open Lean (Json ToJson toJson fromJson?)
open Effect4.Program Effect4.Program.Wire Effect4.Store

namespace Tools.Query

/-! ## The term slots -/

/-- The name of a term slot on the wire. A new slot fails this match: add it to `allSlots`
too. -/
def slotName : ExtSlot → String
  | .catchIfTest => "catchIfTest"
  | .iterateTest => "iterateTest"
  | .iterateStep => "iterateStep"
  | .iterateResult => "iterateResult"
  | .opTerm => "opTerm"

/-- Every term slot, in the order of an answer. -/
def allSlots : List ExtSlot := [.catchIfTest, .iterateTest, .iterateStep, .iterateResult, .opTerm]

/-- The slot of a name, read from the one table. -/
def slotOfName? (name : String) : Option ExtSlot := allSlots.find? fun slot => slotName slot == name

/-! ## The request -/

/-- One request. -/
structure Request where
  /-- The operation: `check`, `addresses`, `focus`, `table`, `refusals`, `slots`, `omit` or
  `fill`. -/
  op : String
  /-- The canonical bytes of the program, in lowercase hex. -/
  program : String
  /-- An address: the child indices from the root. -/
  path : List Nat := []
  /-- One slot, for `slots`. With none, every slot of the node is answered. -/
  slot : Option ExtSlot := none
  /-- The name of the hole row, for `omit`. -/
  holeName : String := "h0"
  /-- The canonical bytes of the filling, in lowercase hex, for `fill`. -/
  replacement : Option String := none
  /-- A value that the answer returns unchanged. -/
  id : Option Json := none
  deriving Inhabited

/-- An optional field of a request. An absent field and `null` are no value. A field of another
type is an error that names the field: the reader reads an input, or it refuses it. -/
def optField {α : Type} (j : Json) (name : String) (read : Json → Except String α) :
    Except String (Option α) :=
  match j.getObjVal? name with
  | .error _ => .ok none
  | .ok .null => .ok none
  | .ok value =>
    match read value with
    | .ok a => .ok (some a)
    | .error why => .error s!"field {name}: {why}"

/-- Read a request. It refuses a missing operation or program, a field of the wrong type, and a
slot name that is no slot. -/
def Request.fromJson? (j : Json) : Except String Request := do
  let op ← j.getObjValAs? String "op"
  let program ← j.getObjValAs? String "program"
  let path ← optField j "path" (Lean.fromJson? (α := List Nat))
  let slot ← optField j "slot" fun value => do
    let name ← Lean.fromJson? (α := String) value
    match slotOfName? name with
    | some slot => pure slot
    | none => throw s!"unknown slot {name}"
  let holeName ← optField j "holeName" (Lean.fromJson? (α := String))
  let replacement ← optField j "replacement" (Lean.fromJson? (α := String))
  let id := (j.getObjVal? "id").toOption
  return { op, program, path := path.getD [], slot, holeName := holeName.getD "h0", replacement, id }

/-- The reader's reason, where it refuses the value. A battery asks this function, so that its
guard holds no `match` on a type that holds JSON: such a matcher is a declaration of the battery,
and the axiom gate refuses it. -/
def Request.refusal? (j : Json) : Option String :=
  match Request.fromJson? j with
  | .error why => some why
  | .ok _ => none

/-- Write a request, as `Request.fromJson?` reads it. -/
def Request.toJson (r : Request) : Json :=
  Json.mkObj <|
    [("op", .str r.op), ("program", .str r.program), ("path", Lean.toJson r.path),
      ("holeName", .str r.holeName)] ++
    (r.slot.map fun slot => ("slot", Json.str (slotName slot))).toList ++
    (r.replacement.map fun hex => ("replacement", Json.str hex)).toList ++
    (r.id.map fun id => ("id", id)).toList

/-- The request of an operation at a program and an address. -/
def ask (op : String) (program : NativeEff) (path : List Nat := []) : Request :=
  { op, program := hexOf program, path }

/-! ## The answer -/

/-- One answer. -/
structure Answer where
  /-- The operation of the request. -/
  op : String
  /-- The application that the program was read at: the empty one. -/
  app : String := "empty"
  /-- The laws that the answer stands on, each with its premises decided here. -/
  laws : List Lean.Name := []
  /-- The request was read and the operation ran. A refusal of the checker is an answer: it
  stands in `result`, and `ok` is true. -/
  ok : Bool
  /-- What the operation answers. -/
  result : Json := .null
  /-- Why the request has no answer, where `ok` is false. -/
  error : Option String := none
  /-- The request's `id`, unchanged. -/
  id : Option Json := none
  deriving Inhabited

/-- Write an answer. -/
def Answer.toJson (a : Answer) : Json :=
  Json.mkObj <|
    [("op", .str a.op), ("app", .str a.app),
      ("laws", Json.arr (a.laws.map fun name => Json.str name.toString).toArray),
      ("ok", .bool a.ok)] ++
    (if a.result.isNull then [] else [("result", a.result)]) ++
    (a.error.map fun why => ("error", Json.str why)).toList ++
    (a.id.map fun id => ("id", id)).toList

instance : ToJson Answer := ⟨Answer.toJson⟩

/-- A request with no answer. -/
def refused (op why : String) (id : Option Json := none) : Answer :=
  { op, ok := false, error := some why, id }

/-! ## The JSON views -/

/-- A list of types. -/
def tysJson (tys : List Ty) : Json := Json.arr (tys.map Tools.ProfileJson.tyJson).toArray

/-- A program's type: its answer, its error and its requirement, key by key
(`Tools.ProfileJson.keyJson`). -/
def effTyJson (t : EffTy) : Json :=
  Json.mkObj [("answer", Tools.ProfileJson.tyJson t.answer),
    ("error", Tools.ProfileJson.tyJson t.error),
    ("requires", Json.arr (t.requires.elems.map Tools.ProfileJson.keyJson).toArray)]

/-- A refusal: its address and the name of its reason. -/
def refusalJson (r : TypeRefusal) : Json :=
  Json.mkObj [("path", toJson r.path), ("reason", .str r.reason.head)]

/-- The checker's answer: a type or a refusal. -/
def checkJson : Except TypeRefusal EffTy → Json
  | .ok t => Json.mkObj [("status", .str "ok"), ("type", effTyJson t)]
  | .error r => Json.mkObj [("status", .str "refused"), ("refusal", refusalJson r)]

/-- The environment of a node. An entry that is not reached has none. -/
def nodeEnvJson : Option NodeEnv → Json
  | none => .null
  | some (.env tys) => Json.mkObj [("kind", .str "env"), ("tys", tysJson tys)]
  | some (.body tys loop) =>
    Json.mkObj [("kind", .str "body"), ("tys", tysJson tys), ("loop", .bool loop)]
  | some .closed => Json.mkObj [("kind", .str "closed")]

/-- One entry of the address table. An address of no program has no result. -/
def entryJson (e : Table.Entry) : Json :=
  Json.mkObj [("path", toJson e.path), ("env", nodeEnvJson e.env),
    ("result", match e.result with
      | none => .null
      | some result => checkJson result)]

/-- The focus at an address, or that the function answers none there. -/
def focusJson : Option (Focus NativeOp) → Json
  | none => Json.mkObj [("found", .bool false)]
  | some focus =>
    Json.mkObj [("found", .bool true), ("env", tysJson focus.env), ("type", effTyJson focus.ty),
      ("program", .str (hexOf focus.program))]

/-- A term as its canonical bytes, in lowercase hex. -/
def termHex (t : Term) : String := hexString (Canonical.encode t)

/-- One slot of a node: its term, the environment of the term, and the term's type there. -/
def slotJson (slot : ExtSlot) (term : Option Term) (env : Option TyEnv) (ty : Option Ty) : Json :=
  Json.mkObj [("slot", .str (slotName slot)),
    ("term", match term with
      | some t => .str (termHex t)
      | none => .null),
    ("env", match env with
      | some tys => tysJson tys
      | none => .null),
    ("termTy", match ty with
      | some t => Tools.ProfileJson.tyJson t
      | none => .null)]

/-! ## The premises of the two edit laws, decided -/

/-- The hole row that declares a focus's type. -/
def holeRow (name : String) (focus : Focus NativeOp) : Row :=
  Row.hole name focus.ty.answer focus.ty.error focus.ty.requires.elems

/-- The premises of `Sketch.check_omit_focusAt` at an answered focus: the checker admits the
sketch, the focus's answer and error are closed and in normal form, and the hole row's columns
are formed. -/
def omitPremises (sketch : Sketch) (name : String) (focus : Focus NativeOp) : Bool :=
  (sketch.check {}).toOption.isSome &&
    focus.ty.answer.closed && focus.ty.error.closed &&
    decide (focus.ty.answer.normalize = focus.ty.answer) &&
    decide (focus.ty.error.normalize = focus.ty.error) &&
    (Formation.check (Formation.instantiatedSites (holeRow name focus).normalizeTypes [])).isNone

/-- The premises of `Sketch.check_fill_focusAt` at an answered focus: the checker admits the
sketch, and it admits the filling at the focus's type in the focus's environment. -/
def fillPremises (sketch : Sketch) (focus : Focus NativeOp) (filling : NativeEff) : Bool :=
  (sketch.check {}).toOption.isSome &&
    effTy (({} : SigApp).withHoles sketch.holes).signature focus.env filling == some focus.ty

/-! ## The operations -/

/-- The slots of the node at an address of a program. The environment of the node is the
table's (`Node.envAt`). A node that is no program, and a node in a generator body, has no
slot. -/
def slotsAt (program : NativeEff) (path : List Nat) (slots : List ExtSlot) : List Json :=
  let sig : Signature NativeOp := ({} : SigApp).signature
  match (Node.eff program).at_ path, (Node.eff program).envAt sig (.env []) path with
  | some node, some (.env env) =>
    slots.filterMap fun slot =>
      let term := node.extSlotTerm sig slot
      let slotEnv := node.extSlotEnv sig env slot
      if term.isSome || slotEnv.isSome then
        some (slotJson slot term slotEnv (term.bind fun t => slotEnv.bind fun e => termTy sig e t))
      else none
  | _, _ => []

/-- **Answer one request.** -/
def answer (req : Request) : Answer :=
  match (bytesOfHex req.program.toList).bind decodeProgram with
  | none => refused req.op "the program's bytes do not decode" req.id
  | some program =>
    let sketch : Sketch := program
    let done (laws : List Lean.Name) (result : Json) : Answer :=
      { op := req.op, laws, ok := true, result, id := req.id }
    match req.op with
    | "check" => done [``Sketch.check_program] (checkJson (sketch.check {}))
    | "addresses" => done [``mem_addresses_iff] (toJson (Node.addresses (.eff program)))
    | "focus" =>
      let focus := sketch.focusAt {} req.path
      done (if focus.isSome then [``focusAt_typed] else []) (focusJson focus)
    | "table" =>
      done [``mem_addresses_iff, ``table_head]
        (Json.arr ((sketch.table {}).map entryJson).toArray)
    | "refusals" =>
      done [``refusals_head, ``refusals_nil_iff]
        (Json.arr ((sketch.refusals {}).map refusalJson).toArray)
    | "slots" =>
      let slots := slotsAt program req.path (req.slot.map ([·]) |>.getD allSlots)
      let typed := (sketch.focusAt {} req.path).isSome
      done (if typed && !slots.isEmpty then [``hasTy_extSlotEnv] else []) (Json.arr slots.toArray)
    | "omit" =>
      match sketch.focusAt {} req.path with
      | none => refused req.op "no focus at the address" req.id
      | some focus =>
        match sketch.omitAt {} req.path (holeRow req.holeName focus) with
        | none => refused req.op "no omission at the address" req.id
        | some omitted =>
          done (if omitPremises sketch req.holeName focus then [``Sketch.check_omit_focusAt]
            else [])
            (Json.mkObj [("program", .str (hexOf omitted.program)),
              ("holes", toJson omitted.holes.length), ("needsHoleTable", .bool true),
              ("check", checkJson (omitted.check {}))])
    | "fill" =>
      match req.replacement.bind fun hex => (bytesOfHex hex.toList).bind decodeProgram with
      | none => refused req.op "the filling's bytes do not decode" req.id
      | some filling =>
        match sketch.fillAt req.path filling with
        | none => refused req.op "no filling at the address" req.id
        | some filled =>
          let matched := match sketch.focusAt {} req.path with
            | some focus => fillPremises sketch focus filling
            | none => false
          done (if matched then [``Sketch.check_fill_focusAt] else [])
            (Json.mkObj [("program", .str (hexOf filled.program)),
              ("matchedFocus", .bool matched), ("check", checkJson (filled.check {}))])
    | other => refused other s!"unknown operation {other}" req.id

/-! ## The driver's one function, and the replay of a transcript -/

/-- **Answer one line**: a JSON object that is a request, or an answer that says why it is
none. The driver prints this for each line of its input. -/
def answerLine (line : String) : String :=
  match Json.parse line with
  | .error why => (toJson (refused "parse" s!"no JSON: {why}")).compress
  | .ok j =>
    match Request.fromJson? j with
    | .error why => (toJson (refused "request" why)).compress
    | .ok req => (toJson (answer req)).compress

/-- The lines of a fixture that hold text. -/
def fixtureLines (text : String) : List String :=
  (text.splitOn "\n").filter fun line => !line.isEmpty

/-- **A transcript replays**: the answer of each recorded request is the recorded answer, line
by line. -/
def replays (requests answers : String) : Bool :=
  let asked := fixtureLines requests
  let recorded := fixtureLines answers
  asked.length == recorded.length &&
    (asked.zip recorded).all fun pair => answerLine pair.1 == pair.2

end Tools.Query
