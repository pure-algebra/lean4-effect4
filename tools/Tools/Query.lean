import Effect4.Laws.Program.CheckAgreement
import Effect4.Program.Sketch
import Effect4.Program.SketchWire
import Effect4.Program.Typing.Table
import Effect4.Store.Domain.ProgramWire
import Effect4.Store.Carrier.Digest
import Effect4.Laws.Program.Sketch
import Effect4.Laws.Program.Typing.Table
import Lean.Data.Json
import Tools.JsonBridge
import Effect4.Api.RefusalsDerived

/-!
# Tools.Query — one function that answers a request about a program (slice QUERY)

**What it is.** `answer` reads one request and gives one answer. A request names an operation
and carries a program as its canonical bytes in lowercase hex (`decodeProgram`,
`src/Effect4/Store/Domain/ProgramWire.lean`). Each operation is one library function. The
driver `tools/Drivers/Query.lean` reads one JSON object for each line of standard input and
prints one answer for each: it is `answerLine` and nothing more.

| Operation | Function | The law that an answer names |
| --- | --- | --- |
| `check` | `Check.run` | `Check.run_module` |
| `addresses` | `Node.addresses` | `mem_addresses_iff` |
| `focus` | `Sketch.focusAt` | at the root, `Sketch.focusAt_nil` and `checkModule_sound`; elsewhere `focusAt_typed`, at the part that holds the address; where the focus is answered |
| `table` | `Sketch.table` | `mem_addresses_iff`, `Sketch.table_head` |
| `refusals` | `Sketch.refusals` | `Sketch.refusals_head`, `Sketch.refusals_nil_iff` |
| `slots` | `Node.extSlotTerm`, `Node.extSlotEnv`, in the part that holds the address | `hasTy_extSlotEnv`, where the part's focus is typed and the node has a slot |
| `omit` | `Sketch.omitAt` | `Sketch.check_omit_focusAt`, where its premises hold |
| `fill` | `Sketch.fillAt` | `Sketch.check_fill_focusAt`, where its premises hold |

**A named law is a claim.** An answer names a law only where this function has decided the
law's premises (`omitPremises`, `fillPremises`, and a typed focus at `slots`). Elsewhere the
answer is a computed check, and it names no law. The names are checked when this file is
compiled: each is a name literal that must resolve. The two deciders are sound
(`fillPremises_sound`, `omitPremises_sound`): where one answers `true`, the edit applies and the
sketch keeps its type, so a `fill` or `omit` answer that names its law is a theorem's instance.

**The application is the empty one**, and each answer says so. A request may carry the sketch's
hole table (`holes`, the bytes of `Wire.encodeHoles`). The program that `omit` answers performs a
hole row that its own bytes do not carry, so the answer says so (`needsHoleTable`) and carries the
grown hole table (`holeTable`): the program and the hole table, sent back together, are the
sketch (`Sketch.decode_exact`, `Program/SketchWire.lean`).

**What it is not.** It is no server, it stores no session, and it adds no theorem. A term is
answered as its canonical bytes, and a type, a refusal or a term's type as its JSON print
(`Tools.JsonBridge.printJson`), the encoding a program's JSON uses.
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
  /-- The canonical bytes of the sketch's hole table, in lowercase hex (`Wire.encodeHoles`). With
  none, the hole table is empty. -/
  holes : Option String := none
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
  let holes ← optField j "holes" (Lean.fromJson? (α := String))
  let id := (j.getObjVal? "id").toOption
  return Request.mk op program (path.getD []) slot (holeName.getD "h0") replacement holes id

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
    (r.holes.map fun hex => ("holes", Json.str hex)).toList ++
    (r.id.map fun id => ("id", id)).toList

/-- The request of an operation at a program and an address. -/
def ask (op : String) (program : NativeEff) (path : List Nat := []) : Request :=
  { op, program := hexOf program, path }

/-! ## The answer -/

/-- One answer. -/
structure Answer where
  /-- The operation of the request. -/
  op : String
  /-- The application that the program was read at: `empty`, or `sha256:` and the digest of the
  application's bytes (the session tool's `open` with `rows` and `services`). -/
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

open Tools.JsonBridge (printJson ofHex? toHex)

/-- A program's type: its answer, its error and its requirement, as a program's JSON spells
them. -/
def effTyJson (t : EffTy) : Json := printJson t

/-- A refusal: its address, the name of its reason, and the whole refusal as its generated
canonical print (`detail`, `Tools.JsonBridge.printJson`), so a reason's own fields reach the
author: a reference's target and the condition it breaks, among them. When `root` is a definition
block, it also names the enclosing `definition` and any invoked `parameter` (`Eff.defAt`,
`Eff.paramAt`). -/
def refusalJson (r : TypeRefusal) (root : Option (Eff NativeOp) := none)
    (sig : Signature NativeOp := nativeSignature []) : Json :=
  Json.mkObj <|
    [("path", toJson r.path)] ++
    (match root.bind (·.defAt r.path) with
      | some d => [("definition", .str d)]
      | none => []) ++
    (match root.bind (·.paramAt sig r.path) with
      | some (callee, name) =>
        [("parameter", Json.mkObj [("callee", .str callee), ("name", .str name)])]
      | none => []) ++
    [("reason", .str (Canonical.head r.reason)), ("detail", printJson r)]

/-- The checker's answer: a type or a refusal. -/
def checkJson (res : Except TypeRefusal EffTy) (root : Option (Eff NativeOp) := none)
    (sig : Signature NativeOp := nativeSignature []) : Json :=
  match res with
  | .ok t => Json.mkObj [("status", .str "ok"), ("type", effTyJson t)]
  | .error r => Json.mkObj [("status", .str "refused"), ("refusal", refusalJson r root sig)]

/-- The environment of a node. An entry that is not reached has none. -/
def nodeEnvJson : Option NodeEnv → Json
  | none => .null
  | some (.env tys) => Json.mkObj [("kind", .str "env"), ("tys", printJson tys)]
  | some (.body tys loop) =>
    Json.mkObj [("kind", .str "body"), ("tys", printJson tys), ("loop", .bool loop)]
  | some .closed => Json.mkObj [("kind", .str "closed")]
  | some (.slots tys params) =>
    Json.mkObj [("kind", .str "slots"), ("tys", printJson tys),
      ("params", toJson (params.map (·.name))), ("requests", printJson (params.map (·.request)))]

/-- One entry of the address table. An address of no program has no result. -/
def entryJson (e : Table.Entry) (root : Option (Eff NativeOp) := none)
    (sig : Signature NativeOp := nativeSignature []) : Json :=
  Json.mkObj [("path", toJson e.path), ("env", nodeEnvJson e.env),
    ("result", match e.result with
      | none => .null
      | some result => checkJson result root sig)]

/-- The focus at an address, or that the function answers none there. -/
def focusJson (focus : Option (Focus NativeOp)) (hex : Bool := true) : Json :=
  match focus with
  | none => Json.mkObj [("found", .bool false)]
  | some focus =>
    Json.mkObj ([("found", .bool true), ("env", printJson focus.env), ("type", effTyJson focus.ty)] ++
      (if hex then [("program", .str (hexOf focus.program))] else []) ++
      [("programJson", printJson focus.program)])

/-- One slot of a node: its term, the environment of the term, and the term's type there. -/
def slotJson (slot : ExtSlot) (term : Option Term) (env : Option TyEnv) (ty : Option Ty) : Json :=
  Json.mkObj [("slot", .str (slotName slot)),
    ("term", match term with
      | some t => .str (toHex t)
      | none => .null),
    ("termJson", match term with
      | some t => printJson t
      | none => .null),
    ("env", match env with
      | some tys => printJson tys
      | none => .null),
    ("termTy", match ty with
      | some t => printJson t
      | none => .null)]

/-! ## The premises of the two edit laws, decided -/

/-- The hole row that declares a focus's type. -/
def holeRow (name : String) (focus : Focus NativeOp) : Row :=
  Row.hole name focus.ty.answer focus.ty.error focus.ty.requires.elems

/-- The premises of `Sketch.check_omit_focusAt` at an answered focus: the checker admits the
sketch, the focus's answer and error are closed and in normal form, and the hole row's columns
are formed. -/
def omitPremises (sketch : Sketch) (name : String) (focus : Focus NativeOp)
    (app : SigApp := {}) : Bool :=
  (sketch.check app).toOption.isSome &&
    focus.ty.answer.closed && focus.ty.error.closed &&
    decide (focus.ty.answer.normalize = focus.ty.answer) &&
    decide (focus.ty.error.normalize = focus.ty.error) &&
    (Formation.check (Formation.instantiatedSites (holeRow name focus).normalizeTypes [])).isNone

/-- The premises of `Sketch.check_fill_focusAt` at an answered focus: the checker admits the
sketch, and it admits the filling at the focus's type in the focus's environment, at the
address's signature (`Sketch.sigAt`: inside a definition block, the block's). -/
def fillPremises (sketch : Sketch) (path : List Nat) (focus : Focus NativeOp)
    (filling : NativeEff) (app : SigApp := {}) : Bool :=
  (sketch.check app).toOption.isSome &&
    effTy (sketch.sigAt app path) focus.env filling == some focus.ty

/-- **The fill decider is sound.** Where `fillPremises` answers `true` at the focus that the
sketch answers at `app`, the filling applies and keeps the sketch's type: the conclusion of
`Sketch.check_fill_focusAt`, the law that the `fill` answer names. So that answer is an instance
of a theorem, not a tested claim (seat ORG's theory map, section 5.3).

- **Concept**: `residual-program-typing` (`docs/core/semantics.md`); property: typing preservation
  under replacement.
- **Question**: helper of `sketch-fill` (consumer: `Tools.Query.answer` on `"fill"`).
- **Reach**: every `sketch : Sketch`, `app : SigApp`, `path : List Nat`, `focus : Focus NativeOp`
  answered by `sketch.focusAt app path`, and `filling : NativeEff`.
- **Exclusions**: does not admit `app` (`admitSig`) or establish any property of a run.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem fillPremises_sound {sketch : Sketch} {path : List Nat} {focus : Focus NativeOp}
    {filling : NativeEff} {app : SigApp} (hf : sketch.focusAt app path = some focus)
    (h : fillPremises sketch path focus filling app = true) :
    ∃ T s', sketch.check app = .ok T ∧ sketch.fillAt path filling = some s' ∧
      s'.check app = .ok T := by
  simp only [fillPremises, Bool.and_eq_true] at h
  obtain ⟨hcheck, hty⟩ := h
  obtain ⟨T, hT⟩ : ∃ T, sketch.check app = .ok T := by
    cases hc : sketch.check app with
    | ok T => exact ⟨T, rfl⟩
    | error e =>
      rw [hc] at hcheck
      cases hcheck
  have hty' : effTy (sketch.sigAt app path) focus.env filling = some focus.ty := eq_of_beq hty
  have hs0 : ({ sketch with holes := sketch.holes ++ [] } : Sketch) = sketch := by
    cases sketch
    simp only [List.append_nil]
  have hq : Checker.check (Sketch.sigAt { sketch with holes := sketch.holes ++ [] } app path)
      focus.env path filling = .ok focus.ty := by
    rw [hs0]
    exact Conform.Effect4.Typing.check_complete _ _ _ _
      (Conform.Effect4.Typing.effTy_sound _ _ _ _ hty') path
  obtain ⟨s', hfill, hs'⟩ := Sketch.check_fill_focusAt sketch app hT hf [] hq
  rw [hs0] at hfill
  exact ⟨T, s', hT, hfill, hs'⟩

/-- **The omit decider is sound.** Where `omitPremises` answers `true` at the focus that the
sketch answers at `app`, the omission applies and keeps the sketch's type: the conclusion of
`Sketch.check_omit_focusAt`, the law that the `omit` answer names.

- **Concept**: `residual-program-typing` (`docs/core/semantics.md`); property: typing preservation
  under omission.
- **Question**: helper of `sketch-omit` (consumer: `Tools.Query.answer` on `"omit"`).
- **Reach**: every `sketch : Sketch`, `app : SigApp`, `path : List Nat`, `name : String`, and
  `focus : Focus NativeOp` answered by `sketch.focusAt app path`.
- **Exclusions**: does not admit `app` (`admitSig`) or establish any property of a run.
- **Unlocks**: R14 (`docs/core/system-map.md`). -/
theorem omitPremises_sound {sketch : Sketch} {path : List Nat} {name : String}
    {focus : Focus NativeOp} {app : SigApp} (hf : sketch.focusAt app path = some focus)
    (h : omitPremises sketch name focus app = true) :
    ∃ T s', sketch.check app = .ok T ∧ sketch.omitAt app path (holeRow name focus) = some s' ∧
      s'.check app = .ok T := by
  simp only [omitPremises, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨hcheck, hans⟩, herr⟩, hansN⟩, herrN⟩, hform⟩ := h
  obtain ⟨T, hT⟩ : ∃ T, sketch.check app = .ok T := by
    cases hc : sketch.check app with
    | ok T => exact ⟨T, rfl⟩
    | error e =>
      rw [hc] at hcheck
      cases hcheck
  obtain ⟨s', homit, hs'⟩ := Sketch.check_omit_focusAt sketch app hT hf name hans herr hansN herrN
    ((Formation.check_eq_none_iff _).mp (Option.isNone_iff_eq_none.mp hform))
  exact ⟨T, s', hT, homit, hs'⟩

/-! ## The operations -/

/-- The slots of the node at an address of a program, read in the part that holds the address
(`Eff.partAt`), at the part's signature and environment, as the module check reads them. The
environment of the node is the part's table's (`Node.envAt`). A node that is no program, a node in
a generator body, and the root of a block have no slot. The second answer is whether the part's
focus there is typed: then `focusAt_typed` gives `hasTy_extSlotEnv` its premise. -/
def slotsAt (sig : Signature NativeOp) (program : NativeEff) (path : List Nat)
    (slots : List ExtSlot) : List Json × Bool :=
  match program.partAt sig [] path with
  | none => ([], false)
  | some (part, rest) =>
    match (Node.eff part.program).at_ rest,
      (Node.eff part.program).envAt part.sig (.env part.env) rest with
    | some node, some (.env env) =>
      (slots.filterMap fun slot =>
        let term := node.extSlotTerm part.sig slot
        let slotEnv := node.extSlotEnv part.sig env slot
        if term.isSome || slotEnv.isSome then
          some (slotJson slot term slotEnv
            (term.bind fun t => slotEnv.bind fun e => termTy part.sig e t))
        else none,
        (focusAt part.sig part.env part.program rest).isSome)
    | _, _ => ([], false)

/-- **Answer one request.** -/
def answer (req : Request) : Answer :=
  match ofHex? (α := NativeEff) req.program, (req.holes.map (ofHex? (α := RowTable))).getD (some []) with
  | none, _ => refused req.op "the program's bytes do not decode" req.id
  | _, none => refused req.op "the hole table's bytes do not decode" req.id
  | some program, some holes =>
    let sketch : Sketch := { program, holes }
    let sig := (({} : SigApp).withHoles holes).signature
    let done (laws : List Lean.Name) (result : Json) : Answer :=
      { op := req.op, laws, ok := true, result, id := req.id }
    match req.op with
    | "check" => done [``Check.run_module] (checkJson (Check.run (.module {} sketch.holes sketch.program)).result (some program) sig)
    | "addresses" => done [``mem_addresses_iff] (toJson (Node.addresses (.eff program)))
    | "focus" =>
      -- the root's focus is the module check's answer, which may be a block's; any other is the
      -- structural focus of the part that holds the address (Codex's S1-QUERY-01)
      let focus := sketch.focusAt {} req.path
      let laws := match req.path with
        | [] => [``Sketch.focusAt_nil, ``checkModule_sound]
        | _ :: _ => [``focusAt_typed]
      done (if focus.isSome then laws else []) (focusJson focus)
    | "table" =>
      done [``mem_addresses_iff, ``Sketch.table_head]
        (Json.arr ((sketch.table {}).map fun e => entryJson e (some program) sig).toArray)
    | "refusals" =>
      done [``Sketch.refusals_head, ``Sketch.refusals_nil_iff]
        (Json.arr ((sketch.refusals {}).map fun r => refusalJson r (some program) sig).toArray)
    | "slots" =>
      let (slots, typed) := slotsAt sig program req.path
        (req.slot.map ([·]) |>.getD allSlots)
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
              ("holeTable", .str (toHex omitted.holes)),
              ("check", checkJson (Check.run (.module {} omitted.holes omitted.program)).result (some omitted.program)
                (({} : SigApp).withHoles omitted.holes).signature)])
    | "fill" =>
      match req.replacement.bind (ofHex? (α := NativeEff)) with
      | none => refused req.op "the filling's bytes do not decode" req.id
      | some filling =>
        match sketch.fillAt req.path filling with
        | none => refused req.op "no filling at the address" req.id
        | some filled =>
          let matched := match sketch.focusAt {} req.path with
            | some focus => fillPremises sketch req.path focus filling
            | none => false
          done (if matched then [``Sketch.check_fill_focusAt] else [])
            (Json.mkObj [("program", .str (hexOf filled.program)),
              ("matchedFocus", .bool matched),
              ("check", checkJson (Check.run (.module {} filled.holes filled.program)).result (some filled.program) sig)])
    | other => refused other s!"unknown operation {other}" req.id

/-! ## The driver's one function -/

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

end Tools.Query
