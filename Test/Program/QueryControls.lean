import Effect4.Tool.Wire
import Tools.WireText
import Test.Program.FocusControls
import Test.Program.TableControls

/-!
# The tool's reads of a program: the controls

`Effect4.Tool.serve` answers each read of a document: its view (the check and the refusals), the
inspection at an address (the focus), the whole address table, the addresses, and the term slots
of a node. A filling and an omission are `dry` edits: the answer is what the edit would do, and
the state stays. These are the finite evaluations, on the examples of
`Test/Program/SketchControls.lean` and `Test/Program/TableControls.lean`. They were the controls of
the retired query tool (`Tools.Query`); each keeps its meaning.

* **Tested: each read.** The answer is the value that the library function gives, and that the
  other controls guard. The table is the session's own (`SourceSession.table`), on these
  reference-free programs the program's table.
* **Tested: the decisions an answer carries.** A slot's answer says whether the node is typed in
  its part, the premise of `hasTy_extSlotEnv`. An omission under the draft policy splices where
  the premises of `Sketch.check_omit_focusAt` hold. A filling under `keepExact` is accepted where
  it keeps the type, and refused `notKept` where it does not. A slot of an open program is
  untyped. The root of a definition block is typed by the module check, and its parts are read at
  the block's signature.
* **Red (tested): a read or an edit with no answer.** No program at the address; a filling and an
  omission at no address; a request line whose program, hole table or operation does not decode.
* **Tested: the wire.** Each new read crosses the wire and reads back; each slot reads back; an
  unknown slot does not read.

No line restates a theorem, and no line prints axioms. The rendered text stays inside the guards.
-/

set_option autoImplicit false

namespace Test.Program.QueryControls

open Effect4 Effect4.Program Effect4.Program.Check Effect4.Tool
open Effect4.Tool.Wire (Envelope Connection decode)
open Effect4.Machine.Env (Requirement)
open Test.Program.SketchControls Test.Program.FocusControls Test.Program.TableControls

/-- Serve one request with the uncached oracle. -/
def serve1 (s : State) (r : Request) : State × Reply := (serve Oracle.uncached s r).value

/-- The state with one document open on a program and a hole table, at the empty application. -/
def opened (program : NativeEff) (holes : RowTable := []) : State :=
  (serve1 empty (.act (.open_ "q" {} ⟨program, holes⟩))).1

/-- The snapshot of a document just opened. -/
def snap0 : Snap := ⟨⟨"q", 0⟩, 0⟩

/-- The answer of a query on the document of a program. -/
def ask (program : NativeEff) (q : Query) (holes : RowTable := []) : Except Tool.Refusal Answer :=
  (serve1 (opened program holes) (.ask q)).2.result

/-- The view of the document of a program, or none. -/
def viewOf (program : NativeEff) (holes : RowTable := []) : Option DocView :=
  match ask program (.doc none) holes with
  | .ok (.doc v) => some v
  | _ => none

/-- The sub-program at an address, or the program itself where the address holds none. -/
def subAt (program : NativeEff) (path : List Nat) : NativeEff :=
  match (Node.eff program).at_ path with
  | some (.eff q) => q
  | _ => program

/-- The commit of one change at an address of a program, under a policy. -/
def change1 (program : NativeEff) (path : List Nat) (c : Change) (policy : FeedPolicy) : Action :=
  .edit snap0 (.commit [(.at_ path (subAt program path), c)] policy)

/-- The answer of a `dry` commit of one change, or none. -/
def dry (program : NativeEff) (path : List Nat) (c : Change) (policy : FeedPolicy) :
    Option (Except Tool.Refusal ActionAnswer) :=
  match ask program (.dry (change1 program path c policy)) with
  | .ok (.dry result) => some result
  | _ => none

/-- The slots answer at an address: the typed flag and each slot's fields. -/
def slotsOf (program : NativeEff) (path : List Nat) (slot : Option ExtSlot) :
    Option (Bool × List (ExtSlot × Option Term × Option TyEnv × Option Ty)) :=
  match ask program (.slots path slot) with
  | .ok (.slots _ typed found) => some (typed, found.map fun v => (v.slot, v.term, v.env, v.ty))
  | _ => none

/-- A closed program that holds `Ref.update` under the binder of its cell:
`Ref.make(0)`, then `Ref.update(cell, current => current)`. -/
def updating : NativeEff := .bind (.perform .refMake (.lit (.nat 0))) update

/-- A filling of the type of the example's last statement: it reads `x`. -/
def readsX : NativeEff := .succeed (.var 0)

/-- A filling of another type. -/
def text : NativeEff := .succeed (.lit (.str "x"))

/-! ## The check, the addresses, the focus, the table and the refusals -/

-- tested: the document's type is the checker's answer at the example
#guard (viewOf original).bind (·.type) == ((original : Sketch).check {}).toOption
#guard (viewOf original).bind (·.type) == some ⟨.nat, .never, Requirement.empty⟩
-- red (tested): a refused program has no type, and its first refusal is the checker's
#guard ((viewOf twoBad).map fun v => (v.type.isNone, v.refusals.head?)) ==
  some (true, Program.explain sig [] twoBad)
#guard (Program.explain sig [] twoBad).isSome

-- tested: the seven addresses of the example, in the fold's order
#guard match ask original .addresses with
  | .ok (.addresses paths) => paths == [[], [0], [1], [1, 0], [1, 1], [1, 1, 0], [1, 1, 1]]
  | _ => false

-- tested: the focus at the last statement is the sketch's focus there
#guard match ask original (.doc (some [1, 1, 1])) with
  | .ok (.doc v) => (v.inspection.bind (·.focus)) == (original : Sketch).focusAt {} [1, 1, 1]
  | _ => false
#guard ((original : Sketch).focusAt {} [1, 1, 1]).isSome
-- red (tested): no program at the address, and the read refuses
#guard match ask original (.doc (some [9])) with
  | .error (.noProgram [9]) => true
  | _ => false

-- tested: the address table, entry by entry
#guard match ask original .table with
  | .ok (.table entries) => entries == table sig [] original
  | _ => false
#guard match ask chained .table with
  | .ok (.table entries) => entries == table sig [] chained
  | _ => false
-- tested: an entry that is not reached has no environment and no result
#guard match ask chained .table with
  | .ok (.table entries) => entries.contains ⟨[1], none, none⟩
  | _ => false

-- tested: no refusal at the example, and both refusals of the body with two refused statements
#guard (viewOf original).map (·.refusals.isEmpty) == some true
#guard (viewOf twoBad).map (named ·.refusals) ==
  some [([0, 0, 0], "requestNotSubtype"), ([0, 1, 0, 0], "requestNotSubtype")]
-- tested: each refusal crosses the wire whole, its reason's fields among them (Codex's
-- cx-refusal review)
#guard
  let reply := (serve1 (opened twoBad) (.ask (.doc none))).2
  match CodecProfile.write reply with
  | .ok j =>
    match CodecProfile.read (α := Reply) j with
    | .ok ⟨.ok (.doc v), _⟩ => some v.refusals == (viewOf twoBad).map (·.refusals)
    | _ => false
  | .error _ => false

/-! ## The term slots -/

-- tested: the operation's own term of `Ref.update`, under the binder of its cell. The slot's
-- environment holds the cell and the current value, the term has the value's type, and the node
-- is typed in its part
#guard slotsOf updating [1] (some .opTerm) ==
  some (true, [(.opTerm, some (.var 1), some [.refOf .nat, .nat], some .nat)])
-- tested: the step of `iterate` reads the cursor and the body's answer
#guard slotsOf loop [] (some .iterateStep) ==
  some (true, [(.iterateStep, some (.var 1), some [.nat, .nat], some .nat)])
-- tested: with no slot named, every slot of the node: the three of `iterate`
#guard slotsOf loop [] none == some (true, [
  (.iterateTest, some (.lit (.bool true)), some [.nat], some .bool),
  (.iterateStep, some (.var 1), some [.nat, .nat], some .nat),
  (.iterateResult, some (.var 0), some [.nat], some .nat)])
-- red (tested): a node with no such slot answers none
#guard (slotsOf caught [] (some .iterateStep)).map (·.2) == some []
-- red (tested): an open program has no typed focus. Its slot has a term and no environment
#guard slotsOf update [] (some .opTerm) == some (false, [(.opTerm, some (.var 1), none, none)])
-- red (tested): no program at the address, and the read refuses
#guard match ask loop (.slots [9] none) with
  | .error (.noProgram [9]) => true
  | _ => false

/-! ## A definition block: the root, and the parts (Codex's S1-QUERY-01) -/

/-- The identity on naturals, declared. -/
def idDecl : DefDecl := { name := "identity", request := .nat, answer := .nat }
/-- An invocation of the identity. -/
def callId : NativeEff := .perform (.call 0) (.lit (.nat 5))
/-- A block that defines the identity, and whose main program invokes it. -/
def idBlock : NativeEff := .defs [idDecl] (.cons (.succeed (.var 0)) .nil) callId .nil
/-- A loop that counts nothing, closed. -/
def closedLoop : NativeEff :=
  .iterate none (.lit (.nat 0)) (.lit (.bool true)) (.var 1) (.var 0) (.succeed (.var 0))
/-- The block whose main program runs the loop after the invocation. -/
def loopBlock : NativeEff := .defs [idDecl] (.cons (.succeed (.var 0)) .nil) (.bind callId closedLoop) .nil

-- control: the structural checker refuses the block, which the module check admits
#guard (Checker.check sig [] [] idBlock).toOption.isNone && (Checker.checkModule sig idBlock).toOption.isSome
-- tested: the root's focus is the module check's answer
#guard match ask idBlock (.doc (some [])) with
  | .ok (.doc v) => (v.inspection.bind (·.focus)).map (·.ty) == (Checker.checkModule sig idBlock).toOption
  | _ => false
-- tested: inside the block, the focus at the part that holds the address
#guard match ask idBlock (.doc (some [1])) with
  | .ok (.doc v) => (v.inspection.bind (·.focus)).isSome
  | _ => false
-- tested: the slots of `iterate` after an invocation, read at the block's signature, typed
#guard (slotsOf loopBlock [1, 1] none).map (fun (typed, found) => (typed, found.length)) ==
  some (true, 3)
-- red (tested): the root of a block has no slot
#guard (slotsOf idBlock [] none).map (·.2) == some []

/-! ## An omission and a filling, as `dry` edits -/

-- tested: an omission of the last statement under the draft policy. The premises of
-- `Sketch.check_omit_focusAt` hold, so the edit splices; the type stays, and the document shows
-- the new hole at the address
#guard match dry original [1, 1, 1] (.omitHole "h0") .draft with
  | some (.ok (.edited v receipt)) =>
    v.type == ((original : Sketch).check {}).toOption &&
      (receipt.steps.map fun step => match step.delta with
        | .spliced _ => true
        | _ => false) == [true] &&
      v.holes.map (fun h => (h.index, h.path)) == [(0, [1, 1, 1])]
  | _ => false
-- tested (the sketch): the omitted program and its hole rows, opened together, check at the
-- original's type; the program without its hole rows is refused, since it performs a hole that
-- no row declares
#guard
  let s := (serve1 (opened original) (.act (change1 original [1, 1, 1] (.omitHole "h0") .draft))).1
  match (serve1 s (.ask (.doc (some [])))).2.result with
  | .ok (.doc v) =>
    match v.inspection with
    | some i =>
      (viewOf i.expected (v.holes.map (·.row))).bind (·.type) == ((original : Sketch).check {}).toOption &&
        (viewOf i.expected).map (·.type.isNone) == some true
    | none => false
  | _ => false
-- red (tested): no omission at no address
#guard match dry original [9] (.omitHole "h0") .draft with
  | some (.error (.doc (.place 0 (.moved [9])))) => true
  | _ => false

-- tested: a filling of the focus's type is kept, and the type stays
#guard match dry original [1, 1, 1] (.fill readsX) .keepExact with
  | some (.ok (.edited v _)) => v.type == ((original : Sketch).check {}).toOption
  | _ => false
-- red (tested): a filling of another type is not kept
#guard match dry original [0] (.fill text) .keepExact with
  | some (.error (.doc (.feed 0 (.notKept _ _)))) => true
  | _ => false
-- tested: under the draft policy the same filling is a new check, and the checker refuses the
-- filled program
#guard match dry original [0] (.fill text) .draft with
  | some (.ok (.edited v _)) => v.type.isNone && !v.refusals.isEmpty
  | _ => false
-- red (tested): a filling at no address
#guard match dry original [9] (.fill readsX) .keepExact with
  | some (.error (.doc (.place 0 (.moved [9])))) => true
  | _ => false

/-! ## The wire -/

/-- A request framed at version 1, as JSON. -/
def framed (r : Request) : Effect4.Json :=
  match CodecProfile.write (⟨r.method, 1, r⟩ : Envelope Request) with
  | .ok j => j
  | .error _ => .null

-- tested: each new read crosses the wire at its selected version and reads back
#guard [Request.ask .table, .ask .addresses, .ask (.slots [1, 1] (some .iterateStep)),
    .ask (.slots [] none)].all fun r =>
  match decode Connection.v1 (framed r) with
  | .ok envelope => envelope.method == r.method && framed envelope.payload == framed r
  | .error _ => false
-- tested: each slot reads back from its JSON
#guard Internal.allSlots.all fun slot =>
  ((CodecProfile.write slot).toOption.bind fun j => (CodecProfile.read (α := ExtSlot) j).toOption) ==
    some slot
-- control: a slots line with a known slot reads, and so does an open line with a well-formed
-- program and an empty hole table
#guard (Tools.WireText.readRequest ("{\"method\":\"slots\",\"version\":1,\"payload\":{\"_tag\":\"ask\"," ++
  "\"q\":{\"_tag\":\"slots\",\"at_\":[],\"slot\":\"opTerm\"}}}")).toOption.isSome
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
  "\"value\":{\"_tag\":\"nat\",\"value\":1}}}}}}}")).toOption.isSome
-- red (tested): an unknown slot, a program, a hole table and an operation that do not decode
#guard (Tools.WireText.readRequest ("{\"method\":\"slots\",\"version\":1,\"payload\":{\"_tag\":\"ask\"," ++
  "\"q\":{\"_tag\":\"slots\",\"at_\":[],\"slot\":\"nope\"}}}")).toOption.isNone
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[],\"program\":{\"_tag\":\"nothing\"}}}}}")).toOption.isNone
#guard (Tools.WireText.readRequest ("{\"method\":\"open\",\"version\":1,\"payload\":{\"_tag\":\"act\"," ++
  "\"a\":{\"_tag\":\"open_\",\"name\":\"n\",\"app\":{\"rows\":[],\"services\":[],\"types\":[]}," ++
  "\"sketch\":{\"holes\":[0],\"program\":{\"_tag\":\"succeed\",\"value\":{\"_tag\":\"lit\"," ++
  "\"value\":{\"_tag\":\"nat\",\"value\":1}}}}}}}")).toOption.isNone
#guard (Tools.WireText.readRequest
  "{\"method\":\"nothing\",\"version\":1,\"payload\":{\"_tag\":\"ask\",\"q\":{\"_tag\":\"nothing\"}}}").toOption.isNone
-- red (tested): a line that is no JSON and a line that is no request each say why, differently
#guard match Tools.WireText.readRequest "not json", Tools.WireText.readRequest "{}" with
  | .error a, .error b => a != b && b == "not a request envelope"
  | _, _ => false

end Test.Program.QueryControls
