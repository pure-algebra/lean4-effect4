import Tools.Query
import Test.Program.FocusControls
import Test.Program.TableControls

/-!
# The query function (slice QUERY): the controls

`tools/Tools/Query.lean` answers one request about a program that arrives as its canonical
bytes. `tools/Drivers/Query.lean` prints `Tools.Query.answerLine` for each line of its input.
These are the finite evaluations, on the examples of `Test/Program/SketchControls.lean` and
`Test/Program/TableControls.lean`.

* **Tested: each of the eight operations.** The answer's `result` is the JSON view of the value
  that the library function gives, and that the other controls guard. No line reads `ok` alone
  at a request that has an answer.
* **Tested: the laws that an answer names.** An answer names a law only where the function has
  decided the law's premises. A focus at no address, a slot of an open program and a filling of
  another type name none.
* **Red (tested): a request with no answer.** Bytes that do not decode, an unknown operation,
  an omission and a filling at no address.
* **Tested: the reader.** It reads what the writer writes. It refuses a field of the wrong type
  and an unknown slot, with the field's name.
* **Tested: the transcript.** `Test/fixtures/query/answers.jsonl` is the driver's own output on
  `Test/fixtures/query/requests.jsonl`. The answer of each recorded request is the recorded
  answer.

No line restates a theorem, and no line prints axioms. The rendered text stays inside the guards.
-/

set_option autoImplicit false

namespace Test.Program.QueryControls

open Lean (Json toJson)
open Effect4 Effect4.Program Effect4.Program.Wire
open Effect4.Machine.Env (Requirement)
open Test.Program.SketchControls Test.Program.FocusControls Test.Program.TableControls
open Tools.Query Tools.ProfileJson

/-- A closed program that holds `Ref.update` under the binder of its cell:
`Ref.make(0)`, then `Ref.update(cell, current => current)`. -/
def updating : NativeEff := .bind (.perform .refMake (.lit (.nat 0))) update

/-- A filling of the type of the example's last statement: it reads `x`. -/
def readsX : NativeEff := .succeed (.var 0)

/-- A filling of another type. -/
def text : NativeEff := .succeed (.lit (.str "x"))

/-! ## `check`, `addresses`, `focus`, `table` and `refusals` -/

-- tested: the checker's answer at the example, and the law of a sketch with no hole table
#guard (answer (ask "check" original)).result == checkJson ((original : Sketch).check {})
#guard (answer (ask "check" original)).result ==
  checkJson (.ok ⟨.nat, .never, Requirement.empty⟩)
#guard (answer (ask "check" original)).laws == [``Sketch.check_program]
-- red (tested): a refused program has an answer, and the answer is the first refusal
#guard ((answer (ask "check" twoBad)).result.getObjVal? "refusal").toOption ==
  (explain sig [] twoBad).map refusalJson
#guard (explain sig [] twoBad).isSome

-- tested: the seven addresses of the example, in the fold's order
#guard (answer (ask "addresses" original)).result ==
  toJson ([[], [0], [1], [1, 0], [1, 1], [1, 1, 0], [1, 1, 1]] : List (List Nat))

-- tested: the focus at the last statement, with its law
#guard (answer (ask "focus" original [1, 1, 1])).result ==
  focusJson ((original : Sketch).focusAt {} [1, 1, 1])
#guard ((original : Sketch).focusAt {} [1, 1, 1]).isSome
#guard (answer (ask "focus" original [1, 1, 1])).laws == [``focusAt_typed]
-- red (tested): no focus at no address, and no law
#guard (answer (ask "focus" original [9])).result == Json.mkObj [("found", .bool false)]
#guard (answer (ask "focus" original [9])).laws == []

-- tested: the address table, entry by entry
#guard (answer (ask "table" original)).result ==
  Json.arr ((table sig [] original).map entryJson).toArray
#guard (answer (ask "table" chained)).result ==
  Json.arr ((table sig [] chained).map entryJson).toArray
-- tested: an entry that is not reached has no environment and no result
#guard ((table sig [] chained).map entryJson).contains
  (Json.mkObj [("path", toJson ([1] : List Nat)), ("env", .null), ("result", .null)])

-- tested: no refusal at the example, and both refusals of the body with two refused statements
#guard (answer (ask "refusals" original)).result == Json.arr #[]
#guard (answer (ask "refusals" twoBad)).result == Json.arr #[
  Json.mkObj [("path", toJson ([0, 0, 0] : List Nat)), ("reason", .str "requestNotSubtype")],
  Json.mkObj [("path", toJson ([0, 1, 0, 0] : List Nat)), ("reason", .str "requestNotSubtype")]]

/-! ## `slots` -/

-- tested: the operation's own term of `Ref.update`, under the binder of its cell. The slot's
-- environment holds the cell and the current value, and the term has the value's type
#guard (answer { ask "slots" updating [1] with slot := some .opTerm }).result ==
  Json.arr #[slotJson .opTerm (some (.var 1)) (some [.refOf .nat, .nat]) (some .nat)]
#guard (answer { ask "slots" updating [1] with slot := some .opTerm }).laws ==
  [``hasTy_extSlotEnv]
-- tested: the step of `iterate` reads the cursor and the body's answer
#guard (answer { ask "slots" loop with slot := some .iterateStep }).result ==
  Json.arr #[slotJson .iterateStep (some (.var 1)) (some [.nat, .nat]) (some .nat)]
-- tested: with no slot named, every slot of the node: the three of `iterate`
#guard (answer (ask "slots" loop)).result == Json.arr #[
  slotJson .iterateTest (some (.lit (.bool true))) (some [.nat]) (some .bool),
  slotJson .iterateStep (some (.var 1)) (some [.nat, .nat]) (some .nat),
  slotJson .iterateResult (some (.var 0)) (some [.nat]) (some .nat)]
-- red (tested): a node with no such slot answers none, and names no law
#guard (answer { ask "slots" caught with slot := some .iterateStep }).result == Json.arr #[]
#guard (answer { ask "slots" caught with slot := some .iterateStep }).laws == []
-- red (tested): an open program has no typed focus. Its slot has a term and no environment, and
-- the answer names no law
#guard (answer { ask "slots" update with slot := some .opTerm }).result ==
  Json.arr #[slotJson .opTerm (some (.var 1)) none none]
#guard (answer { ask "slots" update with slot := some .opTerm }).laws == []

/-! ## `omit` and `fill` -/

-- tested: an omission at the last statement. The premises of the law hold, the omitted sketch
-- keeps the type, and its program needs the hole table
#guard (answer (ask "omit" original [1, 1, 1])).laws == [``Sketch.check_omit_focusAt]
#guard ((answer (ask "omit" original [1, 1, 1])).result.getObjVal? "check").toOption ==
  some (checkJson ((original : Sketch).check {}))
#guard ((answer (ask "omit" original [1, 1, 1])).result.getObjVal? "needsHoleTable").toOption ==
  some (.bool true)
-- red (tested): no omission at no address
#guard !(answer (ask "omit" original [9])).ok

-- tested: a filling of the focus's type. The law is named, and the type is kept
#guard (answer { ask "fill" original [1, 1, 1] with replacement := some (hexOf readsX) }).laws ==
  [``Sketch.check_fill_focusAt]
#guard ((answer { ask "fill" original [1, 1, 1] with
    replacement := some (hexOf readsX) }).result.getObjVal? "check").toOption ==
  some (checkJson ((original : Sketch).check {}))
-- red (tested): a filling of another type. No law is named, and the answer is a new check: the
-- checker refuses the filled program
#guard (answer { ask "fill" original [0] with replacement := some (hexOf text) }).laws == []
#guard (((answer { ask "fill" original [0] with
    replacement := some (hexOf text) }).result.getObjVal? "check").toOption.bind
      fun check => (check.getObjValAs? String "status").toOption) == some "refused"
-- red (tested): a filling at no address, and a filling whose bytes do not decode
#guard !(answer { ask "fill" original [9] with replacement := some (hexOf readsX) }).ok
#guard !(answer { ask "fill" original [0] with replacement := some "zz" }).ok

/-! ## A request with no answer, and the reader -/

-- red (tested): bytes that do not decode, and an unknown operation
#guard !(answer { op := "check", program := "zz" }).ok
#guard !(answer (ask "nothing" original)).ok
#guard (answer (ask "nothing" original)).error == some "unknown operation nothing"

-- tested: the reader reads what the writer writes
#guard ((Request.fromJson? (ask "focus" original [1, 1]).toJson).toOption.map Request.toJson) ==
  some (ask "focus" original [1, 1]).toJson
#guard ((Request.fromJson? ({ ask "slots" loop with slot := some .iterateStep }).toJson).toOption.map
    Request.toJson) == some ({ ask "slots" loop with slot := some .iterateStep }).toJson
-- red (tested): a field of the wrong type and an unknown slot are refused, with the field's name
#guard ((Request.refusal?
    (Json.mkObj [("op", .str "check"), ("program", .str "00"), ("path", .str "x")])).map
      fun why => why.startsWith "field path: ") == some true
#guard Request.refusal?
    (Json.mkObj [("op", .str "slots"), ("program", .str "00"), ("slot", .str "nope")]) ==
  some "field slot: unknown slot nope"
-- green (tested): the reader refuses nothing at a request that the writer wrote
#guard Request.refusal? (ask "focus" original [1, 1]).toJson == none
-- tested: each slot's name reads back from the one table
#guard allSlots.all fun slot => slotOfName? (slotName slot) == some slot
-- red (tested): a line that is no JSON, and a line that is no request, have an answer that
-- says so
#guard (answerLine "not json").startsWith "{\"app\":\"empty\",\"error\":\"no JSON"
#guard answerLine "{}" != answerLine "not json"

/-! ## The transcript -/

-- tested: the answer of each recorded request is the recorded answer
#guard replays (include_str "../fixtures/query/requests.jsonl")
  (include_str "../fixtures/query/answers.jsonl")
#guard (fixtureLines (include_str "../fixtures/query/requests.jsonl")).length == 16

end Test.Program.QueryControls
