import Effect4.Api.Author
import Effect4.Api
import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import TypeScript.Render

/-! Seat PROGRAMS of the data probe (2026-10-01), probe 2: red controls. Each construct here
is one the five model-probe programs use (or the decode route needs), written as close to the
idiom as today's surface allows; each must fail today, and the guard pins where and why. A green
neighbour beside each is the nearest spelling that does build, so a guard cannot pass by the
probe being broken. The printed verdicts of the first run are kept in
`ProbeRedControls.explore.log`. Scratch, not in the tree. -/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Probe.DataRed
open Effect4 Effect4.Program Effect4.Program.Authoring

/-- The build's verdict with its location: the checker's path and reason, admission's path. -/
def verdict (m : Module NativeOp) : String :=
  match Effect4.Api.Author.build m with
  | .ok _ => "built"
  | .error (.scope r) => s!"scope at {r.path}"
  | .error (.typing r) => s!"typing {r.reason.head} at {r.path}"
  | .error (.admission (.uninhabited p)) => s!"admission uninhabited at {p}"
  | .error (.admission (.internalHandle p)) => s!"admission internalHandle at {p}"
  | .error (.admission _) => "admission other"
  | .error (.serviceCarrier _ _ none) => "serviceCarrier: signature none"
  | .error (.serviceCarrier _ _ (some _)) => "serviceCarrier: signature disagrees"

def program (src : Src NativeOp) : Module NativeOp := { main := src }
def pair (a b : TermSrc) : TermSrc := app "pair" [a, b]

/-! ## Records: no literal, no field access by name (stage b) -/

-- RC1. `{ id: 2, name: "bob" }`: no atom builds a record; the checker refuses the term.
#guard verdict (program (succeed (app "record" [str "id", nat 2, str "name", str "bob"]))) =
  "typing term at []"
#guard verdict (program (succeed (pair (nat 2) (str "bob")))) = "built"
-- RC2. `u.name`: `get` is the list atom (an index), so a field name is refused.
#guard verdict (program (bindName "u" (succeed (pair (nat 2) (str "bob"))) fun u =>
    succeed (app "get" [u, str "name"]))) = "typing term at [1]"
#guard verdict (program (bindName "u" (succeed (pair (nat 2) (str "bob"))) fun u =>
    succeed (app "snd" [u]))) = "built"

/-! ## Structured error payloads (DI-62) -/

-- RC4. p2's `NotFound{id: number}`.
#guard verdict (program (fail (pair (str "NotFound") (nat 9)))) = "typing errorNotAdmitted at []"
-- RC5. p1's `HttpError{status, url}` and p5's `InsufficientFunds{needed, available}`.
#guard verdict (program (fail (pair (str "HttpError")
    (pair (nat 503) (str "https://api.example.com/quotes/EFX"))))) = "typing errorNotAdmitted at []"
#guard verdict (program (fail (pair (str "InsufficientFunds") (pair (nat 25) (nat 10))))) =
  "typing errorNotAdmitted at []"
#guard verdict (program (fail (pair (str "NotFound") (str "9")))) = "built"

/-! ## Signed numbers (DI-67, row 108) -/

def balanceRow (t : Ty) : RowDef := Row.host "Ledger.balance" .unit t

-- RC6. a host row answering `int` is refused at admission, at the column.
#guard verdict { rows := [balanceRow .int], main := Row.call (balanceRow .int) unit } =
  "admission uninhabited at [table, 0, answer]"
#guard verdict { rows := [balanceRow .nat], main := Row.call (balanceRow .nat) unit } = "built"
-- RC8. green but wrong: p5's `available - needed` (10 - 25) runs to 0, where rc.112 answers -15
-- (`hostruns.log`: `p5 [-15,[10,10],"settled"]`); `sub` truncates on every face.
#guard (Effect4.Api.Author.program (succeed (app "sub" [nat 10, nat 25]))).toOption.map
    (fun b => decide (b.runSync = .success (.nat 0))) = some true

/-! ## Text, equality, cells, carriers, the host rule -/

-- RC9. `${e.id}`: no atom turns a number into text.
#guard verdict (program (succeed (app "toString" [nat 9]))) = "typing term at []"
-- RC10. structural equality (`Equal.equals`, DI-35): `eq` is at `nat` and `string` only.
#guard verdict (program (succeed (app "eq" [pair (nat 1) (nat 2), pair (nat 1) (nat 2)]))) =
  "typing term at []"
#guard verdict (program (succeed (app "eq" [str "a", str "a"]))) = "built"
-- RC11. a record in a cell (p4's `Window`, p5's `Account`): R4, rows 42-43 steps 3-5.
#guard verdict (program (Ref.make (pair (nat 0) (nat 0)))) = "typing requestNotSubtype at []"
#guard verdict (program (Ref.make (nat 0))) = "built"
-- RC12. a record service carrier (p2's `AppConfig`, `CurrentUser`): rows 114, 118.
def appConfig : ServiceDef := { key := ⟨⟨12⟩, ⟨12⟩⟩, carrier := .prod .string .nat }
#guard verdict { services := [appConfig], main := succeed unit } = "serviceCarrier: signature none"
-- RC16. the row-97 scan reaches inside a product: a record answer with a fiber field is refused
-- at the field's column. A record constructor owes this scan its arm.
def jobsRow : RowDef := Row.host "Jobs.start" .unit (.prod .nat (.fiberOf .nat .never))
#guard verdict { rows := [jobsRow], main := Row.call jobsRow unit } =
  "admission internalHandle at [table, 0, answer, right]"
-- RC17. an `unknown` answer is admitted (row 97's scan passes it), and nothing reads it: the
-- JSON body as `unknown` is a widening, not an embedding.
def jsonRow : RowDef := Row.host "Http.getJson" .string .unknown
#guard verdict { rows := [jsonRow], main := Row.call jsonRow (str "EFX") } = "built"
#guard verdict { rows := [jsonRow], main := (bindName "body" (Row.call jsonRow (str "EFX")) fun body =>
    succeed (app "fst" [body])) } = "typing term at [1]"

/-! ## Variants today: unions of tagged pairs (green, exact for `_tag` + one payload) -/

/-- p5's `Entry = {_tag: "Deposit", amount} | {_tag: "Withdraw", amount}` (p5:23-25). -/
def entryTy : Ty := .union (.prod (.lit "Deposit") .nat) (.prod (.lit "Withdraw") .nat)
def lastEntry : RowDef := Row.host "Ledger.lastEntry" .unit entryTy
def entryModule : Module NativeOp :=
  { rows := [lastEntry]
    main := bindName "entry" (Row.call lastEntry unit) fun entry =>
      selectTag "amount" "other" entry "Deposit"
        (succeed (pair (str "credit") (var "amount")))
        (succeed (pair (str "debit") (app "snd" [var "other"]))) }
#guard verdict entryModule = "built"

#eval show IO Unit from do
  match (Effect4.Api.Author.build entryModule).toOption with
  | some b =>
    match Effect4.Api.printModule "lastMove" b.program b.table with
    | some m => IO.println (TypeScript.Render.module TypeScript.house0 m)
    | none => IO.println "<print refused>"
  | none => IO.println "<not built>"

/-! ## The K2 side: Schema and JSON (the decode route) -/

open Effect4.Schema in
/-- `Schema.Struct({ id: Schema.Number, name: Schema.String })`, as `Ty.schema` would mint the
fields. -/
def userStruct : Representation :=
  struct [property "id" (Bridge.schema .nat), property "name" Effect4.Schema.string]

-- RC13. the schema reader refuses a struct, a tagged union and a recursive reference
-- (`Bridge.ofSchema`, `Schema/Bridge.lean:79-131`): `Ty` has no image for them.
#guard Effect4.Schema.Bridge.ofSchema userStruct = none
#guard Effect4.Schema.Bridge.ofSchema (Effect4.Schema.variant
    [("Deposit", [Effect4.Schema.property "amount" (Effect4.Schema.Bridge.schema .nat)]),
     ("Withdraw", [Effect4.Schema.property "amount" (Effect4.Schema.Bridge.schema .nat)])]) = none
#guard Effect4.Schema.Bridge.ofSchema (Effect4.Schema.suspend (Effect4.Schema.reference "Json")) = none
#guard Effect4.Schema.Bridge.ofSchema (Effect4.Schema.reference "User") = none
-- green: the pair `Ty` mints a tuple, and reads back.
#guard Effect4.Schema.Bridge.ofSchema (Effect4.Schema.Bridge.schema (.prod .nat .string)) =
  some (.prod .nat .string)

-- RC14. the JSON codec at today's record spelling reads an array, not an object: rc.112's
-- `{"id":2,"name":"bob"}` does not decode at `prod nat string`; `[2,"bob"]` does.
#guard Effect4.Schema.decode (.prod .nat .string)
    (.obj [("id", Effect4.Arch.Json.ofNat 2), ("name", .str "bob")]) = none
#guard Effect4.Schema.decode (.prod .nat .string)
    (.arr [Effect4.Arch.Json.ofNat 2, .str "bob"]) = some (.list [.nat 2, .str "bob"])
-- RC15. numbers outside the naturals: p1's fractional price (21.5) and p5's -15 decode at no type.
#guard Effect4.Schema.decode .nat (.number ⟨0x4035800000000000⟩) = none
#guard Effect4.Schema.decode .nat (.number ⟨0xC02E000000000000⟩) = none
#guard Effect4.Schema.decode .int (.number ⟨0xC02E000000000000⟩) = none
#guard Effect4.Schema.decode .nat (.number ⟨0x4035000000000000⟩) = some (.nat 21)

end Probe.DataRed
