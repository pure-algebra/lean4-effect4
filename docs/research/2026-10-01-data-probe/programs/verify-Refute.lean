import Effect4.Api.Author
import Effect4.Api
import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Effect4.Store.Domain.Shape

/-! Verifier of seat PROGRAMS (2026-10-01): attacks on four of the seat's findings with the
tree's own code. The first run printed each outcome (`verify-Refute.explore.log`); this file pins
them as guards, so it must compile green, and each guard is a red or green control.

* A (RC12, PROG-D3): is a record service carrier refused *because it is a record*?
* B (PROG-D3): are the program's own error tags absorbed by today's `Ty`, or by the probe's
  choice of `prod string string` for the infrastructure error?
* C (PROG-D10): what does today's codec already do with JSON objects (excess keys, key order)?
* D (PROG-D9): does an object image need a new `Val` leaf, or does `Val.ctor` under a struct
  shape already print one?
* E (missed by the note): `normalize` distributes a product over a union column, so a record
  that follows `prod` multiplies its union fields out.
Scratch, not in the tree. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Verify.Refute
open Effect4 Effect4.Program Effect4.Program.Authoring

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

/-! ## A. RC12 with green neighbours

The seat's RC12 pins `serviceCarrier: signature none` for a record carrier at code 12 and has no
green neighbour. The same verdict comes back for a `string` and a `nat` carrier at code 12, because
the native signature types no service at that code (`nativeServiceTy`; `Test/Program/
AuthorContract.lean:280`); at a built-in code any carrier but the built-in one is refused. So the
guard shows that `Author.build` declares no new service today, not that a record carrier is
refused; that refusal is a ruling (rows 114, 118), not this probe. -/

def svc (code : Nat) (carrier : Ty) : ServiceDef := { key := ⟨⟨code⟩, ⟨code⟩⟩, carrier := carrier }

#guard verdict { services := [svc 12 (.prod .string .nat)], main := succeed unit } = "serviceCarrier: signature none"
#guard verdict { services := [svc 12 .string], main := succeed unit } = "serviceCarrier: signature none"
#guard verdict { services := [svc 12 .nat], main := succeed unit } = "serviceCarrier: signature none"
#guard verdict { services := [{ key := ⟨⟨4⟩, ⟨4⟩⟩, carrier := .nat }], main := succeed unit } = "built"
#guard verdict { services := [{ key := ⟨⟨4⟩, ⟨4⟩⟩, carrier := .prod .string .nat }], main := succeed unit } =
  "serviceCarrier: signature disagrees"
-- R4's neighbour of RC11: a string cell is refused as a pair cell is (cells read at `nat`).
#guard verdict { main := Ref.make (str "a") } = "typing requestNotSubtype at []"

/-! ## B. p2's handler with literal-tagged infrastructure errors

The seat's probe declares the infrastructure error as `prod string string` (DB-15's spelling) and
reports that the program's own tags are absorbed. With the outer tag as a literal (`Ty.lit`, DB-15
Wave 2: "keep literal tags through const-generic pair construction"), the same handler builds and
its error column keeps every tag; what it does not do is subtract a caught tag while another tag
remains (DI-17, `catchIfError`, `Program/Typing/Rules.lean:217-222`), where rc.112's `catchTag`
removes it. -/

def roleTy : Ty := .union (.lit "admin") (.lit "member")
def userTy : Ty := .prod .nat (.prod .string roleTy)
def configTy : Ty := .prod .string .nat

def mkRows (infraErr : Ty) : RowDef × RowDef :=
  (Row.host "AppConfig.get" .unit configTy .never "p2-handler-layers.ts:51-55",
   Row.host "UserRepo.findById" .nat (.option userTy) infraErr "p2-handler-layers.ts:58-70")

def userId (u : TermSrc) : TermSrc := app "fst" [u]
def userName (u : TermSrc) : TermSrc := app "fst" [app "snd" [u]]
def userRole (u : TermSrc) : TermSrc := app "snd" [app "snd" [u]]

def findOrFail (findById : RowDef) (id idText : TermSrc) : Src NativeOp :=
  bindName "found" (Row.call findById id) fun found =>
    selectOption "user" found
      (fail (app "pair" [str "NotFound", idText]))
      (succeed (var "user"))

def withAuth (rows : RowDef × RowDef) (token id idText : TermSrc) : Src NativeOp :=
  bindName "config" (Row.call rows.1 unit) fun config =>
    ifElse (app "not" [app "eq" [token, app "fst" [config]]])
      (fail (app "pair" [str "Unauthorized", str "bad token"]))
      (bindName "me" (findOrFail rows.2 (nat 1) (str "1")) fun me =>
        ifElse (app "and" [app "not" [app "eq" [userRole me, str "admin"]],
                           app "not" [app "eq" [userId me, id]]])
          (fail (app "pair" [str "Unauthorized", str "not yours"]))
          (findOrFail rows.2 id idText))

def handle (rows : RowDef × RowDef) (token id idText : TermSrc) : Src NativeOp :=
  catchIf "e" (app "tagIs" [str "NotFound", var "e"])
    (catchIf "e2" (app "tagIs" [str "Unauthorized", var "e2"])
      (bindName "user" (withAuth rows token id idText) fun user =>
        succeed (app "pair" [nat 200, userName user]))
      (succeed (app "pair" [nat 401, app "snd" [var "e2"]])))
    (succeed (app "pair" [nat 404, app "concat" [str "no user ", app "snd" [var "e"]]]))

def modOf (infraErr : Ty) (main : RowDef × RowDef → Src NativeOp) : Module NativeOp :=
  let rows := mkRows infraErr
  { rows := [rows.1, rows.2], main := main rows }

def errOf (m : Module NativeOp) : Option Ty :=
  (Effect4.Api.Author.build m).toOption.map fun b => b.ty.error

def pairErr : Ty := .prod .string .string
def litErr : Ty := .prod (.lit "SqlError") .string

/-- The tags, as the literal-tagged handler's error column carries them (first run's print). -/
def taggedColumn : Ty :=
  .union (.prod (.lit "NotFound") (.lit "1"))
    (.union (.prod (.lit "NotFound") (.lit "2"))
      (.union (.prod (.lit "SqlError") .string)
        (.union (.prod (.lit "Unauthorized") (.lit "bad token"))
          (.prod (.lit "Unauthorized") (.lit "not yours")))))

-- the seat's spelling: absorbed, before the catches and after
#guard errOf (modOf pairErr fun r => withAuth r (str "secret") (nat 2) (str "2")) = some pairErr
#guard errOf (modOf pairErr fun r => handle r (str "secret") (nat 2) (str "2")) = some pairErr
-- literal outer tag: admitted, and every tag kept, before the catches and after them
#guard verdict (modOf litErr fun r => handle r (str "secret") (nat 2) (str "2")) = "built"
#guard errOf (modOf litErr fun r => withAuth r (str "secret") (nat 2) (str "2")) = some taggedColumn
#guard errOf (modOf litErr fun r => handle r (str "secret") (nat 2) (str "2")) = some taggedColumn

/-! ## C. Today's codec on JSON objects (`Schema/Codec.lean:74-82`, `fields?`)

The codec already reads objects (Option, Result, Exit, Cause as tagged objects) with an exact
field set in any order: excess and duplicate keys refuse, key order is free, and the encoder
writes one order. So today's codec is already the strict side of the seat's decision K, and it is
exact only modulo key order. -/

def j2 : Json := Effect4.Arch.Json.ofNat 2

#guard Effect4.Schema.decode (.option .nat) (.obj [("_tag", .str "Some"), ("value", j2)]) = some (.some (.nat 2))
#guard Effect4.Schema.decode (.option .nat) (.obj [("value", j2), ("_tag", .str "Some")]) = some (.some (.nat 2))
#guard Effect4.Schema.decode (.option .nat) (.obj [("_tag", .str "Some"), ("value", j2), ("extra", .null)]) = none
#guard Effect4.Schema.decode (.option .nat) (.obj [("_tag", .str "Some"), ("value", j2), ("value", j2)]) = none
#guard Effect4.Schema.encode (.option .nat) (.some (.nat 2)) = some (.obj [("_tag", .str "Some"), ("value", j2)])
-- so the reordered object decodes and does not re-encode to itself
#guard Effect4.Schema.encode (.option .nat) (.some (.nat 2)) ≠ some (.obj [("value", j2), ("_tag", .str "Some")])
-- RC15's "at no type", two more types: `unknown` decodes nothing; negative zero is not a `nat`
#guard Effect4.Schema.decode .unknown (.number ⟨0xC02E000000000000⟩) = none
#guard Effect4.Schema.decode .nat (.number ⟨0x8000000000000000⟩) = none

/-! ## D. The shape-directed image of a constructor value (`Store/Domain/Shape.lean:493-524`)

`ShapeDoc.print` takes names from the shape and structure from the value: a `Val.ctor` under a
`struct` shape prints an object with the field names, under a `sum` shape a `_tag` object; a
`Val.list` prints an array whatever the shape. So an object image needs a constructor frame,
which the carrier already has (`Val.ctor`), not a new `Val` leaf. -/

def userDoc : Effect4.Store.ShapeDoc :=
  { root := .struct "User" [("id", .nat), ("name", .string)], defs := [] }
def entryDoc : Effect4.Store.ShapeDoc :=
  { root := .sum "Entry" [("Deposit", 0, [("amount", .nat)]), ("Withdraw", 1, [("amount", .nat)])], defs := [] }

#guard userDoc.print (.ctor 0 [.nat 2, .str "bob"]) = .obj [("id", j2), ("name", .str "bob")]
#guard userDoc.print (.list [.nat 2, .str "bob"]) = .arr [j2, .str "bob"]
#guard entryDoc.print (.ctor 1 [.nat 25]) = .obj [("_tag", .str "Withdraw"), ("amount", Effect4.Arch.Json.ofNat 25)]

/-! ## E. Normalisation distributes a product over its union columns (`Ty.productMembers`,
`Program/Ty.lean:603-604`)

p2's `User` (a literal-union field) is already two products after normalisation; three binary
union columns give eight. A record arm that follows `prod` would do the same; TypeScript does not
distribute object types. The note's shapes say nothing about `normalize` or `Normal` at a record. -/

def tri : Ty :=
  .prod (.union (.lit "a") (.lit "b")) (.prod (.union (.lit "c") (.lit "d")) (.union (.lit "e") (.lit "f")))

#guard Ty.normalize userTy =
  .union (.prod .nat (.prod .string (.lit "admin"))) (.prod .nat (.prod .string (.lit "member")))
#guard (Ty.members (Ty.normalize tri)).length = 8

end Verify.Refute
