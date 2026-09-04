/-
Contract: `test/contracts/surface-handler-fits.contract.md`.

A prior contract for the same subject exists at
`test/contracts/surface-handler.contract.md` (commit `9f9e0e6`) and rules the
central question the other way: it keeps `Handler.fits` as exact `EffTy`
equality and keeps the typed stub out of the `Handler` carrier entirely. Which
packet governs is finding H-0 and a coordinator ruling.

Frozen by the handler breaker (plan §13.7 ruling 7) before the handler module
exists, from `docs/research/2026-09-04-surface-library-plan.md` §13.2 and the
rc.112 sources it cites. Red until wave 2d lands the module.

Pin: `effect` 4.0.0-rc.112, `node_modules/effect/src`:
`Effect.ts:117`, `:154-157` (the three covariant parameters),
`unstable/httpapi/HttpApiEndpoint.ts:584-586` (the handler slot),
`:720-724` (`ExcludeProvided`),
`unstable/http/HttpRouter.ts:853-857` (`Provided`),
`unstable/httpapi/HttpApiBuilder.ts:126`, `:137-141`, `:169-179`, `:219-221`,
`:241-252`, `:441`.

The module path of the owed import is finding H-1 of this packet's report and
is **not** frozen: plan §2 forbids `Effect4.Surface.*` from importing
`Effect4.Program.*` and `Effect4.Machine.*`, while plan §13.2 puts
`Endpoint.effTy : Endpoint refs → EffTy` in `Effect4/Surface/Handler.lean`
over both. Everything below is stated in namespace `Effect4.Surface`, which
every candidate resolution can honour, so a ruling changes the marked import
line and nothing else in this file.

The first section uses only landed carriers and is green today. It pins the
`Ty.join` facts that `Endpoint.errorTy?` rests on and that
`Effect4/Syntax/Eff.lean` does not prove (finding H-3): that file has exactly
one theorem, `render_ofSpelling`, so the order-independence of a join fold is
evidence at instances here and an owed universal theorem there.

`EffTy` derives `DecidableEq` and not `Repr`, so every receipt in this file is
a `#guard` on an equation and none is an `#eval`.
-/

import Effect4.Program.Typing
import Effect4.Codegen.Print
import Test.Surface.Fixtures
-- Owed by wave 2d. The module path is finding H-1; the namespace is frozen.
import Effect4.Surface.Handler

set_option autoImplicit false

namespace Test.Surface.HandlerFitsContract

open Effect4 (ReferenceEntry ServiceKey)
open Effect4.Program (Ty Row EffTy Signature typeOf)
open Effect4.Machine.Env (Requirement)
open Effect4.Surface
open Test.Surface.Fixtures

/-! ## The `Ty` algebra `Endpoint.errorTy?` rests on

Landed carriers only. These are the instances that stand in for the seven owed
theorems of the contract's table; a builder who folds `Ty.join` over
`e.errors` in any order must agree with them. -/

/-- The three error entities of the reference application of plan §13.3. -/
def notFoundTy : Ty := .handle "NotFound"
def validationTy : Ty := .handle "ValidationError"
def rateLimitedTy : Ty := .handle "RateLimited"
def userTy : Ty := .handle "User"

-- Commutative at two members, in both spellings.
#guard Ty.join notFoundTy validationTy = Ty.join validationTy notFoundTy
#guard Ty.join notFoundTy validationTy = Ty.union notFoundTy validationTy

-- Idempotent: two error responses naming one entity contribute one member.
#guard Ty.join notFoundTy notFoundTy = notFoundTy

-- `.never` is the unit, which is what makes "no errors" the empty join.
#guard Ty.join notFoundTy .never = notFoundTy
#guard Ty.join .never notFoundTy = notFoundTy
#guard Ty.join .never .never = Ty.never

-- Associative at three members.
#guard Ty.join (Ty.join notFoundTy validationTy) rateLimitedTy
  = Ty.join notFoundTy (Ty.join validationTy rateLimitedTy)

-- A fold over an error list is independent of the list's order, in both
-- directions and both fold spellings.
#guard [notFoundTy, validationTy, rateLimitedTy].foldl Ty.join .never
  = [rateLimitedTy, validationTy, notFoundTy].foldl Ty.join .never
#guard [notFoundTy, validationTy, rateLimitedTy].foldr Ty.join .never
  = [rateLimitedTy, validationTy, notFoundTy].foldl Ty.join .never

-- The canonical rendering the members sort into, pinned as bytes so a change
-- of `Ty.key` or `Ty.ltKey` is visible here.
#guard Ty.render ([notFoundTy, validationTy, rateLimitedTy].foldl Ty.join .never)
  = "NotFound | RateLimited | ValidationError"

-- A `void` success beside a `json` success joins to a two-member union, not to
-- the json member: `Ty.unit` is a member like any other.
#guard Ty.render (Ty.join .unit userTy) = "void | User"

-- `EffTy.joinAnswer` is *not* `Ty.join`: typing refuses two distinct answers
-- rather than unioning them. This is what makes a multi-success endpoint's
-- answer unreachable from any control construct (`E4-SURFACE-CE-096`).
#guard EffTy.joinAnswer userTy notFoundTy = none
#guard EffTy.joinAnswer userTy .never = some userTy
#guard EffTy.joinAnswer .never userTy = some userTy
#guard EffTy.joinAnswer userTy userTy = some userTy

/-! ## Requirement rows: duplicates collapse, order does not matter

`Requirement` is `Effect4.Data.Row ServiceKey`, a canonical strictly ascending
list, so a duplicate service name in `Endpoint.requires` cannot survive into
`EffTy.requires`. The clause that refuses the duplicate is still worth having
(`E4-SURFACE-CE-099`): the *alphabet* is where a duplicate does damage. -/

/-- The `Db` service key of the fixture alphabet. -/
def dbKey : ServiceKey := ⟨⟨1⟩, ⟨1⟩⟩
/-- The `RateLimit` service key of the fixture alphabet. -/
def rateKey : ServiceKey := ⟨⟨2⟩, ⟨1⟩⟩
/-- The `Scope` key, which rc.112 provides and never charges
(`HttpRouter.ts:853-857`, `HttpApiBuilder.ts:140`). -/
def scopeKey : ServiceKey := ⟨⟨0⟩, ⟨0⟩⟩

#guard Requirement.ofList [dbKey, dbKey] = Requirement.single dbKey
#guard Requirement.ofList [dbKey, rateKey] = Requirement.ofList [rateKey, dbKey]
#guard (Requirement.ofList [dbKey, rateKey]).elems.length = 2
#guard (Requirement.ofList [dbKey, dbKey]).elems.length = 1

/-! ## The fixture alphabet and its handlers

Everything from here down is owed by wave 2d. -/

/-- The `Db` rows of the `shop` fixture, one per endpoint of `shopApi`. -/
def dbGetUser : ServiceOp :=
  { service := "Db", op := "getUser"
  , row := ⟨"getUser", "db.getUser", .call, [], .sync, .string, userTy, notFoundTy
      , [dbKey], "fixture: the shop Db service"⟩ }

def dbCreateUser : ServiceOp :=
  { service := "Db", op := "createUser"
  , row := ⟨"createUser", "db.createUser", .call, [], .sync, .string, userTy, notFoundTy
      , [dbKey], "fixture: the shop Db service"⟩ }

def dbDeleteUser : ServiceOp :=
  { service := "Db", op := "deleteUser"
  , row := ⟨"deleteUser", "db.deleteUser", .call, [], .sync, .string, .unit, notFoundTy
      , [dbKey], "fixture: the shop Db service"⟩ }

/-- A row that opens a scope, so its requirement carries `scopeKey` and rc.112
excludes it. -/
def dbScoped : ServiceOp :=
  { service := "Db", op := "withConnection"
  , row := ⟨"withConnection", "db.withConnection", .call, [], .sync, .string, userTy
      , notFoundTy, [dbKey, scopeKey], "fixture: the shop Db service"⟩ }

/-- The alphabet of every `shop` handler: the three `Db` rows and the atom the
typed stub needs. -/
def shopAlphabet : Alphabet :=
  { ops := [dbGetUser, dbCreateUser, dbDeleteUser]
  , atoms := [notImplementedAtom]
  , scopeKey := scopeKey }

#guard Alphabet.services shopAlphabet = ["Db"]
#guard (Alphabet.rowAt shopAlphabet 0).spelling = "db.getUser"
#guard Alphabet.requirementOf shopAlphabet ["Db"] = Requirement.single dbKey
#guard Alphabet.requirementOf shopAlphabet [] = Requirement.empty
#guard Alphabet.atomOf shopAlphabet "NotImplemented" [] = some notImplementedTy
#guard Alphabet.atomOf shopAlphabet "absent" [] = none

-- `Alphabet.provided` is rc.112's `HttpRouter.Provided` restricted to what
-- this slice can name: the alphabet's own `Scope` key.
#guard Alphabet.provided shopAlphabet = Requirement.single scopeKey

/-- The `getUser` handler: one `perform` of `db.getUser` on the slug. -/
def getUserHandler : Handler :=
  { group := "users", endpoint := "getUser"
  , alphabet := shopAlphabet
  , body := .perform 0 (.lit (.str "u1")) }

def createUserHandler : Handler :=
  { group := "users", endpoint := "createUser"
  , alphabet := shopAlphabet
  , body := .perform 1 (.lit (.str "{}")) }

def deleteUserHandler : Handler :=
  { group := "users", endpoint := "deleteUser"
  , alphabet := shopAlphabet
  , body := .perform 2 (.lit (.str "u1")) }

/-! ## The endpoint's type, read off the rows of `surface-api.contract.md` -/

#guard Endpoint.answerTy? getUser = some userTy
#guard Endpoint.errorTy? getUser = some notFoundTy
#guard Endpoint.answerTy? createUser = some userTy
#guard Endpoint.errorTy? createUser = some notFoundTy

-- A `204` success with no body answers `.unit`, not `.never`.
#guard Endpoint.answerTy? deleteUser = some Ty.unit

-- The whole `Effect<A, E, R>` the endpoint demands, given the alphabet that
-- supplies the keys. This is the equation plan §13.2 is about.
#guard Endpoint.effTy? getUser shopAlphabet
  = some ⟨userTy, notFoundTy, Requirement.single dbKey⟩
#guard Endpoint.effTy? deleteUser shopAlphabet
  = some ⟨Ty.unit, notFoundTy, Requirement.single dbKey⟩

/-! ## The body's type, and the fit -/

#guard Handler.effTy? getUserHandler
  = some ⟨userTy, notFoundTy, Requirement.single dbKey⟩
#guard Handler.requires getUserHandler = Requirement.single dbKey
#guard Handler.escapes getUser getUserHandler = Ty.never
#guard Handler.errorsDeclared getUser getUserHandler = true

#guard Handler.fits getUser getUserHandler = true
#guard Handler.fitsExactly getUser getUserHandler = true
#guard Handler.fits createUser createUserHandler = true
#guard Handler.fits deleteUser deleteUserHandler = true

#guard Handler.check shopApi getUserHandler = .ok ()
#guard Handler.check shopApi createUserHandler = .ok ()
#guard Handler.check shopApi deleteUserHandler = .ok ()

theorem getUserHandler_wf : Handler.WellFormed shopApi getUserHandler := by decide
theorem createUserHandler_wf : Handler.WellFormed shopApi createUserHandler := by decide
theorem deleteUserHandler_wf : Handler.WellFormed shopApi deleteUserHandler := by decide

/-! ## Subsumption, which is where `fits` differs from §13.2 as written

Each of these is a program rc.112 accepts and equality refuses. The
counterexample file argues each one; here they are pinned as the positive
receipts of the repaired relation. -/

/-- A handler that cannot fail. rc.112 instantiates `E` at `never`
(`HttpApiEndpoint.ts:586`), so this is a legal `getUser` implementation that
happens never to miss. -/
def infallibleHandler : Handler :=
  { getUserHandler with body := .succeed (.app "cachedUser" .nil) }

/-- A handler that needs no service at all: a constant response. -/
def pureHandler : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with ops := [] }
    body := .succeed (.app "cachedUser" .nil) }

/-- A handler that opens a scope. Its `typeOf` requirement carries `scopeKey`,
and rc.112 removes it twice over (`HttpApiEndpoint.ts:720-724`,
`HttpApiBuilder.ts:140`). -/
def scopedHandler : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with ops := [dbScoped] }
    body := .perform 0 (.lit (.str "u1")) }

#guard Handler.fits getUser scopedHandler = true
#guard Handler.requires scopedHandler = Requirement.single dbKey
#guard Handler.fitsExactly getUser scopedHandler = false

/-! ## The typed stub

Plan §13.2: "an endpoint with no handler emits a typed stub whose body is
`Effect.fail(new NotImplemented())` under the same declared type, so the
module typechecks either way". -/

def getUserStub : Handler := Endpoint.stub "users" getUser shopAlphabet

#guard getUserStub.stance = HandlerStance.stub
#guard Handler.effTy? getUserStub
  = some ⟨Ty.never, notImplementedTy, Requirement.empty⟩
#guard Handler.fits getUser getUserStub = true
#guard Handler.check shopApi getUserStub = .ok ()

-- The stub's error is not one the endpoint declares; rc.112 collects it into
-- `Handlers.Error<Return>` (`HttpApiBuilder.ts:139`) rather than refusing it,
-- and the surface reports it as data.
#guard Handler.escapes getUser getUserStub = notImplementedTy
#guard Handler.errorsDeclared getUser getUserStub = false

-- And it is exactly what §13.2's equality refuses (`E4-SURFACE-CE-088`).
#guard Handler.fitsExactly getUser getUserStub = false

theorem getUserStub_fits : Handler.fits getUser getUserStub = true :=
  Endpoint.stub_fits "users" getUser shopAlphabet (by decide)

/-! ## A group's handler set -/

def usersHandlers : Handlers :=
  { group := "users"
  , handlers := [getUserHandler, createUserHandler, deleteUserHandler] }

#guard Handlers.check shopApi usersHandlers = .ok ()
theorem usersHandlers_wf : Handlers.WellFormed shopApi usersHandlers := by decide

/-- A group with no handlers at all still typechecks once completed with
stubs. This is what retires `Endpoint not handled: ${Missing}`
(`HttpApiBuilder.ts:241-252`). -/
def emptyHandlers : Handlers := { group := "users", handlers := [] }

#guard Handlers.check shopApi emptyHandlers
  = .error (.endpointNotHandled "users" "getUser")
#guard (Handlers.complete shopApi emptyHandlers shopAlphabet).isSome
#guard ((Handlers.complete shopApi emptyHandlers shopAlphabet).map
  fun hs => hs.handlers.length) = some 3
#guard ((Handlers.complete shopApi emptyHandlers shopAlphabet).map
  fun hs => hs.handlers.all fun h => h.stance = HandlerStance.stub) = some true
#guard ((Handlers.complete shopApi emptyHandlers shopAlphabet).map
  fun hs => Handlers.check shopApi hs) = some (.ok ())

/-- Completion is a fill, not a replacement: a handled endpoint keeps its
handler. -/
def partialHandlers : Handlers := { group := "users", handlers := [getUserHandler] }

#guard ((Handlers.complete shopApi partialHandlers shopAlphabet).map
  fun hs => hs.handlers.length) = some 3
#guard ((Handlers.complete shopApi partialHandlers shopAlphabet).bind
  fun hs => hs.handlers.find? fun h => h.endpoint = "getUser")
  = some getUserHandler

/-! ## The slot types

The receipts above are only as strong as the shapes they range over. These
definitions are ascribed to the frozen types, so a builder who stored a
`Signature` instead of deriving it, or who indexed `Eff` by something other
than `Nat`, breaks this file rather than silently changing what the clauses can
see. Plan §4 and `AGENTS.md` "Representation rules" are the reason
(`E4-SURFACE-CE-098`). -/

def alphabetOpsSlot : Alphabet → List ServiceOp := Alphabet.ops
def serviceOpRowSlot : ServiceOp → Row := ServiceOp.row
def handlerBodySlot : Handler → Effect4.Program.Eff Nat := Handler.body
def handlerAlphabetSlot : Handler → Alphabet := Handler.alphabet
def handlerStanceSlot : Handler → HandlerStance := Handler.stance
def signatureSlot : Alphabet → Signature Nat := Alphabet.signature
def effTySlot : ∀ refs : List ReferenceEntry,
    Endpoint refs → Alphabet → Option EffTy := @Endpoint.effTy?
def fitsSlot : ∀ refs : List ReferenceEntry,
    Endpoint refs → Handler → Bool := @Handler.fits

#guard (alphabetOpsSlot shopAlphabet).length = 3
#guard (serviceOpRowSlot dbGetUser).answer = userTy
#guard handlerStanceSlot getUserHandler = HandlerStance.implemented

/-! ## The laws -/

theorem getUserHandler_fits_of_exact : Handler.fits getUser getUserHandler = true :=
  Handler.fitsExactly_fits getUser getUserHandler (by decide)

theorem getUserHandler_clauses :
    Handler.Targets shopApi getUserHandler ∧
      Handler.AlphabetMatchesRequires shopApi getUserHandler ∧
      Handler.BodyWellTyped getUserHandler ∧
      ∀ e, Api.endpoint? shopApi "users" "getUser" = some e →
        Handler.Fits e getUserHandler :=
  (Handler.wellFormed_iff shopApi getUserHandler).mp getUserHandler_wf

theorem usersHandlers_clauses :
    Handlers.OnePerEndpoint shopApi usersHandlers ∧
      Handlers.Total shopApi usersHandlers ∧
      ∀ h ∈ usersHandlers.handlers, Handler.WellFormed shopApi h :=
  (Handlers.wellFormed_iff shopApi usersHandlers).mp usersHandlers_wf

/-! ## Emission, `isOk` only: the bytes are the harness's business -/

#guard (Handler.printBody getUserHandler).isOk
#guard (Handler.printBody getUserStub).isOk

end Test.Surface.HandlerFitsContract
