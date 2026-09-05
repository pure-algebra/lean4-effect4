/-
Executable witnesses for `E4-SURFACE-CE-088` through `E4-SURFACE-CE-110`.

Contract: `Test/contracts/surface-handler-fits.contract.md`. Frozen by the
handler breaker (plan §13.7 ruling 7) before the handler module exists; red
until wave 2d lands it.

A prior contract for the same subject exists at
`Test/contracts/surface-handler.contract.md` (commit `9f9e0e6`), claiming
`E4-SURFACE-CE-076` through `E4-SURFACE-CE-087`, which is why these rows start
at `088`. See finding H-0.

Pin: `effect` 4.0.0-rc.112, `node_modules/effect/src`: `Effect.ts:117`,
`:154-157`; `unstable/httpapi/HttpApiEndpoint.ts:584-586`, `:720-724`;
`unstable/http/HttpRouter.ts:853-857`;
`unstable/httpapi/HttpApiBuilder.ts:126`, `:137-141`, `:169-179`, `:219-221`,
`:241-252`, `:441`.

Plan §13.2 states one relation, `typeOf h.sig h.body = some e.effTy`, and the
attacks below are ordered so that the first one settles what the relation must
be. rc.112's handler slot is

    Effect<SuccessType<~Success> | HttpServerResponse, ~Error["Type"] | E, R>

with `Effect<out A, out E, out R>` covariant in all three parameters, so a
handler fits when its type is *below* the endpoint's. Equality refuses
programs rc.112 accepts, and the sharpest of them is the plan's own typed
stub.

Six rows below are not refusals but recorded non-claims and gaps: `094`
(the `HttpServerResponse` arm), `096` (the placement conflict), `097` (the
`ServiceRow` spelling gap) and `098` (the service-key gap) name what this
packet could not decide, and `085` and `086` name what `fits` cannot see. A
row that records a gap is still a row: it fixes the id so the gap cannot be
closed silently.

Every refusal receipt pins the exact `Refusal` value, never a Boolean.
`Handler.fits` and `Handler.fitsExactly` are pinned beside the refusal so the
Boolean and the clause name cannot drift apart.
-/

import Effect4.Program.Typing
import Effect4.Codegen.Print
import Test.Surface.Fixtures
import Test.Surface.HandlerFitsContract
-- Owed by wave 2d. The module path is finding H-1; the namespace is frozen.
import Effect4.Surface.Handler

set_option autoImplicit false

namespace Test.Counterexamples.Surface.HandlerFits

open Effect4 (ReferenceEntry ServiceKey)
open Effect4.Program (Ty Row EffTy Signature typeOf)
open Effect4.Machine.Env (Requirement)
open Effect4.Surface
open Test.Surface.Fixtures
open Test.Surface.HandlerFitsContract

/-! ## The relation itself -/

/--
`E4-SURFACE-CE-088`. Attacked statement: plan §13.2's
`Handler.fits e h := typeOf h.sig h.body = some e.effTy`, together with the
same section's "an endpoint with no handler emits a typed stub whose body is
`Effect.fail(new NotImplemented())` under the same declared type, so the
module typechecks either way". The two sentences contradict each other. The
stub's type is `Effect<never, NotImplemented, never>`; `getUser` demands
`Effect<User, NotFound, Db>`; the three channels disagree on all three, so
`fitsExactly` is `false` and the plan's own stub is refused by the plan's own
relation.

rc.112 accepts the stub precisely because the relation there is subsumption:
`never` is assignable to `User | HttpServerResponse`, `NotImplemented` is
absorbed by the free `E` of `HttpApiEndpoint.ts:586`, and `never` is
assignable to any `R` under `Effect<out A, out E, out R>` (`Effect.ts:117`,
`:154-157`).

Forced repair: `Handler.fits` is subsumption on the three channels;
`Handler.fitsExactly` keeps §13.2's equality and
`Handler.fitsExactly_fits` relates them, so the ruling of finding H-2 is a
choice between two frozen relations rather than a rewrite.
-/
def stubRefusedByEquality : Handler := Endpoint.stub "users" getUser shopAlphabet

#guard Handler.fitsExactly getUser stubRefusedByEquality = false
#guard Handler.fits getUser stubRefusedByEquality = true
#guard Handler.check shopApi stubRefusedByEquality = .ok ()

/-!
`E4-SURFACE-CE-089`. Attacked statement: "a handler whose program does not
have the endpoint's `Effect<A, E, R>` is refused". An implementation that
cannot fail has error `never`, which is *not* the endpoint's `NotFound`, and
equality refuses it. rc.112 admits it: `E` at `HttpApiEndpoint.ts:586` is a
free parameter that unifies with anything the handler does raise, and `never`
raises nothing.

Forced repair: clause 10 and clause 12 of `Handler.check` are containments,
not equations, so a narrower error is a fit. The endpoint keeps declaring
`404 NotFound` because the *client* type is derived from the endpoint's rows,
not from any handler's.
-/
#guard Handler.effTy? infallibleHandler
  = some ⟨userTy, Ty.never, Requirement.single dbKey⟩
#guard Handler.fitsExactly getUser infallibleHandler = false
#guard Handler.fits getUser infallibleHandler = true
#guard Handler.escapes getUser infallibleHandler = Ty.never
#guard Handler.check shopApi infallibleHandler = .ok ()

/-!
`E4-SURFACE-CE-090`. Attacked statement: "`requires` as the service keys of
the named services", with the handler's whole `typeOf` requirement compared
against it. `src/Effect4/Program/Typing.lean`'s `acquireRelease` and `forkScoped`
add `sig.scopeKey` to the requirement, and a row may declare it directly, so
any handler that opens a resource requires `Scope` on top of `Db`. rc.112
removes `Scope.Scope` twice: once from a handler's `R` through
`HttpApiEndpoint.ExcludeProvided` over `HttpRouter.Provided`
(`HttpApiEndpoint.ts:720-724`, `HttpRouter.ts:853-857`) and once from the
group layer (`HttpApiBuilder.ts:140`).

Forced repair: `Alphabet.provided` names the keys rc.112 supplies, and
`Handler.requires` subtracts them before clause 11 compares. A handler that
scopes a connection charges the deployment nothing.
-/
#guard (Handler.effTy? scopedHandler).map (fun t => t.requires)
  = some (Requirement.ofList [dbKey, scopeKey])
#guard Handler.requires scopedHandler = Requirement.single dbKey
#guard Handler.fitsExactly getUser scopedHandler = false
#guard Handler.fits getUser scopedHandler = true

/-!
`E4-SURFACE-CE-091`. The other direction of the requirement channel: a
handler that needs *fewer* services than the endpoint declares. `getUser`
declares `requires := ["Db"]`; a cached implementation performs nothing and
requires nothing. Equality refuses it; rc.112 admits it, because
`HandlerRequirements` (`HttpApiBuilder.ts:169-179`) only ever *adds* what the
handler needs to the layer and never demands that it need everything.

Forced repair: clause 11 is `Row.Subset (Handler.requires h) (endpoint's row)`,
one-sided. The converse, an endpoint declaring a service no handler uses, is
not a refusal here either: it is a deployment fact, and
`requirementUnprovided` in `surface-deploy.contract.md` is where an unbound
name is caught.
-/
#guard Handler.requires pureHandler = Requirement.empty
#guard Handler.fitsExactly getUser pureHandler = false
#guard Handler.fits getUser pureHandler = true

/-! ## The endpoint's type -/

/--
`E4-SURFACE-CE-092`. Attacked statement: "`errorTy` is the join of the error
entities' handles", with no law on `Ty.join`. `Endpoint.errors` is a list, and
`Handler.fits` compares the folded result by `DecidableEq`, so if `Ty.join`
were not commutative and associative then listing `404` before `429` and `429`
before `404` would give two different endpoint types and the same handler
would fit one endpoint and not the other.

`src/Effect4/Program/Eff.lean` proves exactly one theorem, `render_ofSpelling`, and
none about `join`. The property does hold: `join` sorts its members by the
injective `Ty.key` and drops duplicates. But it holds by inspection, not by
receipt.

Forced repair: the seven `Ty.join` laws of the contract's table are owed rows
against the `Syntax` lane (finding H-3), and until they land the batteries pin
the instances. This row is what makes the omission visible rather than
convenient.
-/
def errorsForward : Endpoint shopRefs :=
  { getUser with errors := [⟨404, .json notFoundBody⟩, ⟨409, .json addressBody⟩] }
def errorsReversed : Endpoint shopRefs :=
  { getUser with errors := [⟨409, .json addressBody⟩, ⟨404, .json notFoundBody⟩] }

#guard Endpoint.errorTy? errorsForward = Endpoint.errorTy? errorsReversed
#guard Endpoint.effTy? errorsForward shopAlphabet
  = Endpoint.effTy? errorsReversed shopAlphabet

/--
`E4-SURFACE-CE-093`. The idempotence half of the same attack, which a
sort-only join would still get wrong: one entity used at two statuses. A
`NotFound` at `404` and a `NotFound` at `410` must contribute *one* union
member, not two. A `Ty.union NotFound NotFound` is a different value from
`Ty.handle "NotFound"` under `DecidableEq`, so a handler that fails with
`NotFound` would fit neither.

Forced repair: `Ty.join` deduplicates by structural equality before ordering
(`Ty.insertMember`), and `Ty.join_idem` is one of the owed laws.
-/
def duplicatedErrorEntity : Endpoint shopRefs :=
  { getUser with errors := [⟨404, .json notFoundBody⟩, ⟨410, .json notFoundBody⟩] }

#guard Endpoint.errorTy? duplicatedErrorEntity = some notFoundTy
#guard Endpoint.effTy? duplicatedErrorEntity shopAlphabet
  = some ⟨userTy, notFoundTy, Requirement.single dbKey⟩

/--
`E4-SURFACE-CE-094`. Attacked statement: "one success: the entity handle
`Ty.handle name`". A success body is a `Sch refs .json`, which is any JSON
representation, not necessarily a bare `reference`. `createUser`'s request
body is an inline struct in the same fixture, and a success body may be one
too. There is no entity for it, so there is no name, so there is no handle,
and a `Ty` for it would have to be invented.

Inventing one is the bug: `Ty` has no node for a struct, so the invention is
either a lie (`.handle "unknown"`, which is already what
`Typing.snapshotChildren` is reduced to) or a widening (`.string`), and either
makes two different bodies have one type, so `fits` stops discriminating.

Forced repair: `ResponseBody.ty?` is partial, `Endpoint.answerTy?` and
`Endpoint.errorTy?` propagate the `none`, and clauses 7 and 8 refuse the
endpoint by name. An endpoint whose responses are not entities is well formed
as an endpoint and simply has no handler type, which is the honest answer.
-/
def inlineSuccessBody : Endpoint shopRefs :=
  { getUser with success := [⟨200, .json newUserBody⟩] }

/-- The same endpoint wired into an api, so clause 7 has a handler to refuse. -/
def inlineSuccessApi : Api shopRefs :=
  { shopApi with groups := [{ usersGroup with endpoints := [inlineSuccessBody] }] }

#guard Endpoint.answerTy? inlineSuccessBody = none
#guard Endpoint.effTy? inlineSuccessBody shopAlphabet = none
-- The endpoint is well formed as an endpoint. It simply has no handler type.
#guard Endpoint.check inlineSuccessBody = .ok ()
#guard Handler.fits inlineSuccessBody getUserHandler = false
#guard Handler.check inlineSuccessApi getUserHandler
  = .error (.answerTypeUnrepresentable "getUser")

/--
`E4-SURFACE-CE-095`. Attacked statement: "`answerTy` for zero successes".
`Endpoint.success` is a list (plan §13.1), so the empty list is expressible,
and the join of nothing is `.never`. An endpoint with no success would then
demand a handler that never returns, and the typed stub would be the *only*
handler that fits it.

Forced repair: the clause is not in `Handler.check` but in `Endpoint.check`
clause 10, `successEmpty` (plan §13.7 ruling 5, already in the alphabet). This
row records that `answerTy?` stays total and returns `some .never` rather than
becoming a second place that decides emptiness, which would be two spellings
of one fact (plan §13.6 rule 2).
-/
def noSuccess : Endpoint shopRefs := { getUser with success := [] }

#guard Endpoint.check noSuccess = .error (.successEmpty "getUser")
#guard Endpoint.answerTy? noSuccess = some Ty.never
#guard Handler.fits noSuccess getUserHandler = false

/--
`E4-SURFACE-CE-096`. Attacked statement: "several: their `Ty.join`". Suppose
an endpoint declares a `200 User` and a `201 Address`. Its answer is then
`Address | User`. No `Eff` control construct can produce that answer:
`branch`, `catchCause`, `matchCause`, `choose` and `raceAll` all merge answers
through `EffTy.joinAnswer` (`src/Effect4/Program/Typing.lean:38-42`), which is
`none` unless the two answers are equal or one is `never`, and a `gen` with
two `return`s of different types is refused the same way. So the *only* way to
inhabit a multi-success endpoint's type is a single row that already answers
the union, or an atom that does.

That is the opposite of what a multi-success endpoint is for: the handler is
supposed to *choose* which success it returns.

Forced repair, for the ruling: either v1 keeps one success per endpoint
(plan §12 open question 2 answered "no"), or `Endpoint.answerTy?` for several
successes is not their `Ty.join` and `fits` needs a per-status relation. This
packet freezes the `Ty.join` reading of §13.2 as written and pins the
consequence, so whichever way the ruling goes the receipt changes visibly.
-/
def twoSuccesses : Endpoint shopRefs :=
  { getUser with success := [⟨200, .json userBody⟩, ⟨201, .json addressBody⟩] }

#guard Endpoint.answerTy? twoSuccesses
  = some (Ty.join userTy (Ty.handle "Address"))
#guard Ty.render (Ty.join userTy (Ty.handle "Address")) = "Address | User"

/-- A second `Db` row answering the other entity, so a branch between them is
the natural handler of a two-success endpoint. -/
def dbGetAddress : ServiceOp :=
  { service := "Db", op := "getAddress"
  , row := ⟨"getAddress", "db.getAddress", .call, [], .sync, .string, Ty.handle "Address"
      , notFoundTy, [dbKey], "fixture: the shop Db service"⟩ }

/-- The branch is ill typed: `EffTy.joinAnswer` is `none` on two distinct
handles, so no control construct reaches `Address | User`. -/
def branchingBody : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with ops := [dbGetUser, dbGetAddress] }
  , body := .branch (.lit (.bool true))
      (.perform 0 (.lit (.str "u1"))) (.perform 1 (.lit (.str "a1"))) }

#guard EffTy.joinAnswer userTy (Ty.handle "Address") = none
#guard Handler.effTy? branchingBody = none

/-- The only inhabitant of a two-success endpoint's type is a row that already
answers the union, which is the opposite of choosing between the successes. -/
def unionRow : ServiceOp :=
  { service := "Db", op := "getEither"
  , row := ⟨"getEither", "db.getEither", .call, [], .sync, .string
      , Ty.join userTy (Ty.handle "Address"), notFoundTy, [dbKey]
      , "fixture: the shop Db service"⟩ }

def unionHandler : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with ops := [unionRow] }
  , body := .perform 0 (.lit (.str "u1")) }

#guard (Handler.effTy? unionHandler).map (fun t => t.answer)
  = some (Ty.join userTy (Ty.handle "Address"))
#guard Handler.fitsExactly twoSuccesses unionHandler = true

-- A single-answer handler still fits by subsumption, which is what makes the
-- unreachability of the union answer easy to miss.
#guard Handler.fits twoSuccesses getUserHandler = true
#guard Handler.fitsExactly twoSuccesses getUserHandler = false

/-! ## What `fits` cannot see -/

/--
`E4-SURFACE-CE-097`. Attacked statement: "the service alphabet of a handler is
the `effect_signature` families the endpoint requires". `Signature.rowOf`
answers a `Row`, and a `Row` carries a `spelling` beside its types with no
relation between them. Two alphabets whose rows have the same request, answer,
error and requirement keys and completely unrelated spellings are
indistinguishable to `typeOf`, so `fits` is true of a handler that calls
`totallyUnrelated.thing` exactly as of one that calls `db.getUser`.

`fits` is therefore a claim about types and never about which service is
spoken to. Saying otherwise is the "run-agreement" overreach `AGENTS.md`
forbids.

Forced repair: clauses 5 and 6 tie the alphabet's *service names* to
`e.requires`, which is as far as the rows reach, and the contract's "what this
contract does not claim" says the rest in words. Tying a row's `spelling` to a
`ServiceRow`'s method is `E4-SURFACE-CE-109` and is an owed row.
-/
def lyingOp : ServiceOp :=
  { service := "Db", op := "getUser"
  , row := ⟨"getUser", "totallyUnrelated.thing", .call, [], .sync, .string, userTy
      , notFoundTy, [dbKey], "fixture: a row that lies"⟩ }

def lyingHandler : Handler :=
  { getUserHandler with alphabet := { shopAlphabet with ops := [lyingOp] } }

#guard Handler.effTy? lyingHandler = Handler.effTy? getUserHandler
#guard Handler.fits getUser lyingHandler = true
#guard Handler.check shopApi lyingHandler = .ok ()
#guard (Alphabet.rowAt lyingHandler.alphabet 0).spelling = "totallyUnrelated.thing"

/-!
`E4-SURFACE-CE-098`. Attacked statement: plan §13.2's
`structure Handler (refs) (Op : Type) where sig : Signature Op`.
`Signature Op` has three fields, two of them Lean functions
(`rowOf : Op → Row`, `atomOf : String → List Ty → Option Ty`). A structure with
a function field has no `DecidableEq`, no `Json` view, no `Canonical` address
and no `#guard`, so a `Handler` so spelled is not a surface carrier at all: it
cannot be stored, compared, or checked by `decide`, and `AGENTS.md`
"Representation rules" and plan §4's carrier form both exclude it.

The `Op : Type` parameter is the same problem in the index: a carrier
parameterised by an arbitrary `Type` cannot be a row of a registry.

Forced repair: `Alphabet` is first-order (`List ServiceOp`, `List AtomSig`, a
`ServiceKey`), `Op` is `Nat`, and `Alphabet.signature` *derives* the
`Signature` at the call to `typeOf`. Nothing stores a function. The witness is
the ascribed slot definitions in `Test/Surface/HandlerFitsContract.lean`
plus these two receipts, which cannot even be written for the §13.2 spelling.
-/
#guard (getUserHandler == getUserHandler) = true
#guard (getUserHandler == lyingHandler) = false

/-! ## The handler's place in the api -/

/--
`E4-SURFACE-CE-100`. Attacked statement: `Handler.endpoint : String`, with
nothing checking it names anything. rc.112 makes this a type error twice:
`handle<Identifier extends keyof EndpointsByIdentifier>`
(`HttpApiBuilder.ts:283-296`) rejects an unknown key, and
`HttpApiBuilder.group`'s `groupIdentifier` is
`HttpApiGroup.Identifier<Groups>` (`:126-131`). A Lean row with a free string
would emit `handlers.handle("getUsr", …)`, which rc.112's own types reject at
the pin and which no amount of `fits` sees, because `fits` never looks at the
api.

Forced repair: `Handler.check` takes the whole `Api` and clauses 1 and 2 are
lookups, before any typing clause runs.
-/
def wrongGroup : Handler := { getUserHandler with group := "admins" }
def wrongEndpoint : Handler := { getUserHandler with endpoint := "getUsr" }

#guard Handler.check shopApi wrongGroup = .error (.handlerGroupAbsent "getUser" "admins")
#guard Handler.check shopApi wrongEndpoint = .error (.handlerEndpointAbsent "users" "getUsr")

/--
`E4-SURFACE-CE-101`. Attacked statement: a group's handlers are a list, so one
endpoint may appear twice. rc.112 makes the second `handle` call ill-typed:
`NotHandledIdentifier` (`HttpApiBuilder.ts:219-221`) intersects the identifier
with `never` once it is in `HandledIdentifiers`, applied at `:286` and `:320`.
At run time the second registration would silently win, because `handlers` is
a `Map<string, HandlerRuntime>` (`:277`) keyed by identifier.

Forced repair: `Handlers.check` clause 2. The refusal names the group and the
endpoint, so a user reads `handlerDuplicate users getUser`.
-/
def doubledHandlers : Handlers :=
  { usersHandlers with
    handlers := [getUserHandler, createUserHandler, deleteUserHandler, getUserHandler] }

#guard Handlers.check shopApi doubledHandlers
  = .error (.handlerDuplicate "users" "getUser")

/-!
`E4-SURFACE-CE-102`. Attacked statement: a group with no handlers still
typechecks because of the stub. It does, but only if something *builds* the
stubs. rc.112 refuses the group otherwise, and refuses it in an unusual way:
`ValidateHandlersReturn` (`HttpApiBuilder.ts:246-252`) replaces the return
type with the string literal `` `Endpoint not handled: ${Missing & string}` ``,
so the failure is a type mismatch against a message rather than an error with
a location.

Forced repair: `Handlers.check` clause 3 refuses by name, and
`Handlers.complete` is the function that fills the gap with `Endpoint.stub`.
Completion is a fill and not a replacement: an endpoint that already has a
handler keeps it.
-/
#guard Handlers.check shopApi emptyHandlers
  = .error (.endpointNotHandled "users" "getUser")
#guard Handlers.check shopApi partialHandlers
  = .error (.endpointNotHandled "users" "createUser")
#guard ((Handlers.complete shopApi partialHandlers shopAlphabet).map
  fun hs => Handlers.check shopApi hs) = some (.ok ())

/--
`E4-SURFACE-CE-103`. Attacked statement: `body : Eff Op` with `Op` the
alphabet's positions. With `Op := Nat` (the repair of `E4-SURFACE-CE-098`) a
`perform` may name a position the alphabet does not have. A `Signature` whose
`rowOf` returns a default row for an out-of-range index would give that
`perform` a type, and the handler would fit while naming an operation that
does not exist.

Forced repair: `Handler.check` clause 4 walks the body and refuses the first
out-of-range index by number, *before* clause 9 types anything. The default
row `Alphabet.rowAt` returns out of range is therefore never load-bearing.
-/
def outOfAlphabet : Handler := { getUserHandler with body := .perform 7 (.lit (.str "u1")) }

#guard Handler.check shopApi outOfAlphabet
  = .error (.operationOutOfAlphabet "getUser" 7)

/--
`E4-SURFACE-CE-104`. Attacked statement: "the rows of the services the
endpoint `requires`, from their `ServiceRow`s", with the two never compared. A
handler may carry an alphabet for `RateLimit` while its endpoint requires only
`Db`, or an endpoint may require `RateLimit` while the handler's alphabet has
no row for it. In the first direction the emitted module imports a service
class the deployment need not bind; in the second the handler cannot be
written at all and the omission is invisible until the body is typed.

Forced repair: clauses 5 and 6, set equality in both directions, in that
order, before any typing clause.
-/
def rateOp : ServiceOp :=
  { service := "RateLimit", op := "check"
  , row := ⟨"check", "rateLimit.check", .call, [], .sync, .string, .unit, .never
      , [rateKey], "fixture: the shop RateLimit service"⟩ }

def extraService : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with ops := [dbGetUser, rateOp] } }

#guard Handler.check shopApi extraService
  = .error (.alphabetServiceUnrequired "getUser" "RateLimit")

def missingService : Handler :=
  { getUserHandler with alphabet := { shopAlphabet with ops := [rateOp] } }
def rateRequiringEndpoint : Endpoint shopRefs :=
  { getUser with requires := ["Db", "RateLimit"] }

#guard Handler.check { shopApi with
    groups := [{ usersGroup with endpoints := [rateRequiringEndpoint] }] }
    getUserHandler
  = .error (.requirementWithoutAlphabet "getUser" "RateLimit")

/--
`E4-SURFACE-CE-099`. Attacked statement: "`requires` is a list of service
names" with no distinctness clause, and an alphabet indexed by service name.
The requirement row itself is safe: `Requirement` is
`Effect4.Data.Row ServiceKey`, a canonical strictly ascending list, so
`Requirement.ofList [k, k]` is `Requirement.single k` and a repeated name
cannot survive into `EffTy.requires`.

The damage is in the alphabet. Two `ServiceOp`s of one service with one `op`
name are two different rows the printer will spell identically, so the emitted
service class has a duplicate method and the two `perform` positions become
indistinguishable in the generated code even though `typeOf` keeps them apart.

Forced repair: clause 3 refuses the duplicate by service and operation name.
The `requires` duplicate needs no clause of its own, and this row records that
the absence is deliberate rather than an oversight.
-/
def duplicateOpName : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with
      ops := [dbGetUser, { dbGetUser with
        row := { dbGetUser.row with spelling := "db.getUserAgain" } }] } }

#guard Handler.check shopApi duplicateOpName
  = .error (.alphabetOpDuplicate "Db" "getUser")
#guard Requirement.ofList [dbKey, dbKey] = Requirement.single dbKey

/-! ## The typing clauses -/

/--
`E4-SURFACE-CE-105`. Attacked statement: "emission is `Syntax.Print.print` of
the body into the `handle` slot". `fits` says nothing about printability.
`src/Effect4/Codegen/Print.lean` refuses two classes of program by name: `choose`,
which is a flows-only constructor with no Effect combinator, and five internal
fiber actions with no public rc.112 export. Both are well typed. So a handler
can fit its endpoint perfectly and emit nothing at all, and a generator that
assumed `fits` implied bytes would produce a module missing a route.

Forced repair: `Handler.printBody` returns the printer's own `PrintRefusal`,
and `handlerBodyUnprintable` is in the refusal alphabet for the emitter to
use. The check does *not* refuse an unprintable handler, because a well-typed
handler is a legitimate model row even where the v1 printer has no spelling;
that is the same stance `surface-emit.contract.md` takes for `multipart` and
`stream`.
-/
def unprintableBody : Handler :=
  { getUserHandler with
    body := .choose 3 (.perform 0 (.lit (.str "u1"))) (.perform 0 (.lit (.str "u2"))) }

#guard Handler.fits getUser unprintableBody = true
#guard Handler.check shopApi unprintableBody = .ok ()
#guard Handler.printBody unprintableBody = .error (.choose 3)

/--
`E4-SURFACE-CE-107`. Attacked statement: `Handler.fits : … → Bool` as the
packet's observation. `Test/contracts/surface-facts.contract.md` is explicit
that "a battery that pinned `= false` would pass for a carrier that refused
the right term for the wrong reason", and `fits` is exactly such a Boolean: it
collapses four distinct failures (no answer type, an ill-typed body, a wrong
answer, an unprovided requirement) into one `false`.

Forced repair: `Handler.check : Except Refusal Unit` is the observation every
negative receipt in this packet pins, and `fits` is a Bool projection used
only where a positive fact is wanted. This row is the receipt that the four
failures are four refusals.
-/
def wrongAnswer : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with
      ops := [{ dbGetUser with row := { dbGetUser.row with answer := Ty.string } }] } }

def undeclaredError : Handler :=
  { getUserHandler with
    alphabet := { shopAlphabet with
      ops := [{ dbGetUser with
        row := { dbGetUser.row with error := Ty.handle "RateLimited" } }] } }

def illTyped : Handler :=
  { getUserHandler with body := .perform 0 (.lit (.nat 1)) }

#guard Handler.fits getUser wrongAnswer = false
#guard Handler.fits getUser illTyped = false
#guard Handler.check shopApi wrongAnswer = .error (.handlerAnswerMismatch "getUser")
#guard Handler.check shopApi illTyped = .error (.handlerBodyIllTyped "getUser")
#guard Handler.check inlineSuccessApi getUserHandler
  = .error (.answerTypeUnrepresentable "getUser")
#guard Handler.check shopApi undeclaredError
  = .error (.handlerErrorUndeclared "getUser")
#guard Handler.escapes getUser undeclaredError = Ty.handle "RateLimited"
-- and the same body as a stub is admitted, which is the whole of clause 12.
#guard Handler.check shopApi { undeclaredError with stance := .stub } = .ok ()

/-!
`E4-SURFACE-CE-106`. Recorded non-claim. rc.112's handler answer is
`SuccessType<~Success> | HttpServerResponse` (`HttpApiEndpoint.ts:586`): a
handler may return a raw `HttpServerResponse` instead of the endpoint's
success value, at any endpoint, and `handleRaw` (`HttpApiBuilder.ts:317-325`)
is a second way in. `Ty` has no node for `HttpServerResponse` and the surface
has no row for a raw response, so `Endpoint.answerTy?` is strictly narrower
than the type rc.112 demands.

The consequence is one-sided and worth stating precisely: every handler this
packet admits is one rc.112 admits, and some handlers rc.112 admits are
unrepresentable here. That is a sound refusal and an incomplete admission, and
it is recorded as a non-claim rather than as a clause, because a clause would
assert the surface had looked at something it cannot spell.

Forced repair: none in this packet. The row fixes the id so that adding raw
responses later is a visible change with a place to land.
-/
#guard Endpoint.answerTy? getUser = some userTy
#guard Ty.sub userTy (Ty.join userTy (Ty.handle "HttpServerResponse")) = true
#guard Ty.sub (Ty.join userTy (Ty.handle "HttpServerResponse")) userTy = false

/-! ## The three gaps this packet could not close -/

/--
`E4-SURFACE-CE-108`. Recorded gap, and finding H-1. Plan §2: "`Effect4.Surface.*`
… does **not** import `Effect4.Char.*`, `Effect4.Machine.*`, `Effect4.Program.*`,
or anything under `Effect4.Runtime`." Plan §13.2: "`src/Effect4/Surface/Handler.lean`
(wave 2d; imports `Effect4.Program.Typing` and `.Print`)". `EffTy` is
`Effect4.Program` and its `requires` field is `Effect4.Machine.Env.Requirement`,
so §13.2 crosses the fence twice.

This is a placement question and a breaker does not answer it. Everything in
this packet is stated in namespace `Effect4.Surface`, which each candidate
resolution can honour, and the batteries' owed `import` line is the only place
a ruling touches.

Forced repair: a coordinator ruling. The receipt below is the one fact that is
true whichever way it goes: the type the surface must produce is the landed
`EffTy`, and no second copy of it is admissible under plan §13.6 rule 2.
-/
def endpointTypeIsEffTy :
    ∀ refs : List ReferenceEntry, Endpoint refs → Alphabet → Option EffTy :=
  @Endpoint.effTy?

#guard (endpointTypeIsEffTy shopRefs getUser shopAlphabet).isSome

/-!
`E4-SURFACE-CE-109`. Recorded gap. Plan §13.2: "their `ServiceRow`s already
carry the TypeScript spellings". They carry spellings and nothing else usable
here: `Effect4.Target.EffectV4.OpRow` stores `answer : String` and
`tsAnswer : String`, rendered TypeScript text, while `Effect4.Program.Row`
needs `answer : Ty`, `error : Ty` and `requires : List ServiceKey`. Going from
one to the other means parsing TypeScript type text back into `Ty`, which is a
lane nobody owns and which `Ty.render` is not injective enough to invert
(`Ty.nat` and `Ty.int` both render `"number"`).

Forced repair: `ServiceOp` carries a `Syntax.Row` written beside the
`ServiceRow`, and the *agreement* of the two spellings is an owed row, not a
theorem this packet can state. `Alphabet.check` therefore ties service names
and nothing finer, which is what `E4-SURFACE-CE-097` measures.
-/
#guard Ty.render Ty.nat = Ty.render Ty.int
#guard (Ty.nat == Ty.int) = false

/-!
`E4-SURFACE-CE-110`. Recorded gap, and finding H-4. Plan §13.2: "with
`requires` as the service keys of the named services". `Endpoint.requires` is
`List String`; a `ServiceKey` is `⟨ServiceName, ServiceTypeCode⟩`, two `Nat`s
(`src/Effect4/Machine/Key.lean`), and that file says outright that `Nat` rather
than `String` "is an ordering decision" and that codes are never minted from
names. So there is no function from a service name to a key anywhere in the
estate, and `Endpoint.effTy` cannot be a function of the endpoint alone.

Forced repair: `Endpoint.effTy?` takes the `Alphabet`, whose rows already
carry their `ServiceKey`s, and `Alphabet.requirementOf` is the only bridge.
The refusal that names an unprovided key therefore has to spell it as two
`Nat`s, `handlerRequirementUnprovided endpoint name code`, which is ugly and
honest.
-/
#guard Alphabet.requirementOf shopAlphabet ["Db"] = Requirement.single dbKey
#guard Alphabet.requirementOf shopAlphabet ["Absent"] = Requirement.empty
-- The alphabet is the only place a name becomes a key, so a handler whose
-- alphabet covers `RateLimit` but not `Db` is refused for the missing half.
#guard Handler.check
    { shopApi with groups := [{ usersGroup with endpoints := [rateRequiringEndpoint] }] }
    missingService
  = .error (.requirementWithoutAlphabet "getUser" "Db")

end Test.Counterexamples.Surface.HandlerFits
