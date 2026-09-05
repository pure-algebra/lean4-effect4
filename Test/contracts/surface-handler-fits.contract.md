# Surface handler fit contract

Status: breaker packet, red, 2026-09-04 (plan §13.7 ruling 7, for wave 2d of
`docs/research/2026-09-04-surface-library-plan.md` §13.2)

**Collision notice, read first.** A contract for this subject already exists at
`Test/contracts/surface-handler.contract.md`, landed in commit `9f9e0e6` by the
wave-1b breaker, claiming `E4-SURFACE-CE-076` through `E4-SURFACE-CE-087`. The
repository's own coordination record says it does not: `COORDINATION.md`'s
checkpoint says "the breaker's handler packet (§13.7 ruling 7) not started",
`Test/contracts/surface-api.contract.md` says handlers have "no contract in
this packet", and `REGISTER.md` at that commit ends at `E4-SURFACE-CE-075` with
no row for `076` through `087`. This packet was dispatched on that record. It
is therefore filed beside the prior contract rather than over it, its rows
start at `E4-SURFACE-CE-088` so the prior contract's claimed block stays free,
and "Reconciliation with `surface-handler.contract.md`" below is the row by row
disagreement. Which packet governs is a coordinator ruling (finding H-0).

Implementation (owed): the handler module. **Its path is the subject of finding
H-1 and is not frozen here**; the namespace is. See "Placement" below.

Battery: `Test/Surface/HandlerFitsContract.lean`

Counterexamples: `E4-SURFACE-CE-088` through `E4-SURFACE-CE-110`

Witnesses: `Test/Counterexamples/Surface/HandlerFits.lean`

Shared: `Test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet; `Test/contracts/surface-api.contract.md` owns `Endpoint`, `Group`,
`Api`, `Response` and `ResponseBody`. This contract owns the handler carrier,
the endpoint's type projections, the fit relation and their clause order.

Pin: `effect` 4.0.0-rc.112, `node_modules/effect/src`:
`unstable/httpapi/HttpApiBuilder.ts`, `unstable/httpapi/HttpApiEndpoint.ts`,
`unstable/http/HttpRouter.ts`, `Effect.ts`.

Landed carriers this contract joins onto, read but not edited:
`src/Effect4/Program/Eff.lean` (`Ty`, `Row`, `Eff`, `Term`), `src/Effect4/Program/Typing.lean`
(`EffTy`, `Signature`, `typeOf`), `src/Effect4/Codegen/Print.lean` (`print`,
`PrintRefusal`), `src/Effect4/Machine/Context.lean` (`Requirement`),
`src/Effect4/Machine/Key.lean` (`ServiceKey`), `src/Effect4/Data/Row.lean` (`Row.Subset`).

## Purpose

Plan §13.2 makes one claim: an endpoint's rows already determine the
`Effect<Success, Error, Requires>` that rc.112 will demand of its handler, and
the estate already owns that shape as `Effect4.Syntax.EffTy`. `Handler.fits`
is the typed hole: a program whose type does not answer the endpoint's is
refused before any bytes exist.

The claim is right about the carrier and wrong about the relation. rc.112
declares `Effect<out A, out E = never, out R = never>` (`Effect.ts:117`) with
all three parameters covariant (`Effect.ts:154-157`), and the handler slot is

```ts
export type Handler<Endpoint extends Constraint, E, R> = (
  request: Simplify<Endpoint["~Request"]>
) => Effect<SuccessType<Endpoint["~Success"]> | HttpServerResponse, Endpoint["~Error"]["Type"] | E, R>
```

(`HttpApiEndpoint.ts:584-586`). A handler therefore fits when its type is
*below* the endpoint's, not when it is equal to it: fewer errors fit, fewer
requirements fit, and the free `E` and `R` are collected by the group layer
(`HttpApiBuilder.ts:137-141`, `:169-179`). Equality refuses programs rc.112
accepts, including the plan's own typed stub (`E4-SURFACE-CE-088`). This
contract freezes subsumption as `fits`, keeps equality as `fitsExactly`, and
files the choice as finding H-2 for a coordinator ruling.

The other half of the claim is that `Handler` is a surface carrier. As §13.2
spells it, it is not: `Signature Op` is a record of three Lean fields, two of
them functions (`rowOf : Op → Row`, `atomOf : String → List Ty → Option Ty`),
which `AGENTS.md` "Representation rules" and plan §4 both exclude from stored
program content. This contract replaces the field with a first-order
`Alphabet` and derives the `Signature` from it (`E4-SURFACE-CE-098`), which is
also what resolves the service-key gap: `Endpoint.requires` holds `String`s
and `Requirement` holds `ServiceKey`s, which are pairs of `Nat`
(`src/Effect4/Machine/Key.lean`), and nothing in the slice maps one to the other
(`E4-SURFACE-CE-110`).

## Placement, and why this contract does not fix it

Plan §2 says `Effect4.Surface.*` "does **not** import `Effect4.Char.*`,
`Effect4.Deep.*`, `Effect4.Syntax.*`, or anything under `Effect4.Runtime`".
Plan §13.2 puts `Endpoint.effTy : Endpoint refs → EffTy` in
`src/Effect4/Surface/Handler.lean` over `Effect4.Syntax.Typing`. `EffTy` is
`Effect4.Syntax`, and its `requires` field is `Effect4.Deep.Env.Requirement`,
so §13.2 breaks §2 on two edges at once. That is finding H-1 and it needs a
ruling, not a breaker's decision (`E4-SURFACE-CE-108`).

Everything frozen below is stated in **namespace `Effect4.Surface`**, which
every candidate resolution can honour: a module under `Effect4/Surface/` with
§2 amended, a third module under a new area that imports both and declares
`namespace Effect4.Surface`, or a split where the row-to-type functions live
on the `Syntax` side and the surface hands them rows. Only the battery's
`import` line changes between them, and the battery marks that line.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
open Effect4.Syntax (Ty Row Eff EffTy Signature typeOf)
open Effect4.Deep.Env (Requirement)
open Effect4 (ServiceKey ReferenceEntry)

/-! ### Subsumption on the three channels -/

/-- `a` is below `b` when every union member of `a` is a union member of `b`.
This is rc.112's assignability on the `A` and `E` parameters of
`Effect<out A, out E, out R>` (`Effect.ts:117`, `:154-157`) restricted to the
union fragment `Ty` can express. -/
def Ty.sub (a b : Ty) : Bool

def Ty.Sub (a b : Ty) : Prop := Ty.sub a b = true

/-- The members of `a` that `b` does not have: what rc.112 collects into the
free `E` of `HttpApiEndpoint.ts:586` and reports as `Handlers.Error<Return>`
in the group layer's error channel (`HttpApiBuilder.ts:139`). -/
def Ty.minus (a b : Ty) : Ty

/-! ### The first-order service alphabet -/

/-- One operation a handler may `perform`, with the service it belongs to.
`row` is the landed `Effect4.Syntax.Row`: request, answer, error, requirement
keys and the rc.112 citation. -/
structure ServiceOp where
  service : String
  op      : String
  row     : Row
deriving DecidableEq, Repr

/-- A pure atom's signature, first-order, so `Signature.atomOf` is derived and
not stored. `NotImplemented` lives here, which is what makes the typed stub of
§13.2 well typed at all (`E4-SURFACE-CE-088`). -/
structure AtomSig where
  name   : String
  params : List Ty
  answer : Ty
deriving DecidableEq, Repr

/-- The alphabet a handler body is typed against: first-order data, so a
`Handler` has `DecidableEq`, a `json` view and a store address like every
other surface carrier. -/
structure Alphabet where
  ops      : List ServiceOp
  atoms    : List AtomSig := []
  scopeKey : ServiceKey
deriving DecidableEq, Repr

def Alphabet.services : Alphabet → List String
def Alphabet.rowAt : Alphabet → Nat → Row
def Alphabet.atomOf : Alphabet → String → List Ty → Option Ty

/-- The derived typing signature over `Op := Nat`. Positions outside `ops` are
refused by clause 4 of `Handler.check`, never by a default row's type. -/
def Alphabet.signature (a : Alphabet) : Signature Nat

/-- Every requirement key the named services carry. This is the only bridge
from `Endpoint.requires : List String` to `Requirement`'s `ServiceKey`s
(finding H-4). -/
def Alphabet.requirementOf (a : Alphabet) (services : List String) : Requirement

/-! ### The endpoint's type -/

/-- The `Ty` of one response body: `.unit` for `void`, the entity handle for a
`json` body that is a bare `reference`, `none` for any other body. `none` is
the honest answer for an inline struct: there is no entity, so there is no
handle (`E4-SURFACE-CE-094`). -/
def ResponseBody.ty? {refs : List ReferenceEntry} : ResponseBody refs → Option Ty

/-- The endpoint's answer: the `Ty.join` of its successes' types, `.never` for
none. Independent of the order of `e.success` by `Ty.join_comm` and
`Ty.join_assoc` (finding H-3). -/
def Endpoint.answerTy? {refs : List ReferenceEntry} (e : Endpoint refs) : Option Ty

/-- The endpoint's error: the `Ty.join` of its errors' types, `.never` for
none. -/
def Endpoint.errorTy? {refs : List ReferenceEntry} (e : Endpoint refs) : Option Ty

/-- `Effect<A, E, R>` as the endpoint demands it, given the alphabet that
supplies the service keys. -/
def Endpoint.effTy? {refs : List ReferenceEntry}
    (e : Endpoint refs) (a : Alphabet) : Option EffTy

/-! ### The keys rc.112 provides, which never count against a handler -/

/-- `HttpRouter.Provided` (`HttpRouter.ts:853-857`): the request, the scope,
the parsed search params and the route context. rc.112 removes them from a
handler's `R` at `HttpApiEndpoint.ts:720-724` and removes `Scope.Scope` again
from the group layer at `HttpApiBuilder.ts:140`. A handler that opens a scope
is therefore not requiring a service (`E4-SURFACE-CE-090`). -/
def Alphabet.provided (a : Alphabet) : Requirement

/-! ### The handler -/

inductive HandlerStance
  /-- A body the author wrote. -/
  | implemented
  /-- The typed stub of §13.2, `Effect.fail(new NotImplemented())`. -/
  | stub
deriving DecidableEq, Repr

structure Handler where
  group    : String
  endpoint : String
  stance   : HandlerStance := .implemented
  alphabet : Alphabet
  body     : Eff Nat
deriving DecidableEq

def Handler.effTy? (h : Handler) : Option EffTy :=
  typeOf h.alphabet.signature h.body

/-- The requirement a handler actually charges the deployment: what its body
performs, less what rc.112 provides. -/
def Handler.requires (h : Handler) : Requirement

/-- The errors the body may raise that the endpoint does not declare. rc.112
does not refuse them; it puts them in the group layer's error channel
(`HttpApiBuilder.ts:139`). The surface reports them as data so the emitter can
spell that channel. -/
def Handler.escapes {refs : List ReferenceEntry}
    (e : Endpoint refs) (h : Handler) : Ty

def Handler.errorsDeclared {refs : List ReferenceEntry}
    (e : Endpoint refs) (h : Handler) : Bool

/-- The fit of §13.2, repaired to rc.112's covariance: the body answers within
the endpoint's answer and requires within the endpoint's requirement. -/
def Handler.fits {refs : List ReferenceEntry}
    (e : Endpoint refs) (h : Handler) : Bool

/-- §13.2 as literally written: `typeOf h.sig h.body = some e.effTy`. Retained
so the ruling of finding H-2 has both relations to choose between, and so the
implication below is a theorem rather than a comment. -/
def Handler.fitsExactly {refs : List ReferenceEntry}
    (e : Endpoint refs) (h : Handler) : Bool

theorem Handler.fitsExactly_fits {refs : List ReferenceEntry}
    (e : Endpoint refs) (h : Handler) :
    Handler.fitsExactly e h = true → Handler.fits e h = true

/-! ### The stub -/

/-- The atom every alphabet needs for the typed stub to be well typed, and its
handle type. -/
def notImplementedAtom : AtomSig
def notImplementedTy : Ty

def Endpoint.stub {refs : List ReferenceEntry}
    (groupId : String) (e : Endpoint refs) (a : Alphabet) : Handler

theorem Endpoint.stub_fits {refs : List ReferenceEntry}
    (groupId : String) (e : Endpoint refs) (a : Alphabet) :
    (Endpoint.answerTy? e).isSome = true →
      Handler.fits e (Endpoint.stub groupId e a) = true

/-! ### The checks -/

def Handler.check {refs : List ReferenceEntry}
    (a : Api refs) (h : Handler) : Except Refusal Unit
def Handler.WellFormed {refs : List ReferenceEntry}
    (a : Api refs) (h : Handler) : Prop := Handler.check a h = .ok ()

/-- The handler set of one group, which is what `HttpApiBuilder.group` builds
(`HttpApiBuilder.ts:126`). -/
structure Handlers where
  group    : String
  handlers : List Handler
deriving DecidableEq

def Handlers.check {refs : List ReferenceEntry}
    (a : Api refs) (hs : Handlers) : Except Refusal Unit
def Handlers.WellFormed {refs : List ReferenceEntry}
    (a : Api refs) (hs : Handlers) : Prop := Handlers.check a hs = .ok ()

/-- Every endpoint of the group covered, stubbing what is not handled. This is
what retires `Endpoint not handled: ${Missing}`
(`HttpApiBuilder.ts:241-252`). -/
def Handlers.complete {refs : List ReferenceEntry}
    (a : Api refs) (hs : Handlers) (alphabet : Alphabet) : Option Handlers

/-! ### The lifted clauses -/

def Handler.Targets {refs : List ReferenceEntry} (a : Api refs) (h : Handler) : Prop
def Handler.AlphabetMatchesRequires {refs : List ReferenceEntry}
    (a : Api refs) (h : Handler) : Prop
def Handler.BodyWellTyped (h : Handler) : Prop
def Handler.Fits {refs : List ReferenceEntry} (e : Endpoint refs) (h : Handler) : Prop
def Handlers.OnePerEndpoint {refs : List ReferenceEntry}
    (a : Api refs) (hs : Handlers) : Prop
def Handlers.Total {refs : List ReferenceEntry} (a : Api refs) (hs : Handlers) : Prop

theorem Handler.wellFormed_iff {refs : List ReferenceEntry}
    (a : Api refs) (h : Handler) :
    Handler.WellFormed a h ↔
      (Handler.Targets a h ∧ Handler.AlphabetMatchesRequires a h ∧
        Handler.BodyWellTyped h ∧
        ∀ e, Api.endpoint? a h.group h.endpoint = some e → Handler.Fits e h)

theorem Handlers.wellFormed_iff {refs : List ReferenceEntry}
    (a : Api refs) (hs : Handlers) :
    Handlers.WellFormed a hs ↔
      (Handlers.OnePerEndpoint a hs ∧ Handlers.Total a hs ∧
        ∀ h ∈ hs.handlers, Handler.WellFormed a h)

/-! ### Emission -/

/-- The printed body, or the printer's own refusal. `fits` says nothing about
printability (`E4-SURFACE-CE-105`). -/
def Handler.printBody (h : Handler) :
    Except Effect4.Syntax.PrintRefusal TypeScript.Expr
```

## The `Ty` laws this contract rests on, and does not own

`Endpoint.errorTy?` folds `Ty.join` over a list, and `Handler.fits` compares
the result by `DecidableEq`. The answer is independent of the order of
`e.errors` only if `Ty.join` is commutative, associative and idempotent with
`.never` as its unit. Those theorems do not exist: `src/Effect4/Program/Eff.lean`
has exactly one theorem, `render_ofSpelling`. They belong to the `Syntax`
lane, which this packet does not own, so they are **owed rows**, and the
battery pins them at the fixture instances by `#guard` instead
(`E4-SURFACE-CE-092`, `E4-SURFACE-CE-093`). This is finding H-3.

| owed theorem | statement |
| --- | --- |
| `Ty.join_comm` | `Ty.join a b = Ty.join b a` |
| `Ty.join_assoc` | `Ty.join (Ty.join a b) c = Ty.join a (Ty.join b c)` |
| `Ty.join_idem` | `Ty.join a a = a` for `a` with no top-level union |
| `Ty.join_never` | `Ty.join a .never = a` and `Ty.join .never a = a` |
| `Ty.sub_join_left` | `Ty.Sub a (Ty.join a b)` |
| `Ty.sub_trans` | `Ty.Sub a b → Ty.Sub b c → Ty.Sub a c` |
| `Ty.minus_sub` | `Ty.Sub a b ↔ (Ty.minus a b).isNever = true` |

## Observations

1. `Endpoint.answerTy? e`, `Endpoint.errorTy? e`, `Endpoint.effTy? e a`:
   compared against an exact `some ⟨_, _, _⟩` value or `none`.
2. `Handler.fits e h` and `Handler.fitsExactly e h`: `true` or `false`, always
   accompanied by the `Handler.check` receipt that names the clause.
3. `Handler.check a h`, `Handlers.check a hs`, each `Except Refusal Unit`,
   compared against `.ok ()` or an exact `.error`.
4. `Handler.requires h` and `Handler.escapes e h`: compared against exact
   `Requirement` and `Ty` values.
5. `Handler.printBody h`: `.ok _` or an exact `PrintRefusal`.
6. `Alphabet.signature a`, read by an ascribed definition, so a change of the
   `Op` index type breaks the witness file.

`EffTy` derives `DecidableEq` and **not** `Repr`
(`src/Effect4/Program/Typing.lean:27-32`), so every receipt above is a `#guard` on
an equation and none is an `#eval`. A builder who wants the failure printed
adds `Repr` to `EffTy` in the `Syntax` lane; this packet does not.

## Clause order for `Handler.check`

`check` returns the **first** refusal, so this order is part of the contract.
The context is the whole `Api` because clauses 1 and 2 are lookups in it.

| # | clause | refusal | id |
| --- | --- | --- | --- |
| 1 | `h.group` names a group of `a` | `handlerGroupAbsent h.endpoint h.group` | `E4-SURFACE-CE-100` |
| 2 | `h.endpoint` names an endpoint of that group | `handlerEndpointAbsent h.group h.endpoint` | `E4-SURFACE-CE-100` |
| 3 | no two ops of one service share a name | `alphabetOpDuplicate service op` | `E4-SURFACE-CE-099` |
| 4 | every `perform` index of `h.body` is `< h.alphabet.ops.length` | `operationOutOfAlphabet h.endpoint index` | `E4-SURFACE-CE-103` |
| 5 | every service of `h.alphabet` is in `e.requires` | `alphabetServiceUnrequired h.endpoint service` | `E4-SURFACE-CE-104` |
| 6 | every name of `e.requires` has an op in `h.alphabet` | `requirementWithoutAlphabet h.endpoint service` | `E4-SURFACE-CE-104` |
| 7 | `Endpoint.answerTy? e` is `some` | `answerTypeUnrepresentable h.endpoint` | `082`, `083` |
| 8 | `Endpoint.errorTy? e` is `some` | `errorTypeUnrepresentable h.endpoint` | `E4-SURFACE-CE-094` |
| 9 | `Handler.effTy? h` is `some` | `handlerBodyIllTyped h.endpoint` | `E4-SURFACE-CE-096` |
| 10 | the body's answer is below the endpoint's | `handlerAnswerMismatch h.endpoint` | `084`, `094` |
| 11 | the body's requirement, less `provided`, is below the endpoint's | `handlerRequirementUnprovided h.endpoint name code` | `078`, `079` |
| 12 | `h.stance = .stub`, or the body declares no escaping error | `handlerErrorUndeclared h.endpoint` | `076`, `077` |

Clause 12 is the one clause that reads `stance`, and it is the whole of the
stub exemption. Every other clause holds of a stub exactly as of an
implementation, so a stub is a checked value and not a hole in the check.

Clauses 11 and 12 are deliberately *not* symmetric with clause 10. A missing
requirement is a refusal because nothing downstream can supply it: rc.112 would
turn it into `HttpRouter.Request.From<"Requires", R>` on the layer
(`HttpApiBuilder.ts:179`) and the deployment's `provides` table would not name
it. An extra error is not a refusal at rc.112 (it is `E` at
`HttpApiEndpoint.ts:586`), so the surface reports it by `Handler.escapes` and
refuses it only for an implementation, where an undeclared error is a
documentation bug rather than a type error.

## Clause order for `Handlers.check`

| # | clause | refusal | id |
| --- | --- | --- | --- |
| 1 | every handler's `group` is `hs.group` | `handlerGroupAbsent h.endpoint h.group` | `E4-SURFACE-CE-100` |
| 2 | no endpoint is handled twice | `handlerDuplicate hs.group endpoint` | `E4-SURFACE-CE-101` |
| 3 | every endpoint of the group is handled | `endpointNotHandled hs.group endpoint` | `E4-SURFACE-CE-102` |
| 4 | every handler's own `check` | (its own) | |

Clause 2 retires `NotHandledIdentifier` (`HttpApiBuilder.ts:219-221`, applied
at `:286` and `:320`), which makes a second `handle("getUser", …)` a `never`
argument. Clause 3 retires `` `Endpoint not handled: ${Missing & string}` ``
(`HttpApiBuilder.ts:241-252`), which rc.112 reports as a string literal in
place of the return type. `Handlers.complete` is how a group with no handlers
still satisfies clause 3: it fills the gaps with `Endpoint.stub`, which is
exactly §13.2's "an endpoint with no handler emits a typed stub whose body is
`Effect.fail(new NotImplemented())` under the same declared type, so the module
typechecks either way".

## The rc.112 sites this packet retires or reports

| site | text or shape | disposition |
| --- | --- | --- |
| `Effect.ts:117`, `:154-157` | `Effect<out A, out E = never, out R = never>`, covariant | `Handler.fits` is subsumption, not equality |
| `HttpApiEndpoint.ts:584-586` | `Handler` returns `Effect<Success \| HttpServerResponse, Error \| E, R>` | clauses 10 and 12; the `HttpServerResponse` arm is a stated non-claim |
| `HttpApiEndpoint.ts:720-724` | `ExcludeProvided` | `Alphabet.provided` |
| `HttpRouter.ts:853-857` | `Provided = HttpServerRequest \| Scope.Scope \| ParsedSearchParams \| RouteContext` | `Alphabet.provided`'s four keys |
| `HttpApiBuilder.ts:126` | `export const group` | `Handlers` is its argument as rows |
| `HttpApiBuilder.ts:137-141` | the layer's `Handlers.Error<Return>` and `Exclude<…, Scope.Scope>` | `Handler.escapes`; scope never counts |
| `HttpApiBuilder.ts:169-179` | `HandlerRequirements` | clause 11 |
| `HttpApiBuilder.ts:219-221`, `:286`, `:320` | `NotHandledIdentifier` | `Handlers.check` clause 2 |
| `HttpApiBuilder.ts:241-252` | `Endpoint not handled: ${Missing}` | `Handlers.check` clause 3, `Handlers.complete` |
| `HttpApiBuilder.ts:283-296` | `handle<Identifier extends keyof EndpointsByIdentifier>` | `Handler.check` clauses 1 and 2 |
| `HttpApiBuilder.ts:441` | `export const endpoint` | the per-endpoint emission slot |
| `HttpApiBuilder.ts:95-98` | `Effect.die("HttpApiGroup … not found")` | a run-time death this slice does **not** retire; it is a deployment wiring fact |

## Refusal constructors this contract needs and `Facts.lean` does not have

Fifteen, all appended, none removed or reordered. The coordinator adds them;
this packet does not edit `src/Effect4/Surface/Refusal.lean`.

```lean
  -- handler (plan §13.2, wave 2d)
  | handlerGroupAbsent (handler group : String)
  | handlerEndpointAbsent (group endpoint : String)
  | handlerDuplicate (group endpoint : String)
  | endpointNotHandled (group endpoint : String)
  | alphabetOpDuplicate (service op : String)
  | alphabetServiceUnrequired (endpoint service : String)
  | requirementWithoutAlphabet (endpoint service : String)
  | operationOutOfAlphabet (endpoint : String) (index : Nat)
  | answerTypeUnrepresentable (endpoint : String)
  | errorTypeUnrepresentable (endpoint : String)
  | handlerBodyIllTyped (endpoint : String)
  | handlerAnswerMismatch (endpoint : String)
  | handlerErrorUndeclared (endpoint : String)
  | handlerRequirementUnprovided (endpoint : String) (serviceName serviceCode : Nat)
  | handlerBodyUnprintable (endpoint : String)
```

`handlerRequirementUnprovided` carries the offending `ServiceKey` as its two
`Nat` components rather than a name, because a `ServiceKey` **is** two `Nat`s
(`src/Effect4/Machine/Key.lean`) and has no string spelling anywhere in the
estate. That is the price of finding H-4 and it is visible in the alphabet
rather than hidden.

## Acceptance conditions

- `Handler` and `Alphabet` are first-order: every field is a string, a
  natural, a boolean, a `Ty`, a `Row`, an `Eff Nat` or a list of those, and
  both derive `DecidableEq`. No field is a Lean function. `Signature` is
  derived by `Alphabet.signature` and never stored.
- `Handler.check` and `Handlers.check` are total and return the first refusal
  in the order above.
- `Handler.fits` and `Handler.fitsExactly` are both total `Bool`s over the
  same arguments, and `Handler.fitsExactly_fits` relates them. Neither is the
  observation a negative receipt pins: every refusal is pinned by its
  `Refusal` value through `check` (`E4-SURFACE-CE-107`).
- `Endpoint.answerTy?` and `Endpoint.errorTy?` are independent of the order of
  `e.success` and `e.errors`, pinned by `#guard` at the fixtures until the
  `Ty.join` laws land.
- `Endpoint.stub_fits` is a theorem about the builder, proved by unfolding it,
  never by `decide` over a fixture. A stub that fitted only the fixtures would
  be worth nothing to a generator.
- `Alphabet.provided` contains the `Scope` key of the alphabet, so a handler
  that opens a scope charges the deployment nothing.
- Everything here reaches no axiom beyond `propext` and `Quot.sound`.

## Assurance allocation

Graph edge `SURFACE-PG-HANDLER`, with leaf receipts underneath. It is a
graph-bearing packet under `git:c407ab7:docs/AGENT-ROUTING.md`: `Handler.fits` is an
admission and refusal judgment over a typed program, and `Handlers.complete`
is a generated-code relation.

- `admission-positive`: the fixture handlers fit and check by `decide`.
- `admission-negative`: every counterexample below, each pinning its refusal
  value.
- `laws`: `Handler.fitsExactly_fits`, `Endpoint.stub_fits`,
  `Handler.wellFormed_iff`, `Handlers.wellFormed_iff`.
- `bridges`: the `Ty.join` laws of the table above, **open** and owed to the
  `Syntax` lane.
- `targets`: `Handler.printBody` into `HttpApiBuilder.group`, **open**; its
  bytes and their host typecheck are the harness's business
  (`surface-emit.contract.md`).

## Reconciliation with `surface-handler.contract.md`

The prior contract (commit `9f9e0e6`) and this one agree on the subject, the
carriers they read and the rc.112 pins, and disagree on six points. Every
disagreement is a coordinator ruling, and this table is the whole of it.

| # | prior contract | this packet | why |
| --- | --- | --- | --- |
| 1 | `Handler.fits` is exact `EffTy` equality; a two-success endpoint's handler "must have that union as its answer, not one member of it" | `Handler.fits` is subsumption, `Handler.fitsExactly` keeps equality, `fitsExactly_fits` relates them | rc.112's three parameters are covariant (`Effect.ts:117`, `:154-157`) and the handler slot's `E` and `R` are free (`HttpApiEndpoint.ts:584-586`), so equality refuses an infallible handler (`E4-SURFACE-CE-089`), a scoped handler (`090`) and a handler needing fewer services (`091`), all of which rc.112 admits |
| 2 | the typed stub is `Handler.stubBody : Endpoint refs → TypeScript.Expr`, so it is never a `Handler` and `fits` never sees it; an endpoint with no handler is not a refusal | the stub is `Endpoint.stub : … → Handler` with `stance := .stub`, checked like any other handler, and `Handlers.check` clause 3 refuses an unhandled endpoint that `Handlers.complete` has not filled | the prior spelling is a coherent way out of `E4-SURFACE-CE-088`, and it is the one this packet would adopt if ruling 1 goes the other way. Its cost is that the stub is a second, unchecked path into the emitted module: nothing decides that `stubBody`'s expression has the endpoint's type, so the one place the typed-hole discipline is claimed is the one place it is not applied |
| 3 | `structure Handler (refs) (Op : Type) where sig : Signature Op`, as plan §13.2 spells it, with `handlersModule` monomorphic in `Op` to keep it usable | `Alphabet` is first-order and `Op` is `Nat`; `Alphabet.signature` derives the `Signature` | a stored `Signature` has two Lean function fields, so `Handler` has no `DecidableEq`, no `json`, no store address and no `#guard` (`E4-SURFACE-CE-098`); the prior contract's own finding 1 records the `Op` monomorphism as a wart, and this is the same wart's root |
| 4 | `Endpoint.effTy` takes `services : List (String × ServiceKey)` as a separate argument | `Endpoint.effTy?` takes the `Alphabet`, whose rows already carry their keys | agreement in substance: both resolve `E4-SURFACE-CE-110` the same way, by handing the endpoint a table. The difference is whether the table is a second carrier or the alphabet the handler already has, and plan §13.6 rule 2 favours one spelling |
| 5 | `answerTy`/`errorTy` return `Except Refusal Ty`, refusing a non-entity body with `responseNotAnEntity` | `answerTy?`/`errorTy?` return `Option Ty` and `Handler.check` clause 7 carries the refusal | agreement in substance; the prior spelling is better, because it names the offending status. This packet adopts it if ruling 1 keeps the prior contract |
| 6 | six new `Refusal` constructors | fifteen | the extra nine are the alphabet clauses (3, 5, 6), the out-of-range operation (4), the two type-unrepresentable clauses (7, 8), the split of `handlerTypeMismatch` into answer, error and requirement (10, 11, 12) and `endpointNotHandled`. The split is what `E4-SURFACE-CE-107` argues: one `handlerTypeMismatch` for four distinct failures is the Boolean receipt `surface-facts.contract.md` forbids, wearing a clause name |

Attacks the prior contract has and this packet does not, which survive whichever
way the ruling goes and are recorded here so they are not lost: its
`E4-SURFACE-CE-084`, that `fits` must not be spelled
`typeOf h.sig h.body = (Endpoint.effTy services e).toOption`, since both sides
are `none` for an untypeable body at an endpoint with no computable type; and
its note that `Effect4.Syntax.printDecl` declares `Effect.Effect<A, E>` only
when the requirement is empty, so a handler with a requirement emits an untyped
constant and no contract on either side claims anything about the third type
parameter.

## What this contract does not claim

It does not claim an emitted handler behaves as the endpoint's rows say at run
time. `fits` is a typing claim about `Eff` under an alphabet, and nothing
here relates it to the Deep machine or to a running server.

It does not model the `HttpServerResponse` arm of `HttpApiEndpoint.ts:586`. A
handler that returns a raw response instead of the success value is legal
rc.112 and unrepresentable here; `E4-SURFACE-CE-106` records that as a
non-claim rather than as a refusal, because the carrier cannot spell it and a
refusal would be a lie about what was checked.

It does not model middleware. `HttpApiEndpoint.Middleware`, its provided
services (`:720-724`) and its error contributions (`Errors<Endpoint>`,
`:448-450`) all widen the three channels, and an endpoint with middleware
would fit strictly more handlers than this contract admits. No fixture has
middleware and no clause mentions it.

It does not claim `fits` certifies the handler talks to the endpoint's real
services. A `Row` may declare any spelling beside any type, so two alphabets
that are semantically unrelated are indistinguishable to `typeOf`
(`E4-SURFACE-CE-097`). Clauses 5 and 6 tie the alphabet's *service names* to
`e.requires`; nothing ties a row's `spelling` to a `ServiceRow`'s method,
because `ServiceRow`/`OpRow` carry rendered TypeScript strings and not `Ty`
(`E4-SURFACE-CE-109`). That join is an owed row.

It does not freeze the module path (finding H-1) and it does not freeze
whether `fits` is subsumption or equality (finding H-2). Both are coordinator
rulings, and both are written so that a ruling changes one line of the battery
or one definition, not the clause table.
