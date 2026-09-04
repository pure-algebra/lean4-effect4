# Surface facts and refusal alphabet contract

Status: breaker packet, red, 2026-09-04 (wave 1b, for waves 1a and 2e of
`docs/research/2026-09-04-surface-library-plan.md` §14.2, §14.6, §15.2)

Implementation (owed): `Effect4/Surface/Facts.lean`

Battery: every `Effect4Test/Surface/*Contract.lean` (the refusal each clause
returns is pinned beside the mutant that triggers it)

Counterexamples: `E4-SURFACE-CE-060`, `E4-SURFACE-CE-061`

Witnesses: `Effect4Test/Counterexamples/Surface/Facts.lean`

## Purpose

`Refusal` is the user-facing error vocabulary of the whole slice. Plan §13.6
rule 4: "refusals are constructors, and the message names the clause. A user
who writes an endpoint with a payload on `GET` reads
`payloadOnBodylessMethod getUser`, never a generic failure."

That makes the alphabet a frozen public surface, not an implementation
detail, and it makes every negative receipt in this packet stronger than a
Boolean: a battery that pinned `= false` would pass for a carrier that
refused the right term for the wrong reason. Every negative receipt below and
in the sibling contracts pins the exact refusal value.

## Frozen public declarations

All in namespace `Effect4.Surface`. Every `check` is total, returns the
**first** refusal in clause order, and `WellFormed` is one decidable equation
over it.

```lean
inductive Refusal
  -- the semantic layer (§15.2); `kind` is one of
  -- "entity" | "endpoint" | "tool" | "resource" | "deployment" | "site"
  | identifierMissing (kind name : String)
  | descriptionMissing (kind name : String)
  | propertyDescriptionMissing (entity property : String)
  -- entity and domain
  | nameIllegal (kind name : String)
  | entityNotStruct (entity : String)
  | keyEmpty (entity : String)
  | keyNotAProperty (entity field : String)
  | keyNotRequired (entity field : String)
  | keyDuplicate (entity field : String)
  | entityNameDuplicate (domain entity : String)
  | entityDomainMismatch (entity domain : String)
  | referenceUnresolved (entity target : String)
  -- endpoint, group and api
  | pathParamWithoutSchema (endpoint param : String)
  | schemaParamWithoutPath (endpoint param : String)
  | pathParamDuplicate (endpoint param : String)
  | payloadOnBodylessMethod (endpoint : String)
  | payloadEncodingDuplicate (endpoint contentType : String)
  | multipartPayloadDuplicate (endpoint contentType : String)
  | successEmpty (endpoint : String)
  | statusOutOfRange (endpoint : String) (status : Nat)
  | statusCollision (endpoint : String) (status : Nat)
  | streamSuccessDuplicate (endpoint : String)
  | streamWithVoidStatus (endpoint : String) (status : Nat)
  | streamWithBufferedStatus (endpoint : String) (status : Nat)
  | errorBodyStreams (endpoint : String) (status : Nat)
  | responseHeadersDuplicate (endpoint : String) (status : Nat)
  | streamOnHeadMethod (endpoint : String)
  | sseEventNameReserved (endpoint eventName : String)
  | requirementNameIllegal (endpoint service : String)
  | endpointIdDuplicate (group endpoint : String)
  | groupIdDuplicate (api group : String)
  | routeCollision (method path : String)
  -- agent
  | toolNameIllegal (tool : String)
  | toolNameDuplicate (server tool : String)
  | resourceUriDuplicate (server uri : String)
  | promptNameDuplicate (server prompt : String)
  -- deployment
  | workerNameIllegal (deployment : String)
  | bindingNameIllegal (deployment binding : String)
  | bindingNameDuplicate (deployment binding : String)
  | compatibilityDateIllegal (deployment date : String)
  | mainMissing (deployment : String)
  | mainForbidden (deployment : String)
  | providedBindingAbsent (deployment binding : String)
  | requirementUnprovided (deployment service : String)
  | mountedApiAbsent (deployment api : String)
  -- site
  | routeDuplicate (site route : String)
  | usedEndpointAbsent (site endpoint : String)
  | formEndpointWithoutPayload (site endpoint : String)
  -- kinds
  | kindMismatch (slot : String) (kind : String)
  -- ingest (wire forms)
  | unknownKeyword (name : String)
  | unsupportedContentType (contentType : String)
  | unsupportedRefTarget (pointer : String)
  | unsupportedMethod (name : String)
  | unsupportedParameterLocation (location : String)
  | unsupportedBindingKind (kind : String)
  | unsupportedShape (name : String)
  | streamingResponse (name : String)
  | recursiveSchema (name : String)
  | declarationSchema (name : String)
  | missingField (name : String)
deriving DecidableEq, Repr

def Refusal.clause : Refusal → String        -- the constructor name, as the user sees it
def Refusal.names : Refusal → List String    -- the offending names it carries

def Facts.registry : List (String × String)  -- (clause name, carrier name)
```

The `check`/`WellFormed` shape, identical for every carrier of this slice:

```lean
def X.check (…context…) (x : X) : Except Refusal Unit
def X.WellFormed (…context…) (x : X) : Prop := X.check … x = .ok ()
instance : Decidable (X.WellFormed … x) := inferInstance
theorem X.wellFormed_iff (…) (x : X) :
    X.WellFormed … x ↔ (Clause₁ … x ∧ Clause₂ … x ∧ … ∧ Clauseₙ … x)
```

Each carrier contract lists its own clause order, its lifted clause `Prop`s
and its `wellFormed_iff`. There is no `X.wellFormed : Bool`: the Boolean form
is `(X.check … x).toOption.isSome` if anyone needs it, and no battery uses it.

## Observations

1. `X.check … x : Except Refusal Unit`, compared against `.ok ()` or against
   an exact `.error (.clause "name" …)` value. This is the observation every
   negative receipt in the slice uses.
2. `Facts.registry`, compared against the constructor census.
3. `X.WellFormed … x` by `decide`, for the positive receipts.

## Acceptance conditions

- `check` is total: it returns for every value of the carrier, including
  values whose schemas do not have their slot's kind. It never diverges and
  never throws.
- Clause order is fixed and documented per carrier, because `check` returns
  the *first* refusal; a battery that pins a refusal is pinning the order too,
  and reordering clauses is a visible change of this packet.
- Every constructor carries the offending names, never a rendered message.
  `Refusal` has no `String` arm that holds prose.
- `Facts.registry` has one row per `Refusal` constructor, and a `#guard` keeps
  the two equal in both directions (`E4-SURFACE-CE-060`). A clause cannot
  exist without a name the user can see.
- The `Prop` lift of each clause is a separate declaration, so a capability
  (§14.3) can ask for exactly the clauses a derivation needs
  (`Entity.HasKey`, `Entity.KeyRequired`, `Entity.Described`,
  `Domain.Closed`, `Endpoint.ParamsMatchPath`,
  `Endpoint.BodylessHasNoPayload`, `Api.RoutesDistinct`,
  `Deployment.Satisfies`).
- `wellFormed_iff` is a `theorem` per carrier. Without it a capability that
  proves three clauses could not be related to `WellFormed`, and the
  derivation theorems of §14.4 would each have to re-derive the whole check
  (`E4-SURFACE-CE-061`).
- `check` reaches no axiom beyond `propext` and `Quot.sound`.

## Assurance allocation

Graph edge `SURFACE-PG-FACTS`, obligations `identity` (the alphabet census),
`laws` (each carrier's `wellFormed_iff`), `counterexamples` (the two rows
above plus every clause-pinning receipt in the sibling batteries).

Every negative row in every sibling contract is evidence on this edge as well
as on its own: a refusal pinned by value is what makes the clause name a
frozen surface rather than a comment.

## What this contract does not claim

It does not claim the alphabet is final; later waves append constructors, and
appending is not a breaking change. It does claim no constructor is removed or
has its payload reordered without a coordination item, because a battery pins
the value. It does not claim a refusal is the *best* explanation of a failure,
only that it names the clause that failed and the values it failed on. It says
nothing about rendering: `#surface_check` (wave 3a) prints a refusal; this
packet freezes the datum, not the printer.
