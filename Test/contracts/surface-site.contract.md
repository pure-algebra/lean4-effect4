# Surface site contract

Status: breaker packet, red, 2026-09-04 (wave 1b of
`docs/research/2026-09-04-surface-library-plan.md` §4.7)

Implementation (owed): `src/Effect4/Surface/Site.lean`

Battery: `Test/Surface/SiteContract.lean`

Counterexamples: `E4-SURFACE-CE-050` through `E4-SURFACE-CE-052`,
`E4-SURFACE-CE-068`

Shared: `Test/contracts/surface-facts.contract.md` owns the `Refusal`
alphabet.

Witnesses: `Test/Counterexamples/Surface/Site.lean`

## Purpose

The browser surface, cut to what can be claimed in v1: a page has a route, a
title, the endpoints it reads and at most one endpoint it submits a form to.
The DOM is out of scope by ruling (plan §4.7 and §11); the join point is
lean4-whatwg's `Whatwg.Html`, and this contract carries the refusal rather
than a half model.

The one content-bearing law is the form law: a page that submits a form names
an endpoint that has a payload. Without it the generated client would spell a
submit against an endpoint with nothing to submit, which is exactly the class
of defect the `Method.allowsPayload` clause deletes on the server side.

## Frozen public declarations

All in namespace `Effect4.Surface`.

```lean
abbrev EndpointRef := String × String × String   -- (api id, group id, endpoint id)

structure Page where
  route : Path
  title : String
  uses  : List EndpointRef := []
  form  : Option EndpointRef := none
deriving DecidableEq

structure Site where
  name        : String
  annotations : Effect4.Annotations := none
  pages       : List Page
deriving DecidableEq

def Site.check (s : Site) : Except Refusal Unit
def Site.WellFormed (s : Site) : Prop := Site.check s = .ok ()

def Site.resolves {refs} (s : Site) (apis : List (Api refs)) :
    Except Refusal Unit
def Site.Resolves {refs} (s : Site) (apis : List (Api refs)) : Prop :=
  Site.resolves s apis = .ok ()

def Site.Described (s : Site) : Prop
def Site.RoutesDistinct (s : Site) : Prop

theorem Site.wellFormed_iff (s : Site) :
    Site.WellFormed s ↔ (Site.Described s ∧ Site.RoutesDistinct s)

def Site.routesJson : Site → Effect4.Json
def Site.clientModule {refs} (s : Site) (apis : List (Api refs)) :
    Option TypeScript.Module
```

## Observations

1. `Site.check s : Except Refusal Unit`.
2. `Site.resolves s apis : Except Refusal Unit` against the fixture
   `shopApi`; a failure names the endpoint reference it could not join.
3. `Site.routesJson s : Json`, compared against a literal term, in page
   declaration order.

## Acceptance conditions

- `Site.check s` clause order: `identifier` on the bag
  (`identifierMissing "site" s.name`); `description` on the bag
  (`descriptionMissing "site" s.name`, `E4-SURFACE-CE-068`); rendered routes
  distinct (`routeDuplicate s.name route`, `E4-SURFACE-CE-050`).
  Distinctness is on the rendered string, not on the `Path` value, so two
  segment lists that render the same collide.
- `Site.resolves s apis` is `.ok ()` exactly when every `EndpointRef` in every
  page's `uses`, and every page's `form` when present, resolves through
  `Api.endpoint?` (`usedEndpointAbsent`, `E4-SURFACE-CE-051`), and every
  resolved `form` endpoint has a non-empty `payloads`
  (`formEndpointWithoutPayload`, `E4-SURFACE-CE-052`).
- A page with `form = none` places no payload obligation; a page whose `uses`
  is empty is well formed.
- `routesJson` carries the route, the title, the `uses` triples and the
  optional `form` triple, and nothing else.

## Assurance allocation

Leaf receipts for `Site.wellFormed`; the `SURFACE-PG-API` graph's `bridges`
edge for `Site.resolves`, which is a cross-surface judgment reading the API
carrier and is the second consumer (after `Deployment.satisfies`) of
`Api.endpoint?`.

`surface.site.routes` lands `Stance.emitted` with no receipt; there is no host
that consumes a route table in the landing packet, and the rule may not be
flipped without one.

## What this contract does not claim

No DOM, no markup, no rendering, no hydration, no navigation semantics, no
client-side routing behaviour. It does not claim a page's `uses` list is
complete with respect to any generated client, nor that a route matches any
server route: the site's routes and the API's routes are independent alphabets
in v1 and nothing joins them.
