import Effect4.Program.Provision
import Effect4.Surface.Api

/-!
# Surface.Middleware — authentication is a requirement transformer

Landed 2026-09-04 from the `workshop/Provision` spike (lane B). Plan and grill:
`docs/research/2026-09-04-provision-algebra.md` §5; battery
`Test/Surface/ProvisionContract.lean`.

**The thesis, in one sentence.** An `HttpApiMiddleware` acts on a handler's requirement row
exactly as `Layer.provide` acts on a layer's — `HttpApiMiddleware.ApplyServices`
(`unstable/httpapi/HttpApiMiddleware.ts:199`) *is* the provision algebra's `provide` rule —
so a security middleware is nothing but a middleware that provides a key (`CurrentUser`)
at the price of requiring what the router provides, and "this endpoint is authenticated"
is the statement that the `R` channel of its handler is discharged by such a middleware.

What this module adds, and what it deliberately reuses:

* **Reused, never re-declared.** `Row.diff` and its laws, `LayerTy` and the provision
  algebra (`provide`, `provideMerge`, `merge`, `orDie`, `Closed`), `LayerTerm`, `layerTy`,
  `docsSig`, `DocsOp`, and the two witness keys `dbKey`/`rateKey` — all from
  `Effect4/Program/Provision.lean`. `Requirement := Row ServiceKey` and the row laws
  are `Effect4/Machine/Context.lean` and `Effect4/Data/Row.lean`. `Security` and
  `ApiKeyLocation` are the surface's own carriers (`Effect4/Surface/Api.lean:913-978`),
  not new ones.
* **`Middleware`, the carrier.** The four rows of `HttpApiMiddleware.Service`'s config —
  `requires`, `provides`, `error`, `security` (`HttpApiMiddleware.ts:320-346`,
  `:339-345`) — as first-order data, with `DecidableEq` throughout. The `Endpoint` row
  the surface already carries (`Effect4/Surface/Api.lean:1110-1113`: `security : List
  Security`, `requires : List String`) is the syntactic face of the same thing; the
  connection between the two is an **owed row**, because `Endpoint.requires` is a list of
  service *names* and this algebra runs on `ServiceKey`s, and no name-to-key map exists
  at this pin.
* **`applyServices`, and the one line that identifies the two algebras.**
  `ApplyServices<A, R> = Exclude<R, Provides<A>> | Requires<A>`
  (`HttpApiMiddleware.ts:199`) is `Row.union (Row.diff r m.provides) m.requires`, and
  `applyServices_eq_provide` says it is `LayerTy.provide`'s requirement column, by `rfl`.
* **`securityRequires` and `apply`.** What a security middleware costs: the decoders of
  `HttpApiBuilder.securityDecode` (`HttpApiBuilder.ts:481-536`) read
  `HttpServerRequest` and `Request.ParsedSearchParams`, which is exactly the fragment of
  `HttpRouter.Provided` (`unstable/http/HttpRouter.ts:853-857`) this model carries.
  `apply` is `applyServices` with those added; `apply_of_no_security` is the collapse.
* **`residual` and `afterRouter`.** `endpoint.middlewares` applied in declaration order,
  each wrapping the handler (`HttpApiBuilder.ts:863-870`), and then the router's own
  discharge. The theorems below are the capability discipline made a proof: a key nobody
  provides survives every middleware (`residual_unprovided` — **no auth, no user**), the
  residual never exceeds "what nobody provided plus what everybody required"
  (`residual_subset`), and independent middlewares commute (`apply_comm_of_disjoint`)
  while an auth/consumer pair does not.
* **The boundary, named.** `PROV-FB-KEY-FORGERY`: keys are first-order data, so a
  deployment's `Layer.succeed(CurrentUser, …)` types exactly like the security
  middleware's provision. Unforgeability is the host's object identity of the tag
  (`Context.ts:32-41`), not a theorem of this model.

Every rc.112 line named above and below is in `vendor/effect-4.0.0-rc.112/src/`.
-/

set_option autoImplicit false

namespace Effect4.Surface.Middleware

open Effect4.Machine.Env (Requirement)
open Effect4.Program (Ty)
open Effect4.Program.Provision

/-! ## The keys

Four fixed `ServiceKey`s extend the witness alphabet of `Effect4/Program/Provision.lean` (`dbKey` `10`,
`rateKey` `11`, `dbBinding` `20`, `rateBinding` `21`). As everywhere in this estate a key
is a `Nat` name paired with a `Nat` code (`Effect4/Machine/Key.lean`); the numbers are
allocation, not spelling. -/

/-- `HttpServerRequest` — the request service the router provides
(`unstable/http/HttpRouter.ts:853-857`) and every credential decoder that reads headers or
cookies needs (`HttpApiBuilder.ts:489-497`, `:517-536`). -/
def httpServerRequestKey : ServiceKey := ⟨⟨30⟩, ⟨30⟩⟩

/-- `Request.ParsedSearchParams` — the parsed query string, also router-provided
(`unstable/http/HttpRouter.ts:853-857`), read by `Request.schemaSearchParams`
(`unstable/http/HttpServerRequest.ts:223-233`). -/
def parsedSearchParamsKey : ServiceKey := ⟨⟨31⟩, ⟨31⟩⟩

/-- `CurrentUser` — the service a security middleware provides, and the one a handler that
wants to know its caller requires. There is nothing special about it in the model: it is a
key like any other, which is the whole content of `PROV-FB-KEY-FORGERY` below. -/
def currentUserKey : ServiceKey := ⟨⟨40⟩, ⟨40⟩⟩

/-- A logger — a service an ordinary, non-security middleware requires. Used below to
exhibit a middleware that commutes with the authenticator. -/
def loggerKey : ServiceKey := ⟨⟨41⟩, ⟨41⟩⟩

/-- `HttpRouter.Provided` (`unstable/http/HttpRouter.ts:853-857`), on the fragment this
model carries: the request and the parsed search params. rc.112's union also holds
`Scope.Scope` — which `Provision.lean` already models as `sig.scopeKey` and discharges at
the layer's own `bodyRequires` — and `RouteContext`, which this model does not carry; that
is an **owed row**, not a claim that the union has two members.
`HttpApiMiddleware.ts:70` is where a middleware's answer is allowed to require it. -/
def routerProvided : Requirement :=
  Requirement.ofList [httpServerRequestKey, parsedSearchParamsKey]

/-! ## The middleware carrier -/

/-- One `HttpApiMiddleware.Service` config, as first-order data
(`HttpApiMiddleware.ts:320-346`; the four fields are the `requires`, `provides`, `error`
and `security` entries of the `ServiceClass` type argument at `:339-345`). `name` is the
`id : Id` argument at `:333`, carried for reporting only: no theorem below reads it, and
nothing in the module traverses a `String`. -/
structure Middleware where
  /-- The `id` the service class is created with (`HttpApiMiddleware.ts:333`). -/
  name : String
  /-- `Provides<A>` (`HttpApiMiddleware.ts:183`): what the middleware puts into the
  handler's context. -/
  provides : Requirement
  /-- `Requires<A>` (`HttpApiMiddleware.ts:191`): what running the middleware itself
  costs, before its security schemes are priced. -/
  requires : Requirement
  /-- The declared error schema (`HttpApiMiddleware.ts:335`, `:342`), as the type
  language's error column. -/
  error : Ty
  /-- The security schemes this middleware implements (`HttpApiMiddleware.ts:330`,
  `:345`); `[]` is an ordinary middleware, and `AnyServiceSecurity` (`:156-159`) is the
  non-empty case. -/
  security : List Effect4.Surface.Security
deriving DecidableEq

/-! ## The action on rows -/

/-- `ApplyServices<A, R> = Exclude<R, Provides<A>> | Requires<A>`
(`HttpApiMiddleware.ts:199`), read as a function on requirement rows: remove what the
middleware provides, add what it requires. -/
def applyServices (m : Middleware) (r : Requirement) : Requirement :=
  Row.union (Row.diff r m.provides) m.requires

/-- **A middleware and a layer are the same algebra.** `ApplyServices`
(`HttpApiMiddleware.ts:199`) is the requirement column of `LayerTy.provide`
(`Layer.ts:2089`) at the layer `⟨∅, never, r⟩` provided by `⟨m.provides, m.error,
m.requires⟩`. Definitional: rc.112 writes one rule twice, in two files, for two carriers. -/
theorem applyServices_eq_provide (m : Middleware) (r : Requirement) :
    applyServices m r =
      (LayerTy.provide ⟨Requirement.empty, .never, r⟩
        ⟨m.provides, m.error, m.requires⟩).requires := rfl

/-! ## The security row: what a credential decoder costs

`HttpApiBuilder.securityDecode` (`HttpApiBuilder.ts:481-487`) is declared
`Effect<Type<Security>, never, HttpServerRequest | Request.ParsedSearchParams>` — both
services, for every scheme. Per arm:

* `Http` (which `bearer` is: `HttpApiSecurity.ts:154`, `http({ scheme: "Bearer" })`) maps
  `HttpServerRequest` (`HttpApiBuilder.ts:489-497`).
* `Basic` (`HttpApiSecurity.ts:205`) maps `HttpServerRequest`
  (`HttpApiBuilder.ts:517-536`).
* `ApiKey` (`HttpApiSecurity.ts:177-186`) builds a decoder whose *declared* type is
  `Request.ParsedSearchParams | HttpServerRequest` in all three locations
  (`HttpApiBuilder.ts:503-506`) and then selects
  `Request.schemaSearchParams` / `schemaCookies` / `schemaHeaders`
  (`HttpApiBuilder.ts:507-511`).

The narrow reads, pinned in the vendored tree: `schemaSearchParams` flat-maps
`ParsedSearchParams` alone (`unstable/http/HttpServerRequest.ts:223-233`), `schemaCookies`
flat-maps `HttpServerRequest` alone (`:195-201`), `schemaHeaders` flat-maps
`HttpServerRequest` alone (`:209-215`). This module transcribes the **declared** row at
`HttpApiBuilder.ts:503-506` for the query location — both services — because that is the
row rc.112's types commit an implementation to; the sharper `query ↦ {ParsedSearchParams}`
reading is an **owed row**, and nothing below depends on which of the two is taken. -/

/-- The services one security scheme's credential decode requires. -/
def securityRequires : Effect4.Surface.Security → Requirement
  | .bearer => Requirement.single httpServerRequestKey
  | .basic => Requirement.single httpServerRequestKey
  | .apiKey .query _ => Requirement.ofList [httpServerRequestKey, parsedSearchParamsKey]
  | .apiKey .header _ => Requirement.single httpServerRequestKey
  | .apiKey .cookie _ => Requirement.single httpServerRequestKey

/-- What a middleware really requires: its declared `requires`, plus the decode cost of
every security scheme it implements. `makeSecurityMiddleware` runs every entry's `decode`
(`HttpApiBuilder.ts:888-891`, `:902-909`), so every entry's services are needed. -/
def effectiveRequires (m : Middleware) : Requirement :=
  m.security.foldl (fun r s => Row.union r (securityRequires s)) m.requires

/-- The row a middleware leaves on a handler that had `r`: `ApplyServices` with the
security decode priced in. -/
def apply (m : Middleware) (r : Requirement) : Requirement :=
  Row.union (Row.diff r m.provides) (effectiveRequires m)

/-- The membership law of `apply`; every theorem below is this law and the row laws. -/
theorem mem_apply (m : Middleware) (r : Requirement) (key : ServiceKey) :
    key ∈ apply m r ↔ (key ∈ r ∧ key ∉ m.provides) ∨ key ∈ effectiveRequires m := by
  show key ∈ Row.union (Row.diff r m.provides) (effectiveRequires m) ↔ _
  rw [Row.mem_union, Row.mem_diff]

/-- A middleware with no security scheme is exactly `ApplyServices`
(`HttpApiMiddleware.ts:199`); `makeSecurityMiddleware` on an empty scheme record is
`Function.identity` (`HttpApiBuilder.ts:892-894`). -/
theorem apply_of_no_security (m : Middleware) (r : Requirement) (h : m.security = []) :
    apply m r = applyServices m r := by
  have he : effectiveRequires m = m.requires := by
    show m.security.foldl (fun r s => Row.union r (securityRequires s)) m.requires = m.requires
    rw [h]
    rfl
  show Row.union (Row.diff r m.provides) (effectiveRequires m)
      = Row.union (Row.diff r m.provides) m.requires
  rw [he]

/-! ## The chain -/

/-- `endpoint.middlewares`, applied in declaration order, each wrapping the handler
(`HttpApiBuilder.ts:863-870`: the loop rebinds `handler = apply(handler, options)`), read
on rows. The last middleware in the list is the outermost wrapper and so the last row
transformer. -/
def residual (ms : List Middleware) (r : Requirement) : Requirement :=
  ms.foldl (fun r m => apply m r) r

/-- What the router itself discharges: `HttpRouter.Provided`
(`unstable/http/HttpRouter.ts:853-857`, `HttpApiMiddleware.ts:70`). A deployment must
provide the residual *after* this, and nothing else. -/
def afterRouter (r : Requirement) : Requirement := Row.diff r routerProvided

/-- Everything the listed middlewares provide, as one row. -/
def allProvides : List Middleware → Requirement
  | [] => Requirement.empty
  | m :: rest => Row.union m.provides (allProvides rest)

/-- Everything the listed middlewares effectively require, as one row. -/
def allRequires : List Middleware → Requirement
  | [] => Requirement.empty
  | m :: rest => Row.union (effectiveRequires m) (allRequires rest)

/-- No middleware: the handler's own row. -/
theorem residual_nil (r : Requirement) : residual [] r = r := rfl

/-- The head wraps first (`HttpApiBuilder.ts:863-870`). -/
theorem residual_cons (m : Middleware) (ms : List Middleware) (r : Requirement) :
    residual (m :: ms) r = residual ms (apply m r) := rfl

/-- The empty provision row. -/
theorem allProvides_nil : allProvides [] = Requirement.empty := rfl

/-- One step of the provision union. -/
theorem allProvides_cons (m : Middleware) (ms : List Middleware) :
    allProvides (m :: ms) = Row.union m.provides (allProvides ms) := rfl

/-- The empty requirement row. -/
theorem allRequires_nil : allRequires [] = Requirement.empty := rfl

/-- One step of the requirement union. -/
theorem allRequires_cons (m : Middleware) (ms : List Middleware) :
    allRequires (m :: ms) = Row.union (effectiveRequires m) (allRequires ms) := rfl

/-! ## The theorems: what a typed mounting discharges -/

/-- **A provided key is discharged.** A middleware that provides a key and does not itself
require it removes that key from every row it acts on. This is
`LayerTy.provide_discharges` (`Provision.lean`) transposed onto middlewares, and it is the
whole content of "mounting the authenticator satisfies the handler's `CurrentUser`". -/
theorem apply_provided_absent (m : Middleware) (r : Requirement) (key : ServiceKey)
    (hp : key ∈ m.provides) (hr : key ∉ effectiveRequires m) : key ∉ apply m r := by
  intro h
  rcases (mem_apply m r key).mp h with ⟨_, hnp⟩ | he
  · exact hnp hp
  · exact hr he

/-- **A middleware is monotone on rows.** A handler that needs more leaves more over: no
middleware can turn a larger requirement into a smaller residual. -/
theorem apply_mono (m : Middleware) {r r' : Requirement} (h : Row.Subset r r') :
    Row.Subset (apply m r) (apply m r') := by
  intro a ha
  rcases (mem_apply m r a).mp ha with ⟨hin, hnp⟩ | he
  · exact (mem_apply m r' a).mpr (Or.inl ⟨h a hin, hnp⟩)
  · exact (mem_apply m r' a).mpr (Or.inr he)

/-- **Independent middlewares commute.** If neither middleware provides anything the other
effectively requires, the order rc.112 applies them in (`HttpApiBuilder.ts:863-870`) does
not change the residual row. The hypothesis is exactly the non-independence the
counterexample below exhibits: an authenticator and a middleware that reads the user do
*not* satisfy it, and their two orders genuinely differ (`#guard` in the witnesses). The
row is what commutes; the *run* need not — `makeSecurityMiddleware` tries entries in order
and keeps the last failure (`HttpApiBuilder.ts:902-919`). -/
theorem apply_comm_of_disjoint (m₁ m₂ : Middleware) (r : Requirement)
    (h₁ : ∀ key : ServiceKey, key ∈ m₁.provides → key ∉ effectiveRequires m₂)
    (h₂ : ∀ key : ServiceKey, key ∈ m₂.provides → key ∉ effectiveRequires m₁) :
    apply m₂ (apply m₁ r) = apply m₁ (apply m₂ r) := by
  apply Row.eq_of_mem_iff
  intro a
  have g₁ := h₁ a
  have g₂ := h₂ a
  simp only [mem_apply]
  by_cases hp1 : a ∈ m₁.provides
  · have he2 : a ∉ effectiveRequires m₂ := g₁ hp1
    by_cases hp2 : a ∈ m₂.provides
    · have he1 : a ∉ effectiveRequires m₁ := g₂ hp2
      simp [hp1, hp2, he1, he2]
    · by_cases he1 : a ∈ effectiveRequires m₁ <;> simp [hp1, hp2, he1, he2]
  · by_cases hp2 : a ∈ m₂.provides
    · have he1 : a ∉ effectiveRequires m₁ := g₂ hp2
      by_cases he2 : a ∈ effectiveRequires m₂ <;> simp [hp1, hp2, he1, he2]
    · by_cases he1 : a ∈ effectiveRequires m₁ <;> by_cases he2 : a ∈ effectiveRequires m₂ <;>
        simp [hp1, hp2, he1, he2]

/-- **The residual never exceeds "what nobody provided plus what everybody required".**
The bound is the whole reason a deployment can be checked against a middleware stack
without unfolding the stack. Induction on the chain, generalising the row. -/
theorem residual_subset (ms : List Middleware) (r : Requirement) :
    Row.Subset (residual ms r) (Row.union (Row.diff r (allProvides ms)) (allRequires ms)) := by
  revert r
  induction ms with
  | nil =>
    intro r a ha
    rw [residual_nil] at ha
    rw [allProvides_nil, allRequires_nil]
    exact (Row.mem_union a _ _).mpr (Or.inl ((Row.mem_diff a _ _).mpr ⟨ha, Row.not_mem_empty a⟩))
  | cons m₀ rest ih =>
    intro r a ha
    rw [residual_cons] at ha
    have hstep := ih (apply m₀ r) a ha
    rw [allProvides_cons, allRequires_cons]
    rcases (Row.mem_union a _ _).mp hstep with hd | hr
    · obtain ⟨hin, hnp⟩ := (Row.mem_diff a _ _).mp hd
      rcases (mem_apply m₀ r a).mp hin with ⟨hr0, hnp1⟩ | he
      · refine (Row.mem_union a _ _).mpr (Or.inl ((Row.mem_diff a _ _).mpr ⟨hr0, ?_⟩))
        intro hc
        rcases (Row.mem_union a _ _).mp hc with h1 | h2
        · exact hnp1 h1
        · exact hnp h2
      · exact (Row.mem_union a _ _).mpr (Or.inr ((Row.mem_union a _ _).mpr (Or.inl he)))
    · exact (Row.mem_union a _ _).mpr (Or.inr ((Row.mem_union a _ _).mpr (Or.inr hr)))

/-- **No auth, no user.** A key that no middleware in the chain provides survives every
middleware in the chain. Mount the wrong stack and `CurrentUser` is still in the residual,
so the app does not close (`Provision.appTy_closed_iff`) and the deployment is refused by
the type — which is precisely what "the `R` channel is the capability discipline" means. -/
theorem residual_unprovided (ms : List Middleware) (r : Requirement) (key : ServiceKey)
    (hk : key ∈ r) (hnone : ∀ m ∈ ms, key ∉ m.provides) : key ∈ residual ms r := by
  revert r hk hnone
  induction ms with
  | nil =>
    intro r hk _
    rw [residual_nil]
    exact hk
  | cons m₀ rest ih =>
    intro r hk hnone
    rw [residual_cons]
    exact ih (apply m₀ r)
      ((mem_apply m₀ r key).mpr (Or.inl ⟨hk, hnone m₀ List.mem_cons_self⟩))
      (fun m' hm' => hnone m' (List.mem_cons_of_mem m₀ hm'))

/-- **A middleware's own requirement reaches the residual**, when no middleware in the
chain provides it: mounting the authenticator does not make `HttpServerRequest` free, it
moves the debt from the handler to the deployment (which is where `afterRouter` pays it).

The hypothesis is over the *whole* chain rather than over the middlewares that follow `m`.
An earlier provider is in fact harmless — `apply m` re-adds the key after any earlier
`apply` removed it, and the `#guard` `earlier_provider_is_harmless` below exhibits exactly
that — but stating "later" needs a suffix decomposition of the list that this spike does
not carry; the sharper theorem is an **owed row**. -/
theorem mem_residual_of_requires (ms : List Middleware) (r : Requirement) (key : ServiceKey)
    (m : Middleware) (hm : m ∈ ms) (hreq : key ∈ effectiveRequires m)
    (hnone : ∀ m' ∈ ms, key ∉ m'.provides) : key ∈ residual ms r := by
  revert r hm hnone
  induction ms with
  | nil =>
    intro _ hm _
    cases hm
  | cons m₀ rest ih =>
    intro r hm hnone
    rw [residual_cons]
    have htail : ∀ m' ∈ rest, key ∉ m'.provides :=
      fun m' hm' => hnone m' (List.mem_cons_of_mem m₀ hm')
    rcases List.mem_cons.mp hm with heq | htl
    · refine residual_unprovided rest (apply m₀ r) key ?_ htail
      refine (mem_apply m₀ r key).mpr (Or.inr ?_)
      rw [← heq]
      exact hreq
    · exact ih (apply m₀ r) htl htail

/-! ## Witnesses: the docs example of the Surface plan (§13.3), now authenticated

`Provision.lean`'s `POST /feedback` handler needed `Db` and `RateLimit`. Give it a caller:
it now needs `CurrentUser` too, and the deployment cannot close until something discharges
that key. -/

section Witnesses

/-- The handler of `POST /feedback`, now that it wants to know who is posting. -/
def feedbackRequires : Requirement := Requirement.ofList [dbKey, rateKey, currentUserKey]

/-- The authenticator: provides `CurrentUser`, requires nothing of its own, and implements
one bearer scheme (`HttpApiSecurity.ts:154`). Its *effective* requirement is the decode
cost of that scheme (`HttpApiBuilder.ts:489-497`). -/
def authMiddleware : Middleware :=
  ⟨"Authentication", Requirement.single currentUserKey, Requirement.empty, .never,
    [.bearer]⟩

/-- An ordinary middleware: provides nothing, requires a logger, no security schemes. -/
def logMiddleware : Middleware :=
  ⟨"Log", Requirement.empty, Requirement.single loggerKey, .never, []⟩

/-- A middleware that *reads* the current user — an audit trail, say. It requires exactly
what the authenticator provides, so the two do not satisfy `apply_comm_of_disjoint`. -/
def auditMiddleware : Middleware :=
  ⟨"Audit", Requirement.empty, Requirement.single currentUserKey, .never, []⟩

-- The security row, one arm at a time. The api key in the query needs exactly the two
-- services the router provides (`HttpApiBuilder.ts:503-506`).
#guard securityRequires .bearer = Requirement.single httpServerRequestKey
#guard securityRequires .basic = Requirement.single httpServerRequestKey
#guard securityRequires (.apiKey .header "x-api-key") = Requirement.single httpServerRequestKey
#guard securityRequires (.apiKey .cookie "session") = Requirement.single httpServerRequestKey
#guard securityRequires (.apiKey .query "token") = routerProvided

-- The authenticator's effective requirement is the bearer decode's `HttpServerRequest`.
#guard effectiveRequires authMiddleware = Requirement.single httpServerRequestKey
#guard effectiveRequires logMiddleware = Requirement.single loggerKey

-- `ApplyServices` is `LayerTy.provide`'s requirement column, on the example.
#guard applyServices authMiddleware feedbackRequires =
  (LayerTy.provide ⟨Requirement.empty, .never, feedbackRequires⟩
    ⟨authMiddleware.provides, authMiddleware.error, authMiddleware.requires⟩).requires

-- Mounting the authenticator trades `CurrentUser` for `HttpServerRequest` …
#guard residual [authMiddleware] feedbackRequires =
  Requirement.ofList [dbKey, rateKey, httpServerRequestKey]

-- … and the router pays that: the deployment must provide `Db` and `RateLimit`, and
-- nothing about users.
#guard afterRouter (residual [authMiddleware] feedbackRequires) =
  Requirement.ofList [dbKey, rateKey]

-- No middleware at all: `CurrentUser` is still there, so the app does not close.
#guard residual [] feedbackRequires = feedbackRequires
#guard decide (currentUserKey ∈ residual [] feedbackRequires) = true

-- Mounting only the logger does not help either: nothing provides `CurrentUser`.
#guard decide (currentUserKey ∈ residual [logMiddleware] feedbackRequires) = true

/-- `residual_unprovided` on the example: with only the logger mounted, `CurrentUser`
survives, so `POST /feedback` cannot be deployed closed. -/
theorem currentUser_survives_logging :
    currentUserKey ∈ residual [logMiddleware] feedbackRequires := by
  refine residual_unprovided [logMiddleware] feedbackRequires currentUserKey (by decide) ?_
  intro m hm
  rcases List.mem_cons.mp hm with heq | htl
  · subst heq
    decide
  · cases htl

-- Independent middlewares commute: the logger provides nothing the authenticator needs
-- and the authenticator provides nothing the logger needs.
#guard residual [authMiddleware, logMiddleware] feedbackRequires =
  residual [logMiddleware, authMiddleware] feedbackRequires

-- A consumer of `CurrentUser` does not commute with its provider: authenticate first and
-- the key is discharged; audit first and it is re-added and never removed.
#guard decide (residual [authMiddleware, auditMiddleware] feedbackRequires =
  residual [auditMiddleware, authMiddleware] feedbackRequires) = false
#guard residual [authMiddleware, auditMiddleware] feedbackRequires =
  Requirement.ofList [dbKey, rateKey, httpServerRequestKey, currentUserKey]
#guard residual [auditMiddleware, authMiddleware] feedbackRequires =
  Requirement.ofList [dbKey, rateKey, httpServerRequestKey]

-- The owed row of `mem_residual_of_requires`, exhibited: a provider *earlier* than the
-- requirer is harmless, because the requirer re-adds the key. Only a later provider
-- discharges it, which is why the theorem's hypothesis is over the whole chain.
#guard decide (currentUserKey ∈ residual [authMiddleware, auditMiddleware] feedbackRequires)
  = true

/-! ### The boundary: `PROV-FB-KEY-FORGERY`

A `ServiceKey` is first-order data (`Effect4/Machine/Key.lean`), so `currentUserKey` is a
pair of `Nat`s that any term may name. `forgedProvider` is a deployment layer that provides
`CurrentUser` from a literal — no request read, no credential, no scheme — and `layerTy`
types it exactly as the security middleware's provision is typed. This is the
`LAYER-FB-LAYER-IDENTITY` shape of `Effect4/Machine/Layer.lean:33-40`, one level up:
identity there is *allocation* identity of a layer object, identity here is the *object
identity of the tag* (`Context.ts:32-41`), and neither is structural, so neither is
representable in a first-order model.

**The refusal, stated.** `PROV-FB-KEY-FORGERY`: unforgeability of `CurrentUser` is the
host's object identity of the `Context.Key`, not a theorem of this model. Every theorem
above says what a *typed* wiring discharges; none says who is allowed to provide. A
deployment that mounts `forgedMiddleware` type-checks, closes, and is wrong, and this
module can prove the first two and not the third. -/

/-- `Layer.succeed(CurrentUser, …)` (`Layer.ts:1074`) in a deployment: a forged provider of
the very key the authenticator provides. -/
def forgedProvider : LayerTerm DocsOp := .succeed currentUserKey .unit

-- The model cannot tell it from an honest provision: the signature's output row is the
-- same one `authMiddleware.provides` is.
#guard (layerTy docsSig forgedProvider).map LayerTy.out = some (Requirement.single currentUserKey)
#guard (layerTy docsSig forgedProvider).map LayerTy.out = some authMiddleware.provides

/-- The same forgery as a middleware: no security scheme at all, and it discharges
`CurrentUser` exactly as the bearer-token authenticator does. -/
def forgedMiddleware : Middleware :=
  ⟨"Forged", Requirement.single currentUserKey, Requirement.empty, .never, []⟩

-- Authentication by fiat: the residual is clean, and it did not read a single header.
#guard residual [forgedMiddleware] feedbackRequires = Requirement.ofList [dbKey, rateKey]
#guard afterRouter (residual [forgedMiddleware] feedbackRequires) =
  Requirement.ofList [dbKey, rateKey]
#guard decide (currentUserKey ∈ residual [forgedMiddleware] feedbackRequires) = false

end Witnesses

/-! ## Separation gates: everything here is first-order data -/

example : DecidableEq Middleware := inferInstance

end Effect4.Surface.Middleware
