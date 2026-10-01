# The provision algebra: requirements, layers, deployments and authentication as one row calculus

Date: 2026-09-04. Status: design note with a green workshop spike (`workshop/Provision/`,
lake library `Provision`, non-default), grilled in §8, landing plan in §9. Written from the
PC tree at `f9b4638` plus the uncommitted codegen/OCaml landing. Sources read: the Context
and Layer machine (`src/Effect4/Machine/{Context,Layer}.lean`), the Eff typing and compile
(`src/Effect4/Program/{Eff,Typing,Native,Compile}.lean`), the Surface carriers
(`src/Effect4/Surface/{Api,Deploy}.lean`, `src/Effect4/Ingest/Wrangler.lean`), the rc.112
sources `Layer.ts`, `Context.ts`, `internal/layer.ts`, `Config.ts`, `ConfigProvider.ts`,
`unstable/httpapi/{HttpApiMiddleware,HttpApiSecurity,HttpApiBuilder}.ts`, and the literature
of §7 (the PC's PDFs, `Foldable/research`, the Mac's `lean4-effects` claim boundary).

The question asked: the Eff language is formalised well, but Context, Services and Layers,
the things people associate with *concrete programmatic services*, are lacking. Does the
algebra give good models for demystifying cloud resource provisioning, authentication and
service definition?

The answer, in one paragraph: **yes, and the model is one row calculus.** A requirement row
is a finite set of service keys under union (a bounded join-semilattice, hence CALM: adding a
requirement never invalidates a check). A context is an insertion-ordered map under
right-biased merge (a monoid, *not* commutative: the last provider wins). A layer is a
signature `⟨out, error, requires⟩` and `Layer.provide` is one equation on rows,
`requires (l ◁ d) = (requires l ∖ out d) ∪ requires d`, which is exactly the TypeScript type
rc.112 prints for `Layer.provide` (`Layer.ts:2089`) and for an HTTP middleware
(`HttpApiMiddleware.ts:199`, `ApplyServices`). A cloud deployment is a closed layer: the
bindings are `Layer.succeed` leaves the platform supplies, the `provides` rows are
`Layer.effect` leaves reading one binding each, and the deployment law is the closure
theorem. Authentication is a requirement transformer: a security middleware discharges the
one key (`CurrentUser`) only it can provide, at the price of requiring what the router
provides. Service definition is a signature row: what a service's operations require is a
row on the row table, and `typeOf` already computes it. Everything above is proved or
witnessed in the spike; what the model cannot say (who is *allowed* to provide a key) is
named as a refusal row, not hidden.

---

## 0. What the estate had, exactly

| Face | State on 2026-09-04 morning | Gap this note closes |
| --- | --- | --- |
| `Requirement := Row ServiceKey` | union, subset, normalisation proved (`Data/Row.lean`) | no `diff`; `Exclude<R, S>` was not expressible |
| `Context ValU` (`Machine/Context.lean`) | the eleven `ENV-PG-CONTEXT` laws, `Satisfies`, `interpret_total` | no statement of `Satisfies` as an adjunction; unused by the Eff route |
| the Layer machine (`Machine/Layer.lean`) | all sixteen `layer.*` census rows proved; memo maps, scopes, `provide`, `mergeAll`, `fresh`, `launch`, `provideLayer` run through `runSyncExit` | its programs are `ProgName`/`Construction`, a closed alphabet; no typed face; no term language a user writes |
| `Eff` typing (`Program/Typing.lean`) | `EffTy.requires` is a row computed from the rows performed | `RowKind.program` rows (Layer and Context) are opaque: the compile answers the frontier (`Compile.lean:318`) |
| the Eff machine context | `Machine/Stores.lean:138`: `structure Ctx` with **three fields** (`ambientScope`, `maxOpsBeforeYield`, `preventYield`) | the Eff route has **no service map at all**: `Effect.service`, `provideService`, `Effect.provide` are inexpressible on it; `Env.Ctx` (the map) lives only under the Layer machine |
| `Surface/Deploy.lean` | `Deployment.provides : List (String × String)`, `satisfies` over strings, wrangler ingest with its quotient | strings, not keys; no theorem relates it to the runtime's own notion of provision |
| `Surface/Api.lean` | `Endpoint.security`, `Endpoint.requires : List String` | security is a spelling; nothing says what it discharges |

Two sibling notes were written the same day by another seat and are not superseded here:
`2026-09-04-language-as-data-and-agentic-effects.md` (the language across runtimes, message
passing as decisions, rectification) and `2026-09-04-ts-ingestion-and-programs-as-content.md`
(TypeScript ingestion, programs as content). This note is orthogonal to both: it is about the
*typed wiring* of services, which those notes take as given.

The substrate note (`2026-09-04-substrate-thesis-and-production-model.md` §9.1, finding 2)
already ranked Layer as the idiom to open next: 45k corpus call sites of `Layer.*` and
`Effect.provide` against 53k for the whole streaming stack, and structurally simpler. This
note is that opening, done at the level where it pays: the *typed algebra* over the proved
machine, not a second machine.

## 1. The objects

Everything below is first-order data with `DecidableEq`, at `Type 0`, no closures
(`AGENTS.md`, representation rules; DB-02). File: `workshop/Provision/Provision.lean`.

| Object | Definition | rc.112 |
| --- | --- | --- |
| `Requirement` | `Row ServiceKey` (reused) | the `R` parameter of `Effect<A, E, R>` |
| `Row.diff r s` | `normalize (r.elems.filter (· ∉ s))` | `Exclude<R, S>` |
| `LayerTy` | `⟨out, error : Ty, requires⟩` | `Layer<ROut, E, RIn>` (`Layer.ts:54`) |
| `LayerTerm Op` | `succeed key lit \| effect key (body : Eff Op) \| effectDiscard body \| provide \| provideMerge \| merge \| fresh \| orDie` | `Layer.ts:1074, :1427, :1512, :2258, :2704, :1850, :3850, :3327`; `mergeAll` is the fold of `merge` (`:1652`) |
| `layerTy sig` | the typing, `Option LayerTy`, structural | the TypeScript signatures, read as a function |
| `App Op` | `⟨layer, program : Eff Op⟩` | `Effect.provide(program, layer)` (`internal/layer.ts:8-22`) |
| `appTy sig` | `⟨p.answer, p.error ⊔ l.error, l.requires ∪ (p.requires ∖ l.out)⟩` | `Effect<A, E \| E2, RIn \| Exclude<R, ROut>>` (`internal/layer.ts:14`) |
| `LeafSem Op` | the leaf hook: what `effect key body` answers under a context | the trusted-boundary position `RunInterp` occupies |
| `build sem` | the specification of provisioning, structural over the combinators | the machine's continuations `provideThenK`, `combineWithK`, `Context.mergeAll` |
| `lower sig` | `LayerTerm Op → Option (LayerTable × LayerId)` | the machine's `LayerDesc`/`Construction` alphabet |

Two design choices worth stating:

* **`effect` leaves carry `Eff` bodies.** The same `Eff` the printer prints and the compile
  compiles; `layerTy` types the body with `typeOf` and removes the layer's own scope
  (`Exclude<R, Scope.Scope>`, `Layer.ts:1438`). No second body language.
* **`succeed` carries a `Lit`, not a `Term`.** The Layer machine's value alphabet is
  `Env.Val`; there is no atom evaluator into it yet. A string literal is refused by the
  typing (`litVal`), which is honest: strings are not machine values on either route
  (`Native.lean:48-55`). A `Term` with an `Env.Val` atom table is a landing row (§9).

## 2. The provision algebra (proved)

All in `Effect4.Program.Provision.LayerTy` unless noted; every proof is a membership argument
over `mem_diff`/`mem_union` and closes at `propext`/`Quot.sound`.

| Law | Statement | Name |
| --- | --- | --- |
| provide keeps the dependent's outputs | `(s ◁ t).out = s.out` | `provide_out` (`rfl`) |
| weakening | `(s ◁ t).requires ⊆ s.requires ∪ t.requires` | `provide_requires_subset` |
| discharge | `k ∈ t.out → k ∉ t.requires → k ∉ (s ◁ t).requires` | `provide_discharges` |
| **closure** | `t.Closed → s.requires ⊆ t.out → (s ◁ t).Closed` | `provide_closed` |
| closure, converse | `(s ◁ t).Closed → s.requires ⊆ t.out` | `covers_of_provide_closed` |
| **associativity up to provideMerge** | `(l ◁ d₁) ◁ d₂` and `l ◁ (d₁ ◁⁺ d₂)` have the same `out` and `requires` | `provide_provide_rows` |
| merge is commutative on rows | `(a ⊕ b)` and `(b ⊕ a)` have the same rows | `merge_rows_comm` |
| merge provides nothing to siblings | `k ∈ a.requires ∨ k ∈ b.requires → k ∈ (a ⊕ b).requires` | `merge_requires` |
| antitone in the dependency's outputs | more outputs, fewer requirements | `provide_requires_antitone_out` |
| the adjunction | `ctx.Satisfies r ↔ r ⊆ ctx.keysRow` | `satisfies_iff_subset_keysRow` |
| app closure | `(appTy app).requires = ∅ ↔ l.Closed ∧ p.requires ⊆ l.out` | `appTy_closed_iff` |
| **build totality** | typed leaves + `layerTy l = some t` + `ctx ⊨ t.requires` → `build l ctx = some out ∧ out ⊨ t.out` | `build_total` |

Row-level lemmas added to `Row` (to move into `Data/Row.lean`): `mem_diff`, `diff_subset`,
`diff_empty`, `diff_self`, `diff_eq_empty_iff_subset`, `diff_union_right`,
`union_diff_distrib`, `diff_subset_diff_left`, `diff_subset_diff_right`.

Three sentences the laws license, which are the ones users of Effect actually need:

1. **"Why does my `Layer.provide` still say it requires `Db`?"** Because `Db ∉ out d` or
   `Db ∈ requires d` (`provide_discharges` is an iff-shaped pair with
   `covers_of_provide_closed`). `merge_requires` says the other common mistake exactly:
   siblings under `merge`/`mergeAll` provide nothing to each other.
2. **"Can I regroup my `provide` chain?"** Yes, on the rows: `provide_provide_rows`. The
   error column is `Ty.join`, whose associativity is an owed row of the type language
   (§9 R7), so the theorem is stated over `out` and `requires`.
3. **"Does provider order matter?"** Not to the type (`merge_rows_comm`), yes to the run:
   the spike lifts counterexample CE 5 of `Machine/Context.lean` to layers
   (`leftWins`/`rightWins`: same `layerTy`, different built contexts through both the
   specification and the machine). The type sees rows; the run sees a right-biased merge.

## 3. The specification and its refinement into the machine

`build sem : LayerTerm Op → Ctx → Option Ctx` is the *high-level model* of provisioning, in
the sense Burckhardt et al. use for Durable Functions (§7): a fault-free, scheduler-free
function of the term and the context. `provide` builds the dependency, merges it into the
context, builds the dependent there and keeps the dependent's output; `provideMerge` answers
`that.merge merged`; `merge` answers the right-biased merge; `fresh` is invisible. These are
the machine's own continuations (`Layer.lean` `provideThenK`, `combineWithK`,
`mergeExitContexts`) with the memo map, the scopes and the fibers erased.

`build_total` is proved once, parametric in the leaf semantics: any `LeafSem` that is honest
about its own leaves (`LeafSem.Typed`: a leaf builds whenever its own requirement row is
satisfied) makes every well-typed layer build under every satisfying context, with the
output row satisfied. This is the theorem behind the sentence "the `R` channel guarantees the
wiring"; it does not mention memoisation, scopes or fibers because the wiring guarantee does
not depend on them.

The refinement into the machine is `lower`, a data-to-data map into the proved
`LayerTable`/`LayerDesc`/`Construction` alphabet, and the receipts are finite probes: the
lowered docs deployment runs through `runSyncExit` at the machine's `interp` and answers a
context whose keys are exactly `build`'s (plus `CurrentMemoMap`, `Layer.ts:762`), the values
flow from bindings to services, `Effect.provide(Effect.service(Db), deployment)` answers the
binding's value, and the sibling mistake dies with `serviceNotFound` — a defect, never a typed
error (`Layer.ts:807` through `internal/effect.ts:670-674`). The refinement mapping in
Lamport's sense is `keysRow ∘ decode` of the machine's answer; the general theorem
`lower_refines_build` is owed (§9 R3) and its history variable is the set of built layer ids
in the memo world.

Where the lowering is partial, it says so: `orDie` has no `LayerDesc` at this pin
(`Layer.ts:3327` is a `catchCause` frame the alphabet lacks) and lowers to `none` while its
type still says `E := never`; an `effect` body outside {one `perform` reading one service,
one literal, one numeric `fail`} has no `Construction` and lowers to `none`. Both are
refusals as data, both are landing rows.

## 4. A cloud deployment is a closed layer (`workshop/Provision/Deploy.lean`)

The Surface carrier `Deployment` (`Surface/Deploy.lean`) already holds the three facts a
layer needs: `bindings` (what the platform provides), `provides : (service, binding | builtin)`
(what the worker builds and from what), and `satisfies` (what the mounted apis require).
The lowering, with names mapped to keys by position in a name table (the model's stand-in
for rc.112's tag-string identity, `Context.ts:32-41`):

```
bindingsLayer dep   := mergeAll [ Layer.succeed(key b.name, env index) | b ∈ dep.bindings ]
servicesLayer dep   := mergeAll [ Layer.effect(key s, read binding p) | (s, p) ∈ dep.provides, p ≠ builtin ]
                                 ++ [ Layer.succeed(key s, unit)      | (s, builtin) ∈ dep.provides ]
deploymentLayer dep := servicesLayer.pipe(Layer.provideMerge(bindingsLayer))     -- Layer.ts:2704
```

The theorem: `Deployment.ProvidersKnown dep → (deploymentLayer dep).Closed`, i.e. the
`providersKnown` clause of `Deployment.check` is the hypothesis of `provide_closed`. The
wrangler configuration a worker deploys with *is* `Layer<Bindings ∪ Services, never, never>`.

The relation to the string law: `Deployment.RequirementsMet dep reqs` implies that every
mounted requirement's key is in the layer's output row. The converse fails, by exactly the
bindings: a mounted api that requires a name equal to a binding's name is row-satisfied (the
binding *is* a service in the worker's context, `env.DB`) and string-refused
(`requirementUnprovided`). The row law is the faithful one; the string law is stricter, and
the difference is a `#guard` in the module. (Results as reported by the lane are recorded in
§10 when they land.)

What "demystified" means here, concretely: provisioning is not a separate world with its own
semantics. Terraform's *plan* is `layerTy`; its *apply* is `build`; its *state file* is the
memo world (`MemoWorld`, `Layer.ts:421-458`), which the machine already models with observer
counts and last-observer close; its *destroy* is the scope close in reverse registration
order (`FinalizerStrategy.sequential`, `internal/effect.ts:3813-3818`); `fresh` is "do not
share this resource" (`Layer.ts:3850`). Every one of those is a proved clause of the Layer
machine, and the spike is the typed face over it.

## 5. Authentication is a requirement transformer (`workshop/Provision/Auth.lean`)

rc.112's `HttpApiMiddleware.Service` config is `{ requires, provides, error, security }`
(`HttpApiMiddleware.ts:320-346`) and its action on a handler's requirement row is stated as
a type: `ApplyServices<A, R> = Exclude<R, Provides<A>> | Requires<A>` (`:199`). That is
`LayerTy.provide` verbatim, and the module proves it so
(`applyServices_eq_provide`, definitional). A security middleware (`HttpApiSecurity`:
`bearer` `:154`, `apiKey` `:177`, `basic` `:205`) additionally requires what
`securityDecode` reads — `HttpServerRequest` and, for a query api key, the parsed search
params (`HttpApiBuilder.ts:481-487`) — which the router provides (`HttpRouter.Provided`,
`HttpApiMiddleware.ts:70`). Middlewares apply in declaration order, each wrapping the handler
(`HttpApiBuilder.ts:863-870`).

The theorems: a provided key is discharged; `apply` is monotone; independent middlewares
commute and dependent ones do not (a `#guard` pair); the residual of a chain never exceeds
"what nobody provided plus what everybody required"; and **no auth, no user**
(`residual_unprovided`): a key no middleware provides survives every middleware. On the docs
app, the `POST /feedback` handler that now requires `{Db, RateLimit, CurrentUser}` has
residual `{Db, RateLimit, HttpServerRequest}` under the bearer middleware and `{Db, RateLimit}`
after the router — which is exactly the deployment's row of §4. The three rows compose:
handler ◁ middleware ◁ router ◁ deployment, closed.

The boundary, named as a refusal row **`PROV-FB-KEY-FORGERY`**: keys are first-order data,
so a `Layer.succeed(CurrentUser, …)` in a deployment types as providing `CurrentUser` just
as the security middleware does (the `LAYER-FB-LAYER-IDENTITY` shape of `Layer.lean:33-40`).
Unforgeability of a service tag is the host's object identity (`Context.ts:32-41`), not a
theorem of this model. The model's theorems say what a *typed wiring discharges*; who is
*allowed* to provide a key is a capability question the model records and does not decide.
This is the same honesty the engineering-assurance note asks for ("permissions/capabilities:
set union or a separation algebra; split/merge under ownership laws" — the union half is here,
the ownership half is the host's).

## 6. Service definition, configuration, and what is not here

* **Service definition** already is a row: a service is a `ServiceKey` plus its operation rows
  (`Codegen/Profile.lean` `ServiceRow`, rendered as `class X extends Context.Service<X, Shape>()`),
  and each row's `requires : List ServiceKey` is what `typeOf` folds into `EffTy.requires`.
  The spike's `DocsOp` alphabet is exactly that shape. Nothing new is needed; what was
  missing was the algebra *over* the rows, which is §2.
* **Configuration** (`Config.ts:108`: `Config<T> extends Effect<T, ConfigError>`;
  `ConfigProvider.ts:341`: a `Context.Reference` with a default, `fromEnv` `:1183`) is the
  *reference* half of provisioning: a reference key is satisfied by every context
  (`Context.getOption_reference_default`), so a config read has no hard requirement. The
  spike states it: `SatisfiesRefs` (satisfaction through `getOption`),
  `satisfiesRefs_of_defaults` (a row of reference keys is satisfied by the empty context), and
  `satisfiesRefs_of_hard` — a context satisfying `r ∖ soft` satisfies `r` under the
  references, which is the deployment's obligation with the configuration subtracted; the
  scheduler's two references (`Scheduler.ts:269-298`) are the `#guard`. What is left for
  landing row R8 is the key-table split (`KeyKind := service | reference`) so `layerTy` can
  subtract the soft row itself.
* **Not here, on purpose:** `Layer.mock`, `LayerMap`, `LayerRef`, `Layer.span`, `unwrap`,
  `flatMap`, `catchTag`/`catchCause` (`Layer.ts:2882-3720`) — closure-carrying combinators
  that the corpus uses rarely and that would put a Lean function in canonical content; each
  is a stated refusal, never a fabricated leaf.

## 7. The literature, and what each piece contributes

| Source (on this PC unless noted) | Contribution to this design | Boundary |
| --- | --- | --- |
| Kuessner, Mogk, Wickert, Mezini, *Algebraic Replicated Data Types* (ECOOP 2023, `2023 Secure ARDTs (preprint).pdf`); Pfeil, Scandurra, Haas, *AegisSheet* (2026, `3806077.3806695.pdf`) | consistency as lattice structure, by construction ("the CALM theorem implies that monotonicity …", their §4; delta replication; encryption and authentication as `AEAD[S, A]` messages merged like any other delta, their §5, with coordination-free nonce generation in §5.2): the requirement row is the join-semilattice, so requirement checking is monotone and coordination-free; their authenticated deltas over untrusted intermediaries are the shape a *signed context entry* would take | contexts are not a semilattice (right-biased merge); ARDT-style signed provisions are future work (§9 R9) |
| Burckhardt et al., *Durable Functions: Semantics for Stateful Serverless* (OOPSLA 2021, `Foldable/research/DF-Semantics-Final.pdf`) | the method: an idealised fault-free high-level model (their §3–4, with critical sections in §4.6 as `lock⟨⟩` over entities), then execution models with compute-storage separation and record-replay, proved equivalent (their Theorem 5.3, a weak simulation hiding commit messages; Theorem 6.4, a bisimulation); `build` is the high-level model, the Layer machine over a decision tape is the execution model, and the estate's replay determinism (DB-03) is their record-replay | their equivalence is a theorem; ours is finite probes plus an owed theorem (§9 R3) |
| Lamport & Merz, *Prophecy Made Simple* (2020, `leslie_lamport.pdf`) | the refinement-mapping vocabulary for `lower_refines_build` (their §3–4.1: a history variable `h` recording what was input so far, the mapping `seq ← h`); the memo world's set of built ids is that history variable; no prophecy is needed because the tape fixes every choice; their §7 completeness (history + stuttering + simple prophecy suffice) says the refinement exists if the two models agree at all | — |
| Li, Stutz, Wies, Zufferey, *Complete MST Projection with Automata* (CAV 2023); Barwell, Hou, Yoshida, Zhou, *Crash-Stop Failures in Asynchronous MPST* (LMCS 2023); SPROUT (CAV 2025 proceedings) — `Foldable/tmp/pdfs` | service definition as a global protocol whose server handler and client are projections; the estate already generates both faces of one `Api` (`HttpApi` module, client module, OpenAPI); crash-stop is the `Cause`/interruption channel | protocol projection is not in scope of this note; it is the next altitude above "which services does a handler need" |
| `Foldable/research/2026-08-20-choreographic-programming-calm-and-algebraic-projection.md` | "infer a coordination effect row" — the requirement row *is* an effect row; classify transforms as monotone/join-preserving (`apply_mono`, `provide_requires_antitone_out`) | — |
| `Foldable/research/2026-08-20-lean4-engineering-assurance-modeling.md` | `Budget.authority : CapabilitySet`; "state and cleanup are capability interfaces"; capabilities compose by union or a separation algebra | the union half is here; ownership (who may provide) is the host's, hence `PROV-FB-KEY-FORGERY` |
| `Foldable/research/2026-08-20-formal-agent-workflows-and-algebraic-meaning.md` | "reify the plan; verify capabilities"; MCP as "a typed capability and tool transport" | — |
| Rashie & Rashi, *Type-Checked Compliance* (2026, `2604.01483v1.pdf`) | "an action is permitted iff the kernel proves it" — `Deployment.satisfies`/`appTy_closed_iff` decided by `decide` is that pattern for deployments | their guardrail is on agent actions; ours is on wiring |
| LAMP (`2606.28841v1.pdf`), LeVer (`2026.acl-long.1836.pdf`) | agent loops with MCP tools and attack/repair cycles: the shape of the substrate note's §7 loops | not used here |
| Dvořák's thesis (`2602.12891v3.pdf`) | not relevant to this note | — |
| Mac, `lean4-effects/docs/CLAIM-BOUNDARY.md` | "no theorem transfer between handlers"; hence `build_total` is parametric in a *typed* `LeafSem` and says nothing about an untyped one | — |

## 8. Grill

Attacks against full reification and the lowering path, seam by seam (the standing rule of
`plans-markdown-and-grilled`).

**"You built a second Layer model."** No: `LayerTerm` lowers into the proved
`LayerDesc`/`Construction` table and the witnesses run the proved `interp`. `build` is not a
machine; it is the specification the machine refines, and it has no memo map, scope or fiber
because the wiring theorem does not need them. The only new semantics is the *typing*, which
rc.112 has only as TypeScript types.

**"`build_total` is parametric in `LeafSem.Typed`, so it proves nothing about real leaves."**
It proves the compositional half once; the leaf half is the machine's `Context.interpret_total`
(a program using only its row never meets a missing lookup). The spike's `docsSem` is typed on
its fragment by construction (a `perform` body reads its row's one key). Joining the two is
landing row R3.

**"The Eff route cannot run any of this."** Correct, and it is the finding of §0: the Eff
compile's `Ctx` is a three-field record with no service map (`Stores.lean:138`), so
`Effect.service`, `provideService` and `Effect.provide` are inexpressible on the Eff route
today, and `RowKind.program` compiles to the frontier. The landing (§9 R1, R2) merges the
alphabets (the S5 report's §6 shims, still owed) so that one `RunInterp` carries the map;
until then the Layer machine is where provision runs, and `App` lowers only to
`provideLayer` with a `ProgName` body. This note does not pretend otherwise.

**"`succeed` over a literal is a toy."** It is the fragment the machine's `Construction`
admits; a `Term` with an `Env.Val` atom evaluator is a small landing row (R5), and the
deployment lowering needs only indices (the host object stand-in every store already uses).

**"The string deployment law and the row law disagree."** They do, by the bindings, and the
row law is the faithful one (§4). The landing keeps `Deployment.satisfies` as the emitter's
guard and adds the row law beside it with the theorem relating them; nothing is retracted.

**"Authentication is more than a row."** It is: credential decoding, redaction, the
first-success-wins loop over security schemes (`HttpApiBuilder.ts:896-920`) are behaviour,
not rows. This note claims only the *requirement* content of authentication — which key a
security middleware discharges and what it costs — and names the forgery boundary. The
behavioural clauses are `HttpApiBuilder` census rows for a later machine lane.

**"`orDie`, `mock`, `unwrap`, `flatMap` are missing."** `orDie` is typed and refused by the
lowering with a named reason; the closure-carrying combinators are refused by design (DB-02).
Coverage is stated by the census, never by this note.

**"`Ty.join` has no laws."** True and pre-existing: `provide_provide_rows` is stated over the
rows because of it. R7 adds `join_assoc`/`join_comm`/`join_idem` to the type language.

**"Does it land without a redesign?"** The carriers are additive: `Row.diff` beside `union`;
`LayerTy`/`LayerTerm`/`App` as new modules; no change to `Eff`, `Ty`, `Row`, the machine or
the Surface carriers. The one decision with a redesign risk is D1 (§9): whether `Eff` gains
`provide`/`service` constructors (a mutual block with `LayerTerm`, touching the wire, the
printer, the typing, the compile and the OCaml `eff` library) or whether provision stays an
`App` boundary around a program. The spike works under the second reading; the corpus
(`Effect.provide` inside `gen` bodies, 13.7k sites) argues for the first eventually. The
plan lands the second now and stages the first behind the alphabet merge.

## 9. Landing plan

One landing, coordinator-run, after the two lanes report. Files and moves are exact.

| # | Piece | Files | Who |
| --- | --- | --- | --- |
| R1 | `Row.diff` and its nine lemmas move into `src/Effect4/Data/Row.lean` after `union`; `Requirement.diff` alias in `Machine/Context.lean` | `Data/Row.lean`, `Machine/Context.lean` | coordinator (shared surfaces) |
| R2 | `LayerTy`, `LayerTerm`, `layerTy`, `App`, `appTy`, `LeafSem`, `build`, `build_total`, `lower`, the run helpers → `src/Effect4/Program/Provision.lean`; the docs witnesses → `Test/Program/ProvisionContract.lean` | new modules; `src/Effect4.lean` and `Test/All.lean` gain one import each | Opus, mechanical |
| R3 | the refinement theorem `lower_refines_build`: for terms in the lowered fragment, the keys of the machine's built context equal `build`'s under `docsSem`-shaped leaves; history variable = built ids | `Program/Provision.lean` | coordinator (design) |
| R4 | `Deploy.lean` → `src/Effect4/Surface/Provision.lean` (the deployment-as-layer join, `deploymentLayer_closed`, `requirementsMet_row`, the binding-name counterexample as a register row) | new module; `Surface/Deploy.lean` untouched | Opus |
| R5 | `succeed` over `Term` with an `Env.Val` atom table; `effect` bodies beyond the `Construction` fragment through the alphabet merge (S5 §6 shims) | `Program/Provision.lean`, `Machine/Layer.lean`, `Machine/Stores.lean` | after the merge |
| R6 | `Auth.lean` → `src/Effect4/Surface/Middleware.lean`; `Endpoint.security` read through `securityRequires`; a `middlewares : List Middleware` field on `Endpoint` is a v2 row (rc.112 `endpoint.middlewares`) | new module | Opus |
| R7 | `Ty.join` laws (`assoc`, `comm`, `idem`, `never` identity) so the error column joins the algebra | `Program/Eff.lean` | Opus |
| R8 | the reference split: `KeyKind := service \| reference` on the key table; a reference is satisfied by every context (`getOption_reference_default`); `Config`/`ConfigProvider` rows | `Machine/Context.lean`, `Program/Provision.lean` | later |
| R9 | the printer: `LayerTerm`/`App` → `TypeScript.Expr` (`Layer.succeed(K, v)`, `Layer.effect(K, …)`, `.pipe(Layer.provide(…))`, `Layer.mergeAll(…)`, `Effect.provide(p, l)`), key spellings as a table, `#guard` goldens on syntax never text | `Codegen/Layer.lean` | Opus (lane C, this session) |
| R10 | refusal rows `PROV-FB-KEY-FORGERY` (who may provide is the host's), `PROV-FB-ORDIE-DESC` (`orDie` has no `LayerDesc` at this pin), `PROV-FB-STRING-VALUE` (strings are not machine values); census rows for `Layer.provide`/`provideMerge`/`merge` typing joined to the sixteen `layer.*` rows | `Test/Counterexamples/REGISTER.md`, `Test/Audit/RuntimeCoverage.lean` | coordinator |
| D1 | **decision:** `Eff` gains `provide (layer) (body)` and `service key` (a mutual block with `LayerTerm`; wire tags, printer, typing, compile, OCaml `eff` parity all move) versus provision as the `App` boundary only | — | owner |
| D2 | **decision:** keep `Deployment.satisfies` (strings) as the emitter's guard beside the row law, or replace it by the row law with a name table on the deployment | — | owner |

Gate at landing: `lake build Effect4 Test` green on Windows, `#print axioms` at
`propext`/`Quot.sound` for every theorem of R1-R4/R6, the bash gates in the WSL clone, and the
commit by pathspec (the tree carries other sessions' uncommitted work).

## 10. Lane results

**Auth lane (`workshop/Provision/Auth.lean`, landed as `src/Effect4/Surface/Middleware.lean`):**
green on the first elaboration; `residual_unprovided`, `residual_subset`,
`apply_comm_of_disjoint` at `propext`/`Quot.sound`; 23 `#guard`s. Beyond §5's design the
lane pinned four things worth keeping. (1) `securityRequires` transcribes the *declared*
decoder row (`HttpApiBuilder.ts:503-506`: an api key in the query needs both router
services); the sharper reading — `schemaSearchParams` reads only `ParsedSearchParams`
(`unstable/http/HttpServerRequest.ts:223-233`), `schemaCookies`/`schemaHeaders` only
`HttpServerRequest` (`:195-201`, `:209-215`) — is an owed row. (2) `HttpRouter.Provided`
(`unstable/http/HttpRouter.ts:853-857`) is a four-way union; the model carries
`HttpServerRequest` and `ParsedSearchParams`, `Scope` is the layer's own `bodyRequires`, and
`RouteContext` is owed. (3) `mem_residual_of_requires` quantifies over the whole chain
("no middleware provides it") rather than the suffix; the sharper "no later one" is true
(a `#guard` exhibits that an earlier provider is harmless) and owed. (4) The join to
`Endpoint.requires : List String` needs the name table of §4; owed with it.

**Deploy lane (`workshop/Provision/Deploy.lean`, landed as `src/Effect4/Surface/Provision.lean`):**
green; `deploymentLayer_closed` and `requirementsMet_row` proved at the ceiling, with the
fold lemmas `layerTy_mergeAll`/`layerTy_mergeLeaves` and the leaf-list rows `bindings_rows`/
`services_rows` as the route. The docs fixture lowers to a closed layer providing six keys,
builds through the machine as `[(4, 0), (5, 1), (6, 2), (7, 3), (8, 1), (9, 0), (3, 0)]`
(bindings first with their indices, then the services holding their binding's index, then
`CurrentMemoMap`), and `Effect.provide(Effect.service(Db), deployment)` answers `DB`'s
value. Two findings forced by the machine, both kept: (1) **a name table must skip the
machine's four reserved keys** — at shift one the docs table's first binding lands on
`maxOpsKey` with value `0`, `budgetOf` reads `MaxOpsBeforeYield := 0`, the services build
yields on every step and `runSyncExit` dies with `AsyncFiberError`; `keyOf` shifts by four
and `keyOf_ne_scopeKey` is the theorem that keeps the effect leaf's requirement row honest
(register row `E4-PROV-CE-007`). (2) Seeding the `mergeAll` fold with `Layer.empty` types
identically but does not finish inside `runOver`'s 512-step budget (a fuel frontier, DB-04,
not a failure); the fold is seeded with its own head, which is also the closer reading of
`Layer.mergeAll(l, …)`. The string-versus-row law gap is `E4-PROV-CE-006`.

**Printer lane (`workshop/Provision/Print.lean`, landed as `src/Effect4/Codegen/Layer.lean`):**
green; 22 `#guard`s on syntax, two on rendered bytes; `printAppDecl` reuses
`Program.printDecl` so the two-parameter `Effect.Effect<A, E>` appears exactly when the app
is closed (`appTy_closed_iff`), and `printLayerDecl` spells `Layer.Layer<ROut, E, RIn>` with
the rows in canonical key order. One spelling decision recorded in the module: a left-nested
merge chain flattens *totally* into one `Layer.mergeAll(…)` (so a chain whose first operand is
itself a merge contributes that operand's operands too), a plain `merge` of two leaves prints
`Layer.merge(a, b)`. `orDie` prints even though the lowering refuses it: the printer's
alphabet is rc.112's public exports, the machine's is `LayerDesc`.

**Gate and landing:** `lake build Effect4 Test` green at 202 modules / 23,885 declarations,
runtime coverage 134 / 1 / 0 of 135 unchanged, every new theorem at `propext`/`Quot.sound`;
landed as commit `f182d2b` (2026-09-04), fifteen files, the workshop spike deleted and the
lakefile restored. The bash gates in the WSL clone are owed for this commit, as for every
Windows landing.
