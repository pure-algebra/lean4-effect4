# Ground requirements — Layers, dependencies, runtimes, and Scope

**Slice:** REQUIREMENTS scout, Layer/Scope/Environment design pass.
**Author:** Opus 5 (Mac), 2026-08-31.
**Status:** PRE-GRADE / SCOUT LEDGER. **Claim gate: none.**
A row here records what the surface demands and what breaks without it. No row
ratifies a declaration, promotes a theorem, or closes a packet condition.

This is the *requirements* half of the pass. It does not propose a carrier.
Where it says a representation is refuted, that is a negative result about the
representation named in `REIFICATION-CHECKLIST.md`, not a proposal to replace it.

---

## 0. Method, and what the evidence actually is

Three sources, in descending authority:

1. **The pin, read directly.** `effect@4.0.0-rc.112`, source at
   `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/`
   (`package.json` version confirmed; an identical copy sits under
   `experiments/workbench/node_modules/effect`). Every `Layer.ts` / `Scope.ts` /
   `Context.ts` / `Effect.ts` / `ManagedRuntime.ts` line number below was read
   there. The packet's tsgo fixture at
   `.staging/effect-core-v1/workshop/tsgo/node_modules/effect` is a two-file stub
   and is NOT the pin; do not read the surface from it.
2. **Kernel-checked probe.** `LayerGround.lean`, source inlined at Appendix A,
   run against `library/cas` with a warm cache: **exit 0, 11 receipts, ceiling
   `[propext, Quot.sound]`, 3 axiom-free, no `sorryAx`, no `Classical.choice`.**
   Nothing in this report that could have been checked is asserted without it.
3. **The register.** `COUNTEREXAMPLES.md` rows cited by stable ID;
   `.staging/agent-reports/2026-08-31-effect-core-s17-rulings.md` R18.

The largest structural finding came from (1), not (3), and it resets the question:

> **rc.112's `Layer` has exactly one member, and it is a closure.**
> `Layer.ts:54–60`: `interface Layer<in ROut, out E, out RIn>` whose only
> non-phantom field is `build(memoMap: MemoMap, scope: Scope.Scope):
> Effect<Context<ROut>, E, RIn>`. There is no Layer *datum* at the pin at all —
> no node list, no edge list, no tag. Under **R7** (programs are content, hosts
> are code) that closure cannot be content, so the reification is not
> "represent Effect's Layer graph in Lean". It is **"supply the first-order
> object rc.112 never had, and prove its interpretation is that closure."**
> `EC1-XT104`'s `separateCalculus` disposition is right; its stated reason
> ("Layer remains a dependency/resource-building calculus") understates the
> forcing. The forcing is R7 against a bare closure.

---

## 1. Four structural facts that the checklist row does not carry

These are read off the pin and each one moves a requirement grade below.

**F1 — `Scope` is a service, not an index.**
`Scope.ts:215`: `export const Scope: Context.Service<Scope, Scope> =
effect.scopeTag`. It lives in the same `Context` map as every user service.
Consequently `Layer.build` types as `Effect<Context<ROut>, E, RIn | Scope.Scope>`
(`Layer.ts:800`), `effectContext` types as `Layer<A, E, Exclude<R, Scope.Scope>>`
(`Layer.ts:1479`), and `Effect.scoped` *is* `provideService(Scope)`. There is
one provisioning mechanism, not two. A design that gives `Scope` its own index
must then restate every `Exclude<R, Scope>` transform by hand, and will not match
the pin's declared types.

**F2 — memoization is reference-keyed, reference-counted, and owns a scope.**
`Layer.ts:380–386`: `fromBuildMemo` builds a self-referential layer whose memo
key is *the layer object itself* (`memoMap.getOrElseMemoize(self, …)`).
`Layer.ts:421–457`: `MemoMapImpl.map = new Map<Layer, MemoMapEntry>()` with a
parent chain. `Layer.ts:390–419` (`memoMapBuild`) allocates a **separate
`layerScope`** owned by the memo entry, sets `observers: 1`, and registers a
finalizer into the *consumer's* scope that decrements; only at `observers === 0`
does it `memoMap.map.delete(layer)` and `Scope.close(layerScope, exit)`.
`Layer.ts:241–250` (`memoMapReuse`) increments and registers another decrementing
finalizer. So sharing decides **which scope owns the resource** and **when it is
released** — not merely how many times a build effect runs.

**F3 — `merge` is concurrent, and it mixes finalizer strategies.**
`Layer.ts:1705` `merge` → `mergeAll` (`:1652`) → `mergeAllEffect` (`:1587–1602`),
which forks a `"parallel"` parent scope, gives each layer its own `"sequential"`
child scope, and runs them with `concurrency: layers.length`. Value combination
is `Context.mergeAll` (`Context.ts:1861–1871`), which is **last-wins in argument
order** and independent of acquisition order. So `merge` is deterministic in the
*service values* it yields and nondeterministic in the *acquisition trace*, and
its finalizers do not run LIFO.

**F4 — the layer "graph" is not a graph.**
`flatMap` (`Layer.ts:3038–3047`) computes the successor layer *from the built
context*: `flatMap(self.build(memoMap, scope), (context) => f(context).build(memoMap, scope))`.
`unwrap` (`:1580–1585`) goes further and stores a **`Layer` value inside a
`Context`** under the key `"effect/Layer/unwrap"`. `suspend` (`:1543`) and
`catchCause` (`:3691–3700`) are the same shape over a thunk and over a `Cause`.
The dependency structure is therefore *monadic over contexts*, not a static
node/edge set. The checklist row's representation — "service nodes, dependency
edges, ordered composition, memo key" — describes only the first-order fragment.

---

## 2. The requirement ledger

Grades: **MUST** — the surface is wrong or unstatable without it.
**SHOULD** — droppable at a named, non-trivial cost.
**MAY** — derived, or v1-optional; dropping costs an expansion law at most.
**MUST-DECIDE** — the design cannot stay silent; either arm is defensible, but
silence is a defect.

IDs are packet-local to this scout file (`GR-*`) and carry no authority.

### 2.1 Environment and services

| ID | Capability | Grade | Evidence | What breaks if dropped |
|---|---|---|---|---|
| `GR-E1` | Service identity is a **string key**, first-order | MUST | `Context.ts:64–69` (`Key` has `readonly key: string`); `Context.ts:617–622` (`Context` *is* `ReadonlyMap<string, any>`) | R7 fails on the identity side: requirement rows cannot be hashed, stored, diffed, or shipped, and `R` synthesis has nothing to synthesize over. This is the one part of the pin that is *already* content-shaped; discarding it is pure loss. |
| `GR-E2` | `ask key` — a one-operation program answering the service shape | MUST | `Effect.ts:11914` `service`; `Context.ts:64` `Key<I,S> extends Effect<S, never, I>` — a key **is** an effect | No consumer side. Also loses the cleanest R12 alignment: `Key` being an `Effect` is exactly "a service is a handler, addressed by a one-op program". |
| `GR-E3` | Discharge by exclusion: `provideService` gives `Exclude<R, I>` | MUST | `Effect.ts:12324–12420` | `R` never empties, so no program is ever runnable and `runSync`'s `R = never` constraint is unreachable. This is what the index is *for*. |
| `GR-E4` | Accretion: `updateService` gives `R \| I` — it **demands**, never discharges | MUST | `Effect.ts:12131–12207` | Silently confusing update with provide under-approximates `R`; a program typechecks and then fails at the edge with a missing service. The asymmetry with `GR-E3` is the whole content of the row. |
| `GR-E5` | Shadowing: innermost provision wins; `Context.mergeAll` is last-wins in argument order | MUST | `Context.ts:1861–1871`; `Layer.ts:1920–1923` (`provideWith` applies `provideContext(context)` to `self.build`) | `provide` stops being a function of its arguments. Nested `provide` chains — the ordinary case — have no defined meaning. |
| `GR-E6` | `Reference`: a key with a default, so lookup is **total** | SHOULD | `Context.ts:485`, `:2002–2009` (`Reference = Service` plus `defaultValue: () => Service`) | Every environment read acquires an error arm, and `E` inflates across the whole surface. Droppable because the checklist's own answer — "Reference default is an explicit handler clause" — is a correct encoding; the cost is that the totality is then a handler property, not a type property, and must be re-proved per handler. |
| `GR-E7` | Unrelated-service commutation | SHOULD | checklist row 884, "where stated" | No algebraic normalization of provide chains; every rewrite becomes a bespoke proof. Sound without it, just unwieldy. Note it is *false* in general: two provisions of the same key do not commute (`GR-E5`), so the law needs a disjointness premise and cannot be stated unconditionally. |
| `GR-E8` | `Context` as a first-class value (`Effect.context()`, `succeedContext`, `provideContext`) | MUST | `Effect.ts:11287`; `Layer.ts:1129`, `:1479` | `Layer` cannot even be *typed*: its build returns `Context<ROut>`. Without a context value there is no layer output. |
| `GR-E9` | A ruled boundary on what a service **value** may be | MUST-DECIDE | `Context.ts:622` (`ReadonlyMap<string, any>`); `Layer.ts:1580–1585` — `unwrap` stores a **`Layer`** as a service value | R7 is violated silently. The key side is content (`GR-E1`); the value side is `any`, and rc.112 puts closures, and layers, in it. Either the value schema is first-order and `unwrap` is refused/target-only, or the schema is recursive and admits layers as content. Staying silent means the census admits arbitrary closures through the environment while refusing them everywhere else. |

### 2.2 Scope and resources

| ID | Capability | Grade | Evidence | What breaks if dropped |
|---|---|---|---|---|
| `GR-S1` | Scope is provisioned **as a service**, not as a separate index | MUST | F1: `Scope.ts:215`; `Layer.ts:800`, `:1479`; `Layer.ts:1481` `Scope.provide(effect, scope)` | Two provisioning mechanisms with two law sets; and every `Exclude<R, Scope.Scope>` in the pin's declared types becomes unstatable, so §6.2's `indexTransform` fixtures cannot be reproduced. Refines `EC1-XT106`: the **key** is content, the **scope object** is not. |
| `GR-S2` | Three scope states, `Closed` carrying the exit | MUST | `Scope.ts:45–49`, `:99–110` (`State.Open \| Closed \| Empty`) | Close-idempotence and double-close have no statable subject. `Empty → Closed` without a finalizer effect is a real transition the pin distinguishes; erasing it makes "close is idempotent" a claim about nothing. |
| `GR-S3` | **Exit-indexed** finalizers | MUST | `Scope.ts:422` `addFinalizerExit(scope, (exit) => …)`; `Layer.ts:339–345` — `fromBuild` closes its layer scope with `Scope.close(layerScope, exit)` on `Failure` | `acquireRelease`'s release cannot branch on failure; `EC1-T066` (`cause_finalizer_then`) has no input to combine. **This is a gap in the R18 record, not merely in the pin's coverage:** `EC1-CE045`'s exhibited `ensuring` takes a finalizer of type `WComp` — exit-blind. Probe §4 checks that the exit-indexed form **is** expressible in the R18 target and satisfies word-preservation, refusal-preservation, and genuine exit-dependence (`ensuringExit_keeps_the_word`, `ensuringExit_never_replaces_the_refusal`, `ensuringExit_reads_the_exit`). So the missing thing is a law, not a carrier. |
| `GR-S4` | Per-scope **finalizer strategy** (`sequential` \| `parallel`) | MUST | `Scope.ts:240` `make(finalizerStrategy?)`; `internal/effect.ts:3813–3826` — `sequential` awaits each finalizer in reverse order, `parallel` forks all and `fiberAwaitAll`s; `Layer.ts:1596–1597` mixes both in one build | `EC1-T064` (`release_lifo`) is stated unconditionally and is **false** for a parallel-strategy scope — a scope `Layer.mergeAll` creates on every merge. See §4/C2. |
| `GR-S5` | Scope forking with ownership; a child scope's resources do not escape | MUST | `Scope.ts:489` `fork`; `Layer.ts:339` `Scope.forkUnsafe(scope)` inside every `fromBuild` | `EC1-T060` (`region_non_escape`) loses its region structure, and every layer's private resources are owned by the consumer scope. Layer-local acquisition is then indistinguishable from consumer acquisition. |
| `GR-S6` | Exactly-once release stated as **dependence**, never as a count | MUST | `EC1-CE007`; `EnsuringRepair.lean` `store_finalizer_is_word_idempotent`; probe §2 `memo_is_invisible_in_the_word` (`decide`) vs `memo_counts` (`1` and `2`) | A counting statement is *vacuous* on content-addressed acquisition: `put n` twice leaves the same word. Any "released exactly once" law read at the word mask is trivially satisfiable by a clause that releases twice. |
| `GR-S7` | Release ordering claimed **only** for the sequential strategy | MUST | `internal/effect.ts:3815–3821` | Claiming LIFO unconditionally is a false theorem (see `GR-S4`). Claiming nothing loses the one ordering fact `EC1-CE006` makes observable — two puts in opposite orders leave different words, so release order *is* word-visible. |
| `GR-S8` | `acquireUseRelease`, `ensuring`, `scoped`, Pool/Resource | MAY (derived) | checklist row 886 | Nothing, if `GR-S3`+`GR-S5` are present: these are expansions over acquire / register / exit-indexed release. Each owes an expansion law, not a handler. |

### 2.3 Layer

| ID | Capability | Grade | Evidence | What breaks if dropped |
|---|---|---|---|---|
| `GR-L1` | A **first-order Layer datum** | MUST | `Layer.ts:54–60` — the only member is a closure; R7 | There is no artifact. Nothing to hash, version, store, ship, or generate. This is the entire reification. |
| `GR-L2` | Build is **scope-parameterised and memo-parameterised**: `build(memoMap, scope)` | MUST | `Layer.ts:56`, `:800`, `:863`, `:645` | Sharing and lifetime become ambient, and every law about either becomes a claim about a hidden global. Note the pin passes both *explicitly* through every combinator — this is the pin telling you what the denotation's arguments are. |
| `GR-L3` | `provide`'s A/E/R transform: `Effect<A,E,R>` → `Effect<A, E \| E2, RIn \| Exclude<R, ROut>>` | MUST | `Effect.ts:11383–11470`; `Layer.ts:2339–2348` for the layer-to-layer form | The generated TypeScript does not typecheck, and the §6.2 fixture the checklist names by hand cannot be reproduced. This is a *static* obligation: no runtime test reaches it. |
| `GR-L4` | `ROut` is **contravariant** — weakening on a Layer *forgets provided services* | MUST | `Layer.ts:54` (`in ROut`), `:98–104` (`_ROut: Types.Contravariant<ROut>`), against `Effect.ts:117` and `:154–157` (`out A, out E, out R`, all `Covariant`) | The subsumption direction inverts. The checklist's Type-indices row says "all three source indices are covariant"; that sentence is about `Effect` and is **false of `Layer`**. Carrying it onto the Layer row makes `Layer<A\|B> <: Layer<A>` come out backwards. |
| `GR-L5` | Sharing: one instance per memo key, with reference-counted release | MUST | F2: `Layer.ts:241–250`, `:390–419` | Three separate breakages, any one fatal: (a) a diamond yields **two** instances of a stateful service, observably different in any state-carrying target; (b) the resource's **owner** changes from the memo entry's `layerScope` to each consumer's scope; (c) n consumers run the finalizer n times — probe §3 `release_twice_is_word_observable` shows a non-idempotent release separates in the word. See §3, Q1. |
| `GR-L6` | A ruled **memo-key identity discipline**, and `fresh`'s escape from it | MUST-DECIDE | `Layer.ts:421` `Map<Layer, MemoMapEntry>` (reference identity); `Layer.ts:3850–3851` `fresh` = build against a brand-new `MemoMap`; **R4** (identity hashes presentations) | Under R4 the key becomes a content key, and a content-keyed memo map **shares strictly more than rc.112 does**: two `Layer.succeed(Tag, v)` calls are two objects at the pin and one datum under content addressing. Worse, `fresh(l)` and `fresh(l)` become equal, so `fresh` — whose entire purpose is *not* to be shared — is unrepresentable without an explicit nonce in the content. Nobody has written this obligation down. |
| `GR-L7` | `merge` / `mergeAll` are **concurrent** builds | MUST-DECIDE | F3: `Layer.ts:1587–1602` | Every "merge is associative / commutative" law silently quantifies over a concurrent acquisition. Under `EC1-CE006` (world sequencing is not commutative) and `EC1-CE042` (meaning is relational under decisions), those laws are available only under a **declared trace quotient**, and the Layer row is thereby entangled with slices S9/S10 that the DAG does not record. The defensible alternative is to admit a *sequential* merge in v1 and record the divergence from the pin. Silence is not available. |
| `GR-L8` | Context combination is deterministic (last-wins, argument order) even when acquisition is not | MUST | `Context.ts:1861–1871` | Merge becomes nondeterministic in the **service values** it yields, not merely in trace — a strictly worse failure than `GR-L7`, and one the pin does not have. |
| `GR-L9` | `provide`, `provideMerge`, and `merge` are **one builder** parameterised by a context-combination function | SHOULD | `Layer.ts:1907–1926` (`provideWith`), `:2345–2348` (`provide` = `provideWith(…, identity)`), `:2436` (`provideMerge`) | Three near-duplicate subcalculi with three near-duplicate law sets. This is the estate's consolidate-never-mint order handed to you by the pin's own factoring. |
| `GR-L10` | Layers whose successor is computed from a built value or cause (`flatMap`, `unwrap`, `suspend`, `catchCause`) | MUST-DECIDE | F4 | If admitted, the static node/edge representation in the checklist row is **refuted** and the denotation is a scoped Kleisli structure over contexts. If refused, say so and enumerate the surface lost — `unwrap` alone is load-bearing for config-driven layers. Either way `GR-E9` must be settled first, because `unwrap` puts a Layer in a Context. |
| `GR-L11` | Build-time failure recovery (`catchTag`, `catchCause`, `orDie`, `tapError`) | SHOULD | `Layer.ts:3221`, `:3327`, `:3401`, `:3575` | Layer construction failures cannot be handled *during* construction, only at the consumer. Note `catchCause` uses `fromBuildUnsafe` (`:3695`), so it does **not** close the layer scope on failure the way `fromBuild` does — a real, checkable asymmetry that any law must respect. |
| `GR-L12` | `launch` | MAY (derived) | `Layer.ts:3897–3898` — three combinators | Nothing, given `GR-S8` + a frontier operation. See §3, Q2. |
| `GR-L13` | `mock`, `span` / `withSpan` / `parentSpan`, `satisfies*Type` | MAY | `Layer.ts:3994`, `:4279–4700`, `:4194–4260` | Nothing in v1. `satisfies*Type` is type-level only and emits no runtime value (`typeOnly` in the checklist's own profile split). Tracing is its own calculus. |
| `GR-L14` | `build` (ambient scope) / `buildWithScope` / `buildWithMemoMap` destructors | MUST / SHOULD / MUST-if-shared | `Layer.ts:800`, `:863`, `:645` | `build` is the only way to get a `Context` out; `buildWithScope` is the explicit-lifetime form and is droppable at the cost of forcing every caller through the ambient one; `buildWithMemoMap` is how sharing is *controlled* rather than implicit, and is required the moment `GR-L5` is admitted. |

### 2.4 Runtime

| ID | Capability | Grade | Evidence | What breaks if dropped |
|---|---|---|---|---|
| `GR-R1` | `ManagedRuntime` stays `targetOnly` | MUST | `ManagedRuntime.ts:112–175`, `:285–340`; `EC1-XT110` | Runners become Core syntax and the observation boundary disappears. The disposition is already right; §3 Q3 corrects its *reason*. |
| `GR-R2` | A **process-adapter** concept, separate from `ManagedRuntime` | SHOULD | `Runtime.ts:60` `Teardown`, `:181` `makeRunMain`, `:285` `errorExitCode`, `:374` `errorReported` | Exit codes, teardown, and error reporting are genuinely host-process concerns with no computational denotation. Folding them into "runtime" makes the runtime look irreducible when it is not. |
| `GR-R3` | The scheduler is a **fiber** field, not a runtime field | MUST | `internal/effect.ts:542` `currentScheduler!: Scheduler.Scheduler`, `:716–717` (reassigned on run options); `ManagedRuntime.ts:285–320` carries no scheduler | Modelling the scheduler as part of the runtime value puts it outside the fiber's configuration, and `EC1-T077` (`fixed_decision_replay`, which explicitly says "scheduler policy/state is part of `Configuration`") is then inconsistent with the carrier. |

---

## 3. The three sharp questions

### Q1 — Is `memoize` a MUST?

**Three answers, because the question conflates three things.**

**(a) The combinator does not exist at the pin.** There is no `Layer.memoize`
export in `effect@4.0.0-rc.112`. What exists is `MemoMap` (`Layer.ts:222`),
`fromBuildMemo` (`:380`), `buildWithMemoMap` (`:645`), `makeMemoMap` /
`forkMemoMap` (`:545`, `:564`), `CurrentMemoMap` as a **service** (`:584`), and
`fresh` (`:3850`) as the opt-out. The checklist row at line 885 names a
combinator that is not there. **The row should be repaired**; see §4/C1. Graded
alone, `memoize` is **not a requirement at all**.

**(b) Sharing is a MUST, and it is semantic.** Three independent legs, any one
sufficient:

- **Instance identity.** A diamond (`A ← B`, `A ← C`, both merged) yields one
  instance of `A` under sharing and two without. If `A` is stateful — a `Ref`, a
  pool, a connection, a CAS word — two instances are observably different in any
  state-carrying target. `interpretRef`'s `Word` is exactly such a target.
- **Ownership and release point.** This is the strongest leg and it is pure
  reading, not inference. `memoMapBuild` (`Layer.ts:390–419`) allocates a
  `layerScope` that belongs to the **memo entry**, and closes it when
  `observers` reaches `0`. `memoMapReuse` (`:241–250`) increments and registers
  another decrementing finalizer in the new consumer's scope. So under sharing
  the resource's owner is the memo entry; without it, each consumer's scope.
  That is `EC1-T060` / `T062` / `T065` territory — region ownership, release
  count, and cleanup-before-resume — not a cost model.
- **Finalizer multiplicity.** n unshared consumers run the release n times.
  Probe §3 `release_twice_is_word_observable` exhibits a release that separates
  in the **word** when run twice.

**(c) The costume test, run.** The question asks whether the acquisition-trace
difference is real or whether the identical service value hides it. I checked
this and the answer is *it depends on the observation, and the packet's default
observation hides it*:

```
memo_is_invisible_in_the_word : wordOf acquireOnce = wordOf acquireTwice   -- decide
memo_counts                   : count acquireOnce = 1 ∧ count acquireTwice = 2
memo_is_visible_in_the_count  : count acquireOnce ≠ count acquireTwice
```

Building a content-addressed CAS service once and twice leaves the **same
word** — because `put` is idempotent (`EC1-CE007`; `Cas.put`'s `duplicate`
outcome returns the word unchanged, `Handler.lean:85`). So a memoization law
stated at `ObsEq` would be **vacuous** on exactly the fragment the estate can
currently execute. It separates only in the operation count.

But that is a fact about CAS put's idempotence, **not** about memoization:
`release_twice_is_word_observable` shows a non-idempotent release separating in
the word immediately, and leg (b) does not depend on the observation mask at all.

**Verdict.** The *memo-indexed build judgment* is a **MUST**: the denotation of
a layer takes the memo table as an input and returns it updated, exactly as
`build(memoMap, scope)` does — which is the pin handing you the signature. The
*`memoize` combinator* is a **MAY** and, at rc.112, a phantom. And the
memoization law **must be stated at an acquisition-trace or state-carrying
observation, never at `ObsEq`**, or `EC1-CE010`-style word-blindness makes it
vacuous.

One consequence nobody has recorded: `GR-L6`. Under R4 the memo key becomes a
content key, a content-keyed map **shares more** than rc.112's reference-keyed
one, and `fresh` needs an explicit nonce to survive at all.

### Q2 — Is `launch` in scope at all?

**In scope as a derived term; out of scope as a primitive; and it is not a
runtime concern.**

`Layer.ts:3897–3898`, verbatim, is the whole definition:

```ts
export const launch = <RIn, E, ROut>(self: Layer<ROut, E, RIn>): Effect<never, E, RIn> =>
  internalEffect.scoped(internalEffect.andThen(build(self), internalEffect.never))
```

Three combinators: `scoped`, `build`, `never`. Two are already required
(`GR-S8`, `GR-L14`). The third is the only thing worth asking about, and the
answer is that it costs the design nothing:

`internal/effect.ts:1172` — `never = callback<never>(constVoid)`. A callback
registered and never invoked. That is an **external suspension**, not
divergence. Probe §1 checks that it lives inside **R1**'s inductive Ret/Vis
fragment with no Tau and no guardedness condition:

```
neverP : Prog FrontierSig A := .vis .forever (fun e => e.elim)
neverP_is_one_vis           -- one node, axiom-free
neverP_ne_pure              -- and not a value, axiom-free
forever_ne_refuse           -- and distinct from refusal, axiom-free
forever_continuation_unique -- every continuation out of it is the empty one
```

The `Empty` answer type is the same device the estate already uses for
`CasE.fail` (`Ops.lean:30`, "a refused program has no continuation, by type").
And `EC1-CE003` **already** forces a frontier arm distinct from refusal —
"fuel, pending external answers, and scheduler decisions remain live frontiers
outside refusal and cause". So `never` is justified by a row that exists for
other reasons; `launch` adds no carrier.

Note the direction this settles: "runs until interrupted" is **program-side**
(a frontier operation the handler never answers), and only the *decision to keep
stepping* is runtime-side. So `launch` is not a runtime concern.

**Honest caveat.** `launch`'s *laws* are a different matter from its *syntax*.
What makes a launched layer terminate is interruption, so every law about
`launch` depends on the fiber/interruption bundle (`EC1-T073`–`T076`, slice
S10). As a syntax question it is derived and cheap. As a law question it is
blocked on S10, and the row should say so rather than list it beside `build`.

**Recommendation.** Demote `launch` from the checklist row's primitive list to a
derived expansion owning an expansion law; justify the frontier operation from
`EC1-CE003`, not from `launch`.

### Q3 — What is a "runtime" here?

**Not a distinct concept. A runtime is a saturated `Context` plus a fiber — and
the `Context` is a handler assignment that a program produced.**

This is read off the constructor, not argued. `ManagedRuntime.make`
(`ManagedRuntime.ts:285–340`) takes **a Layer and an optional MemoMap, and
nothing else**, and builds exactly four things:

1. `memoMap` — `Layer.makeMemoMapUnsafe()`;
2. `scope: Scope.Closeable` with `"parallel"` strategy, plus a `"sequential"`
   fork `layerScope` for the layer build;
3. `contextEffect` — the built `Context<R>`, cached;
4. the `runFork` / `runSync` / `runSyncExit` / `runCallback` / `runPromise`
   eliminators (`:347–382`).

And **both alleged extra ingredients are already services in the environment**:

- `Scope.Scope` is `Context.Service<Scope, Scope>` (`Scope.ts:215`);
- `CurrentMemoMap` is `Context.Service<CurrentMemoMap, MemoMap>` (`Layer.ts:584`).

So (1) and (2) are entries in (3). What remains is (3) — a `Context` — and (4) —
eliminators, which `EC1-XT110` already grades `targetOnly`.

**And (4) contributes nothing of its own.** Every eliminator is
`Effect.run*With(self.cachedContext)(effect)` (`ManagedRuntime.ts:347–382`);
the only thing `mergeRunOptions` adds is `onFiberStart: Fiber.runIn(scope)`
(`:294–307`). So a `ManagedRuntime`'s entire contribution to a run is **the
cached `Context`, plus a scope to attach spawned fibers to**.

**Which leaves the scheduler, and it is not in the runtime either.**
`ManagedRuntime` carries no scheduler field and no eliminator supplies one; the
build fiber is forked with `scheduler: fiber.currentScheduler`
(`ManagedRuntime.ts:320`), taken from the *calling* fiber, and
`currentScheduler` is a **mutable field on the fiber**
(`internal/effect.ts:542`, reassigned at `:716`).

**So the decomposition in the question — "handler plus a scope plus a
scheduler" — is close but wrong in two places, and both corrections matter:**

- the **scope is inside the handler assignment**, not beside it (`GR-S1`), so
  there is one environment, not an environment plus a region index; and
- the **scheduler is beside the fiber**, not beside the runtime (`GR-R3`),
  which is what `EC1-T077` already assumes when it says scheduler policy and
  state are part of the `Configuration`.

**The right statement, and it is R12 verbatim.** A `Context` maps each service
key to its implementation — that is a handler assignment, "a service IS a
handler". A Layer is the *program* that produces that assignment — "a handler
CAN BE a program". A runtime is the point at which that program has been run and
its product installed. It is the **fixed point of the tower**, not a new stratum
in it.

**Evidence that decides it.** Two independent readings, both from the pin:
the **constructor** takes a Layer and an optional MemoMap and nothing else, so
if a runtime were irreducible it would need at least one argument not derivable
from a Layer plus ambient defaults, and it has none; and the **eliminators**
pass nothing but `self.cachedContext` and a fiber-attachment scope, so if a
runtime carried anything else semantic, a run would have somewhere to receive
it, and it does not.

**Counter-evidence, named.** `Runtime.ts` is a *different* thing wearing the
same word: `Teardown` (`:60`), `makeRunMain` (`:181`), `errorExitCode` (`:285`),
`errorReported` (`:374`) — a process-exit protocol. That **is** irreducible and
genuinely outside the program, because it is about the host process rather than
the computation. So "runtime" as *process adapter* is a real separate concept
(`GR-R2`); "runtime" as *`ManagedRuntime`* is not. `EC1-XT110` merges them under
one row; the reason it gives — execution is a host boundary — is right for
`Runtime.ts` and wrong for `ManagedRuntime`, whose content is entirely a built
`Context`.

**One thing this does NOT settle.** Whether a `Context` — a handler assignment —
can itself be *content*. `GR-E9` is open: `Context` is
`ReadonlyMap<string, any>`, the keys are content and the values are host
objects, and `unwrap` puts a whole `Layer` in one. Until that is ruled, "a
runtime is a saturated Context" describes the shape without settling whether the
shape is storable.

---

## 4. Collisions with the packet as written

Each of these is a correction owed by a packet file, stated so it can be
checked rather than believed. None is a claim gate.

| ID | Where | The collision |
|---|---|---|
| **C1** | `REIFICATION-CHECKLIST.md:885` | `memoize` is named as an rc.112 public anchor. It is not an export at `4.0.0-rc.112`. The real anchors are `MemoMap`, `fromBuildMemo`, `buildWithMemoMap`, `makeMemoMap`/`forkMemoMap`, `CurrentMemoMap`, and `fresh`. |
| **C2** | `PROOF-DAG.md:338` `EC1-T064` | `release_lifo` is stated with no strategy premise. `internal/effect.ts:3817–3821` runs finalizers LIFO **only** under the `sequential` strategy; under `parallel` they are all forked and awaited. `Layer.mergeAll` (`Layer.ts:1596`) creates a parallel-strategy scope on **every merge**. The theorem as written is false on a path Layer takes by default. |
| **C3** | `PROOF-DAG.md:340` `EC1-T066` | `cause_finalizer_then` names `CauseTree.then` unconditionally. A parallel-strategy scope combines finalizer exits with `exitAsVoidAll` over concurrently-forked fibers (`internal/effect.ts:3823–3826`) — that is `both`, not `then`. Same premise gap as C2. |
| **C4** | `PROOF-DAG.md:336` `EC1-T062` | `release_exactly_once` presumes a single `owner` scope per registered resource. Under memoization the owner is the memo entry's `layerScope`, which is **no consumer's scope**, and each consumer's registration is a *decrement*, not a registration (`Layer.ts:241–250`, `:390–419`). Either "registered" is redefined to mean "first observer", or the theorem is false for every shared layer. |
| **C5** | `REIFICATION-CHECKLIST.md:882` | "all three source indices are covariant at `src/Effect.ts:117–157`" is true of `Effect` and **false of `Layer`**: `Layer<in ROut, …>` with `_ROut: Types.Contravariant<ROut>` (`Layer.ts:54`, `:98–104`). If the Layer row inherits that sentence, output subsumption inverts. |
| **C6** | `REIFICATION-CHECKLIST.md:885` | The `LayerCore` representation — "service nodes, dependency edges, scoped acquisition, ordered composition, memo key" — does not cover `flatMap` (`Layer.ts:3038`), `unwrap` (`:1580`), `suspend` (`:1543`), or `catchCause` (`:3691`), all of which compute the successor layer from a runtime value or cause. The dependency structure is not a static graph. |
| **C7** | `PROOF-DAG.md` (whole file) | **There is no Layer theorem node.** `grep -i layer PROOF-DAG.md` returns exactly one hit, `EC1-H08`, a mutation-harness row. The only environment node anywhere is `EC1-T053` (`provide_lookup` / `provide_restore`) in §7. So the checklist row's owed laws — "identity/associativity for typed composition; dependency discharge; memoization and merge laws" — have **zero** proof nodes and appear in no slice of §15. The Layer lane is undesigned in the DAG, not merely unproved. |
| **C8** | `PROOF-DAG.md` §15 slices | `Layer.merge` is a concurrent build (`Layer.ts:1587–1602`). Any merge law is therefore entangled with `EC1-S9` (fibers/scheduler) and `EC1-S10` (interruption/race). No slice records that dependency. |
| **C9** | S17 rulings, R18 | The ruled target `ExceptT Refusal (StateT Word Id)` keeps the word across the error branch — necessary, but the exhibited `ensuring` gives the finalizer **no access to the refusal**, while the pin's finalizers are exit-indexed (`Scope.addFinalizerExit`; `Layer.ts:339–345`). Probe §4 checks the exit-indexed form is expressible in the same target and satisfies the three laws, so this is a **missing law, not a missing carrier** — but it is currently owed by nobody. |
| **C10** | `EXISTING-TYPES.md` `EC1-XT103`, `EC1-XT106` | `EC1-XT106` says "host scope objects never enter canonical program content" — correct, but incomplete: `Scope`'s **key** is a string in the same map as every service (`Scope.ts:215`), so the key is content and only the object is not. `EC1-XT103` grades `Context.Key` `bridge` as one row, but the key side (`readonly key: string`) is already content-shaped while the value side is `any` and can hold a `Layer`. Both rows need the key/value split (`GR-E1` vs `GR-E9`). |
| **C11** | `EXISTING-TYPES.md` `EC1-XT110` | Grades `Runtime`, `ManagedRuntime`, and the `run*` eliminators under one `targetOnly` row with one reason. The disposition is right for all three; the *reason* is right only for `Runtime.ts`'s process protocol. `ManagedRuntime`'s content is a built `Context` plus eliminators, which is a different argument (§3 Q3). |

---

## 5. What R12 buys, and exactly where it stops

`Handler.through` / `interpret_through` (`Cas/Lang/Tower.lean:65,71`, PROVED) is
the right shape for `provide`: implement a service as a program over a lower
signature, then interpret. `provideWith` (`Layer.ts:1915–1926`) is literally
that — build the dependency, then build the dependent *with the dependency's
context provided*.

It stops at a boundary the S17 rulings already drew, and the Layer lane inherits
it. `Handler.through`'s middle must be `Prog T`-valued, and `EC1-CE041` /
`EC1-CE045` prove the scoped clauses **cannot** be `Prog`-valued. So:

> `Layer.provide` on a layer that acquires no resource is `Handler.through`.
> On a layer that registers a finalizer, it is not, and must interpret directly
> into the R18 target.

**And the split is not visible in the type.** `effectContext` always yields
`Layer<A, E, Exclude<R, Scope.Scope>>` (`Layer.ts:1479–1481`) whether or not the
build registers a finalizer, because it always provides its own scope. So
"does this layer acquire?" is a **classification obligation** over the layer's
first-order content, not a type-level discrimination. That is a concrete piece of
work the S17 note ("FORK A must be restated per-layer") implies but does not name.

---

## 6. What I did NOT check

Stated so nothing here is read as broader than it is.

- **No design was produced.** This file grades requirements; it proposes no
  carrier for `LayerCore`, and the negative results in `GR-L10` / C6 refute a
  representation without supplying one.
- **The probe is four small sections, not a model.** It checks: `never` is an
  inductive one-node program; memoization is word-invisible and count-visible on
  one content-addressed acquisition; a non-idempotent release is word-visible;
  exit-indexed finalization is expressible in the R18 target with three laws. It
  models **no** concurrency, no fibers, no interruption, no real memo map, no
  reference counting, and no multi-layer build. `GR-L5`'s ownership leg and all
  of `GR-L7` rest on **reading rc.112's source**, not on a kernel check.
- **`fresh`'s nonce problem (`GR-L6`) is unchecked.** I argue it from R4 plus
  `Layer.ts:3850`; I did not build a witness showing two content-equal `fresh`
  layers collapsing.
- **The A/E/R transforms were read from the pin's declared types, not run
  through tsgo.** `GR-L3` and `GR-E3`/`E4` cite source lines; no
  `@effect/tsgo` fixture was produced, and `EC1-CE021` is `REPORTED`, so no
  tooling conclusion is available here anyway.
- **Concurrency claims are source reads.** That `mergeAllEffect` runs with
  `concurrency: layers.length` is verbatim from `Layer.ts:1598`. What that
  *means* for merge commutativity is inference from `EC1-CE006` and `EC1-CE042`,
  not a proof.
- **I did not read `workshop/s1/` or `workshop/s2/`.** They are running
  concurrently and were out of scope by brief. Overlap or contradiction with
  their findings is possible and unreviewed. I also did not read the sibling
  `workshop/layer/ground-estate.md`, which appeared during this pass.
- **No `library/`, `formal/`, or packet `.md` file was modified.** No git
  operation was performed. The only file written is this one; the probe lives in
  the session scratchpad and is inlined below so it can be reconstructed exactly.
- **`Pool`, `Resource`, `ScopedRef`, `ScopedCache`** are named in the checklist's
  scope row; I read none of them. `GR-S8` grades them by shape, not by reading.

---

## Appendix A — the probe

Reconstruct verbatim to any path outside every lake target, then:

```
cd /Users/pooks/Dev/foldlab/library/cas && lake env lean <ABSOLUTE-PATH>/LayerGround.lean
```

Observed: **exit 0**, 11 `#print axioms` receipts, ceiling
`[propext, Quot.sound]`, 3 axiom-free, no `sorryAx`, no `Classical.choice`.

```
'LayerGround.neverP_is_one_vis' does not depend on any axioms
'LayerGround.neverP_ne_pure' does not depend on any axioms
'LayerGround.forever_ne_refuse' does not depend on any axioms
'LayerGround.forever_continuation_unique' depends on axioms: [Quot.sound]
'LayerGround.memo_is_invisible_in_the_word' depends on axioms: [propext]
'LayerGround.memo_is_visible_in_the_count' depends on axioms: [propext]
'LayerGround.memo_counts' depends on axioms: [propext]
'LayerGround.release_twice_is_word_observable' depends on axioms: [propext]
'LayerGround.ensuringExit_keeps_the_word' depends on axioms: [propext]
'LayerGround.ensuringExit_never_replaces_the_refusal' depends on axioms: [propext]
'LayerGround.ensuringExit_reads_the_exit' depends on axioms: [propext]
```

Source:

```lean
import Cas.Lang.Ops
import Cas.Lang.Handler
import Cas.Lang.Interp

/-!
Ground-requirements scout probe for the Layer/Scope/Environment design pass.
Two claims are checked here and nowhere else in the report is either asserted
without this file behind it.
-/

namespace LayerGround

open Cas Cas.Lang

/-! ## §1 — `launch`'s `never` is a FRONTIER operation, not divergence.

`Layer.launch self = scoped (build self *> Effect.never)` and
`internal/effect.ts:1172` defines `never = callback<never>(constVoid)`:
a callback registered and never invoked.  That is an operation whose
answer type is uninhabited, not a Tau-loop.  It therefore lives inside
EFFECTS-BACKEND R1's inductive Ret/Vis fragment with no coinduction. -/

inductive FrontierE where
  | forever
  | refuse (reason : String)

abbrev FrontierE.Ans : FrontierE → Type
  | .forever  => Empty
  | .refuse _ => Empty

def FrontierSig : Sig := ⟨FrontierE, FrontierE.Ans⟩

/-- `Effect.never`, spelled in the inductive carrier. -/
def neverP {A : Type} : Prog FrontierSig A :=
  .vis .forever (fun e => e.elim)

/-- It is a one-node program: no recursion, no Tau, no guardedness side condition. -/
theorem neverP_is_one_vis {A : Type} :
    (neverP : Prog FrontierSig A) = .vis .forever (fun e => e.elim) := rfl

/-- And it is not a value. -/
theorem neverP_ne_pure {A : Type} (a : A) :
    (neverP : Prog FrontierSig A) ≠ .pure a := by
  intro h; cases h

/-- The frontier is NOT refusal: the two carry different operations, so a
handler is free to give them different observations.  This is `EC1-CE003`'s
separation restated at the operation level, which is what `launch` needs. -/
theorem forever_ne_refuse (r : String) :
    (FrontierE.forever) ≠ .refuse r := by
  intro h; cases h

/-- Any continuation out of `forever` is the empty one; a handler can never be
resumed past it.  So `launch`'s "runs until interrupted" is a property of the
HANDLER, not of the program's syntax. -/
theorem forever_continuation_unique {A : Type}
    (k k' : FrontierSig.Ans .forever → Prog FrontierSig A) : k = k' := by
  funext e; exact e.elim

/-! ## §2 — memoization of a layer build is invisible to a CAS word
observation but visible to an operation-count observation.

The acquisition of a content-addressed service is word-idempotent
(`EC1-CE007`: duplicate insertion yields one binding), so "built once" and
"built twice" leave the SAME word.  Counting is what separates them.  The
counting observation is `interpret` into a state monad in the order R18
forces: state OUTSIDE error. -/

abbrev CountM := ExceptT Refusal (StateM Nat)

/-- A handler that answers every store operation and counts the operations
performed.  Errors carry no count slot, so the count lives outside the
`Except` — exactly the transformer order `EC1-CE045` forces. -/
def countingHandler (n0 : Node) (a0 : Addr32) : Handler CasSig CountM where
  handle
    | .put _      => fun s => (.ok a0, s + 1)
    | .load _     => fun s => (.ok n0, s + 1)
    | .fail r     => fun s => (.error (.failed r), s + 1)

def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩
def nA : Node := ⟨0, 0, [], []⟩

/-- One acquisition of a layer whose build is a single `put`. -/
def acquireOnce : Prog CasSig Addr32 := put nA

/-- The same layer acquired twice, as an unmemoized diamond would. -/
def acquireTwice : Prog CasSig Addr32 :=
  (put nA).bind (fun _ => put nA)

/-- Word observation, via the estate's reference handler. -/
def wordOf (p : Prog CasSig Addr32) : Word :=
  match interpretRef (fun _ => zeroAddr) p [] with
  | .ok (_, w) => w
  | .error _   => []

/-- **Word-blind.** Building once and building twice leave the same word. -/
theorem memo_is_invisible_in_the_word :
    wordOf acquireOnce = wordOf acquireTwice := by
  decide

/-- **Count-visible.** The same pair separates under the operation count. -/
theorem memo_is_visible_in_the_count :
    (interpret (countingHandler nA zeroAddr) acquireOnce 0).2
      ≠ (interpret (countingHandler nA zeroAddr) acquireTwice 0).2 := by
  decide

/-- Both counts, exhibited, so the inequality is not vacuous. -/
theorem memo_counts :
    (interpret (countingHandler nA zeroAddr) acquireOnce 0).2 = 1
      ∧ (interpret (countingHandler nA zeroAddr) acquireTwice 0).2 = 2 :=
  ⟨rfl, rfl⟩

/-! ## §3 — the word-blindness is a property of CAS acquisition, not of
memoization.  A non-idempotent finalizer separates in the word too, so a
sharing design cannot lean on §2's `rfl` as if memoization were always
unobservable. -/

abbrev WComp := Word → Except Refusal Addr32 × Word

/-- A release action that prepends a binding: not word-idempotent. -/
def prependRelease : WComp := fun w => (.ok zeroAddr, Binding.mk zeroAddr nA :: w)

theorem release_twice_is_word_observable :
    (prependRelease (prependRelease []).2).2 ≠ (prependRelease []).2 := by
  intro h
  simp [prependRelease] at h

/-! ## §4 — finalizers in the pin are EXIT-INDEXED
(`Scope.addFinalizerExit : (scope, (exit : Exit) => Effect<unknown>)`, and
`Layer.fromBuild` closes its layer scope with the build's `Exit`).  The R18
target keeps the word across the error branch, but `EC1-CE045`'s exhibited
`ensuring` gives the finalizer no access to the refusal.  This section checks
that the exit-indexed form is expressible in the SAME target, so the gap is a
missing law, not a missing carrier. -/

/-- The R18 target's computation type, reused. -/
abbrev EComp := Word → Except Refusal Addr32 × Word

/-- Exit-indexed finalization: the finalizer is chosen by the body's outcome. -/
def ensuringExit (body : EComp) (fin : Except Refusal Addr32 → EComp) : EComp :=
  fun w =>
    match body w with
    | (.ok a, w₁)    => match fin (.ok a) w₁ with
                        | (.ok _, w₂)  => (.ok a, w₂)
                        | (.error r, w₂) => (.error r, w₂)
    | (.error r, w₁) => match fin (.error r) w₁ with
                        | (.ok _, w₂)    => (.error r, w₂)
                        | (.error _, w₂) => (.error r, w₂)

/-- The word survives the error branch, finalizer included — the R18 property. -/
theorem ensuringExit_keeps_the_word (body : EComp)
    (fin : Except Refusal Addr32 → EComp) (w : Word) :
    (ensuringExit body fin w).2 = (fin (body w).1 (body w).2).2 := by
  unfold ensuringExit
  cases hb : body w with
  | mk res w₁ =>
    cases res with
    | ok a => cases hf : fin (.ok a) w₁ with
      | mk r₂ w₂ => cases r₂ <;> simp [hf]
    | error r => cases hf : fin (.error r) w₁ with
      | mk r₂ w₂ => cases r₂ <;> simp [hf]

/-- The original refusal is never replaced by the finalizer's outcome. -/
theorem ensuringExit_never_replaces_the_refusal (body : EComp)
    (fin : Except Refusal Addr32 → EComp) (w : Word) (r : Refusal)
    (h : (body w).1 = .error r) :
    (ensuringExit body fin w).1 = .error r := by
  unfold ensuringExit
  cases hb : body w with
  | mk res w₁ =>
    rw [hb] at h
    cases res with
    | ok a => cases h
    | error r₀ =>
      cases hf : fin (.error r₀) w₁ with
      | mk r₂ w₂ => cases r₂ <;> simp_all

/-- **The dependence is real.** Two finalizers that agree on the SUCCESS exit
and differ on the FAILURE exit give different composites, so exit-indexing is
not a redundant parameter. -/
theorem ensuringExit_reads_the_exit :
    ∃ (body : EComp) (fin fin' : Except Refusal Addr32 → EComp) (w : Word),
      (∀ v, fin (.ok zeroAddr) v = fin' (.ok zeroAddr) v)
        ∧ ensuringExit body fin w ≠ ensuringExit body fin' w := by
  refine ⟨fun w => (.error (.failed "body"), w),
    fun _ v => (.ok zeroAddr, v),
    fun e v => match e with
      | .ok _ => (.ok zeroAddr, v)
      | .error _ => (.ok zeroAddr, Binding.mk zeroAddr nA :: v),
    [], fun _ => rfl, ?_⟩
  intro hc
  have : ([] : Word) = [Binding.mk zeroAddr nA] := congrArg Prod.snd hc
  simp at this

end LayerGround
/-! ## Receipts -/
namespace LayerGround
#print axioms neverP_is_one_vis
#print axioms neverP_ne_pure
#print axioms forever_ne_refuse
#print axioms forever_continuation_unique
#print axioms memo_is_invisible_in_the_word
#print axioms memo_is_visible_in_the_count
#print axioms memo_counts
#print axioms release_twice_is_word_observable
#print axioms ensuringExit_keeps_the_word
#print axioms ensuringExit_never_replaces_the_refusal
#print axioms ensuringExit_reads_the_exit
end LayerGround
```
