# Effect4 port manifest

Effect4 now has one independent algebra carrier and a mechanically bounded
cutover inventory. Foldlab remains the downstream compatibility target; no
Foldlab module is an Effect4 dependency.

Status: P1/P3 closure active, 2026-08-31. The generic algebra is implemented
and its current breaker battery is green, but independent review found
retained source declarations that still require row-level dispositions.
Schema, flow, runtime, concurrency, target, and Foldlab compatibility rows
remain open until their own proof graphs close.

## Authority pins

| Authority | Exact pin or digest | Role |
| --- | --- | --- |
| Foldlab source | commit `feb29321fd50204aa338209d313e84a3f8b71c66` | Source declarations, tests, and downstream compatibility target |
| Effect4 toolchain | `leanprover/lean4:v4.33.1`; `lean-toolchain` SHA-256 `3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71` | Kernel, elaborator, compiler, and standard library |
| Effect runtime | `effect@4.0.0-rc.112`; upstream commit `2600f62f4532026928454dcea8d1c48557b3f942`; tree `648a01b9c249448716e1a9474f511b17898f9d93` | Sole Effect TypeScript API and runtime semantic authority |
| Installed Effect package | integrity `sha512-wXxwuh1Ywnv4cPRM3Wfa0vDwuOHnZ1TsTgHJkG9XgzND6inhBH9n1vBxhg3iIXOia/OrpmvVmd3lrD4vq6bF3A==` | Exact host bytes exercised by Foldlab |
| TypeScript | `typescript@7.0.2`; integrity `sha512-8FYau96o3NKOhbjKi/qNvG/W5jhzxkbdm5sj9AbZ/5T5sWqn3hJgLfGx27sRKZWTvyzCP8dLRBTf5tBTSRVUNA==` | Target typechecker |
| Installed Effect diagnostic gate | `@effect/tsgo@0.38.0`; integrity `sha512-eazN0kX+WNT1jNjIm/l5esnkpKVfd1wNh2ig0pfaULKuI2PZh0JwjbepDPUr6MWx5cqOiUgwStNf5hGhg2w00g==` | Auxiliary target diagnostic gate; never semantic authority |
| Language-service research clone | commit `5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4`; Effect v4 harness at `4.0.0-beta.107` | Diagnostic designs and negative fixtures, version-indexed |
| PolyFun acceptance probe | commit `3937f7ff0830cca33d6b35a24aef55bcbe3b6bc9`; Lean `v4.33.1`; Mathlib `v4.33.1`; cslib `v4.33.1` | Prior-art API and optional comparison source; not an Effect4 dependency |

The Effect npm version and upstream revision come from Foldlab's
`.reference/provenance/sources.lock.json` runtime row. The installed package
bytes remain a separate pin because an upstream tag does not prove what a
package manager placed on disk. This distinction is material for Schema:
installed `Schema.ts` has SHA-256
`9358710e2c0d613371d8feeeccb3716fe98a43f67e6aa1076b00d4079a258784`,
while the pinned upstream file has
`f0ecfa4511a62c2eb7ed820449d12653a2bbb8ef82ead842189a56b503d0de2f`.
The exact matching and differing source/declaration digests are recorded in
`docs/SCHEMA-CUTOVER.md`.

## Dispositions

Every source row receives one of these dispositions. A refusal explains why
the row is outside a profile; it is not an additional disposition.

| Disposition | Meaning |
| --- | --- |
| `owned` | Effect4 owns the only generic carrier and its laws. |
| `split` | Generic declarations move to Effect4; domain declarations remain downstream. |
| `downstreamAdapter` | Foldlab retains the type and later relates it to Effect4 in both directions. |
| `separateCalculus` | The family has its own syntax, indices, and semantics rather than becoming a core operation. |
| `derivedExpansion` | The surface lowers to already admitted operations or another admitted calculus. |
| `foreignBoundary` | A stable registered identity crosses to host code; arbitrary closures are not canonical content. |
| `targetOnly` | The item belongs to runtime execution or target tooling, not canonical program data. |
| `evidenceOnly` | A workshop, old implementation, or dependency informs a contract but supplies no carrier. |
| `excludedInternal` | A package-private implementation has no public reification row. |

## Generic algebra extraction

The source files below were hashed at the Foldlab pin. The Effect4 contract is
`test/contracts/algebra-extraction.contract.md`; its central attacks are
`E4-ALG-CE-001` through `E4-ALG-CE-007`.

| Foldlab source | Retained span | SHA-256 | Effect4 owner | Disposition |
| --- | ---: | --- | --- | --- |
| `library/cas/Cas/Lang/Sig.lean` | 1-27 | `91e9d984fead2a36c4503bb8db979e8f085123db754a655846888aac41e87cd6` | `Effect4/Algebra/Signature.lean` | `owned`; operation and answer universes generalized |
| `library/cas/Cas/Lang/Prog.lean` | 1-54 | `a8ac15632d155f9558db1969f2a25faf548e337c35b584f54316d5aba0f958aa` | `Effect4/Algebra/Program.lean` | `owned`; well-founded higher-order proof carrier only |
| `library/cas/Cas/Lang/Handler.lean` | 39-67 | `7170bd9c6de8743d10fff712644fa1d6ce59100e5dc33e0458b17897de933bf9` | `Effect4/Algebra/Handler.lean` | `split`; generic handler moved, CAS reference handler retained |
| `library/cas/Cas/Lang/Representation.lean` | 35-118 | `5ca0f4cfeeb396c0f084d547a72825ddbe8a6c6a37e0786dbed9e94d68b652a8` | `Effect4/Algebra/Laws.lean` | `split`; generic laws moved, CAS observation retained |
| `library/cas/Cas/Lang/Representation.lean` | 119-128 | same file digest | `Effect4/Semantics/Equivalence.lean` | open `downstreamAdapter` |
| `library/cas/Cas/Lang/Tower.lean` | 63-85 | `02b348347431dd80544427bb93fd0c0878b37ac010196ee1faf0c5925773027a` | `Effect4/Algebra/Handler/Composition.lean` | `split`; generic composition moved, byte plane retained |
| `library/cas/Cas/Backend/SumAlgebra.lean` | 172-173, 196-467 | `d6a67f6efa75d81662f79945ce84ce54e83392b786bd9ce5a4884c01c2f7070b` | `Effect4/Algebra/Sum.lean` | `split`; generic sum laws moved |
| `library/cas/Cas/Backend/Universal.lean` | 127-223 | `cce4f2a50a7e2a2e8b57b4de1a82f90c86efcb9749683795fd2b9e96d2ad8010` | `Effect4/Algebra/MonadLaws.lean` | `split`; minimal equation bundles moved |
| `library/cas/Cas/Backend/Universal.lean` | 294-349, 469-625 | same file digest | `Effect4/Algebra/Universal.lean` | `split`; freeness and model initiality moved |
| `library/cas/Cas/Backend/Universal.lean` | 739-749, 757-768, 785-790 | same file digest | `Effect4/Algebra/Handler/Category.lean` | `split`; category laws and endomorphism monoid moved |

There is one `Signature`, one `Program`, and one `Handler` family in Effect4.
`Program` stores Lean continuations and is not serializable content. The later
checked `Flow` graph is not a second free-monad carrier: it owns finite public
identity, sharing, cycles, admission, and generation, with an explicit
elaboration relation into semantic programs.

The algebra landed in three commits with separate roles:

- `bbefc6beaf69f6ac5d3bb8f2f5f62c80ddc956a7` froze the breaker contract;
- `424863e6487c160fcfbdb023ce0ba465f44a47b3` repaired two test elaboration
  sites without changing the contract; and
- `fb6f64571a42f12cc342582f72c917b016093a5b` implemented the algebra and
  made the contract and axiom report part of the default Lake build.

Independent review found that the file-span rows above were broader than the
public declarations actually extracted. The implementation satisfies the
frozen native proposal, but those source rows are not cutover-closed. Their
required dispositions are now explicit:

| Retained Foldlab declaration | Effect4 decision | Closure requirement |
| --- | --- | --- |
| `Representation.eq_of_forall_interpret` | port as generic interpreter-separation theorem | exact statement, proof, axiom receipt |
| `interpret_vis` | port as the named handler beta equation | exact minimal assumptions and receipt |
| `interpret_op_of_rightUnit` | expose the existing private sharp helper as public API | right-unit-only statement and receipt |
| `interpret_isMonadMorphism_of_equations` | port | left-unit/bind-associativity statement and receipt |
| `interpret_inhabits_the_pin` | port | anti-vacuity companion at the same equation boundary as the pin |
| `IsMorphE`, conversions, function-equality initiality | supersede with a first-class `ModelMorphism` API | conversions to the existing predicate plus initial-object uniqueness theorem |
| `syntactic_hyp_iff*` and wide `Prog.inl_unique`/`inr_unique` | port with native names distinguishing one-target strength from all-model corollaries | both directions and adapter aliases proved |
| `existsUnique_handler`, `interpret_satisfies_the_property` | downstream compatibility aliases | aliases resolve to the native freeness and anti-vacuity theorems without a second proof carrier |

No row is closed merely because the missing result is likely derivable. The
derivation theorem and its axiom receipt are the closure evidence.

## Existing Foldlab effect-core material

| Source set | Observed state | Disposition |
| --- | --- | --- |
| `formal/effect-core-v1/EffectCore/**` | 57 empty modules; no semantic declarations | `evidenceOnly`; module breadth informs Effect4 stubs but no code is ported |
| `.staging/effect-core-v1/workshop/EffectCoreProbe.lean` | self-contained finite probe | `evidenceOnly`; eligible as a later first-order-flow regression fixture |
| S1 workshop | 26 compiling files, 13 incompatible local carriers, no production declarations | `evidenceOnly`; keep surviving closure and census obligations, reject every local carrier |
| S2 workshop | eight incompatible raw/admission/program carriers and no composable checker | `evidenceOnly`; one ruled raw/checked flow must replace them |
| Layer workshop | 67 receipts over `Program`, `Handler`, sums, and state-outside-failure | `evidenceOnly`; reuse the algebraic laws and counterexamples, not its `String -> Addr32` service environment or unstratified floor |
| `library/effects/archive/lean-model-0.3/**` | older conformance, replay, remote, and mutation estate | `evidenceOnly`; mine proof and test shapes, never revive its carriers wholesale |

The Layer result is adopted with two corrections. A semantic Layer is a
program whose result is a service handler, and Scope is a separate signature
summand. The rc.112 target has no public `Layer.scoped`; `Layer.effect`
already excludes `Scope` in its result. Effect4 therefore creates no
`Layer.scoped` row or duplicate scoped-layer carrier.

## Schema extraction ruling

The complete ruling and proof graph are in `docs/SCHEMA-CUTOVER.md`. The
source audit rejects a directory copy:

| Foldlab source family | Effect4 disposition |
| --- | --- |
| `Cas.Schema.Ast` | `downstreamAdapter`; an admitted CAS subset/view over the native representation, not a base carrier |
| `Cas.Schema.El` | `evidenceOnly`; its `Empty` branches make it an incomplete denotation |
| pure `Cas.Schema.Codec` | downstream CAS codec; not Effect's directional, effectful four-index calculus |
| generic union/guardedness/discrimination algorithms | `split`; refactor over the native representation and retain their proof patterns |
| deriving handlers | metaprogramming technique only; `Lean.Expr` remains input and checked rows are output |
| CAS declaration rows, admission, refusals, bytes, projections, and store bridges | Foldlab-owned until per-type compatibility closure |

Effect4 will own one first-order representation with all 22 rc.112 persisted
tags, one document-relative relational denotation, one open first-order
reviver registry, one versioned rc.112 wire profile, and one four-index
`Codec decoded encoded decodeRequirements encodeRequirements`. `Getter` and
`Transformation` reuse checked Flow; no Schema-specific effect monad is
admitted. `Schema`, `Decoder`, `Encoder`, and `Top` are existential views of
that codec rather than new carriers.

Decode and encode requirements remain distinct, and transformation encoding
composition runs in reverse order. No universal round-trip law is assigned to
all codecs because lossy transforms are part of the source surface. Schema
issue, wire issue, profile issue, Foldlab `IngestRefusal`, general Cause/Exit,
cutover refusal, and live frontier are separate classifications.

## Effect TypeScript family defaults

These defaults organize the exhaustive surface ledger. Every overload still
needs its own profile row and evidence.

| Family | Default disposition | Required semantic distinction |
| --- | --- | --- |
| Effect success/failure, service lookup, scope close, fiber lifecycle, and primitive state handles | `owned` core operations | Typed failure, defect, interruption, refusal, and live frontier remain distinct. |
| `map`, bind-derived combinators, `gen`, tagged catches, admitted resource brackets, and collection conveniences | `derivedExpansion` | The expansion and preservation theorem are explicit. |
| Schema and Codec | `separateCalculus` | Decoded, encoded, decoding-service, and encoding-service indices are independent. |
| Context and Service | `separateCalculus` feeding core requirements | Stable typed keys own identity; default References have an explicit ambient boundary. |
| Layer | `separateCalculus` | Output, error, input, memo identity, build order, and scoped lifetime remain observable. |
| Runtime and ManagedRuntime | `targetOnly` plus a Lean reference machine | ManagedRuntime lazily builds once, caches Context, owns Scope and fibers, and has disposed state. |
| Scope and Resource | `separateCalculus` with core operations | Registration, delimiter, exit-aware finalization, and state after failure are separate. |
| Fiber, scheduler, race, and interruption | `separateCalculus` | A decision tape fixes replay; safety theorems do not assume fairness. |
| Ref, Deferred, Queue, PubSub, and SubscriptionRef | primitive state operations plus `derivedExpansion` | Allocation, wakeups, shutdown, ownership, and subscriptions are observable. |
| Channel, Stream, Sink, Pull, and Take | `separateCalculus` | Pull suspension, end/error, leftovers, backpressure, cancellation, and cleanup are not list semantics. |
| Schedule | `separateCalculus` | State, input, output, error, environment, and time decisions remain explicit. |
| Config and ConfigProvider | recipe `separateCalculus`; provider `foreignBoundary` or finite-map model | Process environment is not a pure map unless supplied as one. |
| Cause and Exit | pure first-order data outside `Program` | rc.112 Cause is an ordered reason list; richer trees lower through a named lossy quotient. |
| callback, promise, arbitrary thunk, custom Schema predicate or transform | named block, registered `foreignBoundary`, or refusal | Host closures and promises never enter canonical syntax. |
| run functions, runtime handles, and concrete scheduler installation | `targetOnly` | Host execution supplies evidence, not denotational identity. |

Legacy names found in the corpus but absent from rc.112 are profile refusals
or versioned migrations, not new rc.112 declarations:
`Context.Tag`, `Context.GenericTag`, `Layer.scoped`, `Effect.async`,
`Schema.TaggedErrorClass`, `Schedule.intersect`, `Schedule.both`, and
`Schedule.compose`.

## Wild-type corpus baseline

The validation corpus is independent evidence, not a source of semantic
authority. A read-only mechanical sample selected 14 of 34 repositories and
counted 10,138 TypeScript-family files after excluding `.git`,
`node_modules`, `dist`, and `generated` trees.

| Representative repository | Pin | Files |
| --- | --- | ---: |
| Effect language service | `5e4d380b6fcd20f048dd8d41515bcd9ea47ffda4` | 802 |
| anomalyco/opencode | `df35e842f59bc115bb7c0479a8e11f017d443f2c` | 3,276 |
| brandhaug/b2b-saas-starter | `752d4a23551054731adec35b30a9751698f4dff4` | 338 |
| latitude-dev/latitude-llm | `a1a723e8b0e1241592745bd2f6090bf0d2ac3d0e` | 4,250 |
| typeonce-dev/effect-machine | `68092b83e4ab0d131598a5593565e10a2ff02f04` | 209 |
| tim-smart/dfx | `23988a4f182eb5cebc6c3bbac3f3c35fd303168f` | 49 |
| PaulJPhilp/EffectPatterns | `f3a0da2299717cf31d31313c5661cebd2446d5a3` | 613 |
| kitlangton/motel | `c49ab0f1bdb92fdbe27c144881f1d1e45efc864f` | 104 |
| remaining six sampled repositories | exact pins recorded by the corpus audit | 497 |

The first host harness must include direct rc.112 type and runtime tests in
addition to the installed diagnostic gate. The language-service clone is
behind rc.112, and the installed gate still has version-specific gaps.

## Dependency ruling

PolyFun passed its own build, test, validation, and axiom sweep at the exact
pin: 10,588 declarations across 270 modules, with no `sorry` or nonstandard
axiom taint. It is not an Effect4 dependency because its public adoption would
add Mathlib and cslib, a measured full validation checkout of about 8 GB, and
a rapidly changing API. Effect4 instead keeps its small algebra facade and
borrows the stronger API shapes: signature maps, first-class monad morphisms,
handler composition, finite paths, and an optional later ITree comparison.
PolyFun `FreeM` remains higher-order syntax and cannot replace checked
first-order `Flow`.

## Automated gates

| Gate | Command | Current scope |
| --- | --- | --- |
| Default Lean gate | `lake clean && lake build` | all `Effect4.*` and `Effect4Test.*` source files through Lake globs; root-reachability and axiom allowlist enforced |
| Narrow algebra gate | `lake env lean Effect4Test/Algebra/ExtractionContract.lean` | Frozen public signatures and algebra counterexamples |
| Exhaustive module/axiom gate | default build, invoked by `Effect4Test.lean` | currently 101 source files and 240 declarations; semantic/test ceiling `propext`, `Quot.sound`; audit implementation alone also permits `Classical.choice` |
| Human-readable axiom receipt | `lake env lean Effect4Test/Algebra/AxiomReport.lean` | every currently exported algebra theorem, with dependencies printed |
| Diff hygiene | `git diff --check` | Authored source formatting |
| Effect target gate | pending P11 | rc.112 typecheck, installed tsgo, direct runtime vectors, negatives, and mutations |
| Foldlab compatibility gate | pending P12 | Both builds plus per-type round trips and interpretation agreement |

## Open closure edges

No full cutover claim is available while any row below is open.

1. The algebra assurance review must close the exact retained-span omissions
   listed above; current proofs and gates do not by themselves close Foldlab
   compatibility.
2. Exact type ascriptions must replace existence-only declaration checks, and
   the well-founded-but-not-globally-finite `Program` witness must remain in
   the breaker battery.
3. Signature-map and explicit universe-lift bridges need their own breaker
   packet; no implicit lift is admitted.
4. One raw/checked first-order Flow carrier must replace all S2 workshop
   variants and relate finite sequential bodies to `Program`.
5. Refusal, frontier, Cause, Exit, relational runs, nondeterminism, and
   divergence need separate observations and counterexamples.
6. The Schema representation and directional Codec calculus need a frozen
   public declaration graph before porting Foldlab proofs.
7. Context, Service, Layer, Scope, Resource, Runtime, ManagedRuntime, Fiber,
   scheduling, and interruption each need a representative contract before
   any one family is developed deeply.
8. The recursive rc.112 export and overload census must generate a closed
   surface ledger with no manual completeness override.
9. Generated TypeScript needs typed lowering, deterministic bytes,
   independent decoding/typechecking, simulation, and direct runtime tests.
10. Foldlab may cut over a type only after conversion round trips,
   interpretation agreement, source digest, counterexample coverage, and
   axiom receipt all close for that type.
