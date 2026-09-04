# The pedigree: what this estate is and what binds here

Read this before touching any other folder in the room. Everything below is checkable on this
machine; paths are absolute. Cite by `path:line` and file digest.

## 1. The estate

One person, Mepuka Kessy (GitHub `mepuka`), has been building a family of Lean 4 and Effect
TypeScript repositories whose through-line is the **Effect to Lean bridge**: formal
declarations for configurations and operations, executable models and proofs, conformance
evidence, and tooling that carries those results into Effect-based systems. The Lean packages
live under the GitHub organization `pure-algebra`, one listed package per repository:

| Repo | Local path | Holds |
| --- | --- | --- |
| lean4-effect4 | `/Users/pooks/Dev/lean4-effect4` | this repository: the reification of `effect@4.0.0-rc.112` |
| lean4-effects | `/Users/pooks/Dev/lean4-effects` | the generic effect algebra: Hom, transport, Family, Flow v3 |
| lean4-typescript | `/Users/pooks/Dev/lean4-typescript` | TypeScript as a target: syntax, renderer, host pins |
| lean4-hash | pinned in `lakefile.toml` | proved SHA-256, audited to zero declarations reaching `Classical.choice` |
| lean4-whatwg | `/Users/pooks/Dev/lean4-whatwg` | WHATWG streams bridge |
| downstream | `/Users/pooks/Dev/downstream` | the coordination repo that pins the packages to each other |

Three research beds precede and feed this repository:

| Bed | Local path | What it contributed |
| --- | --- | --- |
| foldlab | `/Users/pooks/Dev/foldlab` | "a lab for verifiable computation over streams". `library/cas`: the content-addressing discipline (address = digest of canonical encoding; the injectivity law is a separate class; hash collision is characterized, never assumed; `library/machine/MACHINE-ALGEBRA.md` fixes hash levels 0 and 1). `formal/fips202`: a kernel-checked SHA3-512 bridge between the NIST spec and an optimized implementation. `formal/effect-core-v1`: the Effect Core rulings. `library/effects/archive/lean-model-0.3`: the first conformance corpus, with Replay, Conformance, and **Mutants**, whose rule "one hand-declared mutant per obligation, named by the obligation it attacks; kill rates, not row counts" binds here. |
| foldlab-ssex | `/Users/pooks/Dev/foldlab-ssex` | `VERIFICATION.md`, the claims ledger: every claim with its rung (R0 fixture walls, R1 property tests, R2 bounded model check, R3 inductive invariant, R4 lockstep conformance, R5 mechanized proof), its bounds, its residuals, and `HELD` for a claim written down but not asserted. `docs/research/2026-08-12-jetstream-guarantees-source-verified.md`: the register for source-verified claims, with `VERIFIED`, `VERIFIED-WITH-CAVEAT`, `UNVERIFIED` against pinned upstream commits. |
| Foldable | `/Users/pooks/Dev/jetstream-workflow-model` | the bridge program itself. `formal/effect_nats_substrate` (published as `/Users/pooks/Dev/effect-nats-verified`): a kernel-checked model of the JetStream memory interpreter of effect-nats, including a transliteration of Effect's bounded `Queue` at rc.111 with stages A and B1, seven core theorems, eight subscriber theorems, seven runtime theorems, sixteen traces checked by `decide`, ten negative witnesses, two wrong models, a deterministic fixture exporter, and kept refutations of two frozen statements. `formal/jetstream_workflows`: ack, redelivery, quorum, and load, with `recorded_result_blocks_effect` as the effectively-once lemma. `research/`: the indexed evidence corpus, including the session-types pilot and its adversarial review. `.agents/skills/`: the Lean skill suite named below. |

The consumer side is `/Users/pooks/Dev/effect-nats` (Effect v4 client for NATS; its
`packages/agents/notes/0002` and `0003` hold the guarantee ladder `atMostOnce < atLeastOnce <
dedupWindow < pure` and the Pass A / Pass B contract-then-freeze workflow) and its TypeScript
replay harness `test/LeanTraceReplay.ts`, which decodes Lean-emitted fixtures and drives both
the memory interpreter and a live server.

## 2. What this repository has already built

Read `AGENTS.md`, `docs/ARCHITECTURE.md`, `docs/DESIGN-BASIS.md` (rulings DB-01 to DB-10),
`PORT-MANIFEST.md`, and `docs/RUNTIME-COVERAGE.md` before citing any of it.

- **The Deep machine.** `Effect4/Deep/*.lean`: the rc.112 fiber runtime as a machine: fibers,
  the 17 frame primitives (`Effect4/Runtime/Runtime.lean`), scheduler and dispatcher buckets,
  stores, layers. `Effect4/Concurrency/Scheduler.lean` has a frozen public surface (see
  `Effect4Test/Concurrency/FiberAssurance.lean`, the "freeze chain").
- **The behaviour census and its join.** `generated/effect-runtime-census.tsv` (137 rows, each
  a span of pinned source with its SHA-256) joined to 814 witness theorems in
  `Effect4Test/Audit/RuntimeCoverage.lean`, with `#check` ascription snapshots, axiom receipts,
  and `scripts/check-effect-runtime-census.sh`. This is the only fully mechanized rung ladder
  in the family and the model for every gate in the room.
- **The content-addressed store.** `Effect4/Store/{Canonical,Digest,Store,Trie}.lean`:
  canonical bytes, SHA-256 address, ids, path trie. `LawfulCanonical` is a separate class and is
  not claimed for stored records.
- **The std-lib census as store content.** `Effect4/StdLib/{Entry,Rc112,Links}.lean`: 1,835
  exports of 21 modules with per-file SHA-256 pins, addressed by `[module, name]`, and 65
  checked links from exports to family rows, frame primitives, fiber actions, and store ops.
  Generated by `scripts/generate-stdlib-census.ps1` on the owner's PC; the digests match the
  mac copy byte for byte.
- **Views as Effect Schema documents.** `Effect4/Arch/{Views,Accepts,JsonCanonical}.lean`:
  a Schema `Document` is canonical store content; four architecture views are documents whose
  payloads project from proof carriers; `Effect4/Target/TypeScript/Schema.lean` generates the
  TypeScript module rc.112's own codec decodes. `Effect4Test/Arch/ArchContract.lean` is the
  gate.
- **The family rows.** `Effect4/Stateful/{RefFamily,DeferredFamily}.lean`,
  `Effect4/Runtime/ScopeFamily.lean`, `Effect4/Layer/LayerFamily.lean`,
  `Effect4/Context/ContextFamily.lean`: the house idiom for a characterized service.
- **Multi-face agreement.** `workshop/OCaml5/` and `docs/research/2026-09-03-*.md`: an OCaml 5
  avatar interpreter and a 158-program adversarial corpus, byte-identical across three hosts and
  agreeing with rc.112 on 435 mask pairs. Evidence that "several faces, one fixture" works.
- **The three reports of 2026-09-04** in `docs/research/`: `semantic-api-type-design`,
  `effect-internals-proof-map`, `registry-and-cas-lineage`, and their reconciliation
  `characterized-components-api-synthesis`. The room exists to execute the synthesis.

## 3. Rulings that bind

- Canonical content is first-order data: no closures, no `Expr`, no host objects (DB-02).
- Effect TypeScript is a versioned target profile, pinned by digest (DB-09).
- No Mathlib. Core-only Lean; the toolchain is in `lean-toolchain`.
- Hash level 0 or 1 only: a pin theorem characterizes collision, never assumes injectivity.
- Answers live in the label; the step is `S → L → Option S`; traces are first-order data.
- Invariants are extrinsic `structure … : Prop` with named clauses; one strengthened
  reachability induction per component, exported once.
- Frame laws never certify. A property ships with its anti-vacuity kit; mutants are killed by
  trace suites, a survivor is a build failure, no kill rate is published.
- Replay never turns a claim green. A claim's rung is a function of its evidence.
- Gates are incremental: no re-run when inputs are unchanged; stamp on content hashes and Lake
  traces; planted defects are root-only tests, never a rebuild.
- Freeze chain: a public surface is frozen in its ascription snapshot; a change goes through
  the snapshot, never around it.
- More than one agent edits this worktree; `COORDINATION.md` is the channel; claim before
  writing. The room and `Effect4/Char/**` are claimed there for this bootstrap.

## 4. Skills this estate has used many times

In this repository, `skills/`: `lean-reification` (router), `-contract`, `-model`,
`-breaker`, `-proof`, `-target`, `-audit`, and `runtime-coverage`. In Foldable,
`/Users/pooks/Dev/jetstream-workflow-model/.agents/skills/`: `lean-formalization-strategy`
(Pass A domain contract, Pass B signature freeze), `lean-llm-proof-loop`,
`lean-assurance-review` (five axes: specification, model, proof, implementation, deployment),
`lean-model-invariants`, `lean-algebraic-systems`, `lean-project-bootstrap`. In effect-nats,
`.agents/skills/`: `effect-nats-implementation`, `effect4-stream-discipline`, `tdd`. Estate-wide
(this session's skill list): `implement`, `tdd`, `effect`, `code-review`, `review-spec`,
`to-spec`, `to-tickets`, `writing`, `diagnose`, `handoff`.

A section's skill sequence names these, in order, with the packet each consumes and the
artefact each produces. Do not invent a skill where one of these fits.

## 5. The pinned source

`effect@4.0.0-rc.112` at `/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src`.
`Queue.ts` is SHA-256 `dc355d1a09662ae7b023c98ad47b7fe71051becaf9d461f244c37ad0a4d3dc35` and
is line-stable from rc.111 except `releaseCapacity`, whose head moved from 2040 to 2037.
`vendor/effect-4.0.0-rc.112/src` in this repository is a byte-exact subset (thirteen files)
that does not yet include `Queue.ts`, `PubSub.ts`, `Semaphore.ts`, `Stream.ts`, `Channel.ts`,
`Sink.ts`. The pinned tree has no test directory but 5,879 executable doctest blocks with
`// =>` expectations, in the same files whose hashes are pinned. `/Users/pooks/Dev/effect-smol`
is a stale sibling and its tests are candidate fixtures only.

## 6. The first slice, in one paragraph

The bounded suspend-strategy `Queue`, sequential verbs only: `offer`, `takeAll`, `wake`,
`fail`, `shutdown`, with `takePark` and `takeExit` as the parked and finished reads. Port
`EffectQueue.lean` and `EffectQueueLaws.lean` from effect-nats-verified into the Char API;
stub what does not fit. State the conservation equation `acc w ++ s₀.buffer = del w ++ s.buffer`
on boundary-free runs; the grade `⟨noLoss, noDup, order⟩ = ⟨true, true, true⟩` under `F-none`
and `⟨false, true, true⟩` under `F-shutdown`. Nine pins on the internal helpers of
`Queue.ts:1955-2114` plus six on the public verbs. Seven tests, three mutants. A manifest,
emitted. A certificate document, emitted. A replay driver, emitted, run under `runSync`. A
registry entry with claims at their rungs. One gate.
