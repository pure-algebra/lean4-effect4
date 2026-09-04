# The registry of characterized Effect components: the CAS lineage, and the record types it should carry

Date: 2026-09-04. Status: research report, read-only survey plus a proposed data
model. Nothing in this document is landed code. Every claim about existing code
carries a `path:line` citation; every claim that could not be confirmed on disk
is marked **not verified**.

Scope of the survey: `/Users/pooks/Dev/lean4-effect4` (this tree),
`/Users/pooks/Dev/foldlab`, `/Users/pooks/Dev/foldlab-ssex`,
`/Users/pooks/Dev/effect-nats-verified`, `/Users/pooks/Dev/effect-nats`,
`/Users/pooks/Dev/jetstream-workflow-model`, `/Users/pooks/Dev/lean4-typescript`,
`/Users/pooks/Dev/downstream`, and the pinned Effect source at
`/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src` (4.0.0-rc.112).

The question this report answers: how a registry of characterized Effect
components should be represented so that Lean semantics (models, laws, grades,
tests) are linked to literal Effect TypeScript source spans and to replay
evidence, and so that Effect itself can build and query that registry.

---

## 0. The one-paragraph answer

Five generations have each built one third of the same machine and then stopped.
Foldlab's `library/cas` built the *addressing* discipline and proved that all the
provable work lives in the encoder. Foldlab-ssex built the *rung ladder* and the
claims ledger, then never made the ledger machine-readable. effect-nats-verified
built the *replay* rung: Lean emits deterministic bytes, TypeScript decodes them
under a pinned schema literal, and two interpreters are checked against them.
This tree, in the last two commits, built the *join*: a generic content-addressed
store (`Effect4/Store/*`), a pinned std-lib census as store content
(`Effect4/StdLib/*`), views as Effect Schema documents (`Effect4/Arch/*`), and,
separately and earlier, the only fully mechanized rung ladder in the family
(`Effect4Test/Audit/RuntimeCoverage.lean` plus
`scripts/check-effect-runtime-census.sh`). The registry is the assembly of those
four: one `Store Item` over a sum type, addressed by SHA-256 of canonical bytes,
named by a path trie, with `Claim.rung` as *data* whose coherence with its
evidence is checked at elaboration time exactly as `checkWitnesses` already
checks that a `green` census row names a real theorem.

---

## 1. Lineage: what each generation kept, dropped and learned

### 1.1 The table

| # | Generation | Dates / commits | Kept forward | Dropped | The lesson it contributed |
| --- | --- | --- | --- | --- | --- |
| G1 | foldlab `library/cas` + `docs/entity-store` | KICKOFF 2026-08-25; head-60 window 2026-08-30 to 2026-08-31 (`011d455b`, `d9cf99ee`, `91f443d3`) | `address = digest ∘ encode` with the hash abstract; framed injective encoding; typed refs with per-tag admission; image exactness (`decode_exact`) as a law | alpha-invariance of recursive schemas (recorded non-goal); input addressing; sorting by hash; annotations inside identity; floating point | The provable/assumed boundary must be a *type*, not a comment: `H` is a section variable, so a proof needing collision resistance will not elaborate |
| G2 | foldlab `library/effects` `archive/lean-model-0.3` | retired 2026-08-28; carriers reseeded into `library/cas` | the Replay/Session/Witness carriers; the eight ratified mismatch categories; mutants with a no-waiver kill criterion; per-law statement bundles with a built-in anti-vacuity kit | the whole dual-lane corpus (archived in place); the Merkle plane, dormant | Correlated error is the adversary: the kernel guarantees the proofs, nothing guarantees the statements, so mutation kill-rate is the only machine-measured anchor on statement quality |
| G3 | foldlab-ssex claims ledger and verification ladder | ladder `c8be36e1` 2026-08-12; ledger `223f763a` 2026-08-12; restructured `448db7c4`/`88965a5b` 2026-08-13 | rungs R0 to R5 owned by one file; the four-field entry (Claim / Evidence / Bounds and residuals / Checkable at); the `HELD` status; negative controls at every gate level; pin-by-recording with a numeric canary | any machine-checkable form of the ledger; incremental gating (refused on correctness grounds); mechanical verification of the upstream NATS pin | A claim can be downgraded. `HELD` exists because an external review forced a claimed R3 back to unclaimed. A ledger nothing reads is prose |
| G4 | effect-nats-verified + effect-nats replay | verified head `f193d96` 2026-08-23; harness commits `872bd7f`, `e93315e`, `b436727` | the fixture header carrying `schema` / `snapshot` / `pin` / `foldableCommit` / `compare.ignore`; two encodings of one event for two comparison resolutions; acceptance-set membership with a separate terminal set; findings-linked overrides instead of silent skips; kept refutations of superseded statements | the r4 and r4.1 forms of `A4Complete` (refuted, both kept as files); final-observed-list comparison; the subeffecting `weaken` rule; choice/parallel grade composition | Provenance belongs *in the payload*. A fixture whose header names the model snapshot, the transliteration pin and the producing commit can be traced without a side table |
| G5 | jetstream-workflow-model program map | `2026-08-23-effect-nats-formal-program-map.md` | the five artifact kinds (spec, contract, proofs, conformance, reviews) and one page saying where each lives; the evidence-kind vocabulary proved / model-checked / tested / measured / assumed / unknown | nothing built: it is an index maintained by hand at every merge | An index that is only a markdown table is maintained by discipline, and discipline is what the incremental-gate rule exists to replace |
| G6 | lean4-effect4 `Effect4/Store` + `StdLib` + `Arch` | `ad3027c` 2026-09-04 (store), `a4ba1e9` 2026-09-04 (middle tier) | the generic store with laws; the census as store content with file digests; 65 checked links from export path to model element; views as Schema documents projected from proof carriers | the abstract `H`: the digest here is concrete SHA-256 from `lean4-hash`, with the *step from equal digests to equal bytes* never assumed | Content can be addressed *and* named *and* linked to semantics in one structure, and the whole thing elaborates inside the axiom ceiling |
| G6' | lean4-effect4 runtime coverage (earlier, and the strongest rung machinery in the family) | `Effect4Test/Audit/RuntimeCoverage.lean`, `scripts/check-effect-runtime-census.sh` | anchored span digests; frozen statement snapshots; per-witness axiom receipts; a coverage state that cannot exceed its witnesses; content-hash stamps | none: this is the only piece of the family where the ledger, the evidence and the gate are one artifact | The ledger *can* be code. `checkRowShape` refuses `green` with no witness, and `checkWitnesses` refuses a witness that is not a theorem |

### 1.2 What each generation actually built, with citations

**G1, foldlab CAS.** The carrier/encoding/address stack is three files that
deliberately do not mention the layer above.
`/Users/pooks/Dev/foldlab/library/cas/Cas/Core/Node.lean:27` fixes
`Addr32 := { b : Bytes // b.length = 32 }`, so the width is intrinsic;
`/Users/pooks/Dev/foldlab/library/cas/Cas/Core/Address.lean:36` is
`def addr (n : AdmittedNode) : Addr := H (encodeAdmitted n)` with
`H : Bytes → Addr` a section variable declared at
`/Users/pooks/Dev/foldlab/library/cas/Cas/Core/Address.lean:32`. The three-level
hash-hypothesis lattice is Level 0 unconditional
(`/Users/pooks/Dev/foldlab/library/cas/Cas/Core/Address.lean:56`,
`addr_eq_or_collision`), Level 1 with an explicit injectivity premise
(`:69`), and Level 2 proved empty by the degenerate-`H` example at `:84-87`.
The `Canonical` class at
`/Users/pooks/Dev/foldlab/library/cas/Cas/Core/Canonical.lean:28-32` carries
`decode_exact` as a field, because round-trip plus injectivity does not imply
image exactness. Canonicalization is data, not a class
(`/Users/pooks/Dev/foldlab/library/cas/Cas/Core/Canonicalize.lean:26-30`), with
the ruling that identity hashes presentations and never denotations. The seven
laws of the entity store are at
`/Users/pooks/Dev/foldlab/docs/entity-store/KICKOFF.md:98-186`; L1 at `:100-108`
("all the provable work is in the encoder"), L2 at `:110-118` ("frame everything"),
L7 at `:160-165` ("cycles are unconstructible between addressed units").
Alpha-invariance is a recorded non-goal at
`/Users/pooks/Dev/foldlab/docs/entity-store/KICKOFF.md:1032`; the two
hashing-modulo-alpha papers appear only in the bibliography at
`/Users/pooks/Dev/foldlab/README.md:364` and `:367`.

The most transferable sentence in the whole family is
`/Users/pooks/Dev/foldlab/docs/entity-store/KICKOFF.md:157-158`: integrity
checking catches corruption, never encoder bugs.

**G2, the retired conformance corpus.** Retirement is recorded at
`/Users/pooks/Dev/foldlab/library/effects/archive/lean-model-0.3/README.md:1-9`.
The replay carriers are
`.../Effects/Replay/Session.lean:45-51` (`SessionState`),
`.../Effects/Replay/Witness.lean:21-28` (`Witness` with `mode`, `execId`,
`consumed`, `trace`, `outcome`), and the eight ratified mismatch categories at
`.../Effects/Replay/Decision.lean:28-39`. Obligations are typed data with a
six-arm disposition at
`.../Effects/Conformance/Obligations.lean:14-30`, and a mutant is
`.../Effects/Conformance/Mutant.lean:13-19` with the kill criterion
`manifest(mutant) ≠ manifest(model)`, no waivers, at
`.../MutationMain.lean:40-49`. The statement bundles carry their own
anti-vacuity kit: `.../Effects/Conformance/Schema/Codec.lean:16-27` has
`posVal`, `negBytes` and `neg_rejects` as *fields*. Correlated error is named at
`.../CONFORMANCE-WORKFLOW.md:33-38`.

**G3, the claims ledger.** The rung legend is
`/Users/pooks/Dev/foldlab-ssex/VERIFICATION.md:13-20`: R0 fixture walls, R1
property tests, R2 bounded model check, R3 inductive invariant, R4 lockstep
conformance, R5 mechanized proof. The four-part entry shape is declared at
`/Users/pooks/Dev/foldlab-ssex/VERIFICATION.md:21-27`. The governing rule,
"a claim absent from that ledger is not made", is at
`/Users/pooks/Dev/foldlab-ssex/README.md:34`. The ladder itself is owned by
`/Users/pooks/Dev/foldlab-ssex/docs/map/tickets/009-the-verification-ladder.md:18-29`.
Two findings matter for the design here. First, nothing reads the ledger: the
one gated index is `/Users/pooks/Dev/foldlab-ssex/docs/LAWS.md`, checked by
`/Users/pooks/Dev/foldlab-ssex/scripts/check-laws.ts`, and
`/Users/pooks/Dev/foldlab-ssex/docs/LAWS.md:33-36` explicitly places rungs R0 to
R5 *outside* that gate. Second, the gate battery is deliberately non-incremental:
`/Users/pooks/Dev/foldlab-ssex/.github/workflows/gates.yml:6-11` states the
reason (splitting a cross-language differential lane would half-run and still
report green), and `/Users/pooks/Dev/foldlab-ssex/scripts/gates.ts:12-29` is a
flat sequential list with no change detection. That is the position this tree's
rule 9 rejects.

The upstream pin discipline is `path:line` against a tag plus commit:
`/Users/pooks/Dev/foldlab-ssex/docs/research/2026-08-12-jetstream-guarantees-source-verified.md:3-8`
pins `nats-io/nats-server` v2.14.4 at `bbd6dc5e...`, and `:10-13` sets the rule
that server code is cited as fact and ADRs as intent. Nothing re-resolves those
citations; the three commit SHAs appear in exactly one file, the document
asserting them.

**G4, replay.** The exporter is
`/Users/pooks/Dev/effect-nats-verified/Main.lean`; the determinism claim is at
`:11-14` and the encoding contract read by the harness at `:16-24`. The schema-1
fixture header is `/Users/pooks/Dev/effect-nats-verified/Main.lean:129-137` and
the schema-2 header `:214-222`; both carry `schema`, `producer`, `snapshot`,
`pin` (the effect-nats commit the model was transliterated from),
`foldableCommit` (the producing commit, supplied by `--foldable-commit`, parsed
at `:230-235`) and `compare.ignore`. Determinism is a gate step, not a claim:
`/Users/pooks/Dev/effect-nats-verified/scripts/gate.sh:21-29` runs the exporter
twice and `cmp`s. The acceptance-set model is
`/Users/pooks/Dev/effect-nats-verified/EffectNatsSubstrate/SubPlacements.lean`,
with `placementsOf` at `:100-103`, the separate `terminalPlacementsOf` at
`:105-111` (ordinary acceptance sets are prefix-closed, so quiescent runs need a
terminal set), and the independence caveat stated beside the definition at
`:24-30`. Kept refutations are
`/Users/pooks/Dev/effect-nats-verified/scripts/A4CompleteR4Refutation.lean:21-82`
and `.../A4CompleteR41Refutation.lean:33-42`, each re-stating the *frozen text*
of the disproved statement together with the commit it was frozen at. On the
TypeScript side, the header is pinned by a schema literal
(`origin/main:test/LeanTraceReplay.ts:95`, `schema: Schema.Literal(1)`), and the
agreement check is deep equality after normalization at `:252`; free-running
agreement is set membership at
`origin/main:test/LeanSubscriberFreeRun.ts:318-329`.

The grade ladder on the TypeScript side is a bare string union:
`/Users/pooks/Dev/effect-nats/packages/agents/src/nats/grade.ts:9` is
`export type Guarantee = "atMostOnce" | "atLeastOnce" | "dedupWindow" | "pure"`,
with sequential composition as the meet at `:24-25` and the order at `:27`.
Grades are attached as data fields on recorded publishes
(`/Users/pooks/Dev/effect-nats/packages/agents/src/nats/service.ts:79`, `:91`,
`:115`), never as a type-level index. The graded model note
`/Users/pooks/Dev/effect-nats/packages/agents/notes/0003-graded-algebra-model.md:26-32`
records the meet laws as proved, and `:62-63` admits the mechanical Lean-to-TS
bridge is unbuilt. There is no `noLoss`/`noDup` axis anywhere in either repo
(grep returns zero hits); the ladder is one total order. The note at `:29-32`
explicitly warns against forcing ordering guarantees into the same monoid.

**G5, the program map.** The registry page is
`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-23-effect-nats-formal-program-map.md:7-9`;
its table is seven columns, one row per stage, at `:22-23`, and the five artifact
kinds with their rules are enumerated at `:32-48`. The evidence-kind vocabulary
(proved, model-checked, tested, measured, assumed, unknown) is at
`/Users/pooks/Dev/jetstream-workflow-model/research/2026-08-23-effect-nats-lanes-plan.md:103`.
The verified-citation law is
`/Users/pooks/Dev/jetstream-workflow-model/AGENTS.md:29-31`: a `path:line`
citation may only be written by someone who opened that file at that line.

**G6, this tree.** The store is four files. Canonical bytes are framed
`tag :: length ++ payload` (`Effect4/Store/Canonical.lean:53`), the tag alphabet
is `Effect4/Store/Canonical.lean:57-67`, the class is `:70` and the law is kept
separate at `:78` so a carrier can be stored before its law lands. `Path` is a
`List String` at `Effect4/Store/Canonical.lean:108`. The address is SHA-256 of
canonical bytes: `Effect4/Store/Digest.lean:32` and `:36`, with the width theorem
at `:58`. The doc at `Effect4/Store/Digest.lean:14-21` states the discipline that
matters most here: no security property is claimed, a digest is an *address*, and
every store law that would need collision freedom is stated with the digest's
freshness as a hypothesis (`Effect4/Store/Store.lean:97`, `:102`). The store
itself is `Effect4/Store/Store.lean:32`, `put` deduplicates by address at `:61`,
`putAt` names in one step at `:72`, `resolve` reads a path back at `:77`, and
`under` enumerates a prefix at `:89`. The trie's whole contract is two lemmas:
`Effect4/Store/Trie.lean:131` and `:139`.

The census is `Effect4/StdLib/Entry.lean:44` (`Entry`) and `:52` (`FilePin`),
with the store path `[module, name]` at `:61` and the `Canonical Entry` instance
at `:72`. The generated data is `Effect4/StdLib/Rc112.lean:17` (21 file pins,
`:18-38`) and `:1907` (1,835 entries, count at `:1911`). The links are
`Effect4/StdLib/Links.lean:32` (`ModelRef`, four arms), `:43` (`Link`), `:74`
(65 links), `:145` (`ModelRef.declared`), `:158` (`Link.checked`) and `:162`
(`semanticsOf`). The receipts are `Effect4Test/Arch/ArchContract.lean:119-120`
(every link checked, 65 of them) and `:110` (the store is as large as the
census). The census also records a negative: rc.112's `Layer` exports no
`scoped`, so the family's `scoped` row has no link
(`Effect4/StdLib/Links.lean:120-122`, receipt at
`Effect4Test/Arch/ArchContract.lean:122-123`).

The views are `Effect4/Arch/Views.lean:54`, `:123`, `:144`, `:156`, named and
stored at `:177` and `:184`. The middle tier is described at
`Effect4/Arch/Views.lean:18-22`: proof carriers below, views as data here, the
same schema decoded by rc.112's own codec above. Acceptance is
`Effect4/Arch/Accepts.lean:114`, and what it does not decide is stated in the
module doc at `:18-31`. Schemas are addressable because
`Effect4/Arch/JsonCanonical.lean:92` and `:95` give `Representation` and
`Document` canonical instances through their persisted JSON form.

**G6', the rung machinery.** The census generator anchors spans rather than line
numbers: `scripts/generate-effect-runtime-census.sh:5-15` states the design, the
row format is `kind|id|file|anchor|offset-start|offset-end|expected-span-sha256|summary`
at `:145`, and the extraction is `:336-362`. Because the span runs from
anchor-line plus offsets, an upstream edit *above* a span moves the line numbers
without disturbing the digest, and any edit *inside* a span fails the run. The
frozen join is `Effect4Test/Audit/RuntimeCoverage.lean:2547` (`Row`, with `id`,
`kind`, `disposition`, `coverage`, `witnesses`), the vocabularies at `:2562`,
`:2565`, `:2569`, `:2573`, and the row list at `:2575`. The coherence checks are
`checkRowShape` at `:3893` (a row declared `absent` may carry no witness; a row
not `absent` must carry one; an `owned` row must carry one; an excluded
disposition must carry none), `checkWitnesses` at `:3917` (the declaration must
exist and must be a `thmInfo`, never a Prop-typed def), `canonicalAxiomText` at
`:3883` (any axiom outside `propext`/`Quot.sound` fails), and `checkSnapshot` at
`:3934` (every witness has a frozen `#check (@name : proposition)` ascription and
no ascription is stale). The commands run in the default build:
`Effect4Test/Audit/RuntimeCoverage.lean:4004-4005`, reached because
`Effect4Test.lean:130-131` imports both contracts and `lakefile.toml:8` makes
`Effect4TestGreen` a default target.

### 1.3 The three things nobody has built yet

1. **A machine-checked link from a Lean claim to a literal Effect source span.**
   This tree has 683 `path:line` citations into pinned rc.112 sources inside Lean
   doc comments (counted by `grep -rhoE '(internal/)?[A-Za-z]+\.ts:[0-9]+(-[0-9]+)?' --include='*.lean' Effect4 Effect4Test | wc -l`),
   of which 185 target `internal/effect.ts`, 104 `Layer.ts` and 76 `Deferred.ts`.
   Exactly 137 spans are machine-checked, namely the `mechanism` rows of
   `generated/effect-runtime-census.tsv:18` onward. The internal-citation gate
   deliberately accepts the rest without resolving them:
   `scripts/check-internal-citations.sh:30-33` says line citations into the
   pinned host sources are examined and accepted, and that the gate makes no
   claim about them.
2. **A grade.** No `noLoss`, `noDup`, `Grade` or failure-model carrier exists in
   `Effect4/` (grep over `--include='*.lean' Effect4 Effect4Test` returns nothing
   outside the vendored foldlab tree). The nearest thing is the observation mask:
   `generated/traces/masks.tsv:8-11` declares three masks over trace row kinds,
   and the A0 spike report records 435 of 435 mask pairs agreeing with rc.112
   (`docs/research/2026-09-04-spike-a0-avatar.md:12-22`).
3. **A gate on the census and on the arch contract.** `scripts/sweep.sh:64-77`
   lists twelve gates; `check-effect-runtime-census.sh` is there,
   `check-schema-census.sh` and `check-vendor-foldlab.sh` are not, and there is
   no `check-stdlib-census.sh` at all (`ls scripts/` shows the generator
   `generate-stdlib-census.ps1` with no checker beside it). The std-lib census is
   therefore protected only by the `#guard`s at
   `Effect4Test/Arch/ArchContract.lean:84-94`, which pin four file digests and
   two counts, and by nothing that re-reads the install.

---

## 2. The registry data model

### 2.1 The shape

One `Store Item` over a sum type, not several stores. Reasons: `put`
deduplicates by address across the whole store
(`Effect4/Store/Store.lean:61`), so a `Pin` referenced by three claims is one
entry; ids are stable for the life of the store, so a claim can cite an id; and
the trie already gives prefix enumeration (`Effect4/Store/Store.lean:89`), which
is the query "everything under `["claim", "Queue"]`". Cross-item references are
by `Digest` (content) rather than by id (position), so a registry can be merged
with another registry without renumbering.

The path scheme, chosen so every useful query is a prefix walk:

| Item | Path | Query it serves |
| --- | --- | --- |
| `Pin` | `["pin", package, version, file, spanDigest]` | every pinned span of a file; drift by file |
| `Component` | `["component", name]` | the component index |
| `Verb` | `["verb", component, name]` | every verb of a component |
| `FailureModel` | `["failure", name]` | the failure-model index |
| `Claim` | `["claim", component, verbOrStar, id]` | every claim about a component, or about one verb |
| `Fixture` | `["fixture", family, id]` | every fixture of a family |
| `Grade` | `["grade", component, verbOrStar, failureModel]` | "what grade does this verb carry under F" |
| `Usage` | `["usage", userModule, userName, usedModule, usedName]` | "where is Queue used"; "what does Stream.fromQueue use" |
| `Link` | `[module, name]` (unchanged) | a name in code to its model elements |

`Link` keeps its existing path because `Effect4/StdLib/Links.lean:158` already
resolves it against `rc112` at `Effect4/StdLib/Links.lean:155`, and the census
store is a `Store Entry` addressed by `[module, name]`
(`Effect4/StdLib/Entry.lean:61`). The registry holds a second binding
`["link", module, name]` so the two stores can merge later without a collision;
that is a naming decision, not a semantic one.

### 2.2 The record types

Everything below is a first-order structure with `DecidableEq`, so it has a
`Canonical` instance by the same one-line pattern
`Effect4/StdLib/Entry.lean:72` uses (encode the tuple of fields), and therefore a
digest by `Effect4/Store/Digest.lean:36`. `LawfulCanonical` is *not* claimed for
any of them; that is deliberate, and follows
`Effect4/Store/Canonical.lean:75-78`.

```lean
import Effect4.StdLib.Links
import Effect4.Store.Store

namespace Effect4.Registry

open Effect4.Store Effect4.StdLib

/-- A pinned span of third-party source: the whole-file digest, the anchor and
offsets the census generator uses (`scripts/generate-effect-runtime-census.sh:145`),
the span digest, and the literal text. The anchor is what makes the pin survive
edits above it; the span digest is what makes an edit inside it fail. -/
structure Pin where
  package : String          -- "effect"
  version : String          -- "4.0.0-rc.112"
  file : String             -- "src/Queue.ts"
  fileSha256 : String       -- the whole-file digest, as `FilePin.sha256`
  anchor : String           -- a literal substring occurring exactly once
  offsetStart : Int
  offsetEnd : Int
  spanSha256 : String       -- sha256 of the extracted lines
  text : List String        -- the literal lines, so Lean can `decide` on bytes
deriving DecidableEq, Repr, Inhabited

def Pin.path (p : Pin) : Path := ["pin", p.package, p.version, p.file, p.spanSha256]

instance : Canonical Pin :=
  ⟨fun p => encode ((p.package, p.version, p.file, p.fileSha256),
                    (p.anchor, p.offsetStart.toNat, p.offsetEnd.toNat),
                    (p.spanSha256, p.text))⟩
```

The `text` field is what lets a claim be *checked by `decide` on bytes*, which is
the pinned rung: `#guard (registryPin "Queue.take").text = [...]` is a kernel
computation over the literal lines, and `#guard (registryPin "Queue.take").spanSha256 = "..."`
is the join to the generator. Neither needs the file at elaboration time.

```lean
/-- One operation of a component: the exported name, the pins that establish its
behaviour, and the model elements it reifies. `refs` is `StdLib.ModelRef`
(`Effect4/StdLib/Links.lean:32`), reused rather than duplicated. -/
structure Verb where
  component : String        -- "Queue"
  name : String             -- "take"
  exportPath : Path         -- ["Queue", "take"], resolvable in `rc112`
  pins : List Digest        -- addresses of `Pin` content
  refs : List ModelRef
deriving DecidableEq, Repr

/-- A component as a labelled transition system, named rather than carried: the
carriers live in `Effect4/Deep/*` and the registry cites them. -/
structure Component where
  name : String             -- "Queue"
  module : String           -- "Queue", the census module
  stateCarrier : String     -- the Lean declaration standing for S
  initial : String          -- the Lean declaration standing for s0
  labels : List String      -- L
  observations : List String -- O
  stepRelation : String     -- the Lean declaration standing for step
  verbs : List String
deriving DecidableEq, Repr

/-- A failure model: the boundary labels a run may take that the component does
not choose. `interrupt` and `defect` are rc.112's own; `hostCrash` is not
observable in-process and is named so a grade under it is honestly absent. -/
structure FailureModel where
  name : String             -- "F-interrupt"
  boundaryLabels : List String
  note : String
deriving DecidableEq, Repr
```

The claim and its evidence. This is the part that must not be able to lie.

```lean
/-- The rungs, in order. Data, exactly as `Row.coverage` is data at
`Effect4Test/Audit/RuntimeCoverage.lean:2555`. -/
inductive Rung where
  | pinned    -- checked by `decide` on the bytes of a source span
  | replayed  -- a finite fixture on which the Lean model and rc.112 agree
  | proved    -- a Lean theorem inside the axiom ceiling
deriving DecidableEq, Repr, Inhabited

def Rung.rank : Rung → Nat
  | .pinned => 0
  | .replayed => 1
  | .proved => 2

/-- One piece of evidence. The rung a piece of evidence *can* support is a
function of its constructor, so no claim can name a rung its evidence does not
reach. -/
inductive Evidence where
  /-- The span digest of a `Pin`, plus the guard name that decides on its bytes. -/
  | pin (spanSha256 : String) (guard : String)
  /-- A fixture id and the sha256 of its golden bytes. -/
  | fixture (id : String) (sha256 : String)
  /-- A Lean theorem name and its expected canonical axiom receipt, spelled as
  `RuntimeCoverage` spells one (`Effect4Test/Audit/RuntimeCoverage.lean:3883`). -/
  | thm (name : String) (axioms : String)
deriving DecidableEq, Repr

def Evidence.rung : Evidence → Rung
  | .pin _ _ => .pinned
  | .fixture _ _ => .replayed
  | .thm _ _ => .proved

inductive ClaimKind where
  | equation      -- an equational law between verb compositions
  | invariant     -- an inductive invariant of the LTS
  | traceProperty -- a property of the observation sequence under a mask
  | gradeClause   -- one half of a grade: noLoss, or noDup
deriving DecidableEq, Repr

structure Claim where
  id : String               -- "queue.take.exactly-once", stable for its life
  component : String
  verb : Option String
  kind : ClaimKind
  /-- What is asserted, in one sentence, in the census-summary register. -/
  summary : String
  /-- The rung the registry declares. -/
  rung : Rung
  /-- Every piece of evidence, in a fixed order. -/
  evidence : List Evidence
  /-- What the evidence does not cover, in the register of
  `Effect4/Arch/Accepts.lean:18-31`. Never empty for a non-proved rung. -/
  residual : String
deriving DecidableEq, Repr
```

The coherence rule, decidable and elaboration-checked:

```lean
/-- The highest rung any of a claim's evidence supports. -/
def Claim.supported (c : Claim) : Option Rung :=
  c.evidence.foldl (fun acc e =>
    match acc with
    | none => some e.rung
    | some r => if r.rank < e.rung.rank then some e.rung else some r) none

/-- A claim may not outrank its evidence, and may not carry a rung with no
evidence at all. This is the `decide`-able half; the half that needs the
environment is `checkClaims` below. -/
def Claim.coherent (c : Claim) : Bool :=
  match c.supported with
  | none => false
  | some r => c.rung.rank ≤ r.rank
```

`Claim.coherent` is exactly the shape of `checkRowShape`'s coverage rules at
`Effect4Test/Audit/RuntimeCoverage.lean:3907-3916`, lifted from a string
comparison to a decidable order. The half that a `#guard` cannot see is whether
the named theorem exists, is a theorem, and has the receipt it declares. That is
already written, and should be reused verbatim in shape:
`checkWitnesses` at `Effect4Test/Audit/RuntimeCoverage.lean:3917-3932` looks the
name up in the environment, rejects anything that is not `.thmInfo`, and compares
`canonicalAxiomText` against the declared string. A `checkClaims` command elaborator
does the same over `Evidence.thm`, plus two new obligations: every
`Evidence.pin` names a `Pin` held in the registry store, and every
`Evidence.fixture` names a `Fixture` held in it.

```lean
/-- A replay fixture. Every field of the header
`generated/traces/ref/makeGet.tsv:1-12` and of
`/Users/pooks/Dev/effect-nats-verified/Main.lean:129-137`, in one record. -/
structure Fixture where
  id : String               -- "ref.makeGet"
  family : String           -- "ref"
  format : String           -- "effect4-trace-v1"
  producer : String         -- the generator script path
  producerSha256 : String
  /-- The rc.112 pin the fixture was produced against. -/
  effectVersion : String
  /-- The commit of this tree that produced the bytes. -/
  producingCommit : String
  /-- The mask under which the faces are compared
  (`generated/traces/masks.tsv:8-11`). -/
  mask : String
  /-- The faces that agreed: "lean", "rc112", "ocaml". -/
  faces : List String
  /-- sha256 of the golden bytes. -/
  sha256 : String
  rowCount : Nat
deriving DecidableEq, Repr

/-- One half of a grade. A grade is not a total order: `noLoss` and `noDup` are
independent, which is the correction the effect-nats ladder
(`grade.ts:9`) collapsed into one axis. -/
structure Grade where
  noLoss : Bool
  noDup : Bool
deriving DecidableEq, Repr

/-- The meet: a composite is only as strong as its weakest step, componentwise.
This is `meet` from `grade.ts:24-25`, generalised to two independent axes. -/
def Grade.meet (a b : Grade) : Grade :=
  ⟨a.noLoss && b.noLoss, a.noDup && b.noDup⟩

def Grade.leq (a b : Grade) : Bool :=
  (!a.noLoss || b.noLoss) && (!a.noDup || b.noDup)

structure GradeAssignment where
  component : String
  verb : Option String
  failureModel : String     -- names a `FailureModel`
  grade : Grade
  /-- The claim id backing each true bit. A `true` bit with no claim is refused. -/
  noLossClaim : Option String
  noDupClaim : Option String
deriving DecidableEq, Repr

/-- "Stream.fromQueue uses Queue.takeAll via Channel.fromQueueArray", with the
pin of every call site on the path. -/
structure Usage where
  user : Path               -- ["Stream", "fromQueue"]
  used : Path               -- ["Queue", "takeAll"]
  via : List Path           -- [["Channel", "fromQueueArray"]]
  /-- One span digest per hop, in `user :: via ++ [used]` order. -/
  pins : List String
deriving DecidableEq, Repr

/-- The registry's content alphabet. -/
inductive Item where
  | pin (value : Pin)
  | component (value : Component)
  | verb (value : Verb)
  | failureModel (value : FailureModel)
  | claim (value : Claim)
  | fixture (value : Fixture)
  | grade (value : GradeAssignment)
  | usage (value : Usage)
  | link (value : Link)
deriving DecidableEq, Repr

def Item.path : Item → Path
  | .pin p => p.path
  | .component c => ["component", c.name]
  | .verb v => ["verb", v.component, v.name]
  | .failureModel f => ["failure", f.name]
  | .claim c => ["claim", c.component, c.verb.getD "*", c.id]
  | .fixture f => ["fixture", f.family, f.id]
  | .grade g => ["grade", g.component, g.verb.getD "*", g.failureModel]
  | .usage u => ["usage"] ++ u.user ++ u.used
  | .link l => "link" :: l.path

abbrev Registry := Store Item

def Registry.ofItems (items : List Item) : Registry :=
  items.foldl (fun s item => (s.putAt item.path item).2) Store.empty
```

The `Canonical Item` instance is one `match` producing `encode` of a tagged pair,
the same way `Effect4/Store/Canonical.lean:102-105` handles `Option`.

### 2.3 The worked example: is `Queue` exactly-once

Every citation below was opened.

- `Pin`, three of them: `Queue.ts:1474-1477` is
  `export const take = <A, E>(self: Dequeue<A, E>): Effect<A, E> => internalEffect.suspend(() => takeUnsafe(self) ?? internalEffect.andThen(awaitTake(self), take(self)))`;
  `Queue.ts:1297-1298` is `takeAll = takeBetween(self, 1, Number.POSITIVE_INFINITY)`;
  `Queue.ts:645` is `offer`.
- `Usage`, verified end to end: `Stream.ts:1132-1133` is
  `fromQueue = (queue) => fromChannel(Channel.fromQueueArray(queue))`;
  `Channel.ts:1229-1231` is
  `fromQueueArray = (queue) => fromPull(Effect.succeed(Queue.takeAll(queue)))`.
  So `Usage ⟨["Stream","fromQueue"], ["Queue","takeAll"], [["Channel","fromQueueArray"]], [...]⟩`
  is a real edge with three pins.
- `Claim` at the pinned rung, today: "`Queue.take` retries through `awaitTake`
  after an unsuccessful `takeUnsafe`", `rung := .pinned`, evidence
  `.pin "<span digest>" "queue_take_shape"`, residual "says nothing about what
  happens if the taker is interrupted between `takeUnsafe` and the continuation".
- `Claim` at the proved rung, not available: there is no `Queue` model in
  `Effect4/Deep/*` (`ls Effect4/Deep` shows `Context`, `Fibers`, `ForkFlow`,
  `Layer`, `Stores`, `Witnesses`), so a `noDup` claim under interruption cannot
  be `proved` and must be `pinned` with the residual stated. The registry makes
  that visible rather than hiding it, which is the point.

Grade composition along the usage edge: if `Queue.takeAll` carries
`⟨noLoss := true, noDup := true⟩` under `F-interrupt` and
`Channel.fromQueueArray` contributes nothing of its own, then
`Stream.fromQueue` carries `Grade.meet` of the two, and the composite claim's
rung is the minimum of the rungs of the claims backing each factor. That
minimum rule is the registry's own version of foldlab-ssex's "a claim absent
from that ledger is not made" (`/Users/pooks/Dev/foldlab-ssex/README.md:34`):
a composite grade is only as well-evidenced as its worst step.

---

## 3. The drift gate

### 3.1 What must fail, on what change

| Change | Detected by | Where | Fails as |
| --- | --- | --- | --- |
| Effect bumped, any byte of a pinned file | whole-file digest mismatch | `generated/effect-runtime-census.tsv:5-16` inputs; `Effect4/StdLib/Rc112.lean:18-38`; `Effect4Test/Arch/ArchContract.lean:87-94` | generator exits before reading any span (`scripts/generate-effect-runtime-census.sh:94-95`) |
| Effect edited *above* a span | nothing, by design | anchor plus offsets (`scripts/generate-effect-runtime-census.sh:5-9`) | no failure; line numbers move, span digest does not |
| Effect edited *inside* a span | span digest mismatch | `scripts/generate-effect-runtime-census.sh:355-360` | named row, expected and found digest printed |
| An anchor becomes ambiguous or vanishes | occurrence count is not 1 | `scripts/generate-effect-runtime-census.sh:341-346` | named row, count printed |
| A Lean statement changes | `#check (@name : proposition)` ascription no longer typechecks | `Effect4Test/Audit/RuntimeCoverage.lean:50-3891` | `type mismatch` at the offending line |
| An ascription is deleted | source scan and emitted list differ | `scripts/check-effect-runtime-census.sh:177-190` | diff of two lists |
| A witness stops being a theorem | environment lookup is not `.thmInfo` | `Effect4Test/Audit/RuntimeCoverage.lean:3922-3928` | "a witness must be a theorem" |
| A witness reaches a new axiom | receipt comparison | `Effect4Test/Audit/RuntimeCoverage.lean:3883-3891`, `:3929-3932` | "unexpected kernel axioms" |
| A claim outranks its evidence | `Claim.coherent` plus `checkClaims` | proposed, modelled on `Effect4Test/Audit/RuntimeCoverage.lean:3907-3916` | named claim id |
| A fixture's bytes change | golden byte comparison | `scripts/check-trace-host.sh:83-86` | `cmp` diff, first 20 lines |
| A fixture's producing commit is stale | `Fixture.producingCommit` versus `git rev-parse HEAD` | proposed; the ancestor is `--foldable-commit` at `/Users/pooks/Dev/effect-nats-verified/Main.lean:230-235` | named fixture id |
| A generated projection is stale | regenerate and `cmp` | `scripts/check-effect-runtime-census.sh:133-142` | full diff |
| The vendored evidence bundle drifts | pin plus scope plus per-file digest | `scripts/check-vendor-foldlab.sh:10`, `:26-37`; `vendor/foldlab/PINNED-MANIFEST.tsv:1` | named path |

Two gaps this table exposes. First, the std-lib census has no checker: the file
digests at `Effect4/StdLib/Rc112.lean:18-38` are compared to four vendored ones
by `#guard` at `Effect4Test/Arch/ArchContract.lean:87-94` and to nothing else,
and `scripts/generate-stdlib-census.ps1:20-22` only enforces the package version
when it is run, which the sweep never does (`scripts/sweep.sh:64-77`). Seventeen
of the 21 pins are unchecked. Second, the 683 prose citations into rc.112 are
unchecked by construction (`scripts/check-internal-citations.sh:30-33`). The
registry closes both by turning a citation into a `Pin` record with a span
digest, which the same generator machinery can re-extract.

### 3.2 Keeping the gates incremental

The rule is `docs/research/2026-09-03-refactor-plan.md:24-27` and the memory note
`gates-must-be-incremental`: a gate does not re-run when its inputs are
unchanged; it keys a stamp under `.lake/stamps/<name>/` on the content hash of
its sources, fixtures and the Lake traces of the compiled closure it reads.

Three mechanisms, in order of preference:

1. **Elaboration-time checks are already incremental and cost nothing.** Every
   `#guard` in `Effect4Test/Arch/ArchContract.lean` and every check in
   `Effect4Test/Audit/RuntimeCoverage.lean:4004-4005` runs inside `lake build`,
   and Lake re-elaborates a module only when its trace changes. So the *entire*
   coherence layer of the registry (paths resolve, links are declared, claims do
   not outrank their evidence, grades name a failure model that exists, witnesses
   are theorems with the declared receipts) belongs in Lean, not in a script.
   That is the single most important design decision in this report.
2. **Byte-level drift needs a script, so it needs a stamp.** The pattern is
   `scripts/check-effect-runtime-census.sh:88-131`: build the witness module
   first so the traces hashed are the ones the join will read, collect the
   script, the generator, the shared libs, the witness module, its Lake trace,
   the candidate projection, the installed `package.json`, the lakefile, the
   manifest and the toolchain, then read the *input rows out of the candidate*
   so a doctored input list changes the key
   (`scripts/check-effect-runtime-census.sh:116-122`). `stamp_key` is
   `scripts/lib/stamp.sh:53`, `stamp_hit` is `:74`, `stamp_write` is `:86`, and
   `stamp_lean_traces` is `:118` with the reason at `:16-20`: a module's trace is
   Lake's hash of its source together with the traces of everything it imports,
   so naming direct imports stands for the whole closure.
3. **Generators are never stamped; their callers key on the generator's inputs.**
   `scripts/lib/stamp.sh:29-42` states it: a generator has no verdict to cache,
   so the stamp always sits on the checking side.

For the registry specifically:

- `check-registry.sh` keys on: the script, `scripts/lib/{portable,stamp}.sh`,
  `Effect4/Registry/*.lean`, the Lake traces of `Effect4Test.Registry.Contract`,
  `generated/registry-pins.tsv`, every pinned rc.112 file named in that
  projection's `input` rows, `lakefile.toml`, `lake-manifest.json`,
  `lean-toolchain`, and `stamp_fact "effect-version" "$(jq -r .version …)"`.
- The pin re-extraction reuses the anchor mechanism verbatim, so a bump that does
  not touch a pinned span is a hit for that row and the whole gate is a hit if it
  touches none.
- The fixture rung keys additionally on the golden files and on
  `stamp_fact "producing-commit" "$(git rev-parse HEAD)"`, which is what makes a
  regenerated fixture a miss without re-running the host.

---

## 4. The Effect face

### 4.1 The registry as an Effect Schema document

This is a fifth view in the sense of `Effect4/Arch/Views.lean:177`, and it needs
no new machinery. A `Document` (`Effect4/Schema/Document.lean:127`, pinned to
`SchemaRepresentation.ts:480-483` by its own doc comment at `:125`) is built with
the authoring combinators already used at `Effect4/Arch/Views.lean:43-59`;
`Effect4/Arch/Accepts.lean:114` decides that a projected payload inhabits it; and
`Effect4/Target/TypeScript/Schema.lean:526-528` emits a module. That module has
exactly two imports (`Effect4/Target/TypeScript/Schema.lean:506-507`,
`effect/Schema` and `effect/SchemaRepresentation`), exports the raw JSON at
`:473-483`, and hands it to rc.112's own decoder at `:484-490`:
`SchemaRepresentation.fromJson`, which exists at
`/Users/pooks/Dev/foldlab/library/effects/node_modules/effect/src/SchemaRepresentation.ts:1177`.
So the app face typechecks against Effect's own `Document`, not against a
hand-written mirror. The receipts for this pattern already exist at
`Effect4Test/Arch/ArchContract.lean:65-71`.

The registry document declares a tagged union over `Item`, using
`Schema.Union` (`Schema.ts:4923`) of `Schema.Struct`s (`Schema.ts:3581`) each
carrying a `Schema.Literal` tag (`Schema.ts:2785`). Decoding is
`Schema.decodeEffect` (`Schema.ts:1559`), so a malformed registry is a typed
`Effect` failure rather than a throw.

### 4.2 The query

```ts
// Generated beside the document by Effect4.Target.TypeScript.Schema.generate?.
import * as Effect from "effect/Effect"
import * as Context from "effect/Context"
import * as Layer from "effect/Layer"

export interface GradeAnswer {
  readonly grade: { readonly noLoss: boolean; readonly noDup: boolean }
  readonly rung: "pinned" | "replayed" | "proved"
  readonly evidence: ReadonlyArray<
    | { readonly _tag: "pin"; readonly spanSha256: string; readonly file: string; readonly lines: string }
    | { readonly _tag: "fixture"; readonly id: string; readonly sha256: string }
    | { readonly _tag: "thm"; readonly name: string; readonly axioms: string }
  >
  readonly residual: string
}

export class Registry extends Context.Key<Registry, {
  readonly gradeOf: (
    component: string,
    verb: string,
    failureModel: string
  ) => Effect.Effect<GradeAnswer, RegistryMiss>
  readonly usesOf: (component: string, verb: string) => Effect.Effect<ReadonlyArray<Usage>>
  readonly claimsOf: (component: string) => Effect.Effect<ReadonlyArray<Claim>>
}>()("effect4/Registry") {}

export const layer: Layer.Layer<Registry> = /* decode the generated document, build the tries */
```

`Context.Key` is `Context.ts:64`. Three notes on the shape:

- **The answer always carries provenance.** `gradeOf` returning a bare grade
  would reproduce exactly the failure the effect-nats ladder has, where
  `grade.ts:4-5` claims a one-to-one carrier match with Lean and
  `notes/0003-graded-algebra-model.md:62-63` admits the mechanical bridge is
  unbuilt. The answer type makes the rung and the residual unavoidable at the
  call site.
- **A miss is a typed failure, not `undefined`.** "No grade recorded for this
  verb under this failure model" is the common case and must be distinguishable
  from "grade recorded as false".
- **Yes, it should be a `Layer`.** The registry data is a static generated
  module, so the service could be a plain constant. It should still be a `Layer`
  for two reasons: a test can substitute a smaller registry, which is what
  `Layer` is for; and a codegen tool that consults the registry acquires a
  requirement in its `Effect` type, so a program that generates graded code
  cannot be run without providing the registry it was graded against.

### 4.3 Branding a value with its grade

Two candidate mechanisms exist at the pin. `Brand.Branded<A, Key>` is
`Brand.ts:211` (`A & Brand<Key>`), and `Context.Key` is `Context.ts:64`.

The recommendation is **a phantom brand on the value, and a `Context.Key` on the
registry, never a `Context.Key` on the grade**.

- A brand is erased at runtime and costs nothing, and grade is a static property
  of a construction, so it belongs in the type.
  `Queue.Dequeue<A, E> & Brand<"noLoss:F-interrupt">` says what the codegen
  proved and travels through composition by intersection.
- A `Context.Key` for the grade would put it in the *requirements* channel, which
  is the wrong variance: requirements accumulate on the demand side, while a
  grade attenuates on the supply side. The effect-nats note reached the same
  conclusion from the other direction at
  `notes/0003-graded-algebra-model.md:20-23`, where a subeffecting `weaken` rule
  is omitted because "the TS side has no counterpart (R only accumulates)".
- Composition is the meet, and the meet is not expressible in TypeScript's type
  system over intersections without a conditional-type helper. So the brand is
  *asserted* by the generator at the point where Lean has the claim, and the
  generator emits, beside every branded constructor, the registry query that
  reproduces the brand at runtime. The brand is a convenience; the registry is
  the authority. Saying so in the generated file is the honesty clause, in the
  register of `Effect4/Arch/Accepts.lean:18-31`.

The typed declarations `Effect4/Target/TypeScript/Schema.lean:473-490` already
carry `type : Option String`, so emitting a branded type annotation needs no new
target syntax.

---

## 5. Ranked next steps, smallest first

Each step names the files it touches and the gate that proves it landed. Steps 1
to 3 are hours; 4 to 6 are days; 7 is a wave.

**1. `Effect4/Registry/Pin.lean`: the `Pin` record, and the first ten pins as
data.** Touches: `Effect4/Registry/Pin.lean` (new), `Effect4.lean` (one import),
`Effect4Test/Registry/PinContract.lean` (new), `Effect4Test.lean` (one import),
`lakefile.toml` (one `lean_lib` beside `Effect4TestArch` at `lakefile.toml:105-107`).
Gate: `#guard` receipts in the contract, running in the default build because
`lakefile.toml:8` makes `Effect4TestGreen` a target. Content: ten pins chosen
from the spans already cited in `Effect4/Deep/Witnesses.lean` doc comments, each
with its literal text, so `#guard pin.text.length = pin.offsetEnd - pin.offsetStart + 1`
and `#guard pin.spanSha256 = "..."` are decidable receipts. This converts ten of
the 683 prose citations into data. No script yet.

**2. `scripts/generate-registry-pins.sh` plus `scripts/check-registry-pins.sh`.**
Touches: two new scripts, `generated/registry-pins.tsv` (new),
`scripts/sweep.sh:64-77` (one row). Reuses
`scripts/generate-effect-runtime-census.sh:336-362` verbatim for the anchor and
span extraction, and `scripts/check-effect-runtime-census.sh:88-131` verbatim for
the stamp. Gate: the new sweep row, stamped, hitting on a second run. Proves that
a pin in Lean and a pin extracted from the pinned install are the same bytes.

**3. `scripts/check-stdlib-census.sh`.** Touches: one new script,
`scripts/sweep.sh:64-77` (one row). Closes the gap named in section 3.1: today
17 of the 21 file pins at `Effect4/StdLib/Rc112.lean:18-38` are checked by
nothing. The checker re-reads the install named by
`EFFECT4_EFFECT_NODE_MODULES` (the variable
`scripts/check-effect-runtime-census.sh:102` already uses), compares all 21
digests, and compares the entry count against `Effect4/StdLib/Rc112.lean:1911`.
Gate: the sweep row plus a planted-defect self-test in the shape of
`scripts/test-lowering-coverage-gate.sh`.

**4. `Effect4/Registry/Claim.lean` and `Effect4Test/Registry/Coherence.lean`.**
Touches: `Effect4/Registry/{Claim,Item,Registry}.lean` (new),
`Effect4Test/Registry/Coherence.lean` (new). Content: `Rung`, `Evidence`,
`ClaimKind`, `Claim`, `Claim.coherent`, `Item`, `Registry.ofItems`, and a
`#effect4_check_claims` command elaborator modelled on
`Effect4Test/Audit/RuntimeCoverage.lean:3917-3944` that resolves every
`Evidence.thm` in the environment and every `Evidence.pin` in the registry store.
Gate: `#guard registry.claims.all Claim.coherent` plus the command elaborator,
both in the default build. This is the step that makes "a claim cannot outrank
its evidence" a build failure rather than a convention.

**5. `Effect4/Registry/Grade.lean` and the first `FailureModel`.** Touches:
`Effect4/Registry/Grade.lean` (new), `Effect4Test/Registry/GradeContract.lean`
(new). Content: `Grade`, `Grade.meet`, `Grade.leq`, `FailureModel`,
`GradeAssignment`, and the theorems that `meet` is commutative, associative,
idempotent and has `⟨true, true⟩` as unit, with `leq` the induced order. Two
failure models: `F-interrupt` (boundary labels from
`Effect4/StdLib/Links.lean:49-52`, the frame primitives, and `:54-58`, the fiber
actions) and `F-none`. Gate: the algebra theorems, plus a `#guard` that every
`GradeAssignment` with a `true` bit names a `Claim` id held in the registry.

**6. `Effect4/Registry/Views.lean`: the registry as a fifth Schema document.**
Touches: `Effect4/Registry/Views.lean` (new),
`Effect4Test/Registry/ViewContract.lean` (new). Content: `registryDoc` in the
shape of `Effect4/Arch/Views.lean:54-59`, `registryJson`, and the app face by
`Effect4/Target/TypeScript/Schema.lean:526`. Gate: exactly the receipts at
`Effect4Test/Arch/ArchContract.lean:23-33` and `:65-71`, namely that every
projected payload is accepted by the document, that a payload with a missing
required property is refused, and that the document generates a module.

**7. `Usage` edges, and the first composite grade.** Touches:
`Effect4/Registry/Usage.lean` (new), a corpus of usage edges extracted from the
pinned install, and `Effect4Test/Registry/UsageContract.lean`. Content: the
`Stream.fromQueue → Channel.fromQueueArray → Queue.takeAll` edge as the worked
case (`Stream.ts:1132-1133`, `Channel.ts:1229-1231`, `Queue.ts:1297-1298`), the
composite grade as the meet along the edge, and the composite rung as the minimum
of the backing claims' rungs. Gate: `#guard` on the composite, plus a
`check-registry-usage.sh` sweep row that re-extracts the call sites from the
pinned install and fails on a drifted span. This is where the registry starts
answering the question the owner asked, namely what grade a construction carries
and why.

---

## 6. Explicitly not verified

- Whether `library/cas` consumes `formal/fips202`. No Lake dependency was found;
  `/Users/pooks/Dev/foldlab/library/cas/Cas/Codec/Sha256.lean:17-19` is a
  self-contained and unproved transcription, while
  `/Users/pooks/Dev/foldlab/docs/entity-store/KICKOFF.md:71` planned SHA3-512.
  The documented reason for the switch was not read
  (`library/effects/research/cas-scheme-0-hash-ruling.md` exists, unopened).
- The full foldlab commit history before 2026-08-30. Only the head-60 window was
  read, so the dates in the lineage table for G1 are the head window, not the
  first commit.
- Whether `github.com/mepuka/effect-nats-lean` exists. It is cited at
  `/Users/pooks/Dev/effect-nats/packages/agents/src/nats/grade.ts:3` and is not
  under `/Users/pooks/Dev/`. It is a different Lean lineage from
  `effect-nats-verified`, which publishes `EffectNatsSubstrate`.
- The `ens:`-prefixed paths and the `formal/effect_nats_substrate/` package cited
  throughout the jetstream-workflow-model program map. That repo is not present
  under `/Users/pooks/Dev/jetstream-workflow-model`.
- Whether the two kept refutations in `effect-nats-verified/scripts/` are run by
  any CI. `scripts/gate.sh:1-31` does not run them; no CI configuration was
  located in that repository.
- Whether `downstream/typescript/` would materialise on the next
  `.downstream/update.py -U`. It is registered at
  `/Users/pooks/Dev/downstream/README.md:17` and
  `/Users/pooks/Dev/downstream/repos.toml:13-17` but is absent from the tree and
  untracked.
- Whether the numbers `826` files and `9,456,751` bytes at
  `vendor/foldlab/README.md:20-24` reconcile byte-exactly. The 826 file count was
  confirmed; the byte column was not summed and no digest was recomputed.
- Whether the effect-nats working tree being 32 commits behind `origin/main` is
  intentional.
- The claim that no `Queue` model exists in this tree rests on `ls Effect4/Deep`
  and on a grep for grade vocabulary; a `Queue` carrier under another name
  elsewhere in `Effect4/` was not ruled out exhaustively.
- `README.md:8-9` of this repository says Effects is pinned at `v0.1.0`, while
  `lakefile.toml:84-87` pins the v0.8.0 commit `a4ee7a14...`. The README is stale;
  which is authoritative was not confirmed with the owner.

---

## 7. One-line summary of the design

A registry is a `Store Item` whose contents are addressed by SHA-256 of canonical
bytes and named by a path trie; a `Claim` carries its rung as data and cannot
outrank the evidence it lists, because `Claim.coherent` decides the order and a
command elaborator resolves every named theorem, pin and fixture at build time,
in the default target, incrementally, for free.
