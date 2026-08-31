# Effect Core v1 — organization, generation, and continuity plan

Status: **PRE-GRADE / PROPOSED**, 2026-08-31

Claim gate: none

This document answers the long-duration project question: where each fact
lives, which parts of AGENTS.md are authored, which facts are generated, how a
fresh session resumes, and which gates detect loss of context before it turns
into semantic drift.

## 1. Organizing law

Effect Core v1 uses five non-overlapping authorities:

1. **Authored law and intent** — root/domain AGENTS files, ratified specs, and
   the decision record. These carry operator judgment and routing.
2. **Semantic declarations** — Lean carriers, judgments, interpreters, and
   theorems. These own meaning.
3. **Portable identity and bytes** — the versioned, language-neutral effect
   protocol manifest. It owns stable operation and type IDs, canonical wire
   schemas and encodings, and profile membership. It owns no semantics or
   proof status.
4. **Source evidence** — pinned Effect/TypeScript trees and generated census
   rows. These own what the subject source contains.
5. **Derived orientation** — generated manifests, annotation tables,
   obligation ledgers, status projections, and byte gates. These make the
   first four discoverable and detect disagreement; they own no meaning.

No single Markdown file is asked to be all five. In particular, AGENTS.md is
not a backup semantic specification and generated TypeScript is not a program's
authoritative home.

## 2. AGENTS.md organization

### 2.1 Files and responsibility

| AGENTS file | Stable responsibility | Effect Core v1 addition |
| --- | --- | --- |
| root `AGENTS.md` | estate conduct, disclosure, artifact/claim discipline, skill routing | One pointer to the staged packet after indexing; no packet details copied in. |
| `library/cas/AGENTS.md` | store-language law, proof discipline, existing carriers and handlers | Pointer to the packet as the pre-grade successor study; reminder that `Sig`/`Prog`/`Handler`/`PProg` remain existing bases. |
| `library/effects/AGENTS.md` | generated TS host, runtime/package/LSP lane rules | Pointer to the public-surface/LSP checklist and the TS7 `@effect/tsgo` coverage gate. |
| `library/effect-protocol/AGENTS.md` | portable identity/byte/profile ownership and generation prohibitions | Created in B1 as an authored router; no canonical manifest exists yet. |
| `.staging/effect-core-v1/AGENTS.md` | temporary packet read order, ownership, role split, resume and handoff protocol | Created now; governs only staged design and scratch work. |
| `formal/effect-core-v1/AGENTS.md` | Lean scaffold's declaration freeze, proof loop, axiom and claim gates | Created in B1; every module is empty and no semantic declaration is promoted. |
| `experiments/effect-core-surface/AGENTS.md` | hoover inputs/outputs, independent instruments, mutants, LSP file coverage | Created in B1 with empty v4-detectable modules and exact-file-set tooling only. |

Nearest-file routing narrows the task; it never repeals a parent rule. A child
file may add a stricter gate but cannot redefine an existing term or weaken a
claim boundary.

### 2.2 What is authored and what is generated

AGENTS.md files are always authored; no generator may create or rewrite their
normative prose. The repository's
`BOOTSTRAP.md` distinction is retained:

- **Authored:** operator voice, conduct, read order, role separation,
  two-minute proof rule, lane-specific prohibitions, and escalation rules.
- **Generated facts:** links, spec coverage, source/tool pins, project/task
  names, current slice, declaration digests, obligations, and gate status.

Markdown has no trustworthy include mechanism, so generated facts live in
companion manifests and generated human projections called **sidecars**.
AGENTS.md links to sidecars but does not copy their volatile rows. A
bidirectional gate checks the relationship. This avoids a generator rewriting
operator prose and avoids hand-copying volatile facts into every router. A
sidecar may report the current slice, digests, pins, coverage, obligations, and
gate results; it may not add an instruction or weaken an authored rule.

### 2.3 Bidirectional AGENTS/spec gate

The future orientation gate computes:

```text
SpecRows        = Category 1 or 2 rows in docs/SPECS.md
AgentPointers   = normalized spec links in governed AGENTS.md files
RequiredOwner   = domain -> nearest owning AGENTS.md

missingPointer  = required SpecRows without their owning AgentPointer
unrowedPointer  = AgentPointers to build-bearing Markdown absent from SPECS
brokenPointer   = AgentPointers whose target does not resolve
wrongOwner      = pointers present only in a non-owning domain file
```

All four sets must be empty or contain an explicit, expiring accepted row.
The gate fails in both directions: adding a spec without routing and adding
authority to AGENTS without a spec row are equally red.

## 3. Packet and future directory layout

### 3.1 Current staged layout

```text
.staging/effect-core-v1/
  AGENTS.md                 lane router
  README.md                 generated-status-aware human entry point
  PLAN.md                   scope and slice programme
  EXISTING-TYPES.md         bootstrap annotation ledger
  EXHIBITS-REVIEW.md        applicability of scratch proofs/counterexamples
  COUNTEREXAMPLES.md        central counterexample and falsifier register
  TYPE-CLOSURE.md           per-type proof graph and cutover predicate
  ALGEBRA.md                proposed Semantic Model
  CLASSIFICATION.md         denotational abstract domains
  CONTRACT-PACKET.md        breaker contract and falsifiers
  PROOF-DAG.md              declaration/theorem dependencies
  REIFICATION-CHECKLIST.md  pinned public-surface closure contract
  ORGANIZATION.md           this continuity plan
  WORKSHOP-RESULTS.md       exact disposable-probe receipts
  workshop/                 ignored local probes
```

### 3.2 Current B1 scaffold and reserved generated paths

```text
formal/effect-core-v1/
  .gitignore / AGENTS.md
  README.md / lakefile.toml / lake-manifest.json / lean-toolchain
  EffectCore.lean              imports every empty category module
  EffectCore/
    Foundation/               values, rows, alphabet metadata, pure boundary
    Surface/                  source rows, TypeScript type graph, dispositions
    Syntax/ Admission/ Semantics/
    Handler/ Layer/
    Concurrency/ Stateful/ Channel/
    Foreign/ Classification/
    Bridge/ Protocol/ Target/ Assurance/
  contracts/attacks/
  meta/schemas/ meta/in/ tools/
  # No Generated/ or meta/out/ path exists in B1.

experiments/effect-core-surface/
  AGENTS.md / README.md
  package.json / bun.lock
  tsconfig.json
  src/                       empty v4-detectable module stubs
  fixtures/
    positive/ negative/ mutants/
  # No generated/ path exists in B1.

library/effect-protocol/
  AGENTS.md                   authored portable-seam rules
  README.md
  v1/
    README.md
    schema/ profiles/ vectors/
  # protocol.json and canonical vectors are future generated outputs, absent in B1.

future library/effects/src/generated/effect-protocol/
                               generated Effect TS profile bindings
future library/effects/src/effect-protocol/
                               authored Effect adapter
```

Every current Lean and TypeScript source file in these trees is a stub. The
formal tree will consume generated first-order rows; it will not parse the
Effect package during proof checking. The experiment tree will read the pinned
package and produce evidence; it will not define semantic laws.

### 3.3 Language-neutral effect protocol seam

`library/effect-protocol/` is the smallest shared interface between the Lean
model and every host language. Its versioned manifest owns only:

- stable operation, type, and profile IDs;
- canonical request, response, and portable outcome schemas;
- canonical byte encodings and their shared vectors; and
- membership of operations and types in each named profile.

Lean remains the sole owner of admission, relational meaning, reference
interpretation, and proofs. Generated Lean rows admit a selected manifest
profile into existing `Sig.Op`/`OpDesc` declarations and relate it to the
reference semantics. Generated TypeScript rows provide codecs and identifiers;
an authored Effect adapter realizes one selected profile. Effect TypeScript is
the first consumer, not the protocol authority and not the whole effectful
interface. A later host consumes the same manifest and supplies its own
adapter.

The neutral manifest must not contain theorem status, source-census facts,
Effect-specific AST declarations, concrete handler implementations, host
paths, LSP results, or runtime-conformance claims. Those are generated
sidecars keyed by the protocol digest. There is one neutral manifest family,
not a CAS manifest, an Effect manifest, and a future-host manifest that repeat
the same IDs or bytes.

The first authorized implementation slice is **file stubs only**: create the
agreed directory and file names with ownership headers and no protocol rows,
schema universe, generated declarations, adapter behavior, or semantic claim.
Content begins only after the manifest shape and its admission consumer are
grilled and frozen.

## 4. Generated continuity manifests

### 4.1 `PACKET-MANIFEST.json`

One generated row per packet file and external input:

```text
PacketManifest = {
  schemaVersion,
  packetVersion,
  status,
  currentSlice,
  files[{ path, role, authoredOrGenerated, sha256 }],
  sourcePins[{ id, version, commit, tree, integrity, status }],
  declarationSnapshotDigest,
  publicSurfaceDigest?,
  typeAnnotationDigest?,
  obligationDigest?,
  generatedAtByToolVersion
}
```

It detects a resumed session reading a different packet from the one its
slice was dispatched against. A changed digest does not auto-reject design
work; it blocks implementation until the change is reviewed and the slice is
re-dispatched.

### 4.2 `TYPE-ANNOTATIONS.json`

Generated from:

- the accepted `ExistingTypeAnnotation` rows;
- Lean declaration names and source spans/digests;
- the public Effect surface's canonical symbol/profile IDs; and
- proposed public signature IDs in the frozen snapshot.

Zero counters:

```text
unannotatedRelevantDeclarations = 0
duplicateAnnotationIds = 0
unknownDeclarationTargets = 0
multipleMeaningOwners = 0
multipleCanonicalIdentityOwners = 0
proposedNewWithoutRationale = 0
bridgeWithoutObligations = 0
```

The generated Lean table is decidable data. It does not use reflection to
create semantic declarations and does not attach mutable status to source
docstrings.

### 4.3 `OBLIGATIONS.json`

Every contract, theorem, falsifier, harness, bridge, and open ruling becomes a
row:

```text
ObligationRow = {
  id,
  kind: contract | theorem | falsifier | harness | bridge | ruling,
  ownerFile,
  slice,
  prerequisites[],
  publicDeclarations[],
  observationProfile?,
  claimGate?,
  status: proposed | frozen | failing | discharged | blocked | superseded,
  evidencePaths[],
  axiomReport?,
  finiteBound?,
  lastCheckedDigest?
}
```

Status may change only through a named check or a recorded operator ruling.
“Worked in a previous chat” is not a status transition.

### 4.4 `ORIENTATION.json`

Generated from the spec ledger, AGENTS pointers, task graph, toolchain pins,
and Lean project declarations. It answers without prose search:

- Which AGENTS file owns this path?
- Which spec and decision authorize the current slice?
- Which exact commands generate and check it?
- Which declarations and evidence are inputs?
- Which outputs are generated?
- Is the task in root `check` and `check:ci`?

It follows the already proposed environment-ledger shape. Lean owns the
descriptions; mise owns execution; the doctor for a broken Lean toolchain is
not a Lean executable.

### 4.5 `STATUS.md`

A generated human projection of the four manifests. It contains no free-form
progress estimate. It reports exact counts, digests, current slice,
prerequisites, red controls, theorem/axiom status, and highest satisfied gate.
This becomes the first long-duration resume document after `README.md`.

## 5. Generation direction and ownership

```text
authored contract + decisions       neutral protocol manifest
          |                                  |
          v                                  v
Lean semantic declarations          stable IDs, bytes, profiles
          |                                  |
          +----------------+-----------------+
                           v
                 generated admission rows
                           |
          +----------------+-----------------+
          |                                  |
          v                                  v
pinned source census                 proof/axiom receipts
          |                                  |
          v                                  v
PublicSurface JSON           annotations + obligations + orientation
                                             |
                               +-------------+-------------+
                               v                           v
                       generated host bindings    generated status sidecars
```

The neutral manifest is checked against Lean admission; it does not generate
meaning. No arrow points from generated TypeScript runtime observations back
into the Semantic Model or from a host adapter back into protocol identity. A
counterexample reopens a contract or proof, but the runtime does not silently
rewrite meaning.

## 6. Worktree and integration protocol

Every proof-bearing slice starts from a clean, recorded packet baseline and
uses four distinct worktree roles:

1. **Packet baseline:** an immutable clean commit containing the reviewed
   packet and declaration digest. No slice role edits this worktree.
2. **Integration:** the coordinator-owned worktree. It is the only place where
   shared packet documents, generated sidecars, and accepted slice results are
   reconciled. Unknown or unrelated changes stop integration.
3. **Per-slice breaker and builder:** two worktrees named for one slice and
   based on recorded integration commits. The breaker first lands the frozen
   statement and red controls. The builder starts from that accepted breaker
   commit and may not weaken or rewrite the breaker battery.
4. **Per-slice reviewer:** a fresh worktree at the proposed integration commit.
   The reviewer reruns the named evidence and reports findings; it does not
   repair the submission it reviews.

The coordinator records the baseline commit, packet digest, integration base,
role, file fence, and expected red/green commands before dispatch. Each role
starts and ends with `git status --short` attributable to its own file fence.
Agents never share an authority file concurrently. Accepted work is integrated
in dependency order, conflicts are resolved against the packet authority, and
the reviewer reruns after the exact integrated commit is known. A clean role
worktree is not evidence that integration is clean; both states are recorded.

## 7. Broad sweep before proof depth

Implementation proceeds in these phases:

1. **B0 — seal the baseline:** record the reviewed packet, decisions,
   declaration snapshot, and counterexample register.
2. **B1 — file stubs only:** establish the approved directory and file names,
   ownership headers, imports, and empty gate entry points. Do not add a type,
   operation row, protocol byte, adapter behavior, or proof claim.
3. **B2 — broad ownership sweep:** traverse every required type, operation
   family, profile, public-surface family, theorem edge, and red-control class.
   Record owners, reuse/bridge decisions, and missing rows before proving one
   family deeply.
4. **B3 — broad executable skeleton:** make every planned generator, admission
   boundary, checker, proof module, adapter, and sidecar path reachable with
   explicit pending rows and planted controls. A placeholder cannot report
   closure.
5. **B4 — per-type vertical closure:** deepen one dependency-ready type row at
   a time through breaker, builder, and independent reviewer worktrees. Cutover
   is permitted only when that row's constructor, checker, meaning,
   classification, lowering, byte, and red-control edges close.
6. **B5 — profile integration:** join individually closed rows into a named
   neutral-protocol profile, then run cross-language vectors and profile-level
   closure. Effect TS may cut over as one profile without implying closure for
   other hosts or for the whole effectful interface.

The broad phases prevent a locally elegant proof from fixing the wrong
boundary or duplicating an existing carrier. They do not discharge any deep
proof edge; only B4 and B5 can close type or profile cutover rows.

## 8. Slice state machine

Each slice follows:

```text
proposed -> grilled -> signatureFrozen -> breakerRed
         -> implemented -> locallyGreen -> independentlyReviewed
         -> promoted -> claimStamped
```

Rules:

- `grilled` is an operator decision, never inferred from a review.
- `signatureFrozen` stores the declaration digest.
- `breakerRed` requires the intended falsifiers to fail before implementation.
- `locallyGreen` records exact commands and is not independent review.
- `promoted` is the move/commit into the graded home.
- `claimStamped` is per theorem/bridge and can lag promotion.
- A changed public declaration returns the slice to `proposed`; a proof script
  repair that preserves the snapshot does not.

## 9. Long-duration resume algorithm

A new agent or human performs this bounded recovery:

1. Read root and nearest AGENTS files.
2. Read `PACKET-MANIFEST.json` and verify its own digest/signature fields.
3. Read `STATUS.md`; identify one current slice and its blocking prerequisites.
4. Resolve all source/tool pins before accepting any prior external receipt.
5. Compare the frozen declaration snapshot with current public names.
6. Read only the current slice's contract rows, type annotations, theorem
   dependencies, and breaker controls.
7. Run the slice's cheap status command before editing.
8. Attribute every existing working-tree change; preserve unknown work.
9. Make one bounded change, regenerate derived manifests, and run the narrow
   gate plus its red controls.
10. Record exact results; never update progress prose independently.

This algorithm intentionally does not require old chat transcripts. A chat may
explain intent, but repository state and recorded rulings decide what work is
authorized and what has been established.

## 10. Drift and context-loss gates

Before the generated gates exist, incoming agent work is reconciled by the
authored protocol in `AGENTS.md`: capture its classified revision, assign one
owner per finding, compare it with operator-set rulings, rerun its evidence,
register contradictions centrally, and only then update status projections.
The eventual manifest records each intake as data:

```text
reportId, authorRole, classifiedPacketDigest, evidenceCommands[],
ownerRows[], counterexampleIds[], disposition,
independentReceiptIds[], unresolvedConflicts[]
```

`disposition` is one of `adopted`, `narrowed`, `historical`, `superseded`, or
`rejected-with-witness`. It is not a quality score; it says how the packet used
the report. A report cannot mark its own recommendation adopted.

The future `check:effect-core-v1` must fail on:

1. a packet file changed without a manifest refresh;
2. a current-slice implementation built against a different declaration
   digest;
3. a relevant existing type with no annotation;
4. a proposed type duplicating an existing meaning or byte owner;
5. a Category 1/2 spec without its owning AGENTS pointer;
6. an AGENTS authority pointer absent from the spec ledger;
7. a generated fact copied by hand into an AGENTS file and drifting from its
   source;
8. a theorem marked discharged without a kernel build and axiom receipt;
9. a finite probe reported without its bound;
10. a public Effect row missing a profile/disposition/family-role/transfer;
11. a public closure admitted without a registered first-order implementation
    ID and serializable payload;
12. an LSP run whose checked file set differs from the expected project set;
13. a generated import outside the independent exports-map census;
14. a TypeScript/Effect/package/source pin mismatch;
15. a quick fix that is non-idempotent or changes the structural Core relation;
16. a stock Effect target claiming to preserve richer cause topology after the
    explicit rc.112 quotient; or
17. a CAS value receiving a second canonical program spelling;
18. a required type whose proof-closure row has any open edge;
19. fuel, an external frontier, or a scheduler decision classified as a
    refusal/cause;
20. a contradiction claim absent from `COUNTEREXAMPLES.md`, a registered
    counterexample with no attacked quantifier or reproducible evidence command,
    or a type/theorem row that ignores an active counterexample; or
21. a negative fixture or mutant mislabeled as a semantic counterexample; or
22. an incoming report used without a classified packet digest, one owning row,
    an independently reproduced receipt when it claims verification, and a
    recorded disposition for every conflict with current rulings.

Every gate has a planted positive control and negative mutation. A gate that
has never killed its named mutation is not live evidence.

## 11. Preventing annotation rot

Annotations are keyed by declaration identity, not line number. A source move
updates provenance; a signature/body change updates its digest and opens a
review. Aliases point to one canonical declaration. Removed declarations stay
as tombstoned rows with the last pin and replacement, so old obligations and
receipts remain interpretable.

The source annotation and proof-status planes remain separate:

- `existsAtPin` says a declaration was found;
- `classifiedStructurally` says its census row is total;
- `mappedToCore` says an admission profile has a constructive mapping;
- `kernelChecked` says a named Semantic Model theorem compiled;
- `runtimeCompared` says bounded observations were compared; and
- `bridgeEstablished` says the stated claim gate is satisfied.

No later state is inferred from an earlier one.

## 12. Promotion plan

This organizational layer is useful immediately as staged routing, but its
generated machinery is implemented successively:

1. **O0 — packet routing:** land this AGENTS file, type ledger, central
   counterexample register, organization plan, README, spec rows, and domain
   pointers.
2. **O1 — manifest:** generate packet/source/declaration digests and a status
   projection; add stale-manifest controls.
3. **O2 — orientation:** implement bidirectional spec/AGENTS/link coverage by
   extending the environment-ledger spine after its ruling is released.
4. **O3 — annotations:** emit Lean/JSON/human annotation views and the zero
   counters once the annotation schema is grilled.
5. **O4 — obligations:** extract EC1 IDs and join them to public declarations,
   counterexamples, checks, evidence, and axiom reports; generate the
   counterexample zero counters without making the projection authoritative.
6. **O5 — surface integration:** join recursive Effect census rows and LSP
   coverage to annotations without granting either semantic authority.
7. **O6 — activated lane:** replace the current empty stubs only through their
   first accepted consumers, then wire the admitted generators and red controls
   into root check/CI.

O0 and the B1 file scaffold are present. O1–O6 remain proposed implementation
slices and must not be reported as present until their named files and red
controls exist.
