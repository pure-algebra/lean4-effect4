# The CAS trait — the plan (closing the grilling)

Status: 2026-09-04 ~22:10, from the eight rulings in `2026-09-04-cas-trait-facts.md` §5. This
is the plan a seat lands from; the facts note stays the record of why. It supersedes §4 of
`2026-09-04-store-backend-plan.md` (the Lean carriers) and leaves that plan's host stages
(§5–§6: the Bun loader, the daemon's store domain, the SQL DDL) as the next lane.

## 1. What lands, in one paragraph

One trait, `Canonical α`, whose instance is an isomorphism onto the value tree `Val` plus its
shape; one byte codec over `Val`, proved exact once; one address type `Ref α`; one node
layout `version ∷ kind ∷ spec ∷ payload`; one store with admission, closure, roots, words,
the layered read, the outbox and verify; traits as typed annotation nodes with a proved
resolution. Every one of today's thirty-five hand instances is replaced by a derived one
(the `Eff` family by hand if the generator refuses it), every digest-as-string and every
`Digest` field that names a node becomes a `Ref`, the nine address helpers become the one
`address`, the three hex codecs become one, the JSON tag alphabet and `LawfulCanonical` and
the id/trie store retire. The Wire's bytes are byte-identical before and after, guarded by
the existing goldens.

## 2. The substrate (`src/Effect4/Store`), owner: the coordinator seat

| module | carries |
| --- | --- |
| `Val.lean` (new) | `Bytes`, `be64`, `natBytes`, `framed`, `Tag` 1–11 (`ctor = 10`, `ref = 11`); `inductive Val`; `Val.encode`; `Val.decode` (exact, fuel = length, the Wire's strict UTF-8 and leading-zero rules); `decode_encode`, `decode_exact`, `encode_injective` |
| `Shape.lean` (new) | `Shape`, `ShapeDoc`, `Shape.accepts`, `ShapeDoc.document : Document` (the Q5 table, imports `Effect4.Schema.Authoring`), `ShapeDoc.print : Val → Json` (the printer), the `ref = kind` and `identifier` annotation keys |
| `Canonical.lean` (rewritten) | `class Canonical α := shape, toVal, ofVal, ofVal_toVal, ofVal_exact, fits`; derived `encode`, `decode`, `decode_encode`, `decode_exact`, `encode_injective`, `digest` (the payload digest, for foreign and pin uses); hand instances for `Unit`, `Bool`, `Nat`, `Int`, `UInt8`, `UInt64`, `String`, `Bytes`, `List`, `Option`, `Prod` |
| `Digest.lean` (extended) | `Digest`, `sha256`, `Digest.hex`, `Digest.ofHex?`, `hexOfBytes`/`bytesOfHex` (the one hex codec), `Canonical Digest` (moved here from `Char/Conformance/Consume.lean`) |
| `Node.lean` (new) | `Kind` (§3) with `byte`/`ofByte` and the round trip; `Ref α`, `AnyRef`; `class Content α extends Canonical α := kind`; `spec`, `nodeBytes`, `address`; `Node` (version, kind, spec, payload : Val) with `Node.encode`/`decode` exact; `refsOf` (the scan); `address_eq_or_collision` (level 0), `address_inj` (level 1, named premise), the level-2 example |
| `Store.lean` (rewritten) | `Root`, `RootKind`; `Store {nodes, roots}`; `Admission` (`dangling`, `wrongKind`); `Outcome` (`fresh`, `duplicate`, `conflict`); `put`, `get`, `putRoot`, `root?`; `Closed`, `put_fresh_closed`, `get_put`, `put_duplicate` |
| `Word.lean` (new) | `Binding`, `Word`, `wf`, `wf_closed`, `apply`, `apply_idempotent`, `closure`, `closure_closed`, `Layered` + `layered_get`, `LocalFirst` + `sync_sub`, `verify` + `verify_sound` |
| `Traits.lean` (new) | `Annotation τ {subject, value, prev}`, `Content (Annotation τ)` at kind 6, `traitsOf`, `effective`, `nodeBytes_trait_free`, `effective_deterministic`, supersession as a forest |
| `Pin.lean` (kept) | the carrier and the two pin theorems; its instance derived; `Pin.json` retired (the printer is derived); `contentPath` becomes a tree name |
| `Derived/*.lean` (generated) | one file per source module: `Json`, `Schema` (Representation, Check, Document, the annotation carriers), `Program` (the `Eff` family, or hand in `Wire.lean`), `StdLib`, `Surface`, `Char` |
| `JsonCanonical.lean` | **deleted**; `binary64OfNat`, `highestBit`, `Json.ofNat` move to `Data/Json.lean` |
| `Trie.lean` | **deleted** with its battery section; a name space is a `tree` node |

`Program/Wire.lean` keeps its name and its corpus: the encoders become `toVal`, the decoder
becomes `ofVal`, the byte layer moves to `Val.lean`, and the owed round-trip and exactness
theorems are the instance's fields. `Api.bytesOf`/`ofBytes` keep their signatures.

## 3. The kind table (bytes are identity; fixed now, appended later, never renumbered)

| byte | kind | Lean consumer in this landing |
| --- | --- | --- |
| 1 | `source` | `Source` (today's `FilePin`), `Pin`, `Implementation` |
| 2 | `export` | `Entry` (gains `source : Ref Source`) |
| 3 | `type` | reserved for the extractor lane |
| 4 | `schema` | `Document`: every spec; the meta-schema is the zero-spec genesis |
| 5 | `program` | `Eff NativeOp` |
| 6 | `annotation` | `Annotation τ` (traits), `Receipt`, `Claim`, `Evidence`, `Target`, `Characterized` |
| 7 | `entry` | reserved for the journal |
| 8, 9 | `query`, `result` | reserved |
| 10, 12 | `chunk`, `manifest` | reserved for the blob kinds |
| 11 | `tree` | `Tree` (name → `AnyRef` pairs, the name space) |
| 13 | `component` | the Char room's `Manifest` (named for `Target.model`) |
| 14 | `vector` | `VectorSet`, `Vector`, `Fact` (named for `Receipt.vector`) |
| 15 | `fiber` | reserved |

The Surface carriers (`Entity`, `Domain`, `Api`, `McpServer`, `Deployment`, `Site`) get a
derived `Canonical` and no kind: nothing references them as nodes yet; their documents are
`schema` nodes. A kind enters only with a consumer that references it (Q5 of the store plan).

## 4. The generator (lane G, one Opus seat), `tools/Effect4Gen/`

Reads the environment through `OCaml5.Tools.Describe`'s descriptions (structures, inductives,
mutual blocks, parameters), driven by a manifest of type names, and emits per type:
`T.shapeDoc`, `T.toVal`, `T.ofVal` (structural on `Val`, `List.attach` for the nested
argument list), the three theorems by fixed tactic scripts (`cases`/`simp` with the field
instances' laws; `fits` by `decide` on the shape), and `instance : Canonical T`. Mutual blocks
emit one `ShapeDoc` with `defs`, mutual definitions and mutual theorems. `Ref β` fields emit
`Val.ref (kind β) r.digest`; `Digest` fields emit `Val.bytes` with the length check.

Acceptance, checked in the spike before anything lands: `Entry` (structure), `ExportKind`
(all-nullary sum), `Evidence` (sum with arguments), `Json` (nested recursion), `Eff`
(mutual), `Document` (mutual, nested lists of structures), every output at `[propext]` or
no axioms. The fallback if `Eff` or `Document` resists: a hand instance for that type only,
in the source module, written to the same shape.

The projection guard `Test/Store/DerivedCheck.lean` re-derives the descriptions at build
time and refuses a generated file whose shape disagrees with the inductive; the script
`scripts/generate-derived.ps1` regenerates and `git diff --exit-code` is the receipt.

## 5. The consumers, by lane (disjoint files; two lanes at a time; `lake env lean -M 3072` on their own files, never `lake build`)

| lane | files | what changes |
| --- | --- | --- |
| C: census and views (Opus) | `Evidence/StdLib/{Entry,Rc112}.lean`, `scripts/generate-stdlib-census.ps1`, `Evidence/Views.lean`, `Evidence/SurfaceViews.lean`, `Test/Evidence/ArchContract.lean` | `FilePin` → `Source` with `sha256 : Digest`; `Entry` gains `source : Ref Source`, computed at elaboration from the module's source node (no address literals in the census file); `StdLib.store` → one `tree` node and the root `stdlib/rc112`; the two `viewStore` folds → `Store.tree`; `storeDoc`/`storeJson` lose the id column; the `rc112.find (digestOf …)` guard becomes `get (address …)` |
| U: surface (Opus) | `Surface/{Entity,Api,Agent,Deploy,Site}.lean`, `Surface/Observability.lean`, `Surface/Annotate.lean` | the six hand instances deleted (derived instead); the two hex functions replaced by the store's; `SurfaceMark`'s digest unchanged in type, its JSON through `Digest.hex` |
| X: Char room A (Opus) | `Evidence/Char/{Manifest,Evidence}.lean`, `Evidence/Char/Conformance/{Consume,Surface}.lean` | `Manifest` at kind `component`, its `json` retired; `Evidence.fixture (vector : Ref Vector) (receipt : Ref Receipt)`, `Evidence.pin (span : Ref Pin) (guard)`, `Evidence.thm … (statement : Digest)`, `Evidence.decided … (statement : Digest)`; `Claim.evidence : List (Ref Evidence)`; `Target.model : Ref Manifest`, `Target.implementation : Ref Implementation`; `Receipt.vector : Ref Vector`, `Receipt.pin : Ref Implementation`; `Characterized.{target, vectors, receipts}` typed; `Implementation.addr`/`Target.addr`/`Receipt.addr`/`address` → `address`; `asFixtureEvidence` answers refs; `Canonical Digest` and the `Failure` instance leave `Consume.lean` |
| Y: Char room B (Opus) | `Evidence/Char/Conformance/{Vector,VectorSet,GSet,Cell}.lean`, `Evidence/Char/Queue/*.lean` where they name addresses, `Test/Evidence/Char/**` | the seven tuple instances deleted (derived; `GSet α` and `Fact L C` compose their parameters' shapes); `Vector.addr` retired (a vector's node address is its own; the fact's address is `address v.fact`); `VectorSet.address` → `address`; `Label`'s hand constructor index → derived; the batteries re-pinned |
| B: batteries and docs (Opus, last) | `Test/Store/{StoreContract,NodeContract,WordContract,TraitContract}.lean`, `Test/Audit/AxiomGate.lean`, `Test/All.lean`, `Test/Counterexamples/REGISTER.md`, `docs/ARCHITECTURE.md` | §7 |
| S: the substrate and the Wire (coordinator) | §2, `Program/Wire.lean`, `Data/Json.lean`, `src/Effect4.lean`, `Api.lean` header prose, `lakefile.toml` (the `Effect4Gen` library) | §2 |

Untouched and verified untouched: `ocaml/**`, `src/OCaml5/**` (the goldens under
`ocaml/goldens/eff` are the byte-identity receipt), `harness/**`, `Codegen/**` (the
emitters keep their `json` functions: those are artefacts, not the canonical printer),
`Machine/**`, `Program/{Eff,Typing,Native,Compile,Provision,Config}.lean`.

## 6. Retirements

`JsonTag` and `jsonBytes`; `LawfulCanonical` and its four instances; `Store α`'s ids,
`putAt`, `name`, `resolve`, `idOf`, `under`, `paths` and the `Trie`; `Representation.toJson?`
and `Document.toJson?` as identity (they stay as printers if a consumer reads them; the
default printer is derived); the nine address helpers; the six hex-string digest fields; the
two hex copies; the three store-building folds; `Pin.json`, `Manifest.json`, `Evidence.json`,
`Claim.json` as identity.

## 7. Batteries, receipts, register rows, docs

- `StoreContract`: the tag bytes of every `Val` constructor; the primitives' bytes as today;
  `Val.decode` refusals (a byte appended, a byte dropped, a leading-zero digit, a non-shortest
  UTF-8 sequence, a wrong tag); the §6 numbers of the facts note (`8fab16…61fa` for the
  entry's payload, `fa5f40…62a3` for `p42`); `#print axioms` of the codec at none.
- `NodeContract`: `Kind` round trip; `Ref` refusals (wrong kind byte, wrong length); the entry
  node's bytes and address `1437a1…705b` under its real spec (the number moves once the spec is
  the derived document; the guard is regenerated then); the kind-6 twin; the genesis node;
  `#check` of the lattice; the degenerate example.
- `WordContract`: the three put outcomes on the entry; `dangling` and `wrongKind` on real
  addresses; a word that is `wf` projects to a closed store; `apply` twice equals once;
  `closure` of a root; the layered read; an outbox synced and re-synced; `verify` passing,
  then refusing after one byte is flipped; a root move with a stale version refused.
- `TraitContract`: three traits on the census fragment; `nodeBytes` of the subject unchanged;
  `effective` at node, spec and kind row; supersession through `prev`; an unknown key is a
  dangling spec.
- `DerivedCheck`: the projection guard, green.
- Register rows `E4-CAS-CE-001..008`, SEEDED: one payload at two kinds is two addresses; a
  wrong-kind `Ref` refuses at decode; a trait leaves every address unchanged; a duplicate put
  leaves the store unchanged; `apply` is idempotent; a degenerate store exhibits `conflict`,
  so reflection is never unconditional; a schema node whose spec is not the meta-schema
  refuses, the genesis excepted; `option` renders one way everywhere.
- `docs/ARCHITECTURE.md`: the store rows rewritten; `store-backend-plan.md` §4 gets a pointer
  here.

## 8. Order: a spike, then one landing

1. **Spike** (`workshop/Cas/`, untracked; a temporary `Cas` library hunk in the lakefile by
   the coordinator, as `Provision` was): the substrate of §2 in namespace `Effect4.Store`,
   importing nothing from the old store; the generator (lane G) against it; the acceptance set
   of §4; a probe reproducing the facts note's §6; the Eff goldens byte-identical. Gate: `lake
   build Cas` green at the ceiling. Nothing under `src/` changes during the spike.
2. **Landing**: the substrate rewritten in place; the generator run; lanes C and U, then X and
   Y, then B, on disjoint files, each reporting a targeted `lake env lean -M 3072` on its own
   files; then the one build, `lake build Effect4 Test`, from the coordinator with nothing else
   running (close the VS Code Lean server first: its worker holds 600 MB). The tree cannot be
   green between the class change and the last consumer, so this is **one commit**, by
   pathspec, in the shape of `f182d2b`; the spike's `Cas` hunk leaves the lakefile in the same
   commit and the `Effect4Gen` hunk enters it.
3. **After**: the coordination row updated; the Mac told what moved; the host lanes of the
   store plan (§5–§6 there) start from `Word.apply` and the node bytes, with `tools/CasWire`
   emitting `ocaml/goldens/cas/` for the daemon's differential.

## 9. Risks, each with its answer

| risk | answer |
| --- | --- |
| the generator's proofs on `Eff` and `Document` (mutual, nested) do not close mechanically | the acceptance set is checked in the spike before any consumer moves; the fallback is a hand instance for that type only, written to the same shape; `Json` is small enough by hand |
| `Shape.document` needs `Schema.Authoring` from inside `Store` | no module under `Effect4.Schema` imports the store today (grep 2026-09-04 22:05); if one appears, `Shape.document` moves to `Store/Spec.lean` and `Node.lean` imports it |
| one full rebuild: memory and time | one build, `-M6144` per library as the lakefile sets, nothing else running, the language server closed; the two crashes of 2026-09-04 were one process at 54 GB with a build beside it |
| the Char room's TypeScript driver reads receipt and fixture JSON | the printer writes the same keys (field names, `_tag`) and digests as lowercase hex, so the driver's shape is unchanged; the harness lane confirms after landing |
| `Rc112.lean` grows by 1,835 references | references are computed at elaboration from the module's source node; the census file keeps names only |
| a later kind or constructor changes an address | kind bytes and constructor indices are declaration order and appended, never reordered; a change to the codec or to a Q5 rule is version byte 1 and an announced re-address |
| the Wire's bytes drift | `Tag` numbers unchanged (`ctor` stays 10, `ref` is new at 11); the corpus hex under `ocaml/goldens/eff` is a `#guard` |
| quota | the spike is the long pole and runs on one seat; the mechanical lanes are Opus, two at a time |

## 10. Refused, or left to a later lane

A `deriving Canonical` handler (after the generator has run once and its scripts are known);
the SQL loader, the DDL and the daemon's store domain (the store plan's §5–§6, next); the
`type` kind and the extractor; the query language; Turso; the meta-schema's self-description
beyond its `accepts` theorem; any edit under `ocaml/`; renaming `Canonical`; the Mac's copy.

## 11a. Progress (appended as lanes report)

- Clock note: the lanes' self-reported times run two to three hours fast; the times below are
  file times.
- **S1 done, 2026-09-04 23:25** (`workshop/Cas/REPORT-S1.md`): the codec layer green under
  `lake build Cas` (47 jobs), 251 receipts none above the ceiling, byte identity with the Wire
  on all eight corpus programs; the stretch landed too, so the whole `Eff` family already has
  hand instances (`Cas/Program.lean`) and the plan's fallback for `Eff` is moot. Departures
  the landing inherits: `Digest := {bytes, length_eq : bytes.length = 32}` (so every consumer
  that builds a `Digest` supplies the proof; `sha256` and `ofHex?` do); `named` resolves over
  all bindings; `anyRef` accepts registered kinds only; the ref annotation key is
  `"effect4/ref"` with the kind name; named sums and definition entries carry `identifier`;
  `Canonical.encode = Wire.encodeProgram` is a golden receipt, not a theorem, until the Wire's
  module is rewritten at the landing.
- **S2 and G started 2026-09-04 23:35**, concurrently: S2 owns the one `lake build Cas`; G
  verifies with `lake env lean` only and stages under `workshop/Cas/Gen-out/`.
- **G done, 2026-09-05 00:35** (`workshop/Cas/REPORT-G.md`): the generator and its independent
  projection guard (35 shapes agree); `Json`, `Program` and `Schema` generated at 160 receipts
  none above the ceiling; the `Program` group byte-identical to the eight goldens and
  tree-identical to S1's hand instances; **`Canonical Document` exists**, so the spec of
  `Document` is a stored document with its own address and the genesis theorem can be stated
  on it. Decisions taken by the coordinator: the generated instances are the instances (the
  hand `Program.lean` and the `Json` half of `Templates.lean` retire at the landing; the
  goldens and reader guards stay as receipts); the manifest stays in the regeneration script,
  whose `-Verify` becomes `git diff --exit-code` once `Derived/` is tracked. Open from G:
  emitted line width (a per-group `open` prelude), the unexercised bare-parameter rule, the
  two benign linter warnings.

- **S2 done, 2026-09-05 00:40** (`workshop/Cas/REPORT-S2.md`): node, store, word, traits and
  the probe battery green; 202 receipts none above the ceiling; S1's 251 unchanged beside
  them; the §6 addresses reproduced as node addresses; admission, words, closure, the layered
  read, the outbox, `verify` and trait resolution all guarded. Departures the landing inherits:
  `specFor` chooses the spec per value (zero exactly at the genesis); the lattice takes
  `(toVal a).WF`; `get_put` needs `o ≠ conflict`; `Admission.conflict` exists for `Word.apply`;
  `closure_closed` needs `Sound` and a rank; the trait-identity claim is `nodeBytes_trait_free`
  plus `trait_put_preserves`. Owed: a `wf` word's store is `Ranked` and `Sound`;
  Perm-invariance of `effective`.
- **Spike exit, 2026-09-05 00:50** (`workshop/Cas/Cas/Genesis.lean`, `lake build Cas` 56
  jobs, green): the generated groups copied into `Cas/Derived/`, `Content Document` at kind
  `schema`, `nodeOf_metaSchema`, `nodeOf_document`, `specOf_document`, `metaSchema_fits`, the
  lattice all instantiated at `[propext, Quot.sound]`; the real numbers in the facts note
  §6a (genesis `2794d9…2926`, the entry's spec `268ee1…aa7c`, the entry's address
  `1c3c94…72eb`). Step 1 of §8 is complete; step 2, the landing, follows.

- **Landing started, 2026-09-05 ~01:10** (`workshop/Cas/LANDING.md`): the plan's §5 lanes
  re-cut for what the spike taught — one substrate lane (L1, Fable) first and alone; U (Surface)
  and X (the Char room, one lane because its files depend on each other) in parallel; C (census
  and views) after U; B (batteries, register, docs) last; builds serialised by a lock file since
  several lanes need targeted builds. Two layout decisions taken: the JSON number helpers keep
  the `Effect4.Arch` namespace in a new `Data/JsonNumber.lean` (six modules address them as
  `Arch.…`); derived instances live beside their carriers (`Program/Derived.lean`,
  `Evidence/StdLib/Derived.lean`, `Evidence/Char/Derived.lean`) so the store never imports an
  area above it. The generator gains `--kind Type=kind`, emitting the `Content` instance right
  after the `Canonical` one, because a `Ref` field needs the target's kind first. Generic Char
  carriers get hand instances on S1's templates until the generator takes a bare parameter.

- **L1 done 2026-09-05 01:21 and committed 01:50 as `a47c268`** (by the owner's seat, with
  three OCaml5 commits from another session), so §8's "one commit" became two: the substrate
  and the consumers. The tree on `main` is red between them by design (`NOTES-L1.md` lists the
  exact red files). The session was interrupted before the consumer lanes launched; **resumed
  10:35** with U and X in parallel, then C, then B, then the gate and the completing commit.

## 11. Claims to write in `COORDINATION.md` at the spike's start

`workshop/Cas/**` and the `Cas` lakefile hunk (coordinator); `tools/Effect4Gen/**` (lane G);
at the landing, the lane rows of §5 with their file lists, and the one build announced.
