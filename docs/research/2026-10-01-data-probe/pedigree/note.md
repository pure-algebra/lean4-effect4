# Data probe, seat PEDIGREE: what the record decided about typed data and Schema in programs

## The one thing

**"Native schema support" is decided as a rule, not as a feature, and the record does not yet say
how a program uses a schema.** The rule is tracked: AGENTS.md "Schema and program" (decisions row
13): Schema is data, its effectful slots are holes filled by typed `Eff` programs, and a foreign
transformation is a name that meaning-needing operations refuse. What implements it today is only
the boundary description plane: `Ty → Representation` with a proved retraction, and a type-directed
JSON codec with proved round-trip laws. AGENTS.md names both as exact embeddings, but neither has
its exactness law at `bc77e97f`: `ofSchema` reads a check by its id alone, so it fails outright (T6,
tested), and the codec holds only up to a JSON field-order normaliser that no theorem names (T5,
tested). The carrier of the rule's holes, `Transform`, was
deleted on 2026-09-18. No ruling covers decoding inside a program (`Schema.decodeUnknownEffect` is the
second most frequent unknown head in the 34-project census). Records, named variants, JSON values,
structured error payloads, signed numbers and recursive types are refused by tracked rulings (DB-15,
DI-62, DI-67) or have no row at all. The owner may believe four things are settled that are not:
- DI-08 ("is Schema in the release") is still **open** in the register; only the untracked D12
  note says it was answered.
- Row 2 (records and sums) and D10 (R3 as one DB-15 amendment) are **open**.
- Three incompatible record designs are on file, and none decides how a record value is encoded.
- Row 39's Schema wipe is ruled, but nothing is deleted yet.

DI-67's inhabitance rule is also enforced for `int` only: an empty product type passes admission
(tested and proved, T11 and P3). Any `Ty` constructor append touches `Fits`, `Val.hasTy` and every
`Ty` induction that Codex's M5–M7 work stands on. The record's own order (model-probe synthesis
§5.5) therefore puts R3 after the milestone, behind a ruling of D10.

## 0. Seat, base, and evidence words

Seat: PEDIGREE. Date: 2026-10-01. Base: `refactor/phase1-phase3` at `bc77e97f` (the slice 6 merge),
read with the working tree's uncommitted edits to `docs/STATE.md`, `docs/core/decisions.md` and
`docs/core/system-map.md` (they record the fork-ledger landing; `git diff` shows none touches data
or Schema). No tracked file edited; nothing built but the two probes of §7, through the lock.
Codex's worktree was not touched. During the probe the coordinator committed those three edits and the
regenerated architecture map as `ba9783c3`. `git diff bc77e97f ba9783c3 -- src/ AGENTS.md
docs/DESIGN-BASIS.md docs/DESIGN-ISSUES.md` is empty (tested), so every finding holds at
`ba9783c3`.

Evidence words:
- **proved**: a kernel theorem I ran in a probe here, with its axioms printed (§7).
- **tested**: a finite check I ran (`#guard` in a probe, `grep`, `git`, `ls`, `wc`).
- **reading**: read in code or notes, not run; cited `file:line` or note and section.
- **assumed**: neither read nor run.
- "tracked" means a git-tracked file, which survives a clone. "untracked" means a file under
  `docs/research/` that is not force-added (`git ls-files`, tested for every note cited below).
  The register's own rule (`docs/DESIGN-ISSUES.md:21-26`): **"A ruling is not made until it is
  written into a tracked file."**

## 1. Ledger: every decision about data and Schema

Status words: **ruled** (owner, written in a tracked file), **landed** (in code), **open**,
**recommended** (proposed, not ruled), **history** (a superseded plan). T = tracked, U = untracked.

### 1A. The type language: records, variants, recursion, nominal forms

| # | Decision | Where | Status, by whom, when | What it forbids or allows today |
| --- | --- | --- | --- | --- |
| L1 | DB-15 "What this basis refuses": no `json` leaf in `Ty` ("a codec is a row"), no record type ("columns are pairs"), `.int` uninhabited | T `docs/DESIGN-BASIS.md:664-667` | **ruled**: adopted 2026-09-08 from host-rows decision 3, "ratified as recommended by the owner on 2026-09-08" (U `2026-09-08-host-rows-slice.md:7-8`, §7) | forbids records, `json` and an inhabited `int` in `Ty`. Its origin was "**`string` in this slice, as step 1**" (U, `:500`), argued from "`Ty` has no sum" (`:202`); `Ty` has had tagged unions since DI-15 |
| L2 | DB-15 Wave 2: `Ty.lit` plus subtyping. "No record constructor or arbitrary error-value carrier is added by this ruling" | T `DESIGN-BASIS.md:658-662` | **ruled** 2026-09-09 (owner-approved Wave 2) | allows literal-tagged tuples; forbids records again |
| L3 | DI-15: a tagged sum is `union (prod (lit tag) X)`; identity is subtyping-equivalence; join is the least upper bound | T `DESIGN-ISSUES.md:87`; `Test/contracts/foundation-wave2.contract.md` | **ruled** 2026-09-09, amended 2026-09-11, **landed** 2026-09-12 | allows positional tagged variants. `Decision.tag` reads `.list [.str t, payload]` (`Program/Decision.lean:31-33`, reading) |
| L4 | Row 2, names for records and sums: (c) annotation-carried names now, (b) `Ty.record`/`Ty.variant` "before the first foreign consumer", as stages | T `docs/core/decisions.md:23` | **open**, owner. Source: scouts D (D-1) and E (E-5), 2026-09-17 | nothing landed. STATE told the owner that row 2(c) rides on the `AnnotationKey` row 39 keeps (`docs/STATE.md:549-550`) |
| L5 | Row 3, `Ty.app name args` (scout E's Design A) | T `decisions.md:24` | "do", not started; waits on row 1 | **conflicts** with the type-algebra note and system-map R3, which drop `Ty.app` for `Ty.foreign` (C4) |
| L6 | Charter §4.4 and R7: records and sums are encodings (nested `prod`, tagged unions) with sugar; "neither needs a constructor" | U `2026-09-16-core-goals-and-end-state.md:458-474`, `:618-622` | recommended 2026-09-16; scout D calls it "the ruling" (`2026-09-17-schema-interop-scout-D.md:208`) | **history**: overtaken by rows 2 and R3 (C8) |
| L7 | `Ty.record` as sugar over nested tagged pairs, `Ty.taggedUnion`, `SchemaFn`, `Endpoint`, `SchemaTransform` | U `2026-09-11-higher-order-schema-api-and-functions.md` ("Approved for Implementation") | **landed** at `e75d9e61` (2026-09-11), **deleted** at `b08f3b58` (2026-09-18) (`git show`, tested) | nothing today. The encoding publishes arrays, not objects (T4, tested) |
| L8 | Scout C P10: `Ty.data (name)`, a nominal type whose meaning is a `ShapeDoc` on the `Signature`, with values as `Val.ctor` and one eliminator subsuming `Decision.option`/`.tag`; covers user inductives and recursion | T (force-added) `2026-09-17-scout-schema-and-algebra-simplification.md:690-700`; findings ledger C-P10 `:68` | **queued** by the coordinator 2026-09-17 ("after the reader line"); never ruled | nothing landed; not reconciled with L9 (C5) |
| L9 | Type-algebra note §1.3: structural `Ty.record`/`Ty.variant` over a mutual `Fields` spine (non-nested, so `deriving DecidableEq` holds, F1–F2); `Ty.foreign id args` as an opaque nominal form, invariant, `hasTy = false`; "B lands with row 2 and not before" | T (force-added) `2026-09-18-research-type-algebra.md:126-185` | recommended 2026-09-18 (research seat; no Lean ran there, `:11-13`) | nothing landed. The `Ty` carrier rule it asked for is written (`Program/Ty.lean:11-23`, reading) |
| L10 | System-map §1.1: Σ_app "later, and only if admitted, nominal data declarations (row 2; DB-15)"; "Not in Σ: … structural records and variants, which are growth of the type language" | T `docs/core/system-map.md:46-53` | written 2026-10-01 from the model probe and rows 111–118 | a frame, not a ruling. Row 111 is ruled; data declarations are not |
| L11 | R3 (system-map §8): the type language closed under records and variants through the `Ty`/`Fields` spine; each constructor brings its `Fits` clause, embeddings, folds, assignability and inhabitance | T `system-map.md:232` | a requirement; its status reads "refused by DB-15 as written … open as one DB-15 amendment; recursive types untracked" | names L9's design. The Codex audit adds nothing on R3 (`audit.md` §5, `grep`, tested) |
| L12 | D10: rule R3 as one DB-15 amendment (records, payloads, `int`, decoding); keep the refusals now; rule row 2(c) now; open a recursive-types row now | T (force-added) `2026-09-30-model-probe/synthesis.md:1138-1149` | **recommended, not ruled**. The owner ruled D1–D6 only (rows 111–116) | nothing. **No register row covers recursive types** (`grep -i recursive` over the four registers, tested) |
| L13 | DI-89: modules enter as constructors, as rows generated from pinned declarations "into `Ty`" (refusing function-typed, higher-kinded and variadic signatures), or as named `Forms` templates | T `DESIGN-ISSUES.md:161` | **ruled** 2026-09-16 | generated rows can say only what `Ty` can say; `Schema.decodeUnknown*` has no route (§2.4) |
| L14 | DB-11: one value carrier `Store.Val`, images over it with `ofVal_toVal`/`ofVal_exact`, admission as a premise | T `DESIGN-BASIS.md:417-437` | **ruled** 2026-09-07 | a record value must be a `Val` image. Which image is undecided (C20) |
| L15 | `Store.Shape`, the store's own description language: `struct name fields`, `sum name cases` (wire tags), `named n` (references, hence recursion), rendered to schema structs and `_tag` variants | T `src/Effect4/Store/Domain/Shape.lean:60-82` | **landed** (code; no basis row) | a second data-type language beside `Ty`. "No theorem relates them" (`Test/Schema/DialectContract.lean:1-19`); T2 (tested) |

### 1B. Numbers

| # | Decision | Where | Status | Forbids or allows |
| --- | --- | --- | --- | --- |
| L16 | DI-56: each target's scalar domain is bounded with explicit refusal, intermediate values included; the logical `Nat` stays unbounded. Scout E's cell domain `{string, number in Nat, boolean, null}` "recommended … not ruled" | T `DESIGN-ISSUES.md:128`; DB-09 `DESIGN-BASIS.md:385-392` | **ruled** 2026-09-09 (S0); implementation is row 108, **open**, recommended | numbers are `nat` only |
| L17 | DI-67: every admitted column normalizes to `never` or is inhabited; `int` keeps ordinal 3 and is refused **at admission only**; "the value alphabet is not extended … `Float` lacks [decidable-equality laws]" | T `DESIGN-ISSUES.md:139`, P2a clarification `:190-194` | **ruled** 2026-09-11 | enforced for `int` only: `prod never nat` passes admission (T11 tested, P3 proved; C7) |
| L18 | DI-92: `Ty.int` is "the named landing place of a foreign `Schema.Int`"; `findIntInProgram` added | T `DESIGN-ISSUES.md:164` | **ruled**, landed 2026-09-17 | a foreign integer field parses (T7, tested) and its program is refused |
| L19 | Boundary decision T5: "`nat` stays; a float carrier is the first post-v0 append" | U `2026-09-10-boundary-decisions.md:87-99` | ratified 2026-09-10 per memory, untracked | contradicts DI-67's "not extended" in timing only; rows 108–109 park binary64 until Duration, Schedule or Random needs it (C15) |

### 1C. Errors

| # | Decision | Where | Status | Forbids or allows |
| --- | --- | --- | --- | --- |
| L20 | DB-15: a host error crosses as `prod string string` (`Err.tagged`); for `SqlError` the pair is the reason's tag and message (G1) | T `DESIGN-BASIS.md:605-630` | **ruled** 2026-09-08/09 (DI-00 basis) | structured host errors become two strings |
| L21 | DI-62: a program introduces a failure payload only at `never`, `nat`, `string`, a pair of tags, or unions of these; `Err.text` appended; `Err.value (v : Val)` **refused** "a handle inside a cause would extend the minted-handle invariant into causes" | T `DESIGN-ISSUES.md:134`; DB-15 `:649-656` | **ruled** 2026-09-09, amended 2026-09-12, landed | forbids `NotFound{id: 7}`: `fail (pair "NotFound" 7)` is ill-typed (T10, tested) |
| L22 | Boundary decision T9: keep the closed image for v0, extend by projection at adapters | U `2026-09-10-boundary-decisions.md:132-141` | ratified 2026-09-10 per memory | as L21 |
| L23 | post-Phase C W1: "Arbitrary error payloads need the existing basis ruling amended, not silently enabled" | T `docs/core/post-phase-c-synthesis.md:725` ("not an owner ruling", `:4`) | proposal | as L21 |

### 1D. Equality and collections

| # | Decision | Where | Status | Forbids or allows |
| --- | --- | --- | --- | --- |
| L24 | DI-35: `eq` widens one `Ty` at a time, only where `===` compares faithfully; past that the printed `eq` becomes `Equal.equals`, "its own slice"; `Val.eqAt : Ty → Val → Val → Bool` is the destination; no `Equal` class | T `DESIGN-ISSUES.md:107`; DB-15 `DESIGN-BASIS.md:643-647` | **ruled** 2026-09-09 | `eq` types at `nat` and `string` only; at a product it is refused (T8, tested); `Val.eqAt` does not exist (`grep`, tested) |
| L25 | DI-78: general runtime collections (option elimination, a declared accumulator, value-returning iteration) are required; concrete contracts to freeze first | T `DESIGN-ISSUES.md:150` | **ruled** (scope) 2026-09-16 | the list atoms landed (`Machine/Term.lean:164`, reading); maps and sets are absent |
| L26 | machine-state §7: a keyed table owes "equality and hash agree; stated duplicate and missing policies; stated iteration order" | T `docs/core/machine-state.md:199` | design (row 101's interfaces, parked) | no map today |

### 1E. The Schema plane: description, codec, bridge, wipe

| # | Decision | Where | Status | Forbids or allows |
| --- | --- | --- | --- | --- |
| L27 | DI-08: "Is Schema in the release, and does `Store.Shape` depend on the checker or only on the document carrier?" | T `DESIGN-ISSUES.md:80` | **open**, "the oldest open architecture question". The schema-composition synthesis asked the owner to write it (U, `:122-126`); it was never written | — (C9) |
| L28 | D12 "every boundary value carries an Effect Schema" (the owner's words, quoted at U `2026-09-10-schema-at-boundaries.md:4-9`): S-1 `Ty.schema`, S-2 documents, S-3 codec laws, S-4 `Api.schemaOf` plus the printer emitting the document, S-5 a gate that recorded exits decode under their own schema | U; in tracked files only as docstrings (`Schema/Bridge.lean:10`, `Api.lean:135`, `Test/Codegen/SchemaGenerationContract.lean:120`; `git grep`, tested) | ratified 2026-09-10 per memory, but **not written into a register**. S-1, S-2 and S-3 landed; S-4's printer half and S-5 did not (scout D §7.5) | describes boundary values; consumes none |
| L29 | S-3 owner amendment: the codec admits only values that recover exactly | T docstrings `Schema/Codec.lean:7-8`, `Laws/Schema/Codec.lean:4-8` | **ruled** (owner) 2026-09-11, **landed** | `encode` checks recovery at run time; seven laws plus `encode_injective` are proved (`Laws/Schema/Codec.lean:16-96`, reading) |
| L30 | Rows 1 (the AST as a second carrier), 5 (D12 as a sound/total pair plus the S-5 gate), 7 (handles), 10 (one `Val → Json`; four images today), 11 (where `Schema.*` text comes from) | T `decisions.md:22-32` | 1, 7, 10, 11 **open** (owner); 5 "do", not started | — |
| L31 | Row 6: `ofSchema` refuses what it cannot represent; "answers exactly the nodes `schema` mints, modulo annotations" (`Bridge.lean:73-77`) | T `decisions.md:27` | **landed** `4f2fadc8`; the exactness theorem is open (rows 35, 41) | it reads a check by its id alone, so "number ≥ 5" reads as `nat` (T6, tested; C12) |
| L32 | Row 35: "exactness wherever a read exists (C3: `ofSchema` first, the JSON codec second)" | T `decisions.md:76`; coherence-principle rows 22–23 (`docs/core/coherence-principle.md:128-129`) | "do"; exactness **open** | the JSON codec decodes a reordered object (T5, tested; C13) |
| L33 | Row 39: the Schema wipe (`Check`, `EffectfulField`, `Image`, `Accepts`, `Api.schemaOf`, `Annotations` trimmed, `Store.render` moved out of `Shape.lean`) | T `decisions.md:85`; STATE "What row 39 does" `:541-556` | **ruled** 2026-09-18; **nothing deleted** at `bc77e97f` (`ls`/`wc`, tested; `Api.lean:137`, `Shape.lean:425`, reading) | the dead parts still compile into the core root (`src/Effect4.lean:52-83` imports `Check`, `EffectfulField`, `Annotations`, `Accepts`; `grep`, tested) |
| L34 | Rows 56 (a classifier lists its positive arms and closes with an explicit `false`) and 68 (assignability differential and rows-and-atoms lane against tsgo) | T `decisions.md:103`, `:115` | **ruled** and landed (`0a2cb898`; `f6db74cf`) | DI-95's repair is in the code while DI-95 reads "open" (T9, tested; C14) |
| L35 | DB "Native library boundaries": "Schema separates representation, decoded value, encoded value, decoding services, and encoding services … Foldlab's CAS schema remains a checked downstream profile" | T `DESIGN-BASIS.md:691-695` | basis text, 2026-08-31; the model probe recommends retiring the section ("conflicts with DI-11 and DI-89", synthesis `:837`) | no implementation |
| L36 | `SCHEMA-CUTOVER.md` "Decision": one first-order representation modelled on the persisted `SchemaRepresentation.Document`, a document-relative relational interpretation, a directional codec calculus, eleven independent codec properties and no universal round-trip law | U, "frozen design input, 2026-09-02" | **history** (the Flow era); its getter, transformation, registry and denotation lanes were never built or were deleted | — |

### 1F. Schema in programs

| # | Decision | Where | Status | Forbids or allows |
| --- | --- | --- | --- | --- |
| L37 | "**Schema and program**: Schema is a data language; every effectful slot in it is a hole filled by an `Eff` program with a typing certificate; `Ty` and the schema carriers never mention `Eff`; a foreign transformation is a name with a typed signature that any meaning-needing operation refuses" | T `AGENTS.md:85`; derived from coherence-principle §4b "Ruling: (ii)" (T `coherence-principle.md:283-345`, scout F) | **ruled**: row 13 "done", written `f8c9b7fe`; row 36 | the rule. Its arrow carrier `Transform σ Γ A B E R` (§4b) was deleted at `b08f3b58`; row 12 is "moot" (C11) |
| L38 | Schema composition synthesis: "transforms live in `Eff`"; a transform is a pair of `Eff` programs at a one-slot environment; "Recursion is references, not μ; a `Document` is a guarded letrec"; the codec carrier is a prism | U `2026-09-10-schema-composition-synthesis.md:12-56`, `:75-77` | proposals; "nothing here is a ruling until the owner writes the rows in §5" (`:7-8`) | — |
| L39 | post-Phase C W9: "execute row 39, then admit needed parsing/transform behavior through typed Eff holes" | T `post-phase-c-synthesis.md:733` | proposal ("not an owner ruling") | — |
| L40 | Programs seat P5: decoding is either a host row answering the decoded typed value (checked by `Fits`) or an `Eff` hole with an exact embedding | T (force-added) `2026-09-30-model-probe/programs/note.md:318-328` | finding, carried by D10 | — |

## 2. "Native schema support", as the record defines it

### 2.1 The definition

The record's definition is AGENTS.md's vocabulary entry (`AGENTS.md:85`), from coherence-principle §4b
("Ruling: (ii). … programs over types, not types over programs", `coherence-principle.md:283-345`),
written by decisions row 13 (`f8c9b7fe`). Its four parts, and the carrier each has at `bc77e97f`:

| Part of the rule | What would carry it | At `bc77e97f` |
| --- | --- | --- |
| Schema is a data language | `Representation`/`Document`/`Payload`, the 22-tag persisted alphabet (system-map §4: "schema carrier \| `Representation`") | **exists** (reading) |
| `Ty` and the schema carriers never mention `Eff` | `Program/Ty.lean` imports only `Data.Row`; `Representation` has no program slot | **holds** (reading) |
| every effectful slot is a hole filled by an `Eff` program with a typing certificate | §4b's `Transform σ Γ A B E R`, a program holding `effTy σ (Γ ++ [A]) program = some ⟨B, E, R⟩` | **no carrier**: `Schema/Transform.lean` was deleted at `b08f3b58` (2026-09-18) with `Schema/Endpoint.lean`. Row 12 moves the category laws to `composeAt` (system-map §6, "the laws are future work"). Row 1 (an AST with program slots) is open |
| a foreign transformation is a name with a typed signature that meaning-needing operations refuse | an AST `Link` holding a name, or a registry | **no carrier**; `ofSchema` refuses checks it does not mint (row 6), but nothing holds a named foreign transformation |

### 2.2 What implements Schema at `bc77e97f`

The description plane is real. Scout D's verdict was "Interop is half built and wholly unused"
(`2026-09-17-schema-interop-scout-D.md:5`), and it still holds:

- `Bridge.schema : Ty → Representation` and `ofSchema`, with the retraction `ofSchema_schema` on
  closed types (`Schema/Bridge.lean:38-208`, reading). The image uses 9 of the 22 tags, never
  `objects`, `reference` or `suspend` (scouts D §6 and E §4, reproduced there). T1 and T2 re-check
  that a struct node, and the store's own named record, read back to `none`.
- `Schema.encode`/`decode`, type-directed JSON in rc.112's `toCodecJson` profile
  (`Schema/Codec.lean:12-16`). The laws `encode_eq_some`, `encode_isSome_iff`, `encode_of_hasTy`,
  `decode_of_encode`, `decode_encode`, `hasTy_decode`, `encode_sub` and `encode_injective` are in
  `Laws/Schema/Codec.lean:16-96` (reading). The host comparison is the `schema-codec` gate, finite.
- `effDocument`/`rowDocument` (`Bridge.lean:209-232`) and `Api.schemaOf` (`Api.lean:137`). None has
  a reader: zero call sites (scout D §7.5). Row 39 deletes `schemaOf`.
- The printer `Representation → Schema.*` text (`Codegen/Schema.lean`), held by the `schema-ts` gate.

The ontology probe's summary still holds: "About 1,200 lines carry the estate's two real schema
claims" (`2026-09-17-ontology-and-do-now-probe.md` §3.2).

### 2.3 What is not determined

Each of these lacks a tracked ruling or a carrier:
- whether Schema ships (DI-08, open);
- names for records and sums (row 2, open);
- what a record value is (C20);
- recursive types (no row);
- the decode route in programs (§2.4);
- the hole's carrier (`Transform` deleted; row 1 open);
- exactness of both embeddings (rows 35 and 41, open; T5 and T6 show the unqualified statements are
  false);
- the S-5 gate that would make D12 a claim and not a rendering (row 5, not started).

### 2.4 `Schema.decodeUnknown`-style use in a program: row, form, fold, or refused?

**No ruling exists.** A `grep -i` for `decodeUnknown`, `JSON.parse`, `parse json` and `decode route`
over the registers and `docs/core/` finds only DB-15's host-side `JSON.parse` of bind parameters
(`DESIGN-BASIS.md:626`) and row 2's remark that a foreign `decodeUnknownSync` reads no annotation
(tested). The record gives the following:

- **Under the rule (L37), the use splits in two.** Decoding against a pure schema is a fold over
  values: the object sort's `accepts`/codec. `Schema.decode : Ty → Json → Option Val` is exactly that
  fold for the `Ty` fragment, but it is a Lean API function and not a program operation. The
  effectful transformation links inside the schema are holes. If they are ours, they are `Eff`
  programs. If they are foreign, they are refused names. The rule classifies the pieces; it does not
  say which construct a program writes.
- **Under DI-89 (L13), it has no route.** rc.112's `Schema.decodeUnknownEffect(schema)(input)`
  depends on the schema value's type (`S["Type"]`, `S["DecodingServices"]`;
  `vendor/effect-4.0.0-rc.112/src/Schema.ts:1517-1525`, reading). The declaration reader
  refuses higher-kinded signatures by name, and decode is not on the named `Forms` list (`retry`,
  `catchTag`, `forEach`, `all`, `Schedule`, the option and result eliminators). So it is
  **refused today**: an unknown head at ingest, counted by the census (`Schema.decodeUnknownEffect`
  547, `decodeUnknownSync` 92, `decodeUnknownOption` 50, `decodeUnknownResult` 19 over 34 projects;
  U `2026-09-08-ingest-census.md:39-68`, a finite census not rerun here).
- **Under DB-15 (L1), the codec is the host's.** "A codec is a row" (`DESIGN-BASIS.md:664-665`): the
  adapter decodes and the program receives JSON text in strings (`list (prod string string)`). No atom
  parses text (`Machine/Term.lean:146-164`, reading; programs seat P5). In practice a program cannot
  decode at all.
- **Three candidate routes are written down, none ruled.**
  - (a) The host row answers the decoded typed value, a record type checked by `Fits` at the reply
    (P5 option 1). This needs DB-15 amended for records.
  - (b) A typed `Eff` hole (W9, P5 option 2). This needs a carrier for holes: row 1's AST, or
    `Transform` restored.
  - (c) A decode operation at a declared type, as an atom or a sync row whose meaning is
    `Schema.decode τ`, the fold that exists. No note proposes (c) by name; it is the narrowest form
    of the rule's "fold over values". It needs a `Ty` stored in the program tree. `iterate`'s cursor
    annotation already is one (DI-91; DI-92 scans it, `Program/Admission.lean`
    `findIntInProgram`), so it adds no polymorphism (DI-20, DI-28).
- **D10 recommends deciding the decode route inside the one DB-15 amendment, "when the first real
  program is taken on"** (synthesis `:1138-1149`). This is not ruled.

### 2.5 Answer to "did we determine native schema support?"

**Partly, and less than the notes suggest.** Determined and tracked: the rule (L37); the
description plane's existence and its laws (L28–L29, S-1 to S-3); the wipe's scope (L33). Not
determined: Schema in the release (DI-08 open); records and names (row 2 open); the program-side
decode route (no ruling); the hole's carrier (deleted); exactness (open, and false as stated, T5 and
T6); recursive types (no row). D12 is the owner's stated intent; it lives in an untracked note and
in docstrings. By the register's own rule it is not a ruling.

## 3. Contradictions and gaps

Each item names both sides and says what decides it. "Tested" and "proved" refer to §7.

- **C1. DB-15 against R3 and the type-algebra spine.** DB-15 refuses "a record type in `Ty`"
  (`DESIGN-BASIS.md:665`). System-map R3 (`system-map.md:232`) asks for "the type language closed
  under records and variants through the `Ty`/`Fields` spine". Both are tracked. R3 itself records
  the conflict ("refused by DB-15 as written"); only an amendment (D10) resolves it.
- **C2. D12 against DB-15's "cross as strings".** D12 promises that "we can always say what type it
  may emit" (U, schema-at-boundaries `:4-9`). Under DB-15 a SQL row's column is
  `list (prod string string)` with JSON-text cells. So D12's published schema for a host record is
  an array of string pairs: true, but it describes JSON text, not the record. The published schema
  no longer carries the record's field types, so it degrades exactly where real data enters. Not
  a contradiction in the letter (DB-15 governs `Ty`, D12 describes `Ty`), but D12's purpose fails at
  every host row.
- **C3. W9's typed `Eff` holes against DB-15's "a codec is a row" against P5's "host answers
  decoded typed values".** These are three routes for decoding, two tracked as proposals and one as a
  ruling (DB-15). No ruling chooses among them (§2.4).
- **C4. Row 3 (`Ty.app`, tracked register, "do") against R3 and the type-algebra note (`Ty.foreign`;
  "`Ty.app` … stays refused", `2026-09-18-research-type-algebra.md:173-182`).** Both are tracked
  files. The register was not updated when R3 adopted `Ty.foreign`.
- **C5. Three record designs, unreconciled.**
  - Scout C's nominal `Ty.data` (L8): values are `Val.ctor`; the `ShapeDoc` sits on the signature;
    it covers recursion and user inductives; queued.
  - The type-algebra note's structural `Fields` spine (L9): R3 adopts it.
  - The charter's encodings (L6).

  System-map §1.1 tries to hold both of the first two (structural growth in `Ty`, nominal
  declarations in Σ_app). R3's only nominal form, though, is the **uninhabited** `Ty.foreign`.
  Nominal **data with fields**, and recursion, have a design only in scout C's note, and nothing
  links it to R3.
- **C6. R3's inhabitance clause against `Ty.foreign`.** R3 asks
  `∀ admitted τ, τ.normalize = never ∨ ∃ w v, Fits w v τ` (synthesis `:246`). The type-algebra note
  makes `Ty.foreign` uninhabited by design. P2 (proved) shows the clause is false without the
  admission premise, at `int`. So every uninhabited constructor needs an admission refusal, as `int`
  has (DI-67). R3 does not say so for `Ty.foreign`.
- **C7. DI-67 is ruled but not enforced beyond `int`.** DI-67 rules that every type admitted at "a
  program's answer, error, request or table column either normalizes to `never` or has a value"
  (`DESIGN-ISSUES.md:139`).
  - **Tested (T11):** the program `bind (fail 1) (succeed (pair (var 0) 1))` is typed at answer
    `prod never nat`. `normalize` keeps `prod never nat`, and `admitProgram` admits it. A host row
    whose answer column is `prod never nat` is admitted too.
  - **Proved (P3):** no value and allocation table give `Val.hasTy v (prod never nat) a = true`.
  - The admission docstring lists the `int` scan only (`Program/Admission.lean:10-16`). The
    type-algebra note named this incompleteness (§5.2 item 2, "product annihilation") and
    recommended a register row; none exists.
- **C8. The charter's "records and sums are encodings; no constructor"** (U, core-goals §4.4, R7)
  **against row 2 (b) and R3 (constructors).** Scout D treats the charter as "the ruling" (U,
  `:208`). It never was one: it is untracked, and row 2 later opened the question.
- **C9. DI-08 open (tracked register) against D12 "answers DI-08" (U) and row 39 (tracked, ruled
  wipe that presupposes Schema ships in part).** The register was never updated, although the
  schema-composition synthesis asked for exactly that row (U, `:124-126`). The owner's memory records
  "D12 answers DI-08"; the tracked record does not.
- **C10. D12's S-4 (`Api.schemaOf` as enforcement) against row 39 (delete `schemaOf`).** Row 39
  reverses part of D12: the publisher becomes `EffTy.document` and the consumer the S-5 gate, which is
  row 5, not started. Until row 39 executes, `schemaOf` exists with zero readers (scout D §7.5).
- **C11. The AGENTS rule has no instance.** Its arrow sort, `Transform σ Γ A B E R` (coherence
  §4b), was deleted on 2026-09-18 (`b08f3b58`, the same day row 39 was ruled). No structure in the
  tree attaches an `Eff` program to a schema node (reading over `src/Effect4/Schema/`; the remaining
  `EffectfulField` resolves into the external `Effects.Program`, not `Eff`, and row 39 wipes it).
- **C12. Row 6's "exactly the nodes `schema` mints, modulo annotations" is false.** `checkId` reads
  only a check's id (`Bridge.lean:62-65`), so a `number` carrying `isInt` and
  `isGreaterThanOrEqualTo {minimum: 5}` reads back as `nat`, whose schema says minimum 0 (T6,
  tested). Coherence row 23's "(c) absent and false" is repaired only in part. AGENTS.md lists
  `Ty.schema`/`ofSchema` as an exact embedding (`AGENTS.md:73-76`); by its own definition, "a read
  without exactness is a widening".
- **C13. The JSON codec's exactness needs a normaliser no theorem names.** `decode (option nat)` accepts
  `{"value": 1, "_tag": "Some"}`, while `encode` writes `{"_tag": "Some", "value": 1}` (T5, tested).
  Exactness needs an object-entry-order normaliser that no theorem names. The coherence principle
  already records "(c) absent" (row 22) and "the `⊆ id` half is row 22's missing obligation"
  (`coherence-principle.md:128`, `:598-600`). AGENTS.md lists "the JSON codec" as an exact embedding
  (`:73-76`).
- **C14. DI-95 reads "open" (`DESIGN-ISSUES.md:167`) while its repair has landed.** Row 56
  (`0a2cb898`) put the explicit `false` in place: `Codec.isSupported` closes with `| _ => false`
  (`Schema/Codec.lean:51-55`), and `unknown`, `refOf` and `var` are unsupported (T9, tested). This is
  register lag.
- **C15. Numbers: three timings.** Boundary decision T5 (U): "a float carrier is the first post-v0
  append". DI-67 (T): "the value alphabet is not extended … restrict now, extend by one later". Rows
  108–109 (T, open): binary64 only "when `Duration`, `Schedule` or `Random` arithmetic is modelled".
  Signed integers have no route at all. `Schema.Int` lands on `int`, so a foreign integer field
  always refuses admission (DI-92; T7, tested).
- **C16. Two data-type languages.** `Store.Shape` has named records, tagged sums and named
  references; `Ty` has none. System-map §4's sorts table lists `Ty` as the type sort and
  `Representation` as the schema carrier, and does not list `Shape`. Only a pinned battery relates
  them, with three recorded disagreements (`DialectContract.lean`; T2, tested). "One representation
  per sort" does not hold for data descriptions today.
- **C17. README overstates the Schema face.** It says (`README.md:34-35`) "The same import exposes
  concrete value images, typed effectful transformations, multi-tier cascading CAS stores, and checked
  schema endpoints", and its diagram ends in "JSON Schema". Transformations and endpoints were deleted
  at `b08f3b58`. No JSON Schema emitter exists under `src/`: `Codegen/JsonSchema.lean` is cited in
  `Data/JsonNumber.lean:15` and absent (`ls`, tested).
- **C18. DB-15's refusals hardened a step-1 choice.** Host-rows decision 3 said "`string` in this
  slice, as step 1", argued from "`Ty` has no sum" (U, `:195-202`, `:500`). DB-15 restated it as
  "What this basis refuses". The premise is gone (DI-15's tagged unions landed 2026-09-12), but the
  refusal stands.
- **C19. Recursive types have no row anywhere.**
  - What the record has: R3 says "untracked"; D10 recommends opening a row; JSON values and the
    ledger example need them (synthesis `:267`).
  - The parts that exist:
    - `Shape.named` (store-side recursion through a definitions table);
    - "a `Document` is a guarded letrec" (U, composition synthesis `:56`);
    - `SC-DOC-01`–`07`, open in `Schema/Document.lean`'s header (guardedness, productivity);
    - `E4-SCHEMA-CE-013`/`014`.
  - `Ty` is finite by construction (scout D §6), and `ofSchema` refuses `reference` and `suspend`.
- **C20. A record's value encoding is decided nowhere.** Four candidates are on file:
  - scout C: `Val.ctor` (L8);
  - scout E: `Val.tagPayload?` "gains an object leg" (§5);
  - the deleted sugar: nested two-element lists (T4);
  - the type-algebra note: silent (`grep`, tested).

  DB-11 requires every value to be one `Val` image, so the choice moves `Fits`, `Val.hasTy`, the
  JSON codec, the printer and the OCaml engine together.
- **C21. Equality for records is unruled.** DI-35 admits `eq` one type at a time where JS `===` is
  faithful. On objects `===` is reference identity, so a record `eq` must print as `Equal.equals`,
  "its own slice", never begun. `Val.eqAt` does not exist (`grep`, tested). R3's "owed with records"
  list and the keyed-table interface (machine-state §7) both need it.

### What the owner may believe is decided, but is not

1. **That Schema is in the release (D12 answers DI-08).** DI-08 is open in the tracked register;
   D12 is an untracked note plus docstrings.
2. **That records have a ready design.** Row 2 and D10 are open; DB-15 refuses; three designs
   disagree (C5); the value encoding is undecided (C20). The model probe already said that "the
   design is ready" is a recommendation, not a decision (synthesis `:252-253`, P12).
3. **That the Schema wipe happened.** Row 39 is ruled; nothing is deleted at `bc77e97f`.
4. **That typed effectful transformations and schema endpoints exist.** README says so; they were
   deleted on 2026-09-18.
5. **That `ofSchema` and the JSON codec are exact embeddings.** AGENTS.md says so. `ofSchema` fails
   exactness (T6); the codec's exactness needs a field-order normaliser no theorem names (T5).
6. **That every admitted type is inhabited (DI-67).** Only `int` is enforced (T11, P3).
7. **That recursive types are tracked.** No row exists.
8. **That programs can decode JSON.** No ruling, no atom, no row.

## 4. Pedigree

| Topic | Work | Mark | By which note | Used for |
| --- | --- | --- | --- | --- |
| records, rows | Wand 1989 (LICS); Rémy 1994; Gaster and Jones 1996; Leijen 2005 (scoped labels); Morris and McKinna 2019 (POPL) | **assumed** ("Literature (assumed; not read here)") | type algebra §8 (`:942`, `:964-969`); carried as "assumed" by the model probe §3.1 (`synthesis.md:741`) | "row theories, if `Ty.record` ever needs row polymorphism rather than a closed field list". No note reads any of them for records |
| effect rows (not record rows) | Leijen, *Type Directed Compilation* 2017 §3, §3.2; Hillerström and Lindley 2018 | **read** | lit-papers Q4 (`2026-09-07-lit-papers.md:195-223`) | why the profile has no row polymorphism. It bears on effect rows only |
| coproducts of signatures | Swierstra, *Data Types à la Carte* 2008 §2, §6 | **read** | model-probe pedigree seat (synthesis `:735`) | R2's conservativity, not data |
| deriving and nesting | Lean 4.33.1 toolchain facts F1–F6 | **read** at the toolchain lines | type algebra §0 (`:28-35`) | why the `Fields` spine and not `List Ty` |
| subtyping completeness | Frisch, Castagna and Benzaken 2008; Castagna and Xu 2011 | **assumed** | type algebra §5.3, §8 | the antichain stays; incompleteness to be registered |
| local inference and variance | Pierce and Turner; Odersky et al.; Dunfield and Krishnaswami; Emir et al. 2006 | **assumed** | type algebra §3, §8 | templates; declaration-site variance (rows 55, 60 read rc.112's own declarations instead) |
| schema as a signature | Mattick, *Specifying Hyperdocuments with Algebraic Methods* 2014 §2–§3 | **read** in full | papers review §1.2 and A5 (`2026-09-05-effects-papers-review.md:72-80`, `:494-506`) | accepted values as ground terms; `print_conforms` proposed, absent (`grep`, tested) |
| `Ty` inside `Representation` | McBride, *Ornamental algebras* 2011; Dagand and McBride 2012 | **by name** | coherence principle §1 (C), literature (`coherence-principle.md:83-85`, `:560-562`) | `Ty` as an ornament with a forgetful fold |
| exact embeddings (K2) | Rendel and Ostermann 2010; Matsuda and Wang 2013; Foster et al. 2007; Pickering, Gibbons and Wu 2017 | **by name**, with uses | coherence principle literature (`:554-559`); model probe §3.1 marks them "by name" | the three K2 laws; "`Canonical`'s three fields are the lawful-Prism laws" |
| graded effectful arrows | Power and Robinson 1997; Levy, Power and Thielecke 2003; Katsumata 2014; Orchard et al. 2014 | **by name** | coherence principle §4b, literature | `Transform` as an arrow of a graded Freyd category, now deleted |
| initial-algebra semantics | Goguen, Thatcher, Wagner and Wright 1977 | **by name** | coherence principle | folds out of the free object |
| the host's Schema | rc.112 `Schema.ts`, `SchemaAST.ts`, `SchemaRepresentation.ts`, `SchemaGetter.ts`, `SchemaTransformation.ts` at the pin | **read** at cited lines | scouts D and E; coherence §4b (`SchemaAST.ts:401-415`, `SchemaGetter.ts:64-78`); `Schema/Codec.lean:12-16` (`toCodecJson` lines) | the 22-tag mirror; `Getter` as a host closure (why rule (ii)); the codec profile |
| codec laws | `SCHEMA-CUTOVER.md`'s eleven codec properties; rc.112 `TestSchema.verifyLosslessTransformation` | **read** by the Flow-era notes | U `SCHEMA-CUTOVER.md` "Codec law classification"; consumer survey §4.4 | "No universal round-trip law"; history |
| publication identity | Unison's hash/name split; Avro writer-schema-with-the-data | **by name** | DI-01 (`DESIGN-ISSUES.md:73`) | the published unit, not data typing |
| JSON standards | JSON Schema 2020-12 test suite, RFC 6901/6902, provider strict modes | **by name** here (fetched by that survey, digests only; I did not reread it) | U `2026-09-02-standards-targets-survey.md` (per memory; not reread here) | surfaces; no Lean consumer today |
| real-program need | 34-project ingest census; the five programs of the model probe | **tested** by those seats, not rerun here | U ingest census `:39-68`; T programs seat `:26-30`, `:361-366` | `Schema.Struct` 2,032 and `decodeUnknownEffect` 547 as unknown heads; records in 5 of 5 programs, structured payloads in 4 |

**Net pedigree.** The data-type side of R3 rests on Lean facts (read) and on the estate's own
algebra (proved instances: `Canonical`, print/read, the codec's retraction). The record and row
literature is **assumed** throughout: no note in the tree reads Wand, Rémy, Gaster and Jones,
Leijen 2005 or Morris and McKinna. The exactness pedigree (K2) is **by name**, and the two Schema
instances AGENTS.md lists lack the exactness law (C12, C13). The Schema-as-algebra pedigree (Mattick) is **read**,
but its theorem (`print_conforms`) was never written.

## 5. R3 restated as theorem shapes, and what each ruling already fixes

Let Σ = Σ_core ⊕ Σ_app (system-map §1.1). Let κ be a new type former: a structural record or variant
over `Fields`, `Ty.foreign`, or a nominal `Ty.data` if C5 chooses it. For each κ:

| Shape | Statement | Fixed by an existing ruling | Open |
| --- | --- | --- | --- |
| R3.a membership | `Fits w v (κ args)` has one clause over the actual value encoding, beside the one executable `Val.hasTy` arm, joined by a connector like `fits_hasTy` (`Laws/Program/Typed/Membership.lean:269`) | row 96 (one judgment, landed); host-boundary §4.4 (a row per constructor); system-map §4 ("anything else that checks a value against a type is a leak"); row 97 (handles inside a record answer follow the interim rule) | the value encoding (C20) |
| R3.b schema embedding | `ofSchema (schema t) = some t` (have: `ofSchema_schema`, closed `t`); exactness `ofSchema r = some t → r ≈ schema t` with ≈ a **named** normaliser that drops annotations only | AGENTS.md K2 vocabulary; rows 6 and 35 | exactness is false today (T6); `objects`, `reference` and `suspend` arms; field order and optional fields for records |
| R3.c JSON embedding | `encode t v = some j → decode t j = some v` (have: `decode_of_encode`); `decode t j = some v → ∃ j', encode t v = some j' ∧ N j = N j'` with N the object-entry-order normaliser | S-3 owner amendment (admit only exact recovery, landed); row 35 | the converse (T5); `isCodecValue` as the domain; the codec of a record (an object, not an array) |
| R3.d generated folds | `TyAlgebra` gains a field; `cata_ty`, `hom_eq_cata_ty` regenerated; no classifier defaults into the positive class | row 56 (landed); the `Fold` group (`tools/Effect4Gen`); the carrier rule (`Program/Ty.lean:11-23`: first-order, proof-free, every field a `Shape`, appended never inserted) | the head/variance view (type algebra §2), recommended "with row 2" |
| R3.e assignability | the `Ty.sub` arm for κ agrees with tsgo assignability in both directions on the row-68 differential (tested lane), and the Lean order laws hold on `CTy` (`sub_antisymm_canonical`, `hasTy_sub`/`fits_sub`) | DI-15/DI-53 (canonical forms, least upper bound); row 68 (landed lane); row 57 (one compiler) | width and depth subtyping for records; variance of record fields |
| R3.f inhabitance | `∀ τ, Admitted Σ τ → τ.normalize = .never ∨ ∃ w v, Fits w v τ` | DI-67 (ruled); DI-92 (`int` refused at admission, with its path) | **false at HEAD** for `prod never nat` (T11, P3); needs `normalize` to annihilate never-products, an admission refusal, or a restated DI-67; an uninhabited κ (`Ty.foreign`) needs an admission refusal (P2) |
| R3.g compatibility | `W ⊑ W'`: κ's wire tags appended, old values decode exactly, typing and admission deltas named, nothing reordered | DI-47 (ruled); the retained baseline `Test/fixtures/baseline/`; `tools/Effect4Gen/wire-tags.json` append-only | a finite gate and a discipline, not a theorem (system-map §1.1) |
| R3.h owed with records | collections (keyed-table laws); `Val.eqAt` with `eqAt t v w = true ↔ v = w` on `Fits`-members, printed as `===` or `Equal.equals` per DI-35; error payloads (`FitsCause`'s failure arm, if `Err.value` is admitted); numbers per DI-56/row 108; a decode route (§2.4); recursive types (a row) | DI-35, DI-62, DI-56, DI-78 (ruled scopes); machine-state §7 | every item; D10 would rule them as one packet |

Two further fixed points bound R3:
- **AGENTS "Schema and program"**: `Ty` must not mention `Eff`, so no record field may hold a
  program.
- **DI-89**: generated rows are cut "into `Ty`", so whatever R3 adds is what module rows can then
  say.

## 6. Options at the owner's boundary, and the seat's recommendation

These are owner decisions. The seat records the options and stops there.

1. **Register repair, no new design.**
   - Write DI-08's status from what is true: D12's description plane landed; row 39 is ruled and
     unexecuted.
   - Mark DI-95 landed (row 56).
   - Add the recursive-types row D10 asks for.
   - Register the `prod never` admission gap against DI-67 (C7).

   Recommended now: it costs no `Ty` change and stops the record from misleading.
2. **D10 / row 2.** (a) Keep the refusals and rule row 2(c), annotation names, now (the synthesis's
   recommendation). (b) Rule the R3 packet now. Recommended: (a). Before any record constructor
   lands, the packet should also settle three things this seat found:
   - one record design out of three (C5), with its value encoding (C20);
   - DI-67's enforcement (C7);
   - named normalisers for the two "exact embeddings" (C12, C13), or AGENTS.md amended to call them
     widenings until then.
3. **The decode route (§2.4).** Choose among (a) host rows answering decoded typed values, (b) typed
   `Eff` holes, (c) a decode operation at a declared type, or keep refusing. Recommended order when
   the first real program is taken on: (a) for host data, since `Fits` and the reply check already
   gate answers; then (c) as the in-program fold, since `Schema.decode` and its laws exist; (b) only
   when an effectful transformation is needed, because it first needs a hole carrier (row 1, or
   `Transform` restored with its laws at `denote`).
4. **Sequencing against Codex.** A `Ty` append adds a clause to `Fits` and `Val.hasTy`, an arm to
   every folded `Ty` traversal, and a case to every `Ty` induction in `Laws/Program/Typed/` (reading:
   `Membership.lean:87-137`, the `fits_*` laws, `hasTy_sub`). Codex's M5–M7 and H2 work stands on
   those. The record's order (synthesis §5.5: R10's forms, then R3, "after the milestone") avoids a
   collision. Exploring R3 now, as design and probes in `docs/research`, does not touch Codex's
   worktree; landing it would. The tree seat of this probe measures the append's cost; this seat did
   not repeat it.

## 7. Evidence: the probes

The files are in this folder. Each was compiled through the lock with
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <file>` at `bc77e97f`, with
oleans from the main checkout (`Effect4/Api.olean`, `Laws/Program/Typed/Membership.olean`,
`Laws/Schema/Codec.olean` and `Schema/Bridge.olean` built 2026-10-01; `Store/Domain/Shape.olean`
built 2026-09-20, the source unchanged since `05417cc6`, tested by `git log` and `stat`).

- `PedigreeProbe.lean` exits 0 (`PedigreeProbe.log`). Its guards are T1–T11; all are **tested**
  finite checks:
  - T1: a schema struct reads back `none`; red control, the binary tuple reads back.
  - T2: `Store.render (struct …)` reads back `none`.
  - T3: a foreign nullary declaration reads back as `handle "User"`.
  - T4: the nested-pair record encodes as nested arrays.
  - T5: the JSON codec's decode accepts reordered fields.
  - T6: `ofSchema` reads `number ≥ 5` as `nat`.
  - T7: `Number+isInt` reads as `int`.
  - T8: `eq` at `string` is admitted; at a product it is refused.
  - T9: `isSupported` is false at `unknown`, `refOf` and `var`.
  - T10: `fail (pair "NotFound" 7)` is ill-typed; the two-string pair types.
  - T11: `prod never nat` is admitted as a program answer and as a host-row column; red control, the
    same row at `int` is refused as `.uninhabited ["table", "0", "answer"]`.

  Its theorems are **proved**:
  - `fits_int_empty`, `fits_prod_never_empty` and `inhabitance_needs_admission` at
    `[propext, Quot.sound]`;
  - `hasTy_prod_never_false` and `di67_no_value_at_prod_never_nat` at `[propext]`.
- `PedigreeProbe.run1.log`: the first run, exit 1, failed on my naming error at T8 only. It was
  restored verbatim after an accidental delete.
- `PedigreeRed.lean`, the **RED CONTROL**, exits 1 with exactly four errors, R1–R4
  (`PedigreeRed.log`). R1 asserts a struct reads as a pair. R2 asserts admission refuses
  `prod never nat`. R3 asserts the codec refuses the reordered object. R4 is a proof that a value
  fits `prod never nat`. The probe's guards are therefore not vacuous.
- `scratch-hasTy.log` records a scratch file, deleted after use, in which two proof scripts for P3
  compiled with exit 0.

Every finite check is a finite probe. None is a statement about all programs, and none was run
against rc.112. The census figures and the five-program findings are other seats' runs, reported as
they report them.

**Receipt.** Base `bc77e97f`, current HEAD `ba9783c3` (the coordinator's docs commit). This seat
made no commit and changed no tracked file (`git status` is clean at `ba9783c3`). Files written, all under `docs/research/2026-10-01-data-probe/pedigree/`:
- `note.md`;
- `PedigreeProbe.lean`, with `PedigreeProbe.log` and `PedigreeProbe.run1.log`;
- `PedigreeRed.lean`, with `PedigreeRed.log`;
- `scratch-hasTy.log`.

Commands: as above, two compiles of the probe, one of the red control and one of the scratch file,
each through `serial.sh`. Axiom output: as listed, within `[propext, Quot.sound]`. Open
obligations: §6. All Lean evidence here is a finite probe over the tree's own definitions; none is
host evidence.

## Appendix A. Reading log (written as I read; sections 1-7 condense it)

### R-1. Tracked authorities (reading, at bc77e97f)

- DB-15 (`docs/DESIGN-BASIS.md:584-684`), adopted 2026-09-08, amended 2026-09-09 (S0, Wave 2):
  str is a machine value; a SQL row is `list (prod string string)` with JSON-text cells; an error
  crosses as `prod string string` (`Err.tagged`); "What this basis refuses": a `json` leaf in `Ty`
  ("a codec is a row"), a record type in `Ty` ("columns are pairs"), `.int` inhabited. Wave 2 adds
  `Ty.lit` and says "No record constructor or arbitrary error-value carrier is added by this ruling".
  Scout E's three amendments are "Recommended beside these refusals, not ruled" (`:663`).
- DB-15 also states DI-35 (eq widens one `Ty` at a time where `===` is faithful; `Val.eqAt` is the
  destination) and DI-62 (admissible error image: never, nat, string, prod string string, unions;
  `Err.value` refused).
- Native library boundaries (`DESIGN-BASIS.md:686-700`): "Schema separates representation, decoded
  value, encoded value, decoding services, and encoding services ... Foldlab's CAS schema remains a
  checked downstream profile, not a duplicate generic carrier."
- Required proof graph, "Schema and services" (`DESIGN-BASIS.md:731`): one codec direction proved
  (`ofVal_spec`); "Schema representation well-formedness is *tested* and *reproduced*, not proved".
- DB-08 (`:293-313`): `Expr` is metaprogramming input only; persistent rows are first-order.
  DB-09 (`:315-392`): rc.112 is a versioned target profile; ProfileData/HostSpec/Binding (S0);
  scalar domain bounded with explicit refusal (DI-56). DB-11 (`:417-437`): one value carrier
  `Store.Val`; images over it (`toVal`/`ofVal`, `ofVal_toVal`, `ofVal_exact`); admission a premise.
- DESIGN-ISSUES (tracked register): DI-08 open ("Is Schema in the release ...", oldest open
  architecture question, `DESIGN-ISSUES.md:80`); DI-15 ruled+amended+landed (lit, sub, join);
  DI-35 ruled; DI-47 ruled (baseline gate; `:119`); DI-56 ruled (bounded scalar profile; scout E's
  cell-domain recommendation "not ruled", `:128`); DI-62 ruled (`:134`); DI-67 ruled 2026-09-11
  (inhabitation invariant; `int` refused at admission only; `:139`, P2a clarification `:190-194`);
  DI-78 ruled scope 2026-09-16 (general runtime collections required; contracts to freeze, `:150`);
  DI-89 ruled 2026-09-16 (rows generated from pinned declarations "into `Ty`", refusing
  function-typed, higher-kinded, variadic; `:161`); DI-91 ruled (`ofTy` not injective; `:163`);
  DI-92 ruled (`Ty.int` "the named landing place of a foreign `Schema.Int`"; `:164`); DI-95 open
  (`Codec.isSupported` wildcard; `:167`) but its rule was landed by decisions row 56 (`0a2cb898`);
  DI-97 signed exception (no carrier for an `Effect` as a value; `:169`).
- decisions.md section A "Types and schemas at the boundary" (rows 1-13, `docs/core/decisions.md:18-34`):
  row 1 (canonical schema object, AST as second carrier) open; row 2 (names for records and sums:
  (c) annotation names now, (b) `Ty.record`/`Ty.variant` before the first foreign consumer) **open,
  owner**; row 3 (`Ty.app`) not started; row 4 (checks with meaning) folded into 39; row 5 (D12's
  shape: the sound/total pair plus the S-5 gate) not started; row 6 (`ofSchema` refuses what it
  cannot represent) done `4f2fadc8`, exactness theorem unproved (row 41); row 7 (handles at the
  boundary) open; row 8 not started; row 9 folded into 39; row 10 (one `Val -> Json`) open, four
  images; row 11 (where `Schema.*` text comes from) open; row 12 moot (Transform deleted
  `b08f3b58`); row 13 (the schema/program rule) done: written into AGENTS.md (`f8c9b7fe`).
- decisions row 39 (`:85`): the Schema wipe, **ruled 2026-09-18**, "nothing deleted yet". Its
  files (`Schema/Check.lean` 1,499 lines, `Schema/EffectfulField.lean` 960, `Schema/Image.lean`,
  `Schema/Accepts.lean`, `Annotations.lean` 1,193) are all still in the tree at bc77e97f (`wc -l`, tested).
- decisions rows 42-44 ruled (generic Ref/Deferred, binder-term rows, world typing of handles);
  row 56 ruled+landed (classifier wildcards); row 68 ruled+landed (assignability differential, 600
  pairs, 594 agree, 6 cut; `renderRaw` not injective at nat/int and refOf/handle); row 96 landed
  (`Fits`); row 97 interim landed; row 108 open (numbers per face); rows 111-116 ruled 2026-10-01;
  row 117 open; row 118 open "waits on a program that needs one" (structured service carriers).
- system-map §1.1 (`docs/core/system-map.md:34-65`): Σ_app later "only if admitted, nominal data
  declarations (row 2; DB-15)"; "Not in Σ: ... structural records and variants, which are growth of
  the type language (DB-15's amendment, row 2)". §4 sorts (`:142-165`): `Representation` is the
  schema carrier, "embeddings from `Ty` (row 6)"; "Value fits type": one executable check
  (`Val.hasTy`), one proof judgment (`Fits`), "Anything else that checks a value against a type is
  a leak". §8 R3 (`:232`): "refused by DB-15 as written (records, `json`, `int`, `Err.value`); open as
  one DB-15 amendment; recursive types untracked".
- host-boundary §4.4 (`docs/core/host-boundary.md:131-163`): "Every `Ty` constructor has its
  clause" (a 20-row table; `int`: "no inhabitant today"). §5 (`:218-237`): interim rule, internal
  handle kinds refused in host row answer/error types.
- language-cut.md (dated snapshot 2026-09-18): §2 "no records or variants ... deferred (row 2)";
  §3 error payloads "profile (DESIGN-BASIS)", fix "a ruling: admit `Err.value` ... or keep tags";
  §6 ranks the cuts: records first, error payloads second.
- `Ty` today (`src/Effect4/Program/Ty.lean:37-75`): 20 constructors, no record, variant, json,
  foreign or app; `int` present (uninhabited).

### R-2. The type algebra note (`docs/research/2026-09-18-research-type-algebra.md`, tracked by force-add; reading)

- Status of the note: a read-only research seat; "No Lean ran in this seat" (§0, `:11-13`); its own
  cost figures are **assumed**. F1-F6 (`:28-35`) are read from the Lean 4.33.1 toolchain source.
  F1 nested inductive gets no derived `DecidableEq`; F2 mutual non-nested block does; F3 derived
  `Repr` goes `partial` for nested or multi-member blocks; F4 the trust gate rejects `partial`;
  F5 structural recursion goes through a nested container (cites `Schema/Fold.lean:128-171`);
  F6 well-founded recursion through `List` is supported in core.
- §1.3 recommendation (`:126-185`): keep dedicated constructors for handle sorts; when row 2 lands,
  records and variants as a **mutual spine sibling** `Ty.record (fields : Fields)`,
  `Ty.variant (cases : Fields)`, `Fields := nil | cons (name) (type : Ty) (rest)`; refuse
  `Row (String x Ty)` inside the carrier (proof field); `Ty.app` (row 3) superseded by
  `Ty.foreign (id : String) (args : Fields)`, "an opaque nominal type ... whose `sub` is invariant in
  every argument and whose `hasTy` is `false`". "B lands with row 2 and not before" (`:185`).
- §2 (`:189-407`): `sub` over a head/argument view plus a declared variance table, laws proved once
  (`subArgs_refl/trans/antisymm`, `Head.admits_mono`); "do it with row 2" (§7.2 item 6).
- §5.2-5.3 (`:697-754`): the order is sound, not complete, for value containment (`option (a|b)`
  vs `option a | option b`; `prod never nat`); keep the antichain, register the incompleteness.
- §6.3 (`:794-802`): the carrier rule: `Ty` stays first-order, non-dependent, proof-free, every
  field a `Shape` (now written in `Ty.lean:11-23`, tested by reading the header).
- §8 "Records and rows" (`:964-969`): Wand 1989, Remy 1994, Gaster-Jones 1996, Leijen 2005,
  Morris-McKinna 2019, listed under **"Literature (assumed; not read here)"** (`:942`), "row
  theories, if `Ty.record` ever needs row polymorphism rather than a closed field list".

### R-3. The 2026-09-10 boundary notes (untracked; reading)

- `2026-09-10-boundary-decisions.md`: eleven decisions under the owner's rule "fidelity ...; never
  break host code because a type at a boundary was declared narrower ...; overload rather than
  refuse" (`:7-9`). Four boundaries B-print, B-accept, B-row, B-tape (`:16-21`). Data-relevant:
  T3 tagged column = union of per-tag pairs `prod (lit tag) string` (`:57-75`); T5 `nat` stays,
  "a float carrier is the first post-v0 append" (`:87-99`); T6 `Option` vs `undefined` via the
  adapter (`:101-106`); T9 "keep the closed image for v0 (DI-62 ruled), extend by projection at
  adapters" (`:132-141`). Ratified by the owner "as they are" on 2026-09-10 (memory
  `boundary-decisions-2026-09-10.md`; not in a tracked file as a set).
- `2026-09-10-schema-at-boundaries.md` (Decision 12): the owner's words, quoted there (`:4-9`),
  "an Effect Schema representation of all boundaries ... Enforced for all Eff programs.
  Higher-order schema-native typings and utils; canonical schemas for row types." The note says it
  "also answers DI-08 ... the persisted data plane is in ... The authoring plane stays
  archive-tier" (`:11-13`). Plan: S-1 `Ty.schema`, S-2 `EffTy.document`/`Row.document`, S-3
  `Ty.encode`/`decode` with `encode_of_hasTy`, `decode_encode`, `encode_sub` (`:85-97`), S-4
  `Api.schemaOf` + printer emitting the document (`:99-111`), S-5 two truth-lane gates
  (`:113-123`); §4 the higher-order layer `TySchema (t : Ty)` "indexed by the column", combinators
  mirroring rc.112 Schema at the `Ty` level, "`struct` over named rows" (`:125-149`).
- D12 in tracked files: only module headers and docstrings (`src/Effect4/Schema/Bridge.lean:10`,
  `src/Effect4/Api.lean:135`, `Test/Codegen/SchemaGenerationContract.lean:120`; `git grep`,
  tested). DI-08 in the tracked register is still **open** (`docs/DESIGN-ISSUES.md:80`).
- `2026-09-10-program-as-schema.md`: `Eff` canonical (§1, `:26-33`); `typeMap`/`asSchema` make a
  program's control flow the reference graph of its own Schema document (§3, `:83-111`);
  annotations by address as CAS traits, "never in the bytes" (§4, `:113-129`). Its §12 example
  asks for `"returnType": "List CustomerRecord"` (`:539`), a record type the language cannot say.

### R-4. Schema consumer survey and post-Phase C §11.2 (reading)

- `2026-09-02-schema-consumer-survey.md` (untracked; pre-`Eff`, Flow-route era): rc.112 consumers
  each take one of four constraint views and thread `DecodingServices | EncodingServices` into `R`
  (§1, `:36-39`); "values and codecs are Stratum V and lower as Schema" (§3, `:166-171`); §4.5 the
  steer: "Lawful data constructs (the Optic pattern, repeated)" (`:348-371`); `SqlSchema.findAll`
  rows "arrive as `unknown`; decode failure = `SchemaError`" (`:52`). It cites modules that no longer
  exist (`Schema/Getter.lean`, `Value`, `Transformation`, `Foreign`, `Registry`; `ls src/Effect4/Schema`,
  tested). Nothing in it is a ruling ("Nothing here is a contract", `:3-4`).
- The brief's path `docs/research/2026-09-20-post-phase-c-synthesis-and-architectural-roadmap.md`
  has no §11 (`grep`, tested); the W1/W9 table is in the **tracked** `docs/core/post-phase-c-synthesis.md`
  §11.2 (`:720-736`), whose status line says "reviewed proposal and evidence snapshot; **not an owner
  ruling**" (`:4`). W1 (`:725`): "records/variants, collections, equality/hash/order ... exact
  embeddings"; next deliverable "the selected record/collection/numeric families"; "Arbitrary error
  payloads need the existing basis ruling amended, not silently enabled". W9 (`:733`): "execute row
  39, then admit needed parsing/transform behavior through typed Eff holes"; "Foreign
  transformations remain named and refused where meaning is required". §11.3 (`:759-760`) assigns
  Array, Chunk, Record, Struct, Tuple, HashMap, ... and BigInt, Data, Number, Option, Result,
  String to W1, schema/codecs through W9.

### R-5. Charter, model probe, Codex audit (reading)

- `2026-09-16-core-goals-and-end-state.md` (the charter; untracked): §4.4 "The tag test, records and
  sums (S3c/S4, no new syntax)" (`:458-474`): sums are DI-15 tagged unions `union (prod (lit "A") T)`,
  records "are nested `prod`"; R7 (`:618-622`): "replace 'records and sums' with two small items ...
  neither needs a constructor"; §8 (`:715-716`): "`Val` is a fixed carrier with numeric heaps, so records
  and sums are encodings". §10 charter (`:753-815`): "Data in the IR: one stored tree; positional
  binders; every authoring-layer model is data".
- `2026-09-30-model-probe/synthesis.md` R3 (`:237-275`): shape = the `Ty`/`Fields` spine with
  `Ty.foreign id args` as the nominal form; per constructor: `Fits` clause, exact embedding to Schema
  and JSON (K2), generated folds, assignability (row 68), inhabitance "DI-67 restated over `Fits`:
  `forall admitted tau, tau.normalize = never or exists w v, Fits w v tau`". "Status: refused by a
  settled decision." Programs need records (5 of 5), structured error payloads (4 of 5), signed
  numbers (p5), a decode route (p1, p2); also owed collections, `Val.eqAt`, recursive types ("which no
  register row covers"). §3.1 R3 pedigree (`:771`): F1-F6 read; "the record literature (assumed, type
  algebra §8)". §3.3 (`:833`): "DB-15 ... stands; **blocks R3**"; "Native library boundaries"
  (the basis's only Schema-calculus text) "**conflicts** with DI-11 and DI-89 ... retire" (`:838`).
  D10 (`:1138-1149`): keep the refusals now; rule row 2 stage (c) now; rule the packet together when
  the first real program is taken on; open the recursive-types row now.
- Programs seat (`2026-09-30-model-probe/programs/note.md`): `Schema.decodeUnknownEffect(User)(row)`
  over JSON-text cells is "**absent**: no decode route in `Eff`" and "`ofSchema_schema` is a
  retraction of the type's schema, not a decode in a program" (`:121`); P5 (`:318-328`) offers two
  models: the host row answers the decoded typed value (record answer type, checked by `Fits`), or
  decoding is an `Eff` hole with an exact embedding under the schema-and-program rule; "A JSON value is
  a recursive type".
- Codex audit (`2026-09-30-codex-review-model-probe/audit.md`) §5 (`:228-278`) makes no R3 remark
  beyond "The stateful catalogue's primitive needs map to R3/R4/R7" (`:269-270`); `grep` for R3,
  DB-15, record, D10, JSON, Schema finds nothing else (tested). So R3's shape in system-map §8 is the
  synthesis's, unamended.
- The owner ruled D1-D6 only (rows 111-116, 2026-10-01). D10 is not ruled; no decisions row or DI row
  exists for recursive types (`grep -i recursive` over the four tracked registers, tested).

### R-6. The other Schema research, and the code that exists (reading unless marked)

- `2026-09-10-schema-composition-synthesis.md` (untracked): "transforms live in `Eff` because the
  persisted schema representation cannot hold them" (§0 item 1, `:12-16`); "A transform is a pair of
  `Eff` programs at a one-slot environment" (§1, `:50`); "Recursion is references, not `mu`; a
  `Document` is a guarded letrec" (`:56`); S6 "The lawful codec carrier is a prism, already present as
  `Canonical`/`Image`" (`:75-77`); §5 "Rows the owner writes (nothing above is a ruling until then)",
  first among them DI-08 (`:122-126`). DI-08 was never written (still open, R-1).
- `2026-09-11-higher-order-schema-api-and-functions.md` (untracked), "Status: Approved for
  Implementation": `Endpoint`, `ApiSpec`, `SchemaFn` (a Lean function `run : Val -> Option Val` in a
  structure), `SchemaTransform` (an `Eff` at a one-slot environment) and `Ty.record` as "canonical
  nested tagged products". Implemented at `e75d9e61` (2026-09-11) in `Schema/Endpoint.lean`
  (`def record : List (String x Ty) -> Ty`, nested `prod (tagged k v)`), cut at `b08f3b58`
  (2026-09-18) with `Schema/Transform.lean` (`git show`, tested).
- Scout C (`2026-09-17-scout-schema-and-algebra-simplification.md`, tracked by force-add) §2.4 and
  P10 (`:690-700`): `Ty.data (name : String)`, a **nominal** tree type: "the missing `.reference` arm
  of `Ty.ofSchema`", a `ShapeDoc` carried by the `Signature`, values as `Val.ctor`, one eliminator
  subsuming `Decision.option` and `Decision.tag`; "Any user-declared Lean inductive as language data";
  compiled probe. Findings ledger (`2026-09-17-scout-findings-ledger.md:68`, tracked): C-P10
  "queued after the reader line; invariant by name, the `ShapeDoc` on the `Signature`".
- Scout D (`2026-09-17-schema-interop-scout-D.md`, tracked): `Ty.schema`'s image uses 9 of 22
  tags, never `objects`, `reference`, `suspend` (§6, `:97-118`); "the estate carries two incompatible
  sum encodings at once"; D-1 (`:206-208`) "(c), then (b)"; D12's enforcement "has no reader" (§7.5).
  It calls charter §4.4 "The ruling (core-goals §4.4)" (`:208`), though that note is untracked.
- Scout E (`2026-09-17-schema-ast-lowering-scout-E.md`, tracked): Design A, "`Ty` embeds with a left
  inverse"; "give it the one thing it lacks: `Ty.app`" (§4); §5 the `Decision.tag` eliminator reads
  `.list [.str t, payload]`, so (c) annotation names now, (b) `Ty.record`/`Ty.variant` before the
  first foreign consumer (E-5), which "forces `Val.tagPayload?` to gain an object leg"; E-3 D12 as
  two claims (Lean sound/total pair, host S-5 gate). These became decisions rows 1-5.
- `2026-09-17-ontology-and-do-now-probe.md` §3 (tracked): "About 1,200 lines carry the estate's two
  real schema claims: the `Ty` codec agrees with rc.112 (`schema-codec`), and a `Document` printed as
  `Schema.Struct` text decodes in rc.112 (`schema-ts`)" (§3.2); the wipe list (§3.4) that row 39 ruled.
- `SCHEMA-CUTOVER.md` (untracked, "frozen design input, 2026-09-02", Flow era): one first-order
  representation modelled on rc.112's persisted `SchemaRepresentation.Document`; "Recursive meaning is
  an inductive or fixed-point judgment over the document"; "No universal round-trip law is attached to
  `Codec`" with eleven independent codec properties. Its denotation, getter, transformation and
  registry lanes were never built or were deleted.
- `2026-09-08-ingest-census.md` (untracked, run by the ingest seat, not rerun here): over 34 pinned
  projects, the most frequent unknown heads are `Schema.Struct` 2,032 and
  `Schema.decodeUnknownEffect` 547, then `Schema.Union` 265, `Schema.Literals` 138,
  `Schema.decodeUnknownSync` 92, `Schema.Array` 79, `Schema.brand` 55, `Schema.decodeUnknownOption` 50,
  `Schema.Record` 48, `Schema.TaggedStruct` 44 (`:39-56`). A finite census with the caveats of
  DI-48 and its own note (a unit can count twice on engine disagreement).
- `2026-09-08-host-rows-slice.md` §7 decision 3 (untracked): "**`string` in this slice, as step 1.**
  Records as `list (prod string string)` ... no `json` leaf in `Ty`" (`:500-501`); §2.1 gives the
  reason: at the time `Val.hasTy` had no `.string` or `.option` arm and "`Ty` has no sum"
  (`:190-202`). DB-15's refusals descend from this step-1 choice.
- Code at bc77e97f (reading): `src/Effect4/Schema/` holds `Representation` (22 tags), `Payload`,
  `Document`, `Bridge` (`schema`, `ofSchema`, `ofSchema_schema`, `effDocument`, `rowDocument`),
  `Codec` (type-directed JSON, S-3 laws in `Laws/Schema/Codec.lean:16-106`), `Fold` (generated),
  and the parts row 39 wipes (`Check`, `EffectfulField`, `Image`, `Accepts`, most of `Annotations`).
  `Api.schemaOf` still exists (`src/Effect4/Api.lean:137`). `Store.render` still lives in
  `Store/Domain/Shape.lean:425`. The store's own description language `Shape` has named records
  (`struct name fields`), tagged sums (`sum name cases`) and named references (`named n`)
  (`Store/Domain/Shape.lean:60-82`), rendered to schema `struct` and `_tag` variants; the Dialect
  battery pins that `Ty` cannot read them (`Test/Schema/DialectContract.lean:1-19`).
- `Codec.isSupported` closes with an explicit `| _ => false` (`src/Effect4/Schema/Codec.lean:51-55`),
  so DI-95 is repaired in code (decisions row 56, `0a2cb898`) while the DI-95 row still reads "open".
- Atoms (`src/Effect4/Machine/Term.lean:146-164`): 33, including list and string atoms; none parses
  text to a number or JSON, and none turns a number into text (reading; the programs seat's P5).
- `machine-state.md` §7 (`:199`): a keyed table owes "equality and hash agree; stated duplicate and
  missing policies; stated iteration order".
- Papers review `2026-09-05-effects-papers-review.md` §1.2 and A5 (`:72-80`, `:494-506`): Mattick,
  *Specifying Hyperdocuments with Algebraic Methods* (2014), read in full: accepted values are the
  ground terms of a signature and every view is the unique homomorphism; proposes `print_conforms :
  accepts doc v = true -> Conforms (document doc) (print doc v)` over `Store.Shape`. No `Conforms`
  exists (`grep`, tested).
- Lit-papers Q4 (`2026-09-07-lit-papers.md:195-223`): Leijen, *Type Directed Compilation of
  Row-Typed Algebraic Effects* (2017) §3, §3.2 and Hillerstrom-Lindley 2018, read, about **effect
  rows**, not record rows: "no row polymorphism, no presence types, no duplicate labels" for the
  profile. No lit-papers question touches records, schemas or JSON (`grep`, tested).

## Appendix B. What was read, and how much

- **In full:**
  - DB-08, DB-09, DB-11 and DB-15 (`docs/DESIGN-BASIS.md:293-437`, `:584-684`), with the basis's
    closing sections;
  - `docs/DESIGN-ISSUES.md`, all rows;
  - `docs/core/decisions.md` section A (rows 1–13), rows 35–36, 39, 41–44, 56, 68–69 and 91–118, and
    the order section (the rest of E and F read to their first 240 characters);
  - `docs/core/system-map.md`;
  - `docs/core/host-boundary.md`;
  - `docs/core/language-cut.md`;
  - coherence-principle §1 (C), §2's census table, §4b, F-6 and F-7, the literature, and "Where
    the tree contradicted the brief";
  - post-Phase C §11;
  - the boundary-decisions note;
  - schema-at-boundaries;
  - program-as-schema;
  - the type-algebra note;
  - the schema-composition synthesis;
  - the 2026-09-11 higher-order schema note;
  - `Schema/Bridge.lean`, `Schema/Codec.lean`, `Laws/Schema/Codec.lean`;
  - `Fits` (`Membership.lean:1-150`), `Val.hasTy` (`Program/Typed.lean:34-105`);
  - `Program/Admission.lean:1-200`.
- **By section, after a whole-file `grep` for records, schema, JSON, payload, int, variant, struct,
  collection, equality:**
  - the charter (§4.4, §8, §10, R7);
  - the model-probe synthesis (§1, §2.1, R3, §3, §5.5, D10–D13);
  - the programs seat (P5, the summary table);
  - the Codex audit (header, §5, §6);
  - the consumer survey (§§0–4, 4.4–9);
  - lit-papers (Q4, §D);
  - the papers review (§0, §1.2, A5);
  - scouts C (§0, §2.4, P10), D (summary, §6, §7.5, §10) and E (verdict, §§1, 3–5, 14);
  - the ontology probe §3;
  - `SCHEMA-CUTOVER.md` (Decision, operational rulings, codec law classification);
  - the host-rows slice (§2.1, §7);
  - the ingest census (head counts);
  - the findings ledger (C-P10 and its parked items).
- **Not read:** the other seats' notes in this probe folder (in progress); the standards survey;
  the equality and elimination scout notes that DI-35 and DI-09 cite.

