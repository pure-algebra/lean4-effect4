# Effect4 design map

This document is the framework the other design documents hang from. It names the layers of
the reification, the representations each layer holds, the conversions between them and the
grade of evidence each conversion carries today, the places where one fact is held twice
without a gate, the literature each layer sits in, and the register rows that belong to it.
`docs/DESIGN-BASIS.md` holds what is settled, `docs/DESIGN-ISSUES.md` what is open,
`docs/ARCHITECTURE.md` the tree, `docs/GENERATED.md` the generated families. This map is
cited by section, never by line. It was opened 2026-09-09 from the second design-scout round;
its sections change when a register row moves to basis or a guarantee changes.

## The grades of evidence

Every claim that two representations agree is held by exactly one of four things, and the
vocabulary is the build-systems one (Mokhov, Mitchell and Peyton Jones, *Build Systems à la
Carte*, 2018):

1. **A theorem** — `decode_encode`, `read_print`, `answer_typed`, an `Image` law.
2. **A constructive check** — a gate that regenerates and compares bytes, or a corpus
   differential against an oracle: the hex and `.bin`/`.json`/`.ty` goldens, the printed-corpus
   comparison, the truth column's exit and schedule agreement.
3. **A verifying trace** — a `cut-from:` stamp, which proves the inputs are the ones the
   producer saw and nothing about the committed bytes.
4. **Nothing** — a hand-written copy held equal by attention.

The words a claim carries name the same four things from the claim's side (DI-32, ruled
2026-09-09): **proved** for a theorem, **reproduced** for a byte comparison or a corpus
differential, **tested** for a finite checker run over named inputs (`tsc`, a `#guard`, a host
fixture), **stamped** for a verifying trace. They **co-occur** — one slice's evidence is often
"proved; reproduced (goldens); tested (`tsc`)" — and a finite checker run is *tested*, never
*reproduced*. `docs/GENERATED.md` carries the words family by family.

The map names the grade at every seam. Drift lives mostly where the grade is four, and the cure
is usually the same shape: one source of truth, projections generated from it, conformance
vectors cut from it, gates that are incremental. A theorem is worth stating where it buys a
claim (round trip, compatibility, soundness) and nowhere else.

Two cautions the Codex seat added, both right. The grades are not one ladder: a reproduction
and a behavioural differential establish different facts, and a stamp establishes provenance
only; a claim should say which dimension it holds — proved, reproduced, tested over a named
observer and corpus, or stamped — and drift can survive a theorem whose scope misses the
changed edge or a corpus whose observer drops the changed payload (the truth comparator
compares a defect and an interrupt by kind only). And a shared source of truth should retire
accidental mirrors, not every independent oracle: the hand-written wire fixture and the
literal hex pins catch correlated generator errors that regenerated goldens cannot.

The register also carries a second, cross-cutting classification — six kinds of obligation
(meaning; static semantics; representation and evolution; language interfaces; reproducible
production and evidence; modularity and ownership) — because one change usually touches
several layers, and the kind is what makes its cost visible.

## The layers

| layer | what it holds | state |
| --- | --- | --- |
| L1 reference semantics | the machine (fibers, scopes, the wake list, stores, the layer memo) and the algebra it denotes into; the run API and its refusals | solid; its open rows are about the *reach* of the agreement, not its content |
| L2 the type layer | the `Eff` object language, `Ty`, the row and table discipline, the error and requirement channels, the typing algorithm and the value typing | routed faithfully, coarse in content; no declarative system, no subtyping, one uninhabited binder type |
| L3 representations and bytes | the value carrier, canonical bytes and the content-addressed store, the wire and its ordinals, the JSON forms, the World description and its OCaml and TypeScript projections, the goldens, the stamps | the rank-one rework risks live here: identity, ordinals, four independent reflections of one description |
| L4 the faces | the printer and readers between `Eff` and TypeScript source, the foreign ingest with its two contracts, the truth harness and its tapes, the OCaml face as a conformance suite, the runtime coverage census | the largest subsystem with no contract packet; classification by rule order; the printed image never type-checked |
| L5 process | the generators and their families, the stamps and gates, the one-compiler lane, the basis and the register | the drift-removal machinery; two stamp protocols; five families carried by hand |

## L1 — the reference semantics

The machine is the reference: fibers with continuations, scopes and finalizers, the wake list,
the stores, the layer memo keyed on paths, and the run API (`Api.run`, `runSync`, `replay`,
`replayChecked`) with a first-order refusal alphabet and frontiers that are never failures. It
denotes into the `Effects` package's algebra (signatures, programs, handlers, initiality); the
error channel lives in the *carrier* (`ExitV`), not in the signature, so the algebra needs
nothing for any richer error type, and its own claim boundary says it provides no error
algebra and no requirement polymorphism.

Guarantees: `run_eq_ref` over the compile route — stated with no row-table or oracle-answer
parameter, so it covers the empty profile and says nothing yet about an external package
execution (DI-57); `run_eq_meaning` over the single-fiber straight-line fragment
(`Straight`), which excludes fork, `gen`, loops, layers and async (DI-07); the sync-route row
preservation `answer_typed`; the axiom ceiling `[propext, Quot.sound]` with a named
`Classical.choice` boundary (DI-30). Replay consumes a tape's answers and does not yet check
the recorded call envelope against the row it answers (DI-58). Rows: DI-07, DI-10, DI-11,
DI-17, DI-23, DI-30, DI-31, DI-57, DI-58.

Literature: Plotkin and Pretnar, handlers of algebraic effects (2009/2013); Bauer and Pretnar,
an effect system for handlers (2013); Hillerström and Lindley, liberating effects with rows and
handlers (2016) for the machine shape; de Vilhena and Pottier for the bind-law side condition
the papers review named G8 (DI-10).

## L2 — the type layer

The object language is `Eff Op` — 27 constructors, first-order, binding values in `bind`,
handlers and generators, with no abstraction form — typed by a monomorphic type-and-effect
system in the Lucassen–Gifford line: one
judgment `Σ; Γ ⊢ e : ⟨A, E, R⟩` where `A` and `E` are ground `Ty` (fifteen constructors
including an untagged TypeScript union) and `R` is a finite label set of service keys whose
labels carry a closed type code. Its representations are five and independent: the
algorithmic checker (`Typing.lean`), the extrinsic value typing (`Val.hasTy`), the hand-written
OCaml checker, the intrinsic OCaml GADT surface, and the generated TypeScript reflections. The
first two are proved to agree only for terms; the middle two are held to the first by 42 `.ty`
goldens (grade two); the last is generated (grade three).

Guarantees: weakening in all six forms; syntactic soundness for the term language; row
preservation for the sync route and for the external route's success branch. Non-guarantees,
each named: no declarative rule system, so no rule can be cited or inverted, and the two
typing faces can only be compared by goldens — and already disagree on a program Lean accepts
(DI-54); no subtype relation, so the answer column is discrete where the error and requirement
columns are semilattices (DI-38); the union's canonicalisation is one level deep, so `Ty`
equality is finer than the target's below the top level (DI-53); four of fifteen `Ty`
constructors are uninhabited, and one of them, `causeOf`, is what a catch handler's binder is
typed at, so the value-typing invariant fails at every handler point and preservation for
programs cannot yet be stated (DI-09, DI-17); the failure branch of an external answer gained its
theorem on 2026-09-09 (`external_error_typed`, `external_oracle_error_typed`, in `23e5717`),
while `errAdmits` is still not inverse to `errOf` until S2's admissible image lands (DI-26,
DI-62). The error channel is write-only for a program until the elimination form and the cause
atoms land (DI-09); the error's content is
the DB-15 pair, ruled as the reason tag and the driver message (DI-00), and a literal type
(`Ty.lit`) with a subtype relation is the designed next step (DI-15, DI-55).

Drift points: the atom table (fourteen copies, three stale — DI-40); `Ty` (twenty copies,
thirteen hand-written, no count guard); the typing algorithm written three times; the package
rows' declared types unchecked against the package (DI-29); the `Forms` arity table
re-implemented in both engines (DI-39).

Rows: DI-09, DI-10, DI-12, DI-15, DI-17, DI-20, DI-26, DI-28, DI-35, DI-38, DI-53, DI-54,
DI-55, DI-61, DI-62, DI-63; from the neighbouring layers DI-29, DI-40, DI-41, DI-49.

Literature: Lucassen and Gifford (1988) and Talpin and Jouvelot (1992) for effect sets and
subeffecting; Bauer and Pretnar (2013) and Leijen (2014, 2017) for handler typing and
type-directed compilation of effects; Pierce, *Types and Programming Languages*, §15.5 and
§16.3, for the join rule the two-branch forms need; Dolan, *Algebraic Subtyping* (2017), for the
lattice discipline and not its inference; Frisch, Castagna and Benzaken, *Semantic Subtyping*
(2008), for the equivalence the shallow canonicalisation lacks; Wright and Felleisen (1994) for
the soundness shape; Reynolds (2000) for the intrinsic/extrinsic split the two OCaml files
embody. Row polymorphism and effect polymorphism are refused on the ground that `Eff` has no
polymorphic binder to quantify over — it binds values through environments in `bind`, catch
handlers and generators, but has no abstraction form — not on cost; that supports today's
profile restriction and does not make polymorphism impossible later (DI-20, DI-28). Each
target's scalar domain is its own question: the generated schema admits values the wire
refuses (DI-56).

## L3 — representations and bytes

One byte language and one value tree, of which every *stored* representation is a projection;
host objects, runtime layouts and observations are not, and the identities in play differ —
logical identity, structural and byte identity, a content address, a table-relative key, a
live handle — and must not be conflated. The kernel is the frame `tag :: be64 len ++ payload`,
the twelve-tag value tree, and the `Canonical` class
whose laws make a carrier an exact image of that tree — a partial isomorphism, not a lens. From
those, once and for every carrier: the bytes, the exact decoder, `decode_encode`,
`decode_exact`, `encode_injective` and the payload digest (grade one). Above the kernel the
layer holds six representations of a program (Lean term, value tree, canonical bytes, JSON,
printed TypeScript, CAS node), four of a type (`Ty`, its OCaml and TypeScript twins, a rendered
TypeScript string), three byte alphabets (`Store.Tag`, `Store.Kind`, `HandleKind`) and two
identity schemes — content (a digest of node bytes) and position (service keys, layer paths,
package row indices) — which is the distinction a reader gets wrong first.

Guarantees by grade: the wire theorems (one); the 400-program `.eff` and JSON differentials,
the eight hex goldens and the 42 `.bin`/`.json` goldens (two); every `cut-from` stamp (three);
and the hand copies (four): seventeen ordinal copies, six by hand; four independent reflections
of the family list (the World blocks, the generator manifest, the wire tool's hand list, the
LCNF types — DI-13); a hand value tree that cuts the goldens and is both faces' JSON oracle,
compared with nothing (DI-42); six families with host byte writers and no Lean encoder
(DI-41); a tag alphabet with no census (DI-43); Lean's kind table behind OCaml's (DI-25); the
CAS goldens at grade three only (DI-45).

The partition of that description has three owners, ruled 2026-09-09 (DI-13, DI-14, DI-22), and
they are not one table. The **World** describes *structural identities* — families, constructors
in declaration order, fields, tags — and the wire framing and the target's runtime layout are
**separate columns** of it, never one fixed family list: the LCNF route follows compiler erasure
and a dynamically discovered closure, and a target's in-memory representation is free wherever no
byte writer sees it. The **profile** owns DB-09's data (scalar domains, admitted operations,
adapter identities, the error projection). The **link table** owns program content — which
package row an index names. The World closes only when three consumers read it: the generator
manifest checked equal to its family list, the wire tool's hand lists replaced by a World read,
and the engine's mirror generated from or checked against it (S5b); the six Lean encoders (DI-41)
are a precondition, not the closure.

Beside it, and independent of the generator that will read it, is the **retained baseline**
(DI-47): `Test/fixtures/baseline/66ee4657/README.md` and its four files — the World reflection as
JSON, the OCaml and wire manifests, the golden digests — frozen at `66ee4657` before S2's
`Err.text` and `Defect.error`, S3a's `Eff.catchIf` and S4b's `Ty.lit`, promoted only by a named
command and never written by a generator, so a diff there is a review event. The compatibility
gate compares the reflected description against it and refuses on four counts — old content still
readable, old bytes unchanged, decoding still exact, execution still permitted — and the two `⊑`
theorems follow it. This is what replaces the ordinal-ledger design (DI-02, DI-03).

Rows: DI-01, DI-02, DI-03, DI-04, DI-05, DI-06, DI-11, DI-13, DI-14, DI-18, DI-22, DI-25,
DI-32, DI-33, DI-40, DI-41, DI-42, DI-43, DI-44, DI-45, DI-46, DI-47, DI-64. The single change
that closes the most of them is one World datum with a build-time pin and an order relation under
which append-only is a theorem rather than a review rule (DI-47).

Literature: deterministic serialization (RFC 8949 §4.2; ITU-T X.690 DER); interface
description and one-specification-many-bindings (Cap'n Proto; the WebAssembly specification
with its reference interpreter and conformance suite); schema evolution (Protocol Buffers field
numbers; Avro schema resolution); content addressing with a separate name layer (IPLD and
CIDs, Unison, Nix); build provenance (Mokhov, Mitchell and Peyton Jones, 2018).

## L4 — the faces

One `Eff` program has several representations that must agree, and each pair is held by a
different kind of evidence. The Lean printer and the Lean reader are a partial isomorphism:
both round-trip laws are theorems (`read_print_native`, `read_exact_native`, premised on
`LawfulTable`), and the reader's refusal alphabet names the places rc.112's surface genuinely
loses information, which is why a reader that guessed would be wrong rather than unproved. The
TypeScript printer-image reader is a third implementation of the same relation, held by byte
comparison against Lean-produced oracles over a generated corpus, with its head coverage held
by the type checker because its head union is generated. The two foreign engines are island
recognizers of a sub-language of rc.112, sharing no recognition code and held only by agreement
with each other plus, where an oracle exists, equality with Lean; their refusals are a closed,
exhaustive, injectively coded taxonomy owned in Lean whose classification is still a function
of rule order rather than of the input (DI-48). The printed image is a sub-language of the
foreign one and the two contracts differ on three axes — the admitted language, the refusal
discipline, the service-key numbering — which is a ruling, not an implementation detail
(DI-37). The truth harness is a bounded differential against rc.112 over a frozen corpus at a
pinned host, single-fiber, with recorded tapes as a two-way byte obligation (DI-23); it is not
a bisimulation. The OCaml face is a conformance suite: a second implementation of the wire, the
JSON and the typing, checked against goldens the Lean side cuts, with a generator that refuses
to write when the corpus fails to reach a constructor — the model the OCaml engine's
acceptance test should follow (DI-19). The runtime coverage census is the traceability matrix
for rc.112's runtime, not for this layer.

Non-guarantees: no contract packet covers the printer, either reader, the ingest, the truth
harness or the OCaml face (DI-50); the printed image is executed and parsed but never
type-checked (DI-49); a program with a non-empty requirement row prints untyped (DI-24) — and
four of the six host programs have such a row only because `effTy`'s `.scoped` arm does not
discharge `Scope` as rc.112 does, so they print untyped for a requirement the target does not
give them (DI-63).

Drift points: the engines' atom sets and handler lists (DI-40); the truth prelude's hand
transcription and the import header copied into every generated module; the external corpus
and its pins (DI-34); the wire differential's hand equality list (DI-52); prefix-less citations
the source gate cannot see (DI-51).

Rows: DI-19, DI-21, DI-23, DI-24, DI-27, DI-29, DI-34, DI-37, DI-39, DI-40, DI-48, DI-49,
DI-50, DI-51, DI-52, DI-59, DI-63; the faces halves of DI-09 and DI-15.

Literature that fits: Rendel and Ostermann, invertible syntax descriptions (2010) — the tree
instantiates both laws; Moonen, island grammars (2001), the honest name for the engines; Kim
et al. (ASE 2017), two lifters differentially tested; Le, Afshari and Su (PLDI 2014), the
metamorphic corpus is EMI-shaped; McKeeman, differential testing (1998); O'Callahan et al., rr
(2017), for what a tape proves; Haas et al. (PLDI 2017) and the WebAssembly reference
interpreter; Gotel and Finkelstein (1994) for traceability. False friends today, with the
reason: lenses (a `put` here would guess); decompilation into logic (no formal semantics on
the rc.112 side — ingest can only be recognition plus measured fidelity). Translation
validation does not describe today's dual-recognizer tests, but it is a future option for a
bounded fragment once a source-to-target semantic relation is specified (Alive2 is the model),
so the decision is whether that relation is worth modelling, not whether the technique applies.

## L5 — process

The generators and their ten families, five of which run under one command and five of which
are carried by hand — the ingest README has its own renderer and gate but sits outside that
command (DI-33); the stamps (grade three) and the byte-comparing gates (grade two);
the one-compiler lane under which every acceptance is a serial walk; the basis for what is
settled and the register for what is open, with the rule that a ruling is not made until it is
written into a tracked file. Drift points: two stamp protocols (DI-32); the generated-file map
checked in one direction only (DI-44); a self-test pin outside every gate that stayed stale
for a slice; the ingest README with no producer; citations into gitignored notes accepted
without resolution (DI-51); tracked records already wrong (listed in the register).

Rows: DI-16, DI-18, DI-27, DI-30, DI-32, DI-33, DI-44, DI-45, DI-51.

Literature: Mokhov, Mitchell and Peyton Jones (2018) for what a trace means; reproducible
builds; Nygard's architecture decision records for the register's shape; W3C PROV for
provenance.

## Where the drift is removed first

The order is the foundation settlement's, ratified as **S0** (2026-09-09). Each item names the
register rows it closes and the evidence words it must carry (DI-32); a slice is finished when
its rows are closed *and* its evidence exists, not when its code compiles.

1. **S0 — the decision commit and the baseline.** Every ruled row of the register, the DB-09 and
   DB-15 amendments, the two exclusion lines, this map's §L2 and §L3 corrections,
   `docs/GENERATED.md`'s evidence words, three counterexample rows, `known-red.txt`'s two
   reasons, and the retained baseline frozen before any alphabet moves (DI-47, DI-02, DI-03,
   DI-13, DI-14, DI-18, DI-19, DI-20, DI-27, DI-28, DI-32, DI-37). Evidence: stamped.
2. **S1a — core admission.** `Signature.dom` read in the two typing arms; the shared `asyncRoute`
   dispatcher, so `perform` and `callback` compile alike at an async or external op;
   `Api.checkTable`, `Api.admitProgram` and `runAdmitted`, with the print image a *separate*
   certificate; the 55 × 2 invocation matrix (DI-54, DI-61, DI-60, DI-22, DI-23, DI-24, DI-51). Evidence: proved (the
   compiler equality); tested (the matrix, the replay fixtures).
3. **S2 — the error foundation.** `supportedErrTy` beside `Ty`, `Program/ErrorImage.lean` below
   `Native`, `Err.text`, `Defect.error`, the three typing arms, the `.causeOf` and `.exitOf`
   membership arms, `FitsIn` (DI-62, DI-26, DI-31, DI-17). Evidence: proved; reproduced (goldens,
   tapes); tested (truth fixtures). It shares two files with S1a and follows it in one lane.
4. **S6a — the small host specification.** `ProfileData`, `HostSpec` and `Binding` as DB-09 now
   describes them; the `Envelope` predicate with at most one accepted completion per call;
   `run_eq_ref` stated exactly (DI-57, DI-58). Evidence: proved (local transitions, envelope
   laws).
5. **S1b — the adapter and the type gate.** The pair made at the row adapter with the raw
   diagnostics kept beside it; `tsc --noEmit` over the truth modules and the printed corpus; the
   atom set emitted once and read by both engines and the prelude; the tree-to-map walk; the faces
   packet; the inclusion test (DI-59, DI-49, DI-40, DI-44, DI-33, DI-37, DI-50). Evidence: tested
   (bun, `tsc`); reproduced (tapes, goldens).
6. **S3a — the elimination form.** `Eff.catchIf` and the four cause atoms under the first-`Fail`
   rule, `eq` at `.string` with `or`/`and`, the `Forms` rows and both engines' pipe segment
   (DI-09, DI-35, DI-07, DI-39). Evidence: proved (the compiler proof); reproduced; tested.
7. **S4a → S4b → S4c — the type algebra**, three ratifications, never one: deep `normalize` with
   the laws stated through it (DI-53); then `Ty.lit` with `Ty.sub` and `hasTy_sub` (DI-15, DI-55);
   then the answer join as a least upper bound (DI-38). Evidence: proved; reproduced (`.ty`);
   tested (`tsc`).
8. **S5a → S5b — generation and the World.** Six Lean encoders with a metadata fixture inventory,
   the hand value tree cross-checked, the tag census (DI-41, DI-42, DI-43, DI-45); then the three
   World consumers, the baseline gate and the js_of_ocaml framing repair as its own bounded commit
   (DI-13, DI-14, DI-47, DI-18, DI-52, DI-56). Evidence: proved (encoders, tags); reproduced
   (baseline, vectors).
9. **S6b — envelopes in replay, the table-aware reference, one host integration** (DI-58, DI-57,
   DI-29, DI-24's spelling, DI-56's refusal outcome, the third package). Evidence: tested (host);
   proved (envelope, then the reference).

The theorems in that order are few and each buys a claim: the compiler's invocation equality, the
error image's round trips, the envelope's one-completion law, normalisation and subtyping with
their monotonicity, the compatibility relation, and — last, once `Reached` is defined — the
preservation invariant. Everything else is generation, pins and one-line fixes.

The Codex seat proposed a complementary sequence with reviewable stopping points — state the
boundary as a faces and host contract packet first; close the demonstrated local gaps
(DI-54, DI-40, DI-22, DI-49, DI-29, DI-56); decide the error and type slice; consolidate the
descriptions and canonical metadata; establish publication and evolution; then broaden the
semantic and host claims (DI-57, DI-58) — and one small experiment to validate the
abstractions before scaling them: follow a single host row end to end, from its stable name
and index through its types, values, bytes, printed call, shim, recorded success and failure,
allocation, replay and observer, with one positive case, one malformed request, one failure
and one table reordering.
