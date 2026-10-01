# Data probe synthesis (2026-10-01): full typing with records and JSON, and what "native schema support" is

The entry document of the data probe. It reads the four seat notes (tree, pedigree, effect, programs)
and their four verifications, reruns the probes they rest on, adds one model probe, and proposes the
owner's decisions. Research only: nothing here is a ruling until a row is written into
`docs/core/decisions.md` or another tracked file.

## The one thing

**Full typing with records and JSON is not a design we have, and native schema support is only
partly determined.** Tracked files hold a rule (AGENTS.md "Schema and program"), DB-15's refusals (no
record type in `Ty`, no `json` leaf, `int` uninhabited, no `Err.value`) and a description plane
(`Ty → Schema` and a type-directed JSON codec: both proved retractions, neither exact today, neither on
the host reply path). Decision 12 and the 2026-09-10 boundary rule live only in gitignored notes.
Records, their value encoding, decoding inside a program, error payloads, signed numbers and recursive
types have no ruling.

**The probe narrows records to one smallest coherent design, for the owner to rule as row 119:**
`record (fields : List (String × Ty))` appended to `Ty`, fields in a canonical order by name, values
positional (`ctor 0`, no new `Val` frame), exact subtyping, width projected by the row adapter at the
boundary and refused by name inside a program. It rests on three proved facts and one cost:
- width with positional values is unsound (proved), so positional values mean exact subtyping;
- reading fields in written order breaks `hasTy_normalize` (proved);
- reading them in canonical order keeps that law with no premise and stays a fold (proved here, in a
  model);
- the alternative, labeled values with width, needs a new `Val` frame (16 compile-forced definitions
  and the store codecs) and a rule for the entries a type does not name.

**Nothing changes for Codex.** Its branch, read from the refs, has D and F done but unmerged (its
newest commit, `c42f4a46`, records that D can merge through `fa5add20`), and G, H1 and H2 part one each
held on an owner decision that has nothing to do with data. The first data slice
(records only; acceptance: p2's handler authored, checked, run, printed and read back) re-cuts the
generated groups F just re-cut. So it starts after F is merged (not only D) and, by default, after the
M5–M7 milestone.

**Now, on paper:**
- rule rows 119, 122, 127 and 128;
- register DI-67's inhabitance gap (`prod never nat` and `except never never` are admitted although
  empty);
- add one sentence to the M5–M7 brief (row 132).

---

## 0. Base, inputs, evidence words, counting rule

- **Base.** `refactor/phase1-phase3` at `ba9783c3`, which is the merge `bc77e97f` (items A and C of
  slice 6) plus one documents-only commit; `git status` is clean before and after this seat
  (tested). Codex's branch `codex/slice6-fixes` was read from the main repository's refs with
  `git log`/`git show` only (§7); the worktree `/Users/pooks/Dev/lean4-effect4-slice6` was not touched.
- **Inputs.** `tree/`, `pedigree/`, `effect/`, `programs/` (`note.md` and `verify.md` each, read in
  full), and the authorities: `AGENTS.md` (vocabulary), `docs/core/system-map.md` §1.1, §4, §5, §8,
  `docs/DESIGN-BASIS.md` DB-15 (`:584-683`), `docs/DESIGN-ISSUES.md` (DI-08, -15, -17, -35, -47, -56,
  -62, -67, -78, -89, -91, -92, -95), `docs/core/decisions.md` (rows 1–13, 35, 39, 41, 68, 108–118 and
  the order), `docs/core/host-boundary.md` §4.4, §5, the slice 6 brief's addendum 5, the design-basis
  refresh brief, `Test/contracts/schema-codec.contract.md`, `Test/contracts/foundation-wave2.contract.md`
  (Inhabitation), and the code each claim cites.
- **Evidence words.** **proved**: a kernel theorem run here, axioms printed at `[propext, Quot.sound]`
  or less. **tested**: a finite check run here (a `#guard`, an instrument, a `tsgo` or `bun` run, a
  grep, a `git` command). **reading**: read in code or notes, not run. **assumed**: not checked. A
  model theorem is about the model, not the tree; every Lean check is a finite probe.
- **Counting rule.** A seat finding is used only if its verifier confirmed it or partly confirmed it,
  cited by its verdict id; "(partly: …)" says which part survives. A verifier's own finding is cited
  as "verifier".
- **Reruns (tested).** All 37 Lean probes this synthesis rests on were rerun through the one-compiler
  lock, one at a time, with `-M6144 -DwarningAsError=true`: every exit code is as recorded (red
  controls exit 1) and every log is byte-identical to the seat's or verifier's log apart from the
  appended `time`/`exit=` lines. The 8 `tsgo` runs and 4 `bun` runs the conclusions rest on also
  reproduce (same error counts and codes; `ALL OK`; the red twin fails). Written here: one model probe
  and its red control (Appendix A), and two `tsgo` checks with green and red halves (repeated field
  names; an empty tuple against `never`) (§9).

---

## 1. For the owner: is "full typing with records and JSON" a design we already have?

**No.** We have a rule, a set of refusals, and a boundary description plane. We do not have records
in `Ty`, a record value encoding, a decode operation a program can use, structured error payloads,
signed numbers or recursive types. Exploring them on paper now is safe; landing them now is not (§4).

**Decided, in tracked files** (reading):
- **The rule** (`AGENTS.md:85`, "Schema and program", written by decisions row 13 at `f8c9b7fe`):
  Schema is a data language; an effectful slot is a hole filled by a typed `Eff` program; `Ty` and
  the schema carriers never mention `Eff`; a foreign transformation is a refused name (PED-01).
- **The refusals.** DB-15 (`DESIGN-BASIS.md:664-666`): no `json` leaf ("a codec is a row"), no record
  type in `Ty` ("columns are pairs"), `int` uninhabited. DI-62 (`:655-656`): `Err.value` refused.
  DI-67: every admitted column is inhabited or `never`; `int` refused at admission (TREE-D09, D17;
  PED-07).
- **What sits under them.** DI-15's tagged unions `union (prod (lit tag) X)` and canonical forms;
  DI-35 (`eq` one type at a time, `Val.eqAt` the destination); DI-56 (bounded numbers); DI-78
  (collections required, contracts first); DI-89 (how modules enter; `Schema.decodeUnknown*` has no
  route); the owner-approved S-3 codec contract (exact admission; object field order immaterial; extra
  and duplicate keys refused, `schema-codec.contract.md:26-28`); rows 6, 56, 68, 96, 97 landed; row 39,
  the Schema wipe, ruled 2026-09-18 and not executed (TREE-D10, PED-17).
- **The frame.** System-map §1.1 puts structural records and variants in the type language (growth
  of `Σ_core`) and nominal data declarations in `Σ_app` "later, and only if admitted"; §8 R3 states
  the requirement and its status: "refused by DB-15 as written … open as one DB-15 amendment;
  recursive types untracked".

**Only in gitignored notes** (reading; PROG-D13 partly, PED-03 partly):
- **Decision 12** ("every boundary value carries an Effect Schema", 2026-09-10). Tracked files use its
  name (row 5 "D12's shape", `api-surface.md:74`, module docstrings), no tracked file holds its text,
  and DI-08 ("is Schema in the release") still reads open.
- **The owner's boundary rule of 2026-09-10** (B-print, B-accept, B-row, B-tape; "overload rather than
  refuse"), with T5 ("a float carrier is the first post-v0 append") and T9 ("keep the closed error
  image for v0") (verifier, tree §2.1).
- **Every record design**: the type-algebra note's `Ty`/`Fields` spine with `Ty.foreign`, scout C's
  nominal `Ty.data`, the model probe's D10 packet (PED-08 partly).

**Open** (reading): rows 1, 2, 5, 7, 10, 11, 108, 109, 118 and DI-08; and no row at all for recursive
types (PED-13), for a record's value encoding, or for decoding inside a program (PED-12 partly).

**Where the phrase comes from.** It is the owner's own: Decision 12 (2026-09-10) asks for "an Effect
Schema representation of all boundaries … Higher-order schema-native typings and utils; canonical
schemas for row types" (quoted verbatim at `2026-09-10-schema-at-boundaries.md:3-9`, untracked). The
first half, a schema for every boundary value, is S-1 to S-3 and landed. The second half, a typed schema
layer over `Ty`, was built on 2026-09-11 (`Ty.record` as sugar over nested tagged pairs, `SchemaFn`,
`Endpoint`, `SchemaTransform`; `e75d9e61`) and deleted on 2026-09-18 (`b08f3b58`) (`git show --stat`,
tested; PED-08 partly). AGENTS.md's rule, written the day before (`f8c9b7fe`, 2026-09-17), stands in
its place.

**Did we determine native schema support? Partly.** The record defines it by the rule above. Of its
four parts: Schema as data exists (`Representation` holds rc.112's 21 AST node kinds plus `Reference`;
EFF-06 partly); "`Ty` never mentions `Eff`" holds; effectful slots as typed `Eff` holes have no
carrier (`Transform` was deleted at `b08f3b58`, PED-02); foreign transformations as refused names
have no carrier either. What runs is the description plane: `Ty.schema`/`ofSchema` with a proved
retraction and a type-directed JSON codec with proved round-trip laws (rerun). AGENTS.md lists both
as exact embeddings; neither is exact today (tested, §2 NS1–NS2), neither is on the host reply path,
and a schema struct has no program type because `Ty` has no record.

So native schema support, as this probe recommends completing it, is **growth of `Ty`, not a second
schema carrier**: records in `Ty`; the bridge and the codec made exact embeddings on a stated
fragment; one decision-free operation for decoding inside a program; Decision 12's boundary route
written down. It is not schema-level transformations and not a second representation of programs.

---
## 2. "Native schema support" as requirement shapes over the open signature

The frame is system-map §1.1: a program is a closed term over `Σ = Σ_core ⊕ Σ_app`. The sorts involved
and their one representation each (system-map §4): the type sort `Ty`; the schema carrier
`Representation`; the value sort `Store.Val`; JSON, `Effect4.Json` (`Data/Json.lean`, objects as ordered
entry lists that keep duplicates). The arrows and their claimed kinds (system-map §5): `Ty.schema`/
`Ty.ofSchema` (claimed K2), `Schema.encode`/`Schema.decode` (claimed K2), `Fits`/`Val.hasTy` (the one
value judgment and its executable twin), the printer and reader (K2 on the readable domain). Every
shape below quantifies over the admitted types of `Σ`. If row 2's `Σ_app` half ever admits nominal
data declarations, each shape gains the declaration table as a parameter (verifier, effect §2.14;
PED-23 partly). Each shape names its observation and what it refuses.

### NS0. The rule's two holes (a carrier rule, not a theorem)

- **Shape.** No schema carrier mentions `Eff`. A slot that needs a program is a typed hole whose filler
  carries its certificate (`effTy σ (Γ ++ [A]) p = some ⟨B, E, R⟩`). A foreign transformation is a name
  that every meaning-needing operation refuses.
- **Status.** The first clause holds (reading). The hole carrier `Transform σ Γ A B E R` was deleted at
  `b08f3b58` (PED-02; `git show --stat b08f3b58`, tested); no structure holds a refused foreign name
  (pedigree §2.1, reading).
- **Refuses.** Everything outside rc.112's pure fragment `P`: user getters (`decodeTo`, `transform*`),
  middleware, user filters (`makeFilter`, `refine` with a host predicate), declarations with a user
  `run` (effect §4b; EFF-06 partly). Keep refusing until a program needs an effectful transformation
  (row 123, option d).

### NS1. Schema as data, and the arrow from `Ty`

- **Shape (K2 on admitted closed `τ`).** Retraction `ofSchema (schema τ) = some τ`, and exactness
  `ofSchema r = some τ → N_S r = N_S (schema τ)`, where `N_S` is named: it drops the annotations that do
  not change decoding and, once records exist, orders a struct's properties canonically.
- **Observation.** `Representation` equality modulo `N_S`.
- **Refuses (located).** A check the bridge does not mint, compared as a whole check and not by its
  id; annotations that change decoding (`parseOptions`, `identifier`); a schema with no `Ty` image.
- **Status.** The retraction is **proved** for today's closed types (`Bridge.ofSchema_schema` at
  `[propext]`, `CTy.ofSchema_schema` at `[propext, Quot.sound]`; rerun). Exactness is false today
  (tested, rerun): `ofSchema` reads a check by its id alone (`checkId`, `Schema/Bridge.lean:62`), so
  "number ≥ 5" reads back as `nat` (PED-05) and a filter group, an aborted `isInt` filter and an `isInt`
  payload read back as `int` (verifier, pedigree V1); `schema (var i)` equals
  `schema (handle "effect/schema/TypeParameter")` and reads back as that handle (TREE-D12); a union of
  three literals is refused because `ofSchema` reads exactly two members (verifier, effect Red7);
  `parseOptions` and `identifier` are dropped although rc.112 decodes by them (verifier, effect P4–P6,
  tested by `bun`, rerun). `Representation` already spells records (`objects`, with property and index
  signatures, `Schema/Representation.lean:701-778`; TREE-D11 partly), so the gap is `Ty`'s image, not
  the carrier.

### NS2. Decode and encode as pure folds, exact on a stated fragment

- **Shapes.** Membership: `decode τ j = some v → Fits w v τ`. Retraction on the codec domain:
  `isCodecValue τ v → decode τ (encode τ v) = some v`. Exactness:
  `decode τ j = some v → ∃ j', encode τ v = some j' ∧ N_J j = N_J j'`, with `N_J` = object key order.
- **The fragment.** `isCodecValue` (the S-3 owner amendment's admission domain) intersected with rc.112's
  pure fragment `P` under one fixed set of parse options: `onExcessProperty: "error"`, the default key
  order, the default error mode.
- **Observation.** `Json` equality modulo `N_J`. On the host face (K3, finite): under the profile's
  parse options, rc.112's `decodeUnknownExit(toCodecJson(S_τ))(j)` succeeds iff Lean's `decode τ j`
  does, and then the canonical encodings are equal (the `schema-codec` lane, extended; row 5's S-5).
- **Refuses.** Extra keys and duplicate keys (the owner-approved S-3 clause; on extra keys it equals
  rc.112's `onExcessProperty: "error"`, verifier effect P1; on duplicates rc.112's text route keeps the
  last key, T7 and T21; all tested by `bun`, rerun); fractions, negatives, `int`, handles, fibers,
  `unknown`, `var` (`Codec.isSupported`, `Schema/Codec.lean:51-55`).
- **Status.** Membership (`hasTy_decode`) and retraction (`decode_encode`, `decode_of_encode`) are
  **proved** for today's `Ty` at `[propext, Quot.sound]` (rerun). Exactness is neither stated nor true:
  1. Key order is deliberate and written (`schema-codec.contract.md:26`, `Codec.lean:74-75`); what is
     missing is the normaliser as a function and the theorem (EFF-07 partly).
  2. A decoded value can re-encode as another branch: at `union (except nat nat) (exitOf nat nat)`,
     `{"_tag":"Success","value":1}` decodes to `ctor 0 [nat 1]`, which encodes as
     `{"_tag":"Failure","failure":1}`, because `Val` is untyped (`Exit.success v` and
     `Result.failure v` are both `ctor 0 [v]`) and `decodeRaw`'s union arm accepts a later branch's
     image (verifier, pedigree V2, tested, rerun; PED-06 partly). The contract already makes the
     *encoder* refuse such values (`schema-codec.contract.md:34`); the *decoder* needs the same check:
     `decode τ j = some v` only when `encode τ v` gives back `j` modulo `N_J`.
  3. Row 41 says "the codec agrees with rc.112"; under the strict field policy that holds for Lean's
     encodings and the 17 decoded canonical images, not for rc.112's default decode. That is a wording
     fix, not a live gap (EFF-08 partly).

### NS3. The program-facing operation: one recommendation

**Recommendation: a decision-free machine operation in `Σ_core`, `decode (target : Ty)`**, a sync
native operation that carries its target type as data, typed
`unknown → target ! prod (lit "SchemaError") string`, whose meaning is NS2's fold composed with an
exact image of host JSON as a `Val` at `unknown` (the generated `Canonical Json`,
`Store/Domain/Derived/Json.lean`, is the candidate; the choice belongs with row 10's one `Val → Json`).

- **Why a machine operation.** On the pure fragment decoding is total, pure and decision-free; rc.112
  itself returns an already finished `Exit` for a pure schema (T10, tested by `bun`, rerun). A host row
  would record a pure function's results as tape decisions. A `Forms` template would owe a simulation
  against the fold for the same meaning. A typed `Eff` hole needs the hole carrier NS0 lacks. The
  precedents for an operation that carries data: `NativeOp.refUpdate (f : FnName)`
  (`Program/Native.lean:56`) and `Eff.iterate (cursorTy : Option Ty)` (`Program/Eff.lean:336`) (EFF-12
  partly, reading). The Effect-failing spelling is the one programs write: `decodeUnknownEffect` is 618
  of the 931 `decodeUnknown*` calls in v4 application code (effect §3.3, `member_histogram.log`; the
  total recounted within 4 by the verifier, EFF-02).
- **Why `unknown` in, not JSON text.** 37 of the 40 sampled decode sites decode an already structured
  value; 3 decode JSON text (EFF-05 partly, reading of the sample). Parsing text is a separate
  operation (`parseJson : string → unknown`), added when a program needs it.
- **Obligations** (DI-89's list as R10 states it):
  - typing: `HasTy Γ (perform (decode τ) x) ⟨τ, schemaErr, ∅⟩ ↔ HasTy Γ x unknown ∧ τ.isData`, where
    `isData` means closed, codec-supported and handle-free;
  - one behaviour law: the step equals the fold, and the journal is unchanged (decision-free);
  - membership: the answer fits `τ` (NS2's membership law);
  - printer: `Schema.decodeUnknownEffect(S_τ)(x)` piped through DB-15's error adapter
    `Effect.mapError(toPair)` (DI-59), else the printed error type is a `SchemaError` instance and
    `tsgo` refuses the printed program (verifier, effect §2.7; PROG-D4 partly);
  - reader: reads that spelling back exactly when `S` reads through NS1, a located refusal otherwise;
  - face: NS2's host agreement on `P`;
  - a `Σ_core` append under the DI-47 discipline (R3.8 below).
- **When.** After records (stage 1) and after the JSON image at `unknown` is fixed (with row 10),
  when a program that decodes inside is taken on: p2 as written decodes a SQL row object inside its
  layer, and the 34-project ingest census counts about 756 decode heads against 2,032 for
  `Schema.Struct` (PROG-D14 partly).
- **The alternative, recorded.** A total term atom returning `except` (rc.112's `decodeUnknownResult`
  and `decodeUnknownOption`, 116 uses; verifier, effect §2.6) needs no machine step but needs DI-89's
  result eliminator form to print the Effect spelling; that form does not exist yet (R10's status).

### NS4. `SchemaError` as a payload

There is no `ParseError` in rc.112's Schema; a decode fails with `Schema.SchemaError`, a tagged error
whose one field `issue` is a `SchemaIssue.Issue` (`Schema.ts:1180-1199`; EFF-17 partly).
- **Now, no constructor.** DB-15's pair `prod (lit "SchemaError") string` (tag, default formatter
  message). It is admitted today and `errOf` reads it as `Err.tagged` (tested by the effect seat,
  rerun). Observation: `(_tag, message)`. Message agreement with rc.112 holds only where no annotation
  changes the message (`identifier` does: P6, tested); refuse those by name, or compare tags only.
- **With records and payloads (stages 1 and 3).** rc.112's flat Standard Schema projection,
  `{ message : string, path : list (string | nat) }` per leaf (T16b, tested by `bun`, rerun), as a
  handle-free record payload. Never the issue tree: it is recursive and holds AST references (EFF-13
  partly).

### NS5. The boundary decode route (Decision 12, route A)

- **Shape.** Every reply the session accepts at row `r` is a member at `r.answer` in the new world,
  `accept r v = ok → Fits w' v r.answer` (host-boundary §4.4–§4.5's receipt theorem; the record clause is
  what R3 adds). The host adapter decodes with the row's own schema and lays the record out in the
  type's canonical field order; the session checks a `Val` (a reply is `Completion Val`, not JSON:
  EFF-14 partly). Nothing in the program parses.
- **The S-5 gate** (row 5, not started): every recorded exit decodes under its program's published
  `Schema.Exit` (finite, host).
- **Observation.** Admission of the reply value. **Refuses.** A reply that is not a member (a located
  `envelope` refusal: RC3, tested, rerun); internal handles (row 97).
- **Status.** Works today with records spelled as pairs (`ProbeTodayP2.lean`: p2's handler answers what
  rc.112 answers on the three requests of `run-p2.ts:18`; tested, rerun; PROG-D14 partly). Becomes exact
  with records. Decision 12 must first be written into a tracked place (row 122).

---
## 3. R3 restated as theorem shapes, with a staged landing plan

### 3.1 The shapes, for a new type former κ (records first)

Notation for the recommended record design (row 119): `record (fields : List (String × Ty))`; `canon fs`
is `fs` ordered by field name (the key order `Ty.key` already uses for strings); a record value is
positional, `ctor 0 [v₁, …, vₙ]` in canonical order, with no new `Val` frame.

| Shape | Statement | Observation | Evidence today |
| --- | --- | --- | --- |
| R3.1 membership | `Fits w v (record fs) ↔ ∃ vs, v = ctor 0 vs ∧ FieldsFit w vs (canon fs)`; `Val.hasTy` has the same arm; `fits_hasTy` connects them; `fits_live`, `fits_map` gain one arm | value membership | the connector pattern is **proved** in the tree's model (`fitsV_iff_hasTyV`, `[propext, Quot.sound]`, rerun; TREE-D20) |
| R3.2 normalization | `hasTy v (normalize t) a = hasTy v t a` for every raw `t`, no premise; records are factors (no distribution over union-typed fields); a repeated field name is refused at formation | value membership | canonical-order read **proved** invariant in the synthesis model (`SynthRecord.hasTy_normalize`, `[propext, Quot.sound]`); written-order read **proved** not invariant (verifier tree: `hasTyV_normalize_fails`; synthesis red control `written_order_not_invariant`); under the canonical read a repeated name does not break the law (**tested**, `#guard`), so the formation refusal is the target's: `tsgo` refuses a repeated name (TS2300, TS1117; **tested** here); distribution **tested**: three binary union columns give eight members (verifier programs §2.1, rerun) |
| R3.3 subtyping | exact (depth) rule: `sub (record fs) (record gs)` iff the canonical name lists are equal and each field is below; then `sub a b → Fits w v a → Fits w v b` (`fits_sub`, `hasTy_sub`) and antisymmetry on canonical forms (`sub_antisymm_canonical`); every record pair on row 68's lane agrees with `tsgo` or is classified `incomplete`/`cut`, never `defect` | membership; `tsgo` assignability | exact rule **proved** monotone in the tree's model (`fitsFields_exact_mono`, `[propext]`, rerun); width with positional values **proved** unsound (`positional_width_unsound`, rerun; TREE-D08 partly); a permuted object literal at the declared type passes `tsgo` (**tested** here), which set semantics accepts |
| R3.4 Schema embedding | NS1 at records: `schema (record fs)` is a struct over `canon fs`; `ofSchema` reads an `objects` node with named properties only, refusing index signatures, optional keys and decoding annotations by name | `Representation` modulo `N_S` | none for records; NS1's repairs first |
| R3.5 JSON embedding | NS2 at records: an object keyed by field names, read with the exact field set in any order (`fields?`, `Codec.lean:74-82`) | `Json` modulo key order | the object reader exists for Option, Result, Exit, Cause (**tested**, rerun: `programs/verify-Refute.lean` §C) |
| R3.6 folds | `TyAlgebra` gains `record : List (String × A) → A`; `cata_ty`, `hom_eq_cata_ty` and the `fold_of` connectors regenerate; the single-motive eliminator is generated, not hand-written a third time; every classifier with a catch-all puts `record` in its negative class until given an arm (row 56) | — | the sort lives in the algebra, so `hasTy` stays a fold (`hasTy := cata hasTyAlg`, synthesis model) |
| R3.7 inhabitance | `inhabited : Ty → Bool`, a fold, with `inhabited τ = true ↔ ∃ w v, Fits w v τ`; admission refuses every answer, error, request and table column with `normalize τ ≠ never ∧ inhabited τ = false`, located (`uninhabited at`) | admission verdict | needed today: `prod never nat` (answer, request) and `except never never` (answer) are admitted and uninhabited (**tested** and **proved**, PED-10, rerun); `record [(a, never)]` is canonical and uninhabited (**proved**, verifier tree, rerun) |
| R3.8 conservativity (DI-47) | on κ-free types every existing function and law is unchanged; finitely: the wire tag appended (the loader refuses a repeated tag or name, `tools/Tools/WireTags.lean:12-18`), every existing golden byte-identical, every corpus admission verdict unchanged, the baseline policy file naming the addition | goldens and verdicts | no such statement exists; the comparator was deleted at `243ca0dd` (TREE-D18 partly, PROG-D12) |
| R3.9 faces | printed type `{ readonly a: A; … }` (`TypeRef.object`, `.lake/packages/typescript/TypeScript/TypeRef.lean:17-18`), terms `{ a: x }` and `x.a` (`TypeScript/Syntax.lean:46`, `:70`); `read_print`/`read_exact` over the new forms; the printed module passes `tsgo` (B-print); what rc.112 accepts and Lean refuses is refused by name (B-accept): width inside a program, `eq` at a record (DI-35); a repeated name is refused on both sides | `tsgo`; the reader | the vendored syntax has both forms (TREE-D21) |

The shapes are stated per `Σ_core` constructor because records are type-language growth (system-map
§1.1). Inhabitance and conservativity are not new obligations the record brings: both are open today
(R3.7 for any composite type; R3.8 for every `Σ_core` append).

### 3.2 The stages

Each stage is one slice, landed by explicit paths after narrow builds, in its own worktree.

**Stage 0 — on paper, now.** The rulings of §5 (rows 119–132) and the register repairs of row 129. No
code; displaces nothing but owner time.

**Stage 1 — records, exact (the first slice; §4 says when).**
- *Requirement:* R3.1–R3.9 at `record`, with the design of row 119.
- *Obligations:* the `Fits` clause and the `Val.hasTy` arm with their connector; the `normalize`,
  `Normal`, `key`, `sub`, `isMember`, `closed`, `instantiate`, `renderRaw` arms and their laws;
  `hasTy_normalize`'s record case by the canonical-order read; K2 to Schema and to JSON; the generated
  folds with the generator extended (eliminator, TyView); assignability vectors on row 68's lane;
  inhabitance (its first commit, which also repairs DI-67's gap); the DI-47 discipline; two term forms
  (construction and field projection) with frozen contracts and falsifiers before code (DI-78), typing
  lemmas and behaviour laws; the printer and reader; the OCaml mirrors.
- *Unblocks:* p2's handler data (`User`, `AppConfig`, `Response`) end to end through route A; p1's
  `Quote` and p3's `Job` and `Conn` as values (those programs still need forms, cells and payloads,
  PROG-D1). Not p4 or p5 (record cells need R4).
- *Acceptance (end to end):* `ProbeTodayP2`'s handler re-spelled with records, errors kept as DB-15's
  literal-tagged pairs: authored through `Api.Author` with two host rows; checked at answer `Response`;
  run through the keyed session against a scripted host answering rc.112's objects (the adapter lays
  them out canonically); printed and read back exactly; the printed module passes `tsgo` against p2's
  idiomatic object signatures with DB-15's error adapter (today 12 errors: 10 are positional
  projections on objects, 2 are the error channel; PROG-D4 partly, rerun); the three answers equal
  rc.112's (`{"status":200,"body":"bob"}`, `{"status":404,"body":"no user 9"}`,
  `{"status":401,"body":"bad token"}`).

**Stage 2 — variants.** A union of records discriminated by a literal `_tag` field. No new
constructor (verifier programs §2.4; `square_fits` proved in the tree's model, rerun). The tag decision
(`isTagged`, `diffTag`, `taggedColumn`, `payloadOf`, `tagHit`/`tagIs`, `selectTag`) learns the record
discriminant, and a record whose `_tag` field is a union of literals is split or refused at formation,
the one exception to "records are not distributed" (TREE-D23 partly). Unblocks p5's `Entry` as rc.112's
objects and dogfood 6's events (F30). Cost: hand arms in the tag decision and its laws (`diffTag_sub`,
`diffTag_sound`, `supportedErrTy_diffTag`); row-68 pairs; no new generated group. Goes with row 130.

**Stage 3 — error payloads** (row 120). A program may fail with a handle-free record or variant;
`FitsCause` keeps its form; the six handle-freeness lemmas stay true (`Err.image_handleFree`,
`Defect.image_handleFree`, `causeImage_handleFree`, `Val.keys_exitErr`, `valOfErr_keys`,
`keys_of_cause`; PROG-D11 partly). Unblocks p2's `NotFound{id}`, p3's `JobFailed{id, reason}`, p1's
`HttpError{status, url}`, p5's `InsufficientFunds` (with stage 5). Cost: the 6 compile-forced `Err`
definitions (`Err.image`, `instReprErr.repr`, `Defect.ofError`, `valOfErr`, `Codec.encodeErr`,
`RunnerGen.ErrC.toVal`; tested, rerun), the truth wire's `errJson`, the engine's `Err` through LCNF,
and either a typing premise on six lemmas with eleven use sites or a handle-free carrier (row 120).
Shares `FitsExit`'s failure arm with H2 and item A's reply rule: after H2 part one is merged.

**Stage 4 — optional keys.** `a?: τ` with the absent-versus-`undefined` policy (`Schema.optional` admits
an explicit `undefined`, `optionalKey` does not: T12, tested by `bun`, rerun; `optional(` outnumbers
`optionalKey(` 2,589 to 213 in v4 application code, tested by the effect verifier). `fields?` learns a
missing key. No p1–p5 program needs it; it is the corpus's most frequent field modifier (2,802 uses in
12 of 15 v4 projects, EFF-02). If width is ever admitted, `sub` must refuse TypeScript's
undeclared-optional-key rule (T19, tested; `ProbeRed4`, proved red in the effect seat's model; EFF-10).

**Stage 5 — `int`, with row 108** (row 121). `Fits w v int` the exact signed image; DI-67's admission
refusal lifted; each face equals the reference inside the profile and refuses outside, intermediates
included; a signed literal; LCNF `Int.*` builtins (none in `src/OCaml5` today, tested by the programs
seat). Unblocks p5's −15 and p1's `-e.status`. Cost: a signed `Val` frame (16 compile-forced
definitions, the store tag, every byte codec) or `Int`'s generated `ctor` image (which overlaps
`Result` in unions and needs NS2's canonical-branch check); `Lit` (7 compile-forced, a wire family);
the atoms; the prelude's refusals; row 68's `nat`/`int` cut. Not coupled to records.

**Not staged** (rows open, no slice until a program needs one): the in-program decode operation (NS3,
row 123); recursive types (row 124); keyed maps (row 125); `Val.eqAt` (row 126); plain `number` (row
109); named refinements (row 4's closed check list); class-declared records as nominal declarations in
`Σ_app` (row 2's `Σ_app` half; the class name is forced by rc.112's run-time identifier check, not by
`tsgo`, which is structural at `Schema.Class`: EFF-11 partly, tested, rerun).

### 3.3 Stage 1's measured cost

Every figure is from a rerun instrument unless marked; "assumed" means estimated, not measured.

| Kind | What moves | Measured |
| --- | --- | --- |
| **Generated** | Fold group (`TyAlgebra` field; `cata_ty`, `foldM_ty`, `foldMap_ty`, `foldMapAt_ty`; 16 `fold_of` registrations over `Ty`, 5 of their `.hom`s compile-forced); Program group (`TyC.toValTy` and its laws); TyView group (from `variances.json`); the eff, wire, ts and lcnf groups (16 generated artefacts name the `Ty` alphabet, `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml` among them) | `ProbeBill.log` and `TyBillProbe.log`, rerun; TREE-D19 partly. The generator supports `List (Prod String Ty)` but emits no monadic half for it (no consumer, reading) |
| **Generator extensions** | the TyView generator refuses a composite field (`tools/Effect4Gen/View.lean:162-168`) and pins a fixed variance list per head; the hand variance table (`tools/Tools/Variances.lean`, about `:360-388`) does not fit a head of variable arity; a single-motive eliminator for nested families (third instance, after `Store.Val.ind` and `Json.ind`) | reading (TREE-D06, D07 partly; verifier tree §2.4, §2.11). The hand eliminator is 31 lines and is axiom-free in the model (rerun) |
| **Hand-written tables** | `tools/Effect4Gen/wire-tags.json` (append `record: 20`); `tools/Conform/Effect4/cases-policy.json`: 36 `Ty` rows, 25 default-mode cover lists, `unlisted: refuse`, the gate an append trips (`make check-cases`) | tested by the tree verifier (python read) |
| **Hand arms, compile-forced** | 15 definitions in `Effect4` (`Ty.members`, `Val.hasTy`, `findInt`, `rawSupportedErrTy`, `Ty.templateAdmissible`, `Ty.varsOf`, `Typed.Fits`, `Ty.closed`, `Ty.instantiate`, `Ty.isMember`, `Ty.isNever`, `Ty.key`, `Ty.normalize`, `Ty.renderRaw`, `Bridge.schema`); the private TypeScript type printer `Codegen.Types.ofNormalized`; a hand `Repr` (a nested `deriving Repr` goes `partial`, which the trust gate refuses); a `DecidableEq` (nested deriving is refused; 32 lines by hand, or generated); 6 outside `Effect4` (`OCaml5.Eff.tyO`, `tyV`; `Tools.ProfileJson.tyJson`; `Conform.Effect4.LcnfMl.tyOcaml`, `tyT`; `LcnfSemantics.tyValue`) | `Ty` 65 matcher rows / 27 without a catch-all (58 / 27 distinct definitions), rerun; TREE-D01, D02, D04 |
| **Hand arms, review** | 38 catch-all matcher rows (31 definitions) that compile silently and must classify `record` explicitly: `Ty.sub`, `Ty.infer`, `taggedColumn`, `payloadOf`, `isTagged`, `Codec.encodeRaw`, `decodeRaw`, `layout`, `isSupported`, `TyView.sameHead`, `externalValue`, … ; two hand per-constructor tables the gate cannot see (`src/OCaml5/Eff/Metadata.lean:52-60`, `Variances.lean`); OCaml hand mirrors (`ocaml/engine/e4_program.ml:119-153` with its `= 20` count, `ocaml/eff/test/prop_wire.ml` `rand_ty`) | PROG-D6 partly; verifier tree D19 (reading) |
| **Proofs** | theorems that recurse or case on `Ty`: 62 by the narrow census (34 by recursor: 27 hand-written, 6 generated, 1 Lean's; 28 by cases, 19 hand-written), 183 by the broad one (auxiliaries attributed, principle users added); 8 whose case lists follow a function's own principle and so change with `sub`'s arms (`fits_sub`, `cata_admits_sub`, `cata_admits_extend`, `sub_eq_false_of_not_sameHead`, `sub_eq_argsBelow_of_sameHead`, `sameHead_trans`, `sub_normalize_of_sub`, `infer_widens`); the subtyping algebra through `TyView.sub_eq_args` (`sub_trans_core`, `sub_antisymm_normal`); `hasTy_normalize` (`Laws/Program/TypeAlgebra.lean:309`, used by seven other `Laws` modules); in the typed state, one module only (`Typed/Membership.lean`: `fits_hasTy`, `fits_live`, `fits_map`, `fits_sub`, `flatFits_fits`, `flatFits_map`); the Schema laws (`ofSchema_schema`, `encode_of_hasTy`, `decode_encode`, `hasTy_decode`, `encode_sub`) | both censuses rerun (verifier programs, verifier tree); PROG-D7 partly; TREE-D03 partly. With a registered eliminator, 26 of 29 copied `Ty.lean` theorems kept their text (TREE-D05 partly: the hard proofs were not copied) |
| **Model size** | the tree's nested-record copy of `Ty.lean`: about 270 new lines for the width design (probe-grade; drops `lookupField`, 12 lines, under the exact rule); the canonical-order read: the synthesis model's key-order lemmas are about 115 lines (`Effect4.Row`'s sorted-row library may supply part, reading) | tree §4.2 (TREE-D06 partly); Appendix A |
| **Fixtures and goldens** | `Test/Audit/ExhaustiveFixture.lean` (`catchAllAbsent`), `Test/Counterexamples/Machine/Semantics/ValueMembership.lean` (`ExactSpelling.FitsInv`, 20 arms), `Test/Audit/TraversalCensus.lean` (pins "alts 20"); `ocaml/goldens/eff/{manifest.txt,wire-tags.txt}`, `ocaml/eff/goldens/coverage-metadata.txt`, `generated/assignability.tsv` (record pairs), `generated/row-citations.tsv` (one row per new atom); `Test/fixtures/baseline/` unchanged, its policy file naming the addition by hand | `Test` bill 5 matches / 2 without a catch-all (verifier tree, tested); the rest reading |
| **TypeScript printer and reader** | `ofNormalized` → `TypeRef.object`; `parseLegacy` refuses object types today (`Codegen/Types.lean:20-21`); the reader matches a service's declared type by comparing `ofTy` with the parsed `TypeRef` (`Codegen/Read.lean:356`), so source ingest must produce `TypeRef.object`; object literals and member access printed and read with `read_print`/`read_exact` | reading (TREE-D21) |
| **OCaml route** | the LCNF re-cut of `api_gen.ml`/`api_engine.ml` (members, factors, productMembers, ctorIdx, decEq, sub, key, normalizeRow, normalize, `Val.hasTy`, `externalValue`, `errAdmits`, `externalAdmits` are lowered); nested lists already lower (`Val_list`, `Val_ctor`); the field sort reuses the key comparison `normalizeRow` already lowers | tested by grep (TREE-D22 partly); "no new extern for the sort" is **assumed** |
| **Size** | the last `Ty` append (`unknown`, `0a2cb898`): 44 files, +1,192/−488, `cases-policy.json` +954/−423 | tested (PROG-D6). Stage 1: about 55–65 files, **assumed** (the precedent, the exhaustive readers born since, the term forms; fewer than the programs seat's 60–75, which counted a `Val` append the recommended design avoids) |

### 3.4 The obligations, stage by stage

| Obligation | Stage 1 records | Stage 2 variants | Stage 3 payloads | Stage 4 optional keys | Stage 5 `int` |
| --- | --- | --- | --- | --- | --- |
| `Fits` clause and `Val.hasTy` arm | new clause (R3.1) | none new: a union of records | `FitsCause` unchanged; the payload's image fits the error column | the record clause learns an absent key | the exact signed image replaces `False` |
| K2 to Schema | `objects` arm (R3.4) | `_tag` literal properties | the payload's schema | `optionalKey` | `Schema.Int` reads back (today: refused at admission) |
| K2 to JSON | object layout, key order named (R3.5) | branch selection by `_tag`, canonical-branch check | the error image's JSON (`errJson`, `encodeErr`) | a missing key; absent versus `undefined` | signed JSON numbers (today `-15` decodes at no type) |
| Generated folds | `TyAlgebra` field; eliminator; TyView | none | `Err`'s generated codec (`ErrC.toVal`) | none, if inside the record arm | `Lit` wire family; `Val` group if a frame |
| Assignability (row 68) | record pairs: permutations agree, width `incomplete` | tagged record unions | none new | optional-key pairs (refuse TypeScript's undeclared-optional rule if width ever lands) | the `nat`/`int` cut |
| Inhabitance (DI-67) | R3.7, first commit | a union is inhabited if a branch is | the payload type | an optional field never empties a record | `int` inhabited, its admission refusal lifted |
| DI-47 discipline (R3.8) | wire tag 20, goldens unchanged, verdicts unchanged | goldens unchanged | goldens keep their bytes for old error shapes | goldens unchanged | `Lit` tags appended |
| Programs unblocked | p2's handler data end to end | p5's `Entry`; dogfood 6's events | p1, p2, p3, p5's error fields | none of p1–p5; the corpus's most common field modifier | p5's −15; p1's `-e.status` |
| Cost, generated / hand / proofs | §3.3 | none / tag decision (6 functions) / their laws | `Err` codec, engine `Err` / 6 forced definitions / six handle-freeness lemmas (row 120) | none / codec and arms / record laws re-run | `Val` or `Lit` groups / 16 + 7 forced definitions / row 108's profile laws |

---
## 4. The order

### 4.1 Where Codex's queue stands (reading of the branch refs)

Addendum 5 orders the queue: C step 5, D's held users, F, G, H1, then H2 part one; the `Σ_app` slice
(rows 111–116) after G as the first slice of the M5–M7 brief; then the M5–M7 proofs. C is merged
(`bc77e97f`, recorded at `ba9783c3`). On `codex/slice6-fixes`, eight commits past the merge base
`f05a6ace`, the newest (`c42f4a46`, 03:28) landed while this synthesis ran and changes only the
receipt (read with `git log`/`git show` from the main repository; nothing pushed, nothing merged):
- **D's held users: done** — native fork trace agreement through the machine lifts (`31e44efc`),
  reachable fork-ledger freshness (`4e9bfce7`), diagnostics moved to `Test/` (`fa5add20`). Codex's
  newest receipt names `fa5add20` as the endpoint for a D-only merge (`c42f4a46`).
- **F: done** — layers built in their checked lexical environment (`d20f3292`). It edits
  `Program/Compile.lean` and re-cuts `ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml` and two closure
  manifests.
- **G: held** on its checked fourth-fixture stop; an owner amendment is proposed (`19baddc5`).
- **H1: held** on a checked delivery counterexample to the proposed contract; it needs an owner ruling
  on terminal delivery against saved-code typing (`80f5fbe7`).
- **H2 part one: held** on its measured ninth-body stop: the eight authorized repairs pass, two
  existing test statements (`cancel_typed`, `lookup_typed`) are false under the repaired judgment, and a
  bounded 25-body follow-up is proposed (`3b825aa8`).

So Codex is waiting on three owner decisions on its own branch. None of them concerns data typing.

### 4.2 What the data work touches, against what is in flight

| In flight | Shared with stage 1 (records) | Shared with stage 3 (payloads) |
| --- | --- | --- |
| D (done, unmerged) | nothing | nothing |
| F (done, unmerged) | the LCNF-generated `api_gen.ml`/`api_engine.ml` and closure manifests, which any `Ty` append re-cuts; `Program/Compile.lean` (`externalValue`'s file) | the same |
| G (held) | nothing at the source level: `Checker.lean`'s two `Ty` matches close with a catch-all (PROG-D19); G's check calls `Ty.sub`, whose answers on record-free types R3.8 keeps | nothing |
| H1 (held) | nothing (`Guard/Core`, `Typed/Assembly`, `Typed/Scheduler`) | nothing |
| H2 part one (held) | nothing: no theorem or definition in `Typed/Admission`, `Residual`, `Stack` cases on `Ty` (census, PROG-D19) | `FitsExit`'s failure arm and the cause handle-freeness, which `ExitOk` reads |
| item A (merged) | `internalHandleScan` is the one hand-written `TyAlgebra` instance (`Program/Admission.lean:58`): the new algebra field forces its record arm, which must scan every field (row 97) | "typed failures need no new check" (`host-boundary.md:231`) stops being true under row 120's option (b) |
| the `Σ_app` slice (rows 111–116) | admission (`Program/Admission.lean` and the `AdmittedProgram` certificate) if R3.7's repair lands in the same window; row 118's structured carriers wait on records | nothing |
| row 108 (numbers) | nothing | nothing; stage 5 goes with it |
| row 39 (ruled, not executed) | independent of Codex; it deletes the parts of the Schema plane a record arm would otherwise keep consistent (`Check`, `Accepts`, `Image`, `EffectfulField`, `Api.schemaOf`) and cuts the `Store/Domain/Shape → Schema.Authoring → Schema.Check` import (verifier, pedigree §2.9) | nothing |
| the design-basis refresh (briefed, docs only) | it leaves DB-15 untouched and notes that the R3 amendment waits on its row (`2026-10-01-design-basis-refresh-brief.md:70`); the amendment is written after it lands | nothing |

### 4.3 The earliest safe slot, and the first slice

1. **Now, on paper.** The owner rules rows 119–132 (§5); the coordinator makes row 129's register
   repairs and registers DI-67's counterexample. Displaces nothing.
2. **Any time, independent of Codex:** execute row 39 (ruled), as its own deletion series with narrow
   builds; it touches the root imports and `Test/All.lean` at the coordinator's anchors and no file in
   Codex's queue. It shrinks what stage 1 must keep consistent.
3. **Stage 1, the first data slice: records only.** Its earliest safe base has F merged, not only D
   (F re-cut the LCNF group; two regenerations of it on different bases conflict). By default it
   lands **after the M5–M7 milestone**: the owner's route puts the foundation first ("Now: finish the
   foundation, small", system-map §3) and the model probe's order puts R3 after the milestone (a
   recommendation, PED-24 partly). If the owner wants M5–M7 stated over records from the start, it fits
   between the `Σ_app` slice and the M5–M7 proofs, delaying the milestone by one slice, not causing
   rework, provided the M5–M7 proofs keep to `Fits`'s lemmas (row 132).
4. **Stage 2 (variants)** right after stage 1, with row 130. **Stage 3 (payloads)** after H2 part one is
   merged, and after row 117's contract if part two changes the exit judgment. **Stage 4 (optional
   keys)** when the first program needing them is taken on. **Stage 5 (`int`)** inside row 108's slice,
   before WASM at the latest.

**Why records alone are the first slice ("don't bite off too much").** No data stage makes a model
program fully expressible on its own (PROG-D1; PROG-D2 partly: p2 also needs payloads, service
carriers and Config;
p4 and p5 need R4's cells; all five need R10's forms). Stage 1 is the smallest slice that makes one real
program's data exact end to end — p2's handler, authored, checked, run, printed and read back — while
everything it adds is used by every later stage. Taking records, variants, payloads and `int` together
(the model probe's D10 packet) would put the exit judgment, the reply rule and the number profile into
one slice, against the owner's scope discipline (system-map §1: a large contract is written down and
parked until a need arrives).

**What starting stage 1 now would displace.** A slice of about 55–65 files (assumed) regenerating the
groups F just regenerated on an unmerged branch, conflicting in generated files and `cases-policy.json`;
D, F, G, H1, H2 part one and the milestone behind it; and still no program fully expressible (PROG §4).

---
## 5. Decision rows for the owner (numbered from 119)

The register's last row is 118. Each entry gives the question, the options, the recommendation and
the row as it would read. **Rows 119, 122, 127 and 128 gate the first data brief** (and row 39 should
be executed first). None gates Codex's queue or the M5–M7 brief; row 132 adds one sentence to the
latter.

**Row 119 — Records: the DB-15 amendment, row 2's stage (b).**
- *Question.* Does `Ty` gain records, and with which value encoding, subtyping, field order,
  constructor encoding and normalization? The parts are one decision: the value encoding and `sub`
  are coupled (PROG-D9 partly; TREE-D08 partly).
- *Options.*
  - (a1) **Exact records**: positional `ctor 0` values in canonical order; `sub` exact (same names, each
    field below); width refused by name inside a program and projected by the row adapter at the
    boundary. No `Val` change. The law shapes hold once the value is read in canonical order
    (`fitsFields_exact_mono`, tree model; `SynthRecord.hasTy_normalize`, synthesis model; both proved).
  - (a2) **Width records**: labeled values (a `Val` object frame: 16 compile-forced definitions, a store
    tag, the byte-codec laws); entries the type does not name must be constrained (handle-free or live:
    `width_admits_unnamed_handle`, proved); `sub` must refuse TypeScript's undeclared-optional-key rule
    (EFF-10); TyView needs a width rule. Membership is closed under width only with labels (`fitsN_sub`,
    `hasTyObj_sub`, proved; `positional_width_unsound`, proved red; all rerun).
  - (a3) **Coercive width**: positional values; width as a projection at subsumption (`fits_coerce`,
    proved on a small model, verifier tree); a coercion term in the stored program, cost unmeasured.
  - (b1) **Set semantics**: canonical order by name, membership reads in canonical order (a sort inside
    the algebra, still a fold; proved here). (b2) **Declaration order**: no sort; field permutations are
    distinct types, so a permuted object literal is refused by name; every ordered arrow is exact as is.
  - (c1) nested `record (fields : List (String × Ty))`, with the eliminator and the equality generated;
    (c2) the mutual `Ty`/`Fields` spine (R3's tracked wording): derived equality, but a second family in
    every generated table and a list twin and bridge for every spine function a law uses (tree §4.3).
  - (d) records are factors, not distributed over union-typed fields (an incompleteness registered as
    `option (a | b)`'s is), except stage 2's discriminant rule. (e) A repeated field name is refused at
    formation.
- *Recommendation:* **(a1) + (b1) + (c1) + (d) + (e).** (a1) is the one design with no `Val` append, no
  unconstrained entries and no optional-key hole, and it is what the owner-approved S-3 contract
  (strict field set) and DB-15's adapter (DI-59: project at the row) already do at the boundary. Width
  stays a later amendment, (a2) or (a3), once row 68's lane shows how often real programs meet
  `incomplete` record pairs. (b1) accepts object literals in any key order, as TypeScript programs write
  them; its price is one sort in the algebra and a named field-order normaliser on the arrows that carry
  order (Schema struct, JSON object, TypeScript object type, `Shape.struct`). (c1) keeps core list
  lemmas usable for that sort. The eliminator and the equality come from the generator, not a third hand
  copy (the top-of-abstraction rule; verifier, tree §2.11).
- *Row:* "R3, records (DB-15 amended; row 2 stage b): `Ty.record (fields : List (String × Ty))`,
  appended (wire tag 20). Canonical field order by name; a record value is `ctor 0` of its fields in
  that order; membership reads in canonical order. Subtyping is exact; width is refused by name inside
  a program and projected by the row adapter at the boundary. Records are not distributed over union
  fields. A repeated field name is refused at formation. Eliminator and equality generated. System-map
  R3's 'through the `Ty`/`Fields` spine' becomes 'through a record constructor over a field list'.
  Width and optional keys are later amendments."

**Row 120 — Error payloads (DI-62 amended).**
- *Options.* (a) Keep the pair (DI-62; boundary decision T9). (b) `Err.value (v : Val)` with a type-level
  handle-free condition on error types at every introduction, `unknown` excluded: six unconditional
  lemmas become conditional, with eleven use sites (PROG-D11 partly). (c) A payload carrier that cannot
  hold a handle, with an exact embedding into `Val`: the six lemmas stay unconditional and
  host-boundary §5's "typed failures need no new check" stays true.
- *Recommendation:* (c), with its cheapest instance measured before the ruling (a new first-order
  family with no `handle` or `ref` frame, or an existing handle-free family read through the codec);
  stage 3, after H2 part one is merged.
- *Row:* "Error payloads: a program may fail with a handle-free record or variant, carried by a payload
  type that cannot hold a handle (exact embedding into `Val`); `FitsCause` unchanged; lands after H2
  part one."

**Row 121 — `int` and numbers.**
- *Options.* (a) Keep `int` uninhabited. (b) Inhabit `int` inside row 108's slice: a signed image (a
  `Val` frame, or `Int`'s generated image with NS2's canonical-branch check), a signed literal, LCNF
  `Int.*` builtins, refusal outside the profile. (c) Binary64 `number` now.
- *Recommendation:* (b) inside row 108's slice; plain `number` stays with row 109 (parked), and
  `Schema.Number` is refused at the reader by name. The effect seat filed binary64 under row 108; it
  belongs to row 109, DI-67 and T5 (EFF-15 partly).
- *Row:* "Numbers: `int` becomes inhabited inside row 108's profile slice; binary64 stays with row 109;
  `Schema.Number` is refused by name at the reader until then."

**Row 122 — Decision 12 and the boundary decode route.**
- *Options.* (a) Write Decision 12 into a tracked place with its scope: S-1 (`Ty.schema`), S-2 (the
  documents) and S-3 (the codec) landed; the publisher of a program's exit schema is `EffTy.document`
  (row 39 deletes `Api.schemaOf`); S-5 is row 5's gate; route A (typed host answers, checked by
  membership at the reply) is the one boundary decode route; DI-08 moves to ruled with the answer the
  Decision 12 note itself gives (the persisted description plane ships, the authoring plane stays
  archive-tier; `2026-09-10-schema-at-boundaries.md:11-13`, untracked). (b) Leave it in notes.
- *Recommendation:* (a). Cite "Decision 12" with rows 5, 9 and 39, never the bare "D12": in tracked files
  "D12" also names the certificate protocol and scout C's `Repr` choice (verifier, pedigree §2.8;
  PROG-D13 partly).
- *Row:* "Decision 12 (2026-09-10): every boundary value carries an Effect Schema: the row's columns and
  the program's exit by `EffTy.document`; host data enters by typed host answers checked by membership;
  the S-5 gate is row 5. DI-08: ruled."

**Row 123 — The in-program schema operation (native schema support's operation).**
- *Options.* (a) A decision-free `Σ_core` machine operation `decode (target : Ty)`,
  `unknown → target ! prod (lit "SchemaError") string` (NS3). (b) A total term atom returning `except`.
  (c) A host row. (d) A typed `Eff` hole (W9), which needs a hole carrier. (e) A `Forms` template.
  (f) Keep refusing.
- *Recommendation:* (a) in principle now; it lands after stage 1 and after the JSON image at `unknown`
  is fixed, when a program that decodes inside is taken on. (d) only for effectful transformations.
- *Row:* "Decoding inside a program is one decision-free operation at a declared type, `decode τ`, whose
  meaning is the codec's fold on the pure fragment; effectful transformations stay refused names until a
  typed hole carrier exists."

**Row 124 — Recursive types.**
- *Options.* (a) Open the row now: recursion through nominal declarations in `Σ_app` (precedents
  `Shape.named`, rc.112's `Suspend` and `Reference`), `Fits` by recursion on the value, `sub` nominal,
  DI-67's inhabitance as a least fixed point (`{next: T}` is empty). (b) μ-types in `Σ_core`.
  (c) Leave it untracked.
- *Recommendation:* (a), no slice: 0 of 5 programs need them; `suspend(` has 5 uses in 3 v4 projects
  (EFF-02); JSON bodies under row 123 and the issue tree would.
- *Row:* "Recursive types: tracked; through nominal declarations in `Σ_app` when a program needs them."

**Row 125 — Keyed collections.**
- *Recommendation:* no slice until a program needs one (0 of 5; `Schema.Record(` 220 uses in 11 v4
  projects, EFF-02; 48 census heads in 7); then a map constructor whose key, duplicate and order policy
  is frozen first (DI-78; `machine-state.md` §5, §7). Records with index signatures are not records.
- *Row:* "Keyed maps: a separate constructor with DI-78's contract, when needed; not an index signature
  on records."

**Row 126 — Equality at records.**
- *Recommendation:* `eq` stays refused at records (DI-35: `===` on objects compares references,
  `Machine/Term.lean:215-216`); `Val.eqAt : Ty → Val → Val → Bool` with `eqAt t v w = true ↔ v = w` on
  members, printed as `Equal.equals`, when a program needs it (0 of 5). Stage 1 keeps the refusal as a
  red control.
- *Row:* "`eq` at a record stays refused; `Val.eqAt` lands with the first program that compares records."

**Row 127 — DI-67's admission gap.**
- *Evidence.* DI-67 rules that every admitted column is inhabited or `never`; admission enforces it for
  `int` only. `prod never nat` is admitted at a program answer and at a host-row request column, and
  `except never never` at a host-row answer (tested; `fits_except_never_never_empty` and
  `hasTy_prod_never_false` proved; PED-10, rerun). The sentence broken is in the frozen
  `Test/contracts/foundation-wave2.contract.md:217`. Also, an answer-only template parameter (`var 0`,
  bound by no request) is admitted and typed at `never` (tested; no canonical row has one).
- *Options.* (a) A decidable `inhabited : Ty → Bool` (a fold) with `inhabited τ = true ↔ ∃ w v, Fits w v
  τ`, checked at admission with a located refusal. (b) `normalize` annihilates empty products and
  `except never never`: it changes canonical forms and printed types, and `tsgo` does not reduce an
  empty tuple (`readonly [never, number]` is not assignable to `never`, TS2322; tested here), so
  B-print's mutual assignability breaks. (c) Restate DI-67.
- *Recommendation:* register the counterexample now (proposed line: "DI-67's inhabitation is enforced
  for `int` only", witness `pedigree/verify-Probe.lean` V3, SEEDED); repair by (a) as stage 1's first
  commit (it is R3.7). The typed-state proofs do not read the certificate (PED-24 partly), so nothing in
  Codex's queue waits on it.
- *Row:* "DI-67 enforced by a decidable inhabitance check at admission, agreeing with `Fits`; lands as the
  first commit of the records slice."

**Row 128 — The two exact embeddings AGENTS.md names.**
- *Options.* (a) Amend the vocabulary now: `Ty.schema`/`ofSchema` and the JSON codec are retractions
  (proved) whose exactness is owed, citing the counterexamples. (b) Prove exactness now for today's
  `Ty`: NS1's whole-check comparison and the `var` repair, NS2's canonical-branch check and a named
  key-order normaliser.
- *Recommendation:* (a) now (AGENTS.md: "a read without exactness is a widening"); (b) as stage 1's
  second commit, before any record arm claims K2.
- *Row:* "Until their exactness theorems land, `ofSchema` and the JSON codec are retractions."

**Row 129 — Register and tracked-text repairs** (coordinator; no owner content; cheap, now).
- DI-95 → landed (row 56, `0a2cb898`; PED-18).
- DI-08 → per row 122; its path `Store/Shape.lean` → `Store/Domain/Shape.lean` (verifier, pedigree §2.9).
- System-map §1.1: "under DI-47's compatibility gate over the retained baseline" → what runs: the
  wire-tag loader's refusals, the case-site policy, the baseline as a review authority (the comparator
  was cut at `243ca0dd` on the owner's testing ruling, `docs/STATE.md:443-445`; PROG-D12, TREE-D18
  partly); the baseline policy file names the four 2026-09-18 appends.
- Row 41: "the codec agrees with rc.112" → "for Lean's encodings and the decoded canonical images, under
  the strict field policy" (EFF-08 partly).
- Row 3 (`Ty.app`, "do") is superseded by row 119; R3's `Ty.foreign` is dropped for records (classes go
  to `Σ_app`, row 2) (PED-09 partly).
- Row 39's `Arch/Accepts.lean` → `Schema/Accepts.lean` (TREE-D10).
- Stale text: `README.md:34-35` (typed effectful transformations and schema endpoints were deleted at
  `b08f3b58`; PED-18); `Schema/Bridge.lean:13` ("for all types": the theorem needs `t.closed`) and `:19`
  ("16 constructors": 20); `Data/JsonNumber.lean:12-16` (nine cited modules missing); the `wire-tags.json`
  comment and `docs/GENERATED.md:89` still cite the deleted compatibility lane (verifier, tree D18).
- The 2026-09-10 boundary rule (B-print, B-accept, B-row, B-tape): write it into a tracked place or
  retire it; it decides between record designs at B-tape and B-accept (verifier, tree §2.1).

**Row 130 — `catchTag`'s residual.** rc.112's `catchTag` removes the caught tag from the error type;
`catchIfError` (`Program/Typing/Rules.lean:217`) subtracts only when no other tag remains (DI-17), so p2's
`handle` keeps both caught tags in its error column (tested; PROG-D3 partly). Boundary decision T3 asks
for `Exclude`. *Recommendation:* subtract the caught literal tag, with the retained-failure evidence DI-17
requires, together with stage 2 (both read the tag decision). *Row:* "`catchTag` subtracts its literal tag
from the error column (rc.112 `Types.ts:158`), with DI-17's evidence; lands with variants."

**Row 131 — A number-to-text atom.** p2's `` `no user ${e.id}` `` and p3's log lines print numbers; none
of the 33 atoms does (RC9, tested; PROG-D2 partly). *Recommendation:* one atom by DI-89's atom route (3
compile-forced definitions, the prelude, LCNF), independent of records, any time after F is merged
(it re-cuts the LCNF group too). *Row:* "Add `natToString` (rc.112 template-literal and `String(n)` semantics on naturals)."

**Row 132 — Keep the typed state's coupling to `Ty` in one module.** *Recommendation:* the M5–M7 brief
says: "no case analysis on `Ty` outside `Laws/Program/Typed/Membership.lean`; the typed state reads
values through `Fits`'s lemmas", checked by the environment census (`programs/verify-TyProofCensus.lean`),
not by a grep for `induction` (it misses `cases`, `match` and `rcases`; PROG-D7 partly). Cost now: one
sentence; benefit: the records slice costs the typed state one module. *Row:* "M5–M7 keep `Ty` case
analysis inside `Typed/Membership.lean`."

---
## 6. Pedigree and corrections

### 6.1 What the seats got right (confirmed or partly confirmed, rerun here)

| Finding | Seat → verdict |
| --- | --- |
| Records are every model program's first data need (5 of 5); payloads 4 of 5; recursive types and structural equality 0 of 5 | PROG-D1 confirmed |
| No ruling says how a program uses a schema; DB-15 refuses records; row 2 and D10 are open; DI-08 is open; row 39 is unexecuted | PED-01, -02, -07, -13, -17 confirmed; TREE-D09, D10 confirmed |
| Positional values plus TypeScript's width rule make `fits_sub` false (proved); width needs labeled values (proved in two models) | TREE-D08 partly; EFF-09 partly; PROG-D9 partly |
| A registered single-motive eliminator keeps `induction t with` on both encodings | TREE-D04 confirmed; the opposite claim refuted (PROG-D8) |
| The typed state reads `Ty` in one module, `Typed/Membership.lean` | PROG-D7 partly (the module claim holds by an environment census; the named five do not) |
| The bridge's retraction and the codec's laws hold; neither arrow is exact | TREE-D12, D13 partly; PED-04 confirmed; PED-05 confirmed and stronger |
| DI-67 is enforced for `int` only | PED-10 confirmed, and wider |
| `Representation` covers rc.112's AST; native support is growth of `Ty`, not a second carrier; decoding is decision-free | EFF-06 partly; EFF verifier's one thing |
| The record stage goes after G and H2 part one, by default after the milestone | PROG-D19 confirmed |
| The corpus counts (`Schema.Struct` 2,730 uses in 12 of 15 v4 projects; `decodeUnknown*` 931 in 11) | EFF-02 confirmed (recount within 4) |

### 6.2 What the verifiers corrected

| Seat claim | Correction (verdict) |
| --- | --- |
| Tree: exact records keep every existing law shape | False on the seat's own model: the record arm read fields in written order while `normalize` sorts them, so `hasTy_normalize` fails (TREE-D08 partly; verifier proved). Repaired here: a canonical-order read keeps the law with no premise and stays a fold (synthesis model, proved) |
| Tree D24, as the verifier strengthened it: the formation refusal of a repeated field name is forced by `hasTy_normalize` | True for written-order reads (positional or named). Under the canonical-order read the law holds with repeats, because the check and `normalize` both keep the first occurrence (synthesis model, `#guard`s); the refusal is still needed, because TypeScript refuses a repeated name (TS2300 in a type, TS1117 in a literal; tested here with `tsgo`) |
| Tree: only `Shape` has records | `Representation` has `objects` with property and index signatures (TREE-D11 partly) |
| Tree: the `Test` bill is 3/1 and the oleans are stale; the proof census is 147 | 5/2, fresh (TREE-D01 partly); 183 by the broad census, 8 principle-split proofs (TREE-D03 partly) |
| Tree: the frozen baselines list 16 `Ty` constructors | 15 (TREE-D18 partly) |
| Tree: a JSON object reply has no decode route | The keyed reader decodes `{ctor,args}` objects, untyped; "no typed route" stands (TREE-D14 partly) |
| Tree: the reply check of `90df5d21` answers DI-62's reason | Only for host payloads; a program-made failure needs a type-level condition (TREE-D16 partly) |
| Pedigree: the codec is exact modulo field order | False at overlapping unions: a later branch's image decodes (PED-06 partly; verifier V2) |
| Pedigree: Decision 12 appears only in docstrings | Row 5 and two core documents name it; still not a ruling, because DI-08 never moved and no tracked file holds its text (PED-03 partly) |
| Pedigree: signed integers have no route; DB-15 hardened a step-1 choice whose reason has gone | DB-15's recommended text calls `int` the cheapest to lift (PED-15 partly); "step 1" was dispatch order and "columns are pairs" still stands (PED-20 partly) |
| Effect: the decode gap is live and unwritten | Written and owner-approved (`schema-codec.contract.md:26-28`); equal to rc.112's `"error"` mode (EFF-08 partly) |
| Effect: the census refusals call for a wider program-head table | All 2,888 are top-level declarations: they call for DI-89's declaration reader (EFF-01 partly) |
| Effect: decode takes JSON text; the reply check would decode JSON | 37 of 40 sampled sites decode structured values; a reply is a `Val` (EFF-12, EFF-14 partly) |
| Effect: class-declared records need a nominal marker because `tsgo` refuses object literals at classes | `tsgo` is structural at `Schema.Class`; the name is forced by rc.112's run-time identifier check, so it belongs in `Σ_app` (EFF-11 partly) |
| Effect: binary64 is row 108's; `.issue` is read 36 times | Row 109, DI-67, T5 (EFF-15 partly); 5 real reads (EFF-05 partly) |
| Programs: the spine turns each induction into a mutual pair | Refuted: one eliminator keeps plain `induction` (PROG-D8) |
| Programs: the JSON normaliser is an open decision | Already taken on the strict side; `N` only reorders (PROG-D10 partly) |
| Programs: the handler's error tags are absorbed; the 12 `tsgo` errors are all positional projections | An artefact of the pair spelling; the gap is `catchIf`'s subtraction (PROG-D3 partly); 10 + 2, the 2 from the error channel (PROG-D4 partly) |
| Programs: payloads break three lemmas; route B waits for a program | Six lemmas (PROG-D11 partly); about 756 decode heads make route B a scope call (PROG-D14 partly) |
| Programs: RC12 shows a record service carrier is refused | `Author.build` refuses every new service today; records are not the cause (PROG-D3, D20 partly) |
| All four: needs listed as capabilities | Restated as theorem shapes in §2 and §3 (TREE-D11, PED-23, EFF-02, PROG-D5 partly) |

### 6.3 What all four seats missed (the verifiers' findings, used here)

- `normalize` distributes a product over its union columns; records need the rule "factors, not
  distributed" (verifier, programs §2.1; tree D23).
- The coercive-width design that rc.112's own decoder follows (verifier, tree §2.1).
- No arrow is named between `Ty.record` and the store's `Shape.struct`, whose fields are in declaration
  order (verifier, tree §2.10). Under row 119's (b1) that arrow is an exact embedding modulo the
  field-order normaliser.
- No conservativity statement exists for a `Σ_core` append now that the comparator is gone
  (verifiers, tree §2.14 and programs §2.14).
- The case-site pin is the gate an append trips (verifier, tree §2.5).
- The DI-67 repair edits admission, which Codex's slices also edit (verifier, pedigree §2.11).

### 6.4 Literature, marked

| Work | Mark | Where | Bears on |
| --- | --- | --- | --- |
| Wand (LICS 1987 in the types scout; "1989" in the type-algebra note); Rémy (1994); Gaster and Jones (1996) | **by name**, with a reasoned verdict: row variables are a "false friend" here, since `Eff` has no binder and `Ty` is ground | types scout 2026-09-09 §2.2, §2.5 (untracked); listed as assumed in the type-algebra note §8 and the model-probe synthesis | why closed records, not row polymorphism (PED-22 partly; verifier, pedigree §2.12) |
| Leijen, *Extensible Records with Scoped Labels* (TFP 2005) | **by name** | types scout §2.2 | label removal as the model of `catchTag`'s residual (row 130) |
| Morris and McKinna (POPL 2019) | **assumed** | type-algebra note §8 | nothing used |
| Leijen (POPL 2017); Hillerström and Lindley | **read** (lit-papers Q4) | effect rows, not record rows | nothing here |
| Swierstra, *Data Types à la Carte* (2008) | **read** | model-probe pedigree | R2's conservativity, not data |
| Lean 4.33.1 deriving and induction facts (F1–F6) | **read**, and now **tested** (`E2Eliminator`, `RecordSpine`, `ProbeSpine` rerun here; `E1Instruments` rerun by the tree verifier) | type-algebra note §0 | row 119 (c) |
| Frisch, Castagna and Benzaken (2008); Castagna and Xu (2011) | **assumed** | type-algebra note §5.3 | the registered incompleteness of `sub` (row 119 d) |
| Mattick, *Specifying Hyperdocuments with Algebraic Methods* (2014) | **read** in full | papers review §1.2, A5 | schemas as signatures; `print_conforms` proposed, absent |
| McBride (2011); Dagand and McBride (2012), ornaments | **by name** | coherence principle §1 | `Ty` inside `Representation` |
| Rendel and Ostermann (2010); Matsuda and Wang (2013); Foster et al. (2007); Pickering, Gibbons and Wu (2017) | **by name** | coherence principle | the three K2 laws |
| Power and Robinson; Levy, Power and Thielecke; Katsumata; Orchard et al. (graded arrows) | **by name** | coherence principle §4b | `Transform`, deleted |
| rc.112 `Schema.ts`, `SchemaAST.ts`, `SchemaParser.ts`, `SchemaIssue.ts`, `SchemaGetter.ts`, `SchemaTransformation.ts`, `SchemaRepresentation.ts` | **read** at cited lines; behaviour **tested** on bun 1.4.2 (T1–T21, P1–P7, V1–V5; rerun here) | effect seat and verifier | NS1–NS4, row 119's boundary projection |
| TypeScript assignability (`tsgo` 7.0.0-dev.20260629.1) | **tested** (rerun) | effect, programs and their verifiers | R3.3, R3.9, EFF-10, EFF-11 |
| JSON Schema 2020-12; RFC 6901, 6902 | **by name** | standards survey | no consumer |

The record literature is by name or assumed throughout; nothing in this probe promotes it. The
estate's own algebra carries the design: `Canonical`'s K2 laws, the codec's retraction, the generated
folds, and the models proved in this probe.

---
## 7. Codex queue impact

**Nothing changes for D, F, G, H1 or H2 part one.** No file in their scope would need a record arm:
the `Ty` matches they contain close with a catch-all (`Program/Checker.lean`, `externalValue` in
`Program/Compile.lean`), the typed-state modules they edit do not case on `Ty` (census, PROG-D19), and
none touches `Ty.lean`, `Schema/` or the codec (reading of `git show --stat` on the eight branch
commits). The data work stays on paper until D and F are merged.

**What Codex is actually waiting on** (reading of the branch, §4.1): three owner decisions, none of them
about data — G's fourth-fixture amendment, H1's ruling on terminal delivery against saved-code typing,
and H2 part one's bounded follow-up for the two false test statements. D and F are done and unmerged;
D merges alone through `fa5add20`, F after it (`d20f3292`).

**Facts the coordinator needs when the data work starts.**
- F re-cut `ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml` and their closure manifests, and edited
  `Program/Compile.lean`; stage 1 re-cuts the same group, so it starts from a base that contains F.
- R3.7's inhabitance repair edits `Program/Admission.lean` and adds an `AdmittedProgram` field that
  `Laws/Run.lean:208-219`, `Laws/Program/CheckedTyping.lean:112-115`, `Api/Built.lean:23` and
  `Api/HostSession.lean:85` consume (PED-24 partly); the `Σ_app` slice also edits admission. Sequence them.
- One sentence for the next M5–M7 brief (row 132). Nothing else in Codex's briefs changes.

**What the first data brief would contain.**
1. *Base and place:* `refactor/phase1-phase3` with Codex's D and F merged (and whatever of G, H1 and H2
   has landed), by default after the M5–M7 milestone; its own worktree; one compiler at a time; commits by explicit paths after
   narrow builds.
2. *Rulings it rests on:* rows 119, 122, 127, 128; row 39 executed first.
3. *Commit series:*
   1. R3.7: `inhabited : Ty → Bool` (a fold), its law against `Fits`, the admission refusal at answer,
      error, request and table columns; DI-67's counterexample marked REPAIRED.
   2. Exactness for today's `Ty`: `decode` refuses a branch image the encoder would not write; the
      key-order normaliser named; `ofSchema` compares whole checks and refuses the type-parameter
      handle; the two exactness theorems.
   3. Generator extensions: the single-motive eliminator (and the equality) for nested families; TyView
      over a field list; the variance table's shape for a head of variable arity.
   4. `Ty.record` appended: the hand arms, the canonical-order membership arm, `normalize`/`Normal`/
      `key`/`sub` and their laws, `hasTy_normalize`'s record case; the generated groups regenerated in
      the fixed order; `cases-policy.json` re-seeded; wire tag 20; the OCaml hand mirrors.
   5. Schema and JSON arms: `schema`/`ofSchema` at objects; the codec's object layout; the laws extended.
   6. Two term forms (construction, field projection): frozen contract and falsifiers first (DI-78),
      then typing lemmas, behaviour laws, printer and reader with `read_print`/`read_exact`.
   7. Row 68's vectors over records (permutations agree; width pairs classified `incomplete`).
   8. The acceptance program: p2's handler end to end (§3.2).
4. *Red controls kept as fixtures:* width with positional values is unsound; the written-order read is
   not normalization-invariant; a repeated field name is refused; `eq` at a record is refused; a width
   subsumption inside a program is refused by name; a record with a field at `never` is refused as
   uninhabited; the Lean decoder refuses an extra key that the adapter strips.
5. *Stop rules:* a classifier that would put `record` in a positive class by a catch-all; a generated
   path outside the named groups; any existing golden that changes bytes, or any corpus admission
   verdict that changes (R3.8).
6. *Receipt:* AGENTS.md's handoff form, with the axiom print of every new theorem and the measured file
   count against §3.3's estimate.

---
## 8. Open questions, each with a proposed owner decision

1. **Width subtyping: ever, and how?** Proposed: not in stage 1. Decide after stage 1 from row 68's lane:
   how many record pairs real programs meet as `incomplete`. If width is needed, choose between labeled
   values (row 119 a2) and coercion (a3) then, with a probe of the coercion term's cost.
2. **Field order** (row 119 b). Proposed: set semantics, canonical by name.
3. **Does the 2026-09-10 boundary rule stand as a ruling?** It is the reason for projecting at the
   adapter (B-row) and for named refusals (B-accept), and it lives only in a gitignored note. Proposed:
   yes; write it into `host-boundary.md` with row 122.
4. **The payload carrier** (row 120 c). Proposed: measure a new handle-free family against reading
   through the codec before ruling.
5. **Row 39 before stage 1?** Proposed: yes; it is ruled, deletion-only and independent of Codex.
6. **The JSON image of host data at `unknown`** (needed by row 123) **and row 10's one `Val → Json`.**
   Proposed: decide together when row 123 lands; the type-directed codec stays the boundary's arrow.
7. **When is a program that decodes inside taken on?** About 756 decode heads against 2,032 for
   `Schema.Struct` in the ingest census (PROG-D14 partly). Proposed: right after stage 1, with p2 as
   written (it decodes a SQL row object inside its layer).
8. **Record term forms: atoms or `Term` constructors?** Proposed: atoms (DI-89's atom route; no `Term`
   family append), with field labels read from literal arguments as `pair` reads its tag; the contract
   frozen first (DI-78).
9. **Is `Ty.foreign` still wanted?** Proposed: not for records. Class-declared records go to `Σ_app` with
   a duplicate-identifier refusal (rc.112 identifies a class by its identifier at run time: V2, V4,
   tested, rerun); `Ty.foreign` only if reading a foreign schema needs an opaque type (row 1's trigger).
10. **Stage 1 before or after the milestone?** Proposed: after, by the owner's route; between the
    `Σ_app` slice and the M5–M7 proofs only if the owner wants M5–M7 stated over records.

---

## 9. Receipt

**Base and head.** `refactor/phase1-phase3` at `ba9783c3` (`bc77e97f` plus documents). Codex's
`codex/slice6-fixes` at `c42f4a46` (it was `3b825aa8` when this seat began), read from the main
repository's refs only. `git status` clean at the
start and at the end (tested).

**Files written.** In the tree: this file only. In the session scratchpad
(`/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/`,
session-local, so the results are copied below): `synth-rerun/run.sh`, `compare.py`, `summary.txt`, the
37 rerun logs, `host/tsgo.log` and four `bun` logs; `synth-probe/SynthRecordOrder.lean` with its logs
(`.run1.log`, the failed first compile; `.run2.log` = `.log`), `SynthRecordOrderRed.lean` with its log;
`synth-probe/ts/` (`dup-{green,red}.ts`, `empty-{green,red}.ts`, four tsconfigs, `dup.log`, `empty.log`).
The probe's source is Appendix A; the `tsgo` results are in the table below.

**Commands and results.**

| Command | Result |
| --- | --- |
| `bash …/scratchpad/synth-rerun/run.sh` (each probe: `bash …/serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`, one at a time) over 37 probes: tree `RecordNested`, `verify-RecordRed`, `verify-CoerciveWidth`, `RecordSpine`, `explore/E2Eliminator`, `SchemaProbe`, `verify-TyBillCensus`, `verify-TyProofCensus`, `TyBillProbe`; pedigree `PedigreeProbe`, `PedigreeRed`, `verify-Probe`, `verify-Red`; effect `lean/ProbeCodecStatus`, `lean/ProbeRecordModel`, `lean/ProbeRed1`–`4`, `verify-ProbeTreeFacts`, `verify-ProbeModelWitnesses`, `verify-ProbeRed5`–`9`; programs `ProbeTodayP2`, `ProbeRedControls`, `ProbeSpine`, `ProbeRecordK2`, `RedMustFail`, `ProbeBill`, `verify-SpineInduction`, `verify-Refute`, `verify-WidthCoupling`, `verify-StageC`, `verify-TyProofCensus` | exit 0 for the 25 green probes; exit 1 for the 12 red controls (`PedigreeRed`, `verify-Red`, `ProbeRed1`–`4`, `verify-ProbeRed5`–`9`, `RedMustFail`), as recorded; started 03:07, done 03:09 |
| `python3 …/synth-rerun/compare.py`, then `diff` on the eight one-line differences | every log equal to the seat's or verifier's log; the only differences are the appended `time` and `exit=` lines |
| `tsgo -p` (7.0.0-dev.20260629.1) on `effect/ts` green/red, `effect/verify-ts` green/red, `programs/ts` green/red, `programs/verify-ts` × 2 | 0 / 1 (7 errors: TS2322, TS2353, TS2375 ×3, TS2740 ×2); 0 / 1 (2); 0 / 1 (12: TS2345 ×9, TS2375 ×3); 1 (10) and 1 (2) — as the seats and verifiers recorded; `noEmit`, nothing written |
| `bun run` (1.4.2) `effect/ts/rc112-schema-behaviour.ts`, `effect/verify-ts/verify-parse-options.ts`, `verify-class-runtime.ts`, `verify-class-runtime-red.ts` | `ALL OK` ×3; the red twin `1 MISMATCH(ES)`, exit 1; logs equal to the seat's apart from the version and `exit=` lines |
| `bash …/serial.sh lake env lean -M6144 -DwarningAsError=true …/synth-probe/SynthRecordOrder.lean` | run 1 exit 1 (`simp` used `h2 : p.1 = q.1` as a rewrite, leaving three unused `simp` arguments and two type mismatches; one `rw` pattern was hidden by unfolding the algebra; all fixed by `if_pos`/`if_neg` and a `record_congr` lemma); run 2 exit 0, every `#guard` holding |
| the same for `SynthRecordOrderRed.lean` (the RED CONTROL) | exit 1 with exactly one error, at the asserted `#guard` (`… did not evaluate to true`) |
| `tsgo -p` on `synth-probe/ts/tsconfig.green.json` and `tsconfig.red.json` (scratchpad; `noEmit`) | green exit 0: `{ b: "x", a: 1 }` at `{ readonly a: number; readonly b: string }`; red exit 1: TS2300 ×2 and TS2717 on a repeated property in a type literal, TS1117 on a repeated property in an object literal |
| `tsgo -p` on `synth-probe/ts/tsconfig.empty-green.json` and `tsconfig.empty-red.json` (scratchpad; `noEmit`) | green exit 0 (`never` is assignable to `readonly [never, number]`); red exit 1, TS2322: `readonly [never, number]` is not assignable to `never` |
| `git show --stat e75d9e61`; `git show e75d9e61:src/Effect4/Schema/Endpoint.lean` | `Schema/Endpoint.lean` (+395), `Schema/Transform.lean`, `Schema/Image.lean`, `Schema/Bridge.lean` added on 2026-09-11; `def record : List (String × Ty) → Ty` at `:384`, `structure Endpoint` at `:131`, `structure SchemaFn` at `:276` |
| `git show --stat b08f3b58`; `git show b08f3b58^:src/Effect4/Schema/Transform.lean` | `Schema/Transform.lean`, `Laws/Schema/Transform.lean`, `Schema/Endpoint.lean` deleted; `structure Transform (σ) (Γ) (A B E) (R)` at `:39` before the deletion |
| `git log`/`git show --stat` on `codex/slice6-fixes` (`31e44efc` … `c42f4a46`); `git show codex/slice6-fixes:docs/research/2026-09-30-seat-codex-slice6-receipt.md`; `git show c42f4a46` | §4.1; `c42f4a46` changes two receipt files only |
| `grep -n` for every tracked line cited (DB-15, AGENTS.md, DI rows, system-map R3, host-boundary §4.4 and §5, the two contracts, `STATE.md:443-445`, `Rules.lean:217`, `Membership.lean`, `Admits.lean:183`, `TypeAlgebra.lean:309`) | as cited |

**Axioms of the new probe, verbatim.**

```text
'SynthRecord.T.ind'' does not depend on any axioms
'SynthRecord.canon_map' depends on axioms: [propext]
'SynthRecord.canon_idem' depends on axioms: [propext, Quot.sound]
'SynthRecord.hasTy_normalize' depends on axioms: [propext, Quot.sound]
'SynthRecord.written_order_not_invariant' depends on axioms: [propext]
'SynthRecord.hasTyW_normalizeD' depends on axioms: [propext, Quot.sound]
```

SHA-256: `SynthRecordOrder.lean` `b7bdf58b5d0f031628a5aa0283d86d7d255c3f3e477d322f78eb5ef5ee2ada5e`;
`SynthRecordOrderRed.lean` `31bd1c63ba8a36852b76ef1b29e08409adc9d514b5a008fab4d7a0485f8d42f0`.

**Read.** The eight seat notes and verifications in full; the authorities and code listed in §0; the
Decision 12 note (`2026-09-10-schema-at-boundaries.md:1-14`); the model-probe synthesis R3, §5.5 and D10; the type-algebra note §1.3; the 2026-09-10 boundary-decisions note
§1; the ingest census head table; the types scout §2.2 and §2.5; the slice 6 brief's addendum 5; the
design-basis refresh brief; Codex's receipt on its branch ("After addendum 5", G).

**Not run, and why.** No `lake build`, `make`, generator, `git add` or `git commit` (the brief). No tracked
file edited. `/Users/pooks/Dev/lean4-effect4-slice6` not touched.

**What this synthesis could not settle** (each bounded or assumed):
- whether the canonical field sort lowers through LCNF without a new extern (assumed; `normalizeRow`'s key
  comparison already lowers);
- the subtyping algebra at records (`sub_trans_core`, `sub_antisymm_normal` through `TyView.sub_eq_args`):
  no seat probed it; the exact rule fits the view law with names as payload by reading only;
- the cheapest payload carrier (row 120 c) and the coercion term's cost (row 119 a3): unmeasured;
- stage 1's file count (55–65, assumed) and how much of the ~115-line order machinery `Effect4.Row`
  already supplies (reading);
- conservativity as a theorem: only its finite form (goldens and verdicts) is proposed;
- `tsgo` on a printed module with object types and member access: not run; it is stage 1's acceptance;
- every model theorem here is about a model (names as `Nat` keys, no unions, no handles, no world), not
  about the tree's `Fits`.

---
## Appendix A. The synthesis model probe (`SynthRecordOrder.lean`)

Compiled through the one-compiler lock with `-M6144 -DwarningAsError=true`: exit 0; axioms in §9. The
red control `SynthRecordOrderRed.lean` is this file with the `#print axioms` lines removed and one
guard appended, `#guard SynthRecord.hasTyW (SynthRecord.normalize SynthRecord.permuted)
SynthRecord.laidOut = SynthRecord.hasTyW SynthRecord.permuted SynthRecord.laidOut`, which fails as it
must (exit 1, one error). Probe-grade: `ins_map` uses unqualified `simp`, which AGENTS.md bars only
under `src/`. To rerun, copy the block into a `.lean` file and compile it the same way.

```lean
/-! Synthesis seat, data probe (2026-10-01). Question: with exact records whose canonical field
order is by key (`normalize` sorts), can the membership check read a record value in canonical
order and still be a fold, with `hasTy (normalize t) = hasTy t` and no premise? The tree
verifier proved the written-order arm breaks that law (`hasTyV_normalize_fails`) and left the
repair unpriced. Model only: field names are `Nat` keys, no unions, no handles, no world.
Red control inside: the written-order arm (`hasTyW`) is not normalization-invariant. -/
set_option autoImplicit false

namespace SynthRecord

inductive T where
  | nat
  | str
  | record (fields : List (Nat × T))

inductive V where
  | nat (n : Nat)
  | str (s : String)
  | ctor (args : List V)

/-- Insert by key; an existing equal key wins, so a left fold keeps the first occurrence. -/
def ins {α : Type} (p : Nat × α) : List (Nat × α) → List (Nat × α)
  | [] => [p]
  | q :: qs => if p.1 < q.1 then p :: q :: qs else if p.1 = q.1 then q :: qs else q :: ins p qs

/-- Canonical field order: ascending by key, the first of a repeated key kept. -/
def canon {α : Type} (xs : List (Nat × α)) : List (Nat × α) :=
  xs.foldl (fun acc p => ins p acc) []

/-! ## The fold: one carrier field per constructor. -/

structure Alg (A : Type) where
  nat : A
  str : A
  record : List (Nat × A) → A

mutual
def cata {A : Type} (alg : Alg A) : T → A
  | .nat => alg.nat
  | .str => alg.str
  | .record fs => alg.record (cataFields alg fs)
def cataFields {A : Type} (alg : Alg A) : List (Nat × T) → List (Nat × A)
  | [] => []
  | (n, t) :: fs => (n, cata alg t) :: cataFields alg fs
end

/-- Positional fit of argument values against checkers. -/
def fitPos : List V → List (Nat × (V → Bool)) → Bool
  | [], [] => true
  | v :: vs, (_, c) :: cs => c v && fitPos vs cs
  | _, _ => false

/-- The canonical-order read: the algebra receives each field's checker with its key and sorts
them; the recursion stays the generated fold's. -/
def hasTyAlg : Alg (V → Bool) where
  nat := fun v => match v with | .nat _ => true | _ => false
  str := fun v => match v with | .str _ => true | _ => false
  record := fun rs v => match v with | .ctor vs => fitPos vs (canon rs) | _ => false

def hasTy (t : T) : V → Bool := cata hasTyAlg t

/-- The written-order read (the red control): the same fold without the sort. -/
def hasTyWAlg : Alg (V → Bool) where
  nat := hasTyAlg.nat
  str := hasTyAlg.str
  record := fun rs v => match v with | .ctor vs => fitPos vs rs | _ => false

def hasTyW (t : T) : V → Bool := cata hasTyWAlg t

mutual
def normalize : T → T
  | .nat => .nat
  | .str => .str
  | .record fs => .record (canon (normalizeFields fs))
def normalizeFields : List (Nat × T) → List (Nat × T)
  | [] => []
  | (n, t) :: fs => (n, normalize t) :: normalizeFields fs
end

/-! ## The nested eliminator (the `Json.ind`/`Val.ind` idiom). -/

theorem T.ind' {motive : T → Prop} (nat : motive .nat) (str : motive .str)
    (record : ∀ fs, (∀ p ∈ fs, motive p.2) → motive (.record fs)) : ∀ t, motive t :=
  fun t =>
    T.rec (motive_1 := motive) (motive_2 := fun fs => ∀ p ∈ fs, motive p.2)
      (motive_3 := fun p => motive p.2)
      nat str record
      (by intro _ hmem; cases hmem)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      (fun _ _ ih => ih)
      t

/-! ## Order lemmas over `Nat` keys. -/

def Sorted {α : Type} (l : List (Nat × α)) : Prop := l.Pairwise (fun a b => a.1 < b.1)

theorem ins_map {α β : Type} (f : α → β) (p : Nat × α) (l : List (Nat × α)) :
    ins (p.1, f p.2) (l.map (fun q => (q.1, f q.2))) = (ins p l).map (fun q => (q.1, f q.2)) := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    by_cases h1 : p.1 < q.1
    · simp [ins, if_pos h1]
    · by_cases h2 : p.1 = q.1
      · simp [ins, if_neg h1, if_pos h2]
      · simp [ins, if_neg h1, if_neg h2, ih]

theorem foldl_ins_map {α β : Type} (f : α → β) (xs acc : List (Nat × α)) :
    (xs.map (fun q => (q.1, f q.2))).foldl (fun a p => ins p a) (acc.map (fun q => (q.1, f q.2))) =
      (xs.foldl (fun a p => ins p a) acc).map (fun q => (q.1, f q.2)) := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.foldl_cons]
    rw [ins_map f x acc]
    exact ih (ins x acc)

theorem canon_map {α β : Type} (f : α → β) (xs : List (Nat × α)) :
    canon (xs.map (fun q => (q.1, f q.2))) = (canon xs).map (fun q => (q.1, f q.2)) :=
  foldl_ins_map f xs []

theorem mem_ins {α : Type} (p x : Nat × α) (l : List (Nat × α)) (h : x ∈ ins p l) :
    x = p ∨ x ∈ l := by
  induction l with
  | nil =>
    simp only [ins, List.mem_singleton] at h
    exact Or.inl h
  | cons q qs ih =>
    by_cases h1 : p.1 < q.1
    · simp only [ins, if_pos h1, List.mem_cons] at h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_cons.mpr (Or.inl h))
      · exact Or.inr (List.mem_cons.mpr (Or.inr h))
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2] at h
        exact Or.inr h
      · simp only [ins, if_neg h1, if_neg h2, List.mem_cons] at h
        rcases h with h | h
        · exact Or.inr (List.mem_cons.mpr (Or.inl h))
        · rcases ih h with h' | h'
          · exact Or.inl h'
          · exact Or.inr (List.mem_cons.mpr (Or.inr h'))

theorem ins_sorted {α : Type} (p : Nat × α) (l : List (Nat × α)) (hl : Sorted l) :
    Sorted (ins p l) := by
  induction l with
  | nil => exact List.pairwise_singleton _ p
  | cons q qs ih =>
    have hq : ∀ y ∈ qs, q.1 < y.1 := (List.pairwise_cons.mp hl).1
    have hqs : Sorted qs := (List.pairwise_cons.mp hl).2
    by_cases h1 : p.1 < q.1
    · simp only [ins, if_pos h1]
      refine List.pairwise_cons.mpr ⟨?_, hl⟩
      intro y hy
      rcases List.mem_cons.mp hy with hy | hy
      · rw [hy]; exact h1
      · exact Nat.lt_trans h1 (hq y hy)
    · by_cases h2 : p.1 = q.1
      · simp only [ins, if_neg h1, if_pos h2]
        exact hl
      · simp only [ins, if_neg h1, if_neg h2]
        refine List.pairwise_cons.mpr ⟨?_, ih hqs⟩
        intro y hy
        rcases mem_ins p y qs hy with hy | hy
        · rw [hy]; omega
        · exact hq y hy

theorem foldl_ins_sorted' {α : Type} (xs acc : List (Nat × α)) (h : Sorted acc) :
    Sorted (xs.foldl (fun a p => ins p a) acc) := by
  induction xs generalizing acc with
  | nil => exact h
  | cons x xs ih => exact ih (ins x acc) (ins_sorted x acc h)

theorem canon_sorted {α : Type} (xs : List (Nat × α)) : Sorted (canon xs) :=
  foldl_ins_sorted' xs [] List.Pairwise.nil

theorem ins_last {α : Type} (p : Nat × α) (l : List (Nat × α)) (h : ∀ q ∈ l, q.1 < p.1) :
    ins p l = l ++ [p] := by
  induction l with
  | nil => rfl
  | cons q qs ih =>
    have hq : q.1 < p.1 := h q (List.mem_cons_self ..)
    have h1 : ¬ p.1 < q.1 := by omega
    have h2 : ¬ p.1 = q.1 := by omega
    simp only [ins, if_neg h1, if_neg h2, List.cons_append]
    rw [ih (fun r hr => h r (List.mem_cons_of_mem q hr))]

theorem foldl_ins_of_sorted {α : Type} (xs acc : List (Nat × α)) (h : Sorted (acc ++ xs)) :
    xs.foldl (fun a p => ins p a) acc = acc ++ xs := by
  induction xs generalizing acc with
  | nil => simp only [List.foldl_nil, List.append_nil]
  | cons x xs ih =>
    have hx : ∀ q ∈ acc, q.1 < x.1 := fun q hq =>
      (List.pairwise_append.mp h).2.2 q hq x (List.mem_cons_self ..)
    simp only [List.foldl_cons]
    rw [ins_last x acc hx]
    have h' : Sorted ((acc ++ [x]) ++ xs) := by
      rw [List.append_assoc, List.singleton_append]
      exact h
    rw [ih (acc ++ [x]) h', List.append_assoc, List.singleton_append]

theorem canon_of_sorted {α : Type} (l : List (Nat × α)) (h : Sorted l) : canon l = l :=
  foldl_ins_of_sorted l [] (by simpa only [List.nil_append] using h)

theorem canon_idem {α : Type} (xs : List (Nat × α)) : canon (canon xs) = canon xs :=
  canon_of_sorted (canon xs) (canon_sorted xs)

theorem cataFields_eq_map {A : Type} (alg : Alg A) (fs : List (Nat × T)) :
    cataFields alg fs = fs.map (fun p => (p.1, cata alg p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [cataFields, List.map_cons, ih]

theorem normalizeFields_eq_map (fs : List (Nat × T)) :
    normalizeFields fs = fs.map (fun p => (p.1, normalize p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [normalizeFields, List.map_cons, ih]

/-! ## The law: the canonical-order read is invariant under normalization, with no premise. -/

/-- Two field lists with the same canonical order give the same record check. -/
theorem record_congr (rs1 rs2 : List (Nat × (V → Bool))) (h : canon rs1 = canon rs2) :
    hasTyAlg.record rs1 = hasTyAlg.record rs2 := by
  funext v
  cases v with
  | nat n => rfl
  | str s => rfl
  | ctor vs =>
    show fitPos vs (canon rs1) = fitPos vs (canon rs2)
    rw [h]

theorem hasTy_normalize : ∀ t : T, hasTy (normalize t) = hasTy t := by
  intro t
  induction t using T.ind' with
  | nat => rfl
  | str => rfl
  | record fs ih =>
    have hmap : (normalizeFields fs).map (fun p => (p.1, cata hasTyAlg p.2)) =
        fs.map (fun p => (p.1, cata hasTyAlg p.2)) := by
      rw [normalizeFields_eq_map, List.map_map]
      exact List.map_congr_left (fun p hp => by
        simp only [Function.comp_apply]
        exact congrArg (fun c => (p.1, c)) (ih p hp))
    have key : canon ((canon (normalizeFields fs)).map (fun p => (p.1, cata hasTyAlg p.2))) =
        canon (fs.map (fun p => (p.1, cata hasTyAlg p.2))) := by
      rw [← canon_map (cata hasTyAlg) (normalizeFields fs), canon_idem, hmap]
    simp only [hasTy, normalize, cata]
    rw [cataFields_eq_map, cataFields_eq_map]
    exact record_congr _ _ key

/-! ## Finite checks, and the red control. -/

def permuted : T := .record [(2, .nat), (1, .str)]
def laidOut : V := .ctor [.str "x", .nat 0]     -- canonical order: key 1 (str), then key 2 (nat)

#guard hasTy permuted laidOut = true
#guard hasTy (normalize permuted) laidOut = true
-- the written-order read sees the same value differently before and after normalization
#guard hasTyW permuted laidOut = false
#guard hasTyW (normalize permuted) laidOut = true

/-- Red control (proved): the written-order arm is not normalization-invariant. -/
theorem written_order_not_invariant : hasTyW (normalize permuted) laidOut ≠ hasTyW permuted laidOut := by
  decide

/-- A repeated key: the canonical read keeps the first, as `normalize` does, so the law holds;
formation must still refuse the repeat for the target's sake (TypeScript refuses it), not the law's. -/
def dup : T := .record [(1, .nat), (1, .str)]
#guard hasTy dup (.ctor [.nat 0]) = true
#guard hasTy (normalize dup) (.ctor [.nat 0]) = true
#guard hasTyW dup (.ctor [.nat 0]) = false

/-! ## Contrast: declaration order (no sort anywhere) keeps the law trivially. -/

mutual
def normalizeD : T → T
  | .nat => .nat
  | .str => .str
  | .record fs => .record (normalizeFieldsD fs)
def normalizeFieldsD : List (Nat × T) → List (Nat × T)
  | [] => []
  | (n, t) :: fs => (n, normalizeD t) :: normalizeFieldsD fs
end

theorem normalizeFieldsD_eq_map (fs : List (Nat × T)) :
    normalizeFieldsD fs = fs.map (fun p => (p.1, normalizeD p.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, t⟩ := p
    simp only [normalizeFieldsD, List.map_cons, ih]

theorem hasTyW_normalizeD : ∀ t : T, hasTyW (normalizeD t) = hasTyW t := by
  intro t
  induction t using T.ind' with
  | nat => rfl
  | str => rfl
  | record fs ih =>
    funext v
    simp only [hasTyW, normalizeD, cata]
    rw [cataFields_eq_map, cataFields_eq_map, normalizeFieldsD_eq_map, List.map_map]
    have hmap : fs.map ((fun p => (p.1, cata hasTyWAlg p.2)) ∘ fun p => (p.1, normalizeD p.2)) =
        fs.map (fun p => (p.1, cata hasTyWAlg p.2)) :=
      List.map_congr_left (fun p hp => by
        simp only [Function.comp_apply]
        exact congrArg (fun c => (p.1, c)) (ih p hp))
    rw [hmap]

end SynthRecord

#print axioms SynthRecord.T.ind'
#print axioms SynthRecord.canon_map
#print axioms SynthRecord.canon_idem
#print axioms SynthRecord.hasTy_normalize
#print axioms SynthRecord.written_order_not_invariant
#print axioms SynthRecord.hasTyW_normalizeD
```
