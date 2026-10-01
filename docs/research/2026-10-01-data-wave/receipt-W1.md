# Seat W1 receipt: exactness for today's `Ty` (data wave, commit 1; row 128, TY-09)

Written incrementally by seat W1 in `/Users/pooks/Dev/lean4-effect4-seat-W1`, branch `seat/W1`,
base `74dae8d2`. Brief: `docs/research/2026-10-01-data-wave/brief-W1.md` with its amendments
(route (b) at dispatch; check annotations, Codex 21:16; the ninth erased key, `arbitrary`; the last
two by the coordinator's messages). Evidence
words: **proved** (a kernel theorem in the tree, its axioms printed at or below
`[propext, Quot.sound]`), **tested** (a `#guard`, a `#guard_msgs` fixture, a build or a command run
here, with its exit), **reading** (code or notes read, not run), **assumed** (not checked).

## The one thing

**Both boundary pairs are exact embeddings now, by construction on the plain readers (route (b),
no re-encoding guard), and the Schema reader is stricter than before in three ways a merge must
expect: it reads `nat`/`int` only from whole checks, refuses `effect/schema/TypeParameter` by name
(so the retraction `ofSchema_schema` gained a premise, `reservedFree`), and refuses every annotation
key outside row 179's nine erased keys (the eight documentation keys and `arbitrary`) at every bag
it reads (node, check, tuple element, the defect slot). rc.112's own `Schema.Int` and
`Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))` documents read `int` and `nat` (tested in
Lean, and their transcriptions against the vendored source under bun 1.4.2). The defect slot is
`effect/schema/Json`.**
The JSON decoder changed in one arm (a union's second branch only for a value outside the first);
the contract's 17 cases encode and decode as before and the schema-codec gate passes (tested);
that the checked encoder's domain is exactly the old one is not proved (seat P's note says the
same, reading: the two decoders can differ only on JSON the old one read at a non-canonical
branch somewhere inside it).

## Merge notes

- **Overlap with the parallel seats** (tested: `git grep -nE 'Effect4\.Schema\.Bridge|Effect4\.Schema\.Codec|Bridge\.(ofSchema|schema|defectRep)|Ty\.ofSchema|ofSchema_schema|decode_of_encode|effect/schema/Defect|effect/schema/TypeParameter'`
  over D2–D4's `Laws/Program/Typed/`, `Machine/Stores.lean`, `Laws/Program/InterpR.lean`, J2's
  `Program/Authoring/`, `ts/eff`, `Makefile`, W2's `tools/Effect4Gen`, `tools/Tools/Variances.lean`,
  `Program/FoldOf.lean`, `OCaml5/Lcnf/Translate.lean`, `scripts/check-conservativity.sh`: no match,
  exit 1). The one shared
  cone is `fold_of`: `Laws/Program/Folds/Ty.lean:34`, `:38` register `Bridge.schema` and
  `Codec.decodeRaw` through W2's `Program/FoldOf.lean`, and `Folds/Representation.lean:27` registers
  `Bridge.checkId`. Here `fold_of Codec.decodeRaw` re-elaborated against the repaired union arm (a
  paramorphism, as before; tested). If W2 lands a `FoldOf` change, rebuild `Effect4.Laws.Program.Folds.Ty`
  after merging both.
- **Signatures changed**: `Bridge.ofSchema_schema`, `Bridge.ofSchema_schema_cty` and
  `CTy.ofSchema_schema` gained `reservedFree`; `Schema.decode_of_encode` takes any `Ty` (it took
  `CTy`). Their only consumers outside the two modules are the battery's `#check`s (tested by `git grep`).
- **For W4's append**: `normS_schema` and `ofSchema_schema` have one arm per `Ty` constructor and
  `reservedFreeAlg` one field per constructor, so each gains one as `schema` and `TyAlgebra` do;
  `decodeRaw_normJ` and `decodeRaw_exact` end in a wildcard arm, so a constructor with no codec arm
  costs them nothing. Under row 182 (ruled on main after this base, read at `f1231fe9`):
  `reservedFree` is a predicate over handle targets, so it is a generic fold over the signature once
  W2's machinery lands (today a hand `TyAlgebra` literal, the only one this seat adds), and
  `normS_schema` becomes one fusion statement when `Bridge.schema` is generated from the face table
  (D-U2).
- **Main moved** since this base (`74dae8d2` → `f1231fe9` at the time of writing): no commit touches
  this seat's cone (`git diff --stat 74dae8d2 f1231fe9` over `src/Effect4/Schema`,
  `src/Effect4/Laws/Schema`, the battery, `Laws/Program/Folds`, `Program/FoldOf.lean`,
  `Program/Fold.lean`, `Program/Ty.lean`, `Program/Typed.lean`: empty), and
  `git merge-tree --write-tree f1231fe9 seat/W1` merges without conflict (exit 0; tested).

## The two exactness theorems (proved)

| Theorem | File:line (head) | Statement | Axioms |
| --- | --- | --- | --- |
| `Effect4.Schema.decode_iff` | `src/Effect4/Laws/Schema/Codec.lean:1052` | `decode t j = some v ↔ ∃ j', encode t v = some j' ∧ normJ j' = normJ j`, at every `Ty` | `[propext, Quot.sound]` |
| its exactness half `Effect4.Schema.encode_of_decode` | `:1032` | `decode t j = some v → ∃ j', encode t v = some j' ∧ normJ j' = normJ j` | `[propext, Quot.sound]` |
| its retraction half `Effect4.Schema.decode_of_encode` | `:1015` | `encode t v = some j → decode t j = some v`, generalized from `CTy` to every `Ty` | `[propext, Quot.sound]` |
| `Effect4.Schema.Bridge.ofSchema_exact` | `src/Effect4/Schema/Bridge.lean:492` | `∀ r t, ofSchema r = some t → normS r = schema t` (by `fun_induction ofSchema`, 39 cases) | `[propext, Quot.sound]` |
| `Effect4.Schema.Bridge.ofSchema_exact'` | `:607` | `ofSchema r = some t → normS r = normS (schema t)` (the vocabulary's `r ≡ write t`) | `[propext, Quot.sound]` |
| the retraction `Effect4.Schema.Bridge.ofSchema_schema` | `:412` | `t.closed = true → reservedFree t = true → ofSchema (schema t) = some t` | `[propext, Quot.sound]` |

Supporting, proved: `Codec.decodeRaw_normJ` (`Laws/Schema/Codec.lean:400`, the decoder reads
`N_J`'s quotient, every arm including the cause, reason, defect and error decoders),
`Codec.decodeRaw_exact` (`:767`), `Codec.sortE_perm` (`:66`, `[propext]`), `Codec.fields?_normJ`
(`:133`); `Bridge.normS_schema` (`Bridge.lean:322`, `[propext]`), `Bridge.normS_of_isDefect`,
the ten `normS_*` node equations; `ofSchema_schema_cty` (`:484`) and `CTy.ofSchema_schema` (`:681`)
with the new premise.

Axiom sweep (tested, rerun at the head): `Lean.collectAxioms` over every declaration of the four
touched modules, internal and private ones included (850: `Effect4.Schema.Codec` 98,
`Effect4.Laws.Schema.Codec` 495, `Effect4.Schema.Bridge` 170, `Test.Codegen.SchemaGenerationContract`
87; 847 at `03403dc8`): none above `[propext, Quot.sound]`. The battery prints `#print axioms` for the headline
theorems (`Test/Codegen/SchemaGenerationContract.lean:391-394`, `:610-614`, `:753`): each
`[propext, Quot.sound]`, `normS_schema` `[propext]`.

## The normalisers (definitions)

- **`N_J` = `Codec.normJ`** (`src/Effect4/Schema/Codec.lean:248`, mutual with `normJs`, `normEs`):
  every object's entries sorted by key bytes (`keyBytes s := s.toUTF8.data.toList.map
  UInt8.toNat`, `:234`), stably (`insertE` `:237`, `sortE` `:243`: an insertion sort, equal keys keep
  their order, no entry dropped, so a repeated key survives for `fields?` to refuse), recursively;
  arrays element-wise; every other node unchanged. Keys compared with `Ty.ltKey` on the byte lists,
  never through `String`'s order.
- **`N_S` = `Bridge.normS := cata_representation normSAlg`** (`Bridge.lean:155`, algebra `:128`),
  a fold: every annotation bag of the tree (node, check, tuple element, property) replaced by
  `normAnn` of it; nothing else changes (no property sort, no union flattening: the statement is at
  the bridge). `normAnn` (`:111`) is row 179's policy, amended twice: an annotation that does not
  change decoding is erased, one that does (or an unknown one) is refused. The erased keys
  (`erasedKeys`, `:105`) are revision 5's eight documentation keys (`identifier`, `title`,
  `description`, `documentation`, `examples`, `default`, `message`, `expected`) and `arbitrary`, a
  fast-check generator hint; every other entry is kept in order, an empty remainder `none`. The
  reader admits a bag only when `normAnn` leaves nothing, at every bag it reads; a check is compared
  after `normCheck := cata_check normSAlg` (`:159`) with the bare `isIntCheck`/`nonNegativeCheck`.
- **`reservedFree`** (`Bridge.lean:405`): a `cata_ty` fold (`reservedFreeAlg`, `:380`), no handle
  target equal to `effect/schema/TypeParameter`. No hand case analysis on `Ty` was added.

## What changed in the production functions

1. `Codec.decodeRaw`'s union arm (`Codec.lean:217-220`): `(decodeRaw b j).filter (fun v => Val.hasTy
   v b && !Val.hasTy v a)` in place of `... Val.hasTy v b` (seat P's arm, seat S's text).
2. `Bridge.defectRep` and `Bridge.isDefect` name `effect/schema/Json` (`E4-SCHEMA-CE-061`), and
   `isDefect` reads the slot's annotation bag under the policy (`Bridge.lean:52`, `:166`).
3. `Bridge.ofSchema` (`:181`): the guard `normAnn ann = none` first in every arm; the `number` arm
   compares `checks.map normCheck` with `[isIntCheck, nonNegativeCheck]` (`nat`) and `[isIntCheck]`
   (`int`); the bare declaration refuses `effect/schema/TypeParameter`; the tuple arm guards both
   elements' bags. `checkId` stays (its `fold_of` registration, `Laws/Program/Folds/Representation.lean:27`,
   and the red control of the id reading use it).
4. `Schema.decode_of_encode` restated at every `Ty` with seat P's proof; its two same-file callers
   (`decode_encode`, `encode_injective`) pass the raw type, `decode_encode`'s two `simp`s replaced by
   `rw`/`exact` (a touched proof). `encode_sub`, `hasTy_decode`, `encode_eq_some`,
   `encode_isSome_iff` and the three `encode_*` leaf theorems untouched (they keep their unqualified
   `simp`s; not touched).

## Red controls kept (fixtures) and green twins

All in `Test/Codegen/SchemaGenerationContract.lean` (the battery the schema-codec gate emits from;
no root import edited). The red controls are stated on the functions as they stood at `74dae8d2`,
kept verbatim as fixtures: `ofSchemaBefore` (`:150`, the whole pre-repair reader with
`isDefectBefore`) and `unionArmBefore` (`:533`, `decodeRaw`'s pre-repair union arm, children by the
production decoder, which is the old one off unions).

| Control | Kind | What it shows (tested) |
| --- | --- | --- |
| `codec_not_exact` (`:541`) | theorem (proved) | the pre-repair arm reads `Exit.Success(1)`'s JSON at `union (except nat nat) (exitOf nat nat)` as `ctor 0 [nat 1]`, whose encoding is `Result.Failure(1)`'s JSON; the two differ modulo `N_J` (P's control) |
| `red_productionExact` (`:555`) | `#guard_msgs (error)` | S's control, on the arm it was about: "the pre-repair arm refuses the `Success` image" fails |
| `red_decodesExitAsResult` (`:567`) | `#guard_msgs (error)` | "the production decoder reads the `Success` image" fails |
| `red_exactWithoutNJ` (`:579`) | `#guard_msgs (error)` | exactness without the normaliser fails (a permuted `Some` decodes; its encoding is the other order) |
| `ofSchema_reads_check_ids` (`:230`) | theorem (proved) | the pre-repair reader read `≥ 5` as `nat` (P's control) |
| `ofSchema_reads_groupedInt` (`:235`) | theorem (proved) | the pre-repair reader read a filter group as `int` (S's `groupedInt`) |
| `ofSchema_reads_typeParameter` (`:241`) | theorem (proved) | `schema (var 0)` read back as a handle; `var 0`, `var 1` share a schema (P) |
| `ofSchema_drops_parseOptions` (`:247`) | theorem (proved) | a `parseOptions` annotation read as absent (P) |
| `ofSchema_refused_rcExit` (`:254`) | theorem (proved) | `E4-SCHEMA-CE-061`: the pre-repair reader refused rc.112's own `Exit` and read Lean's invented id |
| `red_ge5` (`:260`), `red_groupedInt` (`:270`) | `#guard_msgs (error)` | S's controls: "the pre-repair reader refuses them" fails; both still red |
| `red_typeParameter` (`:283`) | `#guard_msgs (error)` | S's control on the production pair: the handle `effect/schema/TypeParameter` does not round-trip, which refutes the old unconditional retraction at that type (hence `reservedFree`) |
| `red_exactWithoutNS` (`:296`) | `#guard_msgs (error)` | exactness without `N_S` fails (a documented node reads) |
| `red_parseOptionsIsInt` (`:345`) | `#guard_msgs (error)` | the amendments' control: an `isInt` check carrying `parseOptions`, a key outside the nine, does not read as `int` (it was `red_arbitraryIsInt` until `arbitrary` became the ninth erased key) |

Green twins (`#guard`s that hold): `repaired_refuses` (`:548`, proved); the production reader
refuses `ge5`, `groupedInt`, `schema (var 0)`, `stringParseOptions`, Lean's old `Exit` id and a
defect slot carrying `parseOptions`; reads a `title`-annotated string, an empty bag, rc.112's own
`Exit(Int, String, Defect())` document (its `expected` annotations erased).

**The coordinator's check-annotation controls** (Codex 21:16, then the ninth key; all tested):
1. a documented `isInt` (`documentedIsInt`, `:323`, a `title` on the check) reads `int`, with the
   nonnegative check reads `nat`, and a documented nonnegative check reads `nat`; `normS` of the
   documented node is `schema .int`;
2. a check carrying a key outside the nine is refused: `parseOptions` on `isInt`
   (`parseOptionsIsInt`, `:326`) alone and beside the nonnegative check, an unknown key on `isInt`,
   `parseOptions` on the nonnegative check, `parseOptions` beside `arbitrary` (all `none`), with the
   red fixture `red_parseOptionsIsInt`. The reader is `Option`-valued: a refusal carries no path, so
   "at `["checks[i]"]`" is the located reader's (seat S's `ofSchemaLocated`), not landed here;
3. S's `ge5` and `groupedInt` stay refused, and their red fixtures (`red_ge5`, `red_groupedInt`)
   stay red;
4. rc.112's own documents read (the ninth key): `rcIntDocument` (`:371`, `Schema.Int`: the `isInt`
   filter with `expected` and `arbitrary`, `rcIsIntFilter` `:360`) reads `int`, and `rcNatDocument`
   (`:373`, `Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))`, which is `Schema.Natural`'s
   document, adding `rcNonNegativeFilter` `:366` with its `expected`) reads `nat`; `normS` of each is
   `schema .int`, `schema .nat`.

(`Test/Api/ApiContract.lean:387`'s `foreignInt` is the bare `Check.int`, not rc.112's persisted
`Schema.Int`; its guard still reads `int`, tested.)

**The host case of the ninth key** (tested, host-only:
`docs/research/2026-10-01-data-wave/W1/host/vendored/`): `EmitIntDocs.lean` writes the battery's
`rcIntDocument` and `rcNatDocument` and the production reader's answer on each; `int-twin.ts`, under
bun 1.4.2 with `effect/*` mapped by `tsconfig.json` to the worktree's vendored rc.112 source (the
log names the resolved file, `vendor/effect-4.0.0-rc.112/src/Schema.ts`; the 452 files of that
source match `SHA256SUMS`, tested with `shasum -a 256 -c`), passes 5 checks: the vendored
`Schema.Int`, `Schema.Int.check(Schema.isGreaterThanOrEqualTo(0))` and `Schema.Natural` persist
exactly Lean's transcriptions, and Lean reads them as `int` and `nat` (exit 0). The red twin
`int-twin-red.ts` (the `Schema.Int` transcription without `arbitrary` claimed equal to the vendored
one) exits 1. Logs: `W1/host/vendored/logs/{emit,int-twin,int-twin-red}.log`.

**The host twin of `E4-SCHEMA-CE-061`** (tested, host-only:
`docs/research/2026-10-01-data-wave/W1/host/`): `EmitDefectDocs.lean` writes Lean's `Exit` and
`Cause` documents from the production `Bridge.schema` and one with the old id; `defect-twin.ts`
under bun 1.4.2 against the installed effect 4.0.0-rc.112 (an untracked `node_modules` link to the
main checkout's `ts/eff/node_modules`, as probe S did): 8 checks pass (both documents revive with
`[ExitReviver, CauseReviver, JsonReviver]`, both equal rc.112's own persisted `Exit`/`Cause`
modulo annotations, the revived schemas encode `Exit.succeed(true)`, a failing cause and a cause as
rc.112's own do; the old id refuses), exit 0; the red twin `defect-twin-red.ts` exits 1 with
"Missing reviver for effect/schema/Defect". Logs: `W1/host/logs/{emit,defect-twin,defect-twin-red}.log`.

## Commands and results

| Command (in the worktree, `LEAN_NUM_THREADS=4`) | Result |
| --- | --- |
| `lake build Effect4.Schema.Codec` | exit 0 |
| `lake build Effect4.Laws.Schema.Codec` | exit 0 (rebuilt `Laws.Program.Folds.Ty`, whose `fold_of Codec.decodeRaw` reads the repaired arm as a paramorphism) |
| `lake env lean -DwarningAsError=true src/Effect4/Schema/Bridge.lean` | exit 0, no message |
| `lake build Effect4.Schema.Bridge Effect4.Laws.Schema.Codec` | exit 0 |
| `lake build Effect4.Api Effect4.Laws.Program.Folds.Representation Effect4.Laws.Program.Folds.Ty` (direct importers) | exit 0 |
| `lake build TestSchema Test.Codegen.SchemaGenerationContract Test.Api.ApiContract` | exit 0 (every `Test/Schema` battery; `DialectContract`'s pins unchanged) |
| the axiom sweep (a scratch `collectAxioms` command over the four modules) | 847 declarations at `03403dc8`, 850 at the head; 0 above the ceiling |
| schema-codec gate, its three steps: `lake env lean -M4096 --run harness/truth/schema-codec/Emit.lean <tmp>/values.ts`; `node <main>/harness/truth/node_modules/@typescript/native-preview/bin/tsgo --project <main>/harness/truth/schema-codec/tsconfig.json`; `bun <main>/harness/truth/schema-codec/check.ts <tmp>/values.ts` | exit 0, 0, 0: "PASS schema-codec: 17 fresh Lean/rc.112 comparisons, 17 host round trips, 2 negative controls" (tsgo 7.0.0-dev.20260629.1, bun 1.4.2; the worktree has no `node_modules`, so the host steps ran the main checkout's `check.ts`, byte-identical to this branch's: `diff -r`, tested; nothing written there) |
| the defect host twin (above) | exit 0; red twin exit 1 |
| after the ninth key: `lake build Effect4.Schema.Bridge Effect4.Api Effect4.Laws.Program.Folds.Representation Effect4.Laws.Program.Folds.Ty TestSchema Test.Codegen.SchemaGenerationContract Test.Api.ApiContract` | exit 0, 317 jobs (`ofSchema_exact` re-proved unchanged, `[propext, Quot.sound]`) |
| the ninth key's host case (above) | exit 0; red twin exit 1 |
| roots, second run (at the head, after the ninth key): `lake build Effect4 Effect4.Laws Test.All` | exit 0, 745 jobs; the trust gate: "checked 526 modules and 73194 declarations; semantic/test axioms are [propext, Quot.sound]" |
| roots, first run (at `03403dc8`): `lake build Effect4 Effect4.Laws Test.All` | exit 0, 745 jobs; the trust gate: "Effect4 module and axiom gate: checked 526 modules and 73191 declarations; semantic/test axioms are [propext, Quot.sound]" (the 15-module implementation boundary unchanged); the traversal census prints `reservedFree` as a `fold` row of `Ty` (`reservedFreeAlg`) and `normS` as a `fold` row of `Representation` (`normSAlg`); `ofSchema` stays a `structural` row and `isDefect` a `one-level` row (as at the base, reading `docs/core/traversal-census.md`) |

Not run, with the reason: `make check-cases` (no new match on a policy family: the new matches are
on `Representation`, `Option`, `List`, `Json`; `decodeRaw`'s match keeps its shape, one arm's body
changed); `make check-gen` (no generator ran; `git grep` finds the old defect id nowhere outside
the bridge, the battery and the register); `make check-target`/`check-truth` (no face changed).

## Status log (incremental)

- Read: the brief and its amendments; the wave's `README.md` (landing style, testing); plan §4;
  decisions rows 8, 122, 128, 179 (and 121, 132 for scope); probe P's note (question 5, the brief
  text, the receipt) and its probes `P8Codec.lean`, `P8Schema.lean` with their logs (both exit 0,
  every printed axiom line at or below `[propext, Quot.sound]`); probe S's note §§1, 4, 6, 7.1 and
  its copy's controls (`K2Copy.lean`), `q4-defect.ts`; revision 5's annotation review (the eight
  documentation keys); Codex's 21:16 review (data).
- No production file the probes read changed between P's base `bff50631` and this base
  (`git log bff50631..74dae8d2` over `Schema/`, `Laws/Schema/`, `Program/Ty.lean`,
  `Program/Typed.lean`, `Data/Json.lean`: empty; tested).
- P's codec proofs compiled on the production pair unchanged but for names (`decodeRawC` →
  `decodeRaw`, `bytesKey` → `keyBytes`); P's 39-case `fun_induction` closed with row 179's policy,
  the check arm and the element guard on the first compile (tested).
- Code commit `03403dc8`; receipt and the defect twin `a2cfb3d6`, receipt edits `2ad7c1ab`,
  `4579c3f6` (handed back).
- The coordinator's second message (row 179 amended: `arbitrary` is the ninth erased key; the
  element and property bags stand): `erasedKeys` replaces `documentationKeys` in
  `Schema/Bridge.lean` (a list literal and docstrings; no proof changed, as P said: the proofs read
  only `normAnn none = none` and the guard); the battery's `arbitrary` controls flipped to reads, the
  red fixture moved to `parseOptions`, rc.112's own `Int` and nonnegative `Int` read; the host case
  against the vendored source added; one commit, the head.

## Proposed lines for the coordinator's files (this seat edits none of them)

**Decisions row 128** (append to its status): "**Landed (seat W1, `03403dc8` and the head), route (b)**: the JSON
pair is exact modulo `N_J` at every `Ty`, `decode_iff` (`Laws/Schema/Codec.lean`; halves
`encode_of_decode`, `decode_of_encode`, the latter generalized from `CTy`), through
`decodeRaw_normJ` and `decodeRaw_exact`; the reader is exact modulo `N_S`, `ofSchema_exact`
(`Schema/Bridge.lean`, `fun_induction`, 39 cases), with `normS_schema` and the retraction
`ofSchema_schema`, which now takes `reservedFree` (the `TypeParameter` refusal refutes the old
unconditional statement at `handle "effect/schema/TypeParameter"`, red control `red_typeParameter`);
the defect slot is `effect/schema/Json` (`E4-SCHEMA-CE-061`, host twin under bun); every declaration
`[propext, Quot.sound]`; red controls on the pre-repair functions kept as fixtures in
`Test/Codegen/SchemaGenerationContract.lean`. Not proved: that the repaired checked encoder has
today's domain (tested on the contract's 17 cases)."

**Decisions row 179** (append): "Landed with `ofSchema_exact` (seat W1, `seat/W1`'s head): `normAnn`
erases nine keys, revision 5's eight documentation keys and `arbitrary` (`erasedKeys`), and keeps
every other key for the reader to refuse; `N_S` applies it to every annotation bag (node, check,
tuple element, property) and the reader guards every bag it reads (node, check, tuple element, the
defect slot); the amendments' controls in the battery; rc.112's own `Schema.Int` and
`Schema.Int.check(isGreaterThanOrEqualTo(0))` read `int` and `nat` (Lean guards; the transcriptions
checked against the vendored source under bun 1.4.2, `W1/host/vendored/int-twin.ts`)."

**`Test/Counterexamples/REGISTER.md`, `E4-SCHEMA-CE-061`**: status "REPAIRED 2026-10-01 (seat W1,
`03403dc8`)"; witnesses "`ofSchema_refused_rcExit` on the pre-repair reader and the green twins
(`Test/Codegen/SchemaGenerationContract.lean`); host twin
`docs/research/2026-10-01-data-wave/W1/host/defect-twin.ts` (8 checks, exit 0) and its red twin
`defect-twin-red.ts` (exit 1)".

**`AGENTS.md`, the exact-embedding bullet**: replace "`Ty.schema`/`ofSchema` and the JSON codec are
retractions until their exactness theorems land (decisions row 128)." by: "The JSON codec is exact
modulo `normJ`, the object-key sort (`decode_iff`), and `Bridge.schema`/`ofSchema` modulo `normS`,
the annotation keys that change no decoding erased (row 179's nine; `ofSchema_exact`; its retraction
on closed types whose
handles avoid `effect/schema/TypeParameter`), stated at the bridge because `Ty.schema` normalizes
first (decisions row 128)."

**`docs/core/system-map.md`**:
- §4, the schema-carrier row, "Maps out": "embeddings from `Ty` (row 6)" → "an exact embedding
  from `Ty` modulo `normS` (rows 6, 128)".
- §5, the K2 row, "Proved instances": replace "`Ty.schema`/`ofSchema` and the JSON codec are
  retractions until their exactness lands (row 128; the JSON normaliser is key order)" by "the JSON
  codec modulo `normJ` (`decode_iff`); `Bridge.schema`/`ofSchema` modulo `normS` (`ofSchema_exact`,
  `ofSchema_schema` with `reservedFree`), at the bridge (row 128)".
- §9, the `Representation` row: cite `Schema/Bridge.lean:56`, `:181`; theorems "`ofSchema_schema`
  (`:412`), `ofSchema_exact` (`:492`)"; the last column "not an ornament (McBride 2011): an
  ornament's forgetful map is total; a partial isomorphism onto the image modulo `normS` (row 128)".
- §9, the JSON codec row: cite `Schema/Codec.lean:277`, `:286`; shape "an exact embedding on the
  codec domain modulo key order"; theorems "`decode_of_encode`, `encode_of_decode`, `decode_iff`".
- §10.1 item 5: "(write/read pairs with a named normaliser; the retractions of row 128 become exact
  in the data wave's commit 1)" → "(write/read pairs with a named normaliser: the JSON codec modulo
  `normJ`, the Schema bridge modulo `normS`, row 128)".

## Open obligations, bounded evidence, scope

- **Owed consumption** (plan §5): nothing in the tree consumes the two exactness theorems yet
  beyond the battery's `#check`/`#print axioms`. Their readers: W5 (commit 5) extends both at the
  new forms (records, optional keys, maps, tuples, `app`, the leaves); route A's adapter (row 122)
  and its `codec_sub_adapt` sit beside `decode_iff`; system map §10.1 item 5 cites them.
- **Repeated proofs removed**: none; the CTy-only proof of `decode_of_encode` (through
  `encode_eq_some`) became the general one, so `encode_eq_some` has no consumer in the tree (kept: a
  characterization). **Program-to-execution connection closed**: none; this is the boundary.
  **Eventual claim**: M7 is unchanged; what this adds is the boundary clause of §10.1 item 5.
- **Not proved**: the repaired checked encoder's domain equals today's (tested on 17 cases); the
  reader reads `N_S`'s quotient (`ofSchema (normS r) = ofSchema r`), which would give an `iff` like
  the codec's; neither is needed for the vocabulary's three laws.
- **Owed elsewhere, each with its obstacle**: the refusal path (`["checks[i]"]`) needs the located
  reader (seat S's `ofSchemaLocated`, W5's); `reservedFree` goes when formation refuses a handle named
  `effect/schema/TypeParameter` (seat S's `schemaWf`); the safe-integer bound is not landed because
  row 121 is not ruled ("open, recommended", read at this base: `decode .nat` still accepts 2^53,
  the battery's existing guard).
- **Scope** (as Codex's 21:16 review states it, confirmed by reading): today's forms only (binary
  `anyOf`, plain binary tuples, exact bare checks after `N_S`); the writer in the theorem is
  `Bridge.schema`, and the public `Ty.schema` normalizes first, so `N_S` does not reorder union
  members or sort anything (probe S's `N_S` also flattened an `anyOf` right spine, for its n-ary
  reader: W5's, with that reader); the retraction needs `closed` and `reservedFree`. On the public
  pair, exactness holds for reads whose type is canonical, since `Ty.schema t` unfolds to
  `Bridge.schema t.normalize` (reading; no theorem stated for it); a read of a union in
  non-canonical order is exact only against the bridge writer.
- **Positional proof cases**: `ofSchema_exact` names its cases `case1` … `case39` from the reader's
  own principle; W5's new arms renumber them (the refusing cases close by `nomatch`).
- **Row 132** (no case analysis on `Ty` outside `Membership.lean`, scoped to the typed state):
  no definition with a hand case analysis on `Ty` was added (`reservedFree` is a `cata_ty` algebra;
  `decodeRaw` kept its match, one arm's body changed). Four proofs induct on `Ty`, all outside
  `Laws/Program/Typed/` and copied from probe P as the brief directs: `decodeRaw_normJ`,
  `decodeRaw_exact` (`Laws/Schema/Codec.lean`), `normS_schema`, `ofSchema_schema` (the last
  replacing today's proof, which inducted on `Ty` too).
- **Host-only evidence**: the schema-codec gate's host steps and the defect twin (bun 1.4.2, tsgo
  7.0.0-dev.20260629.1, effect 4.0.0-rc.112 installed in the main checkout's `ts/eff/node_modules`,
  read through an untracked link; nothing written in the main checkout).
- **Refused permissions**: none.

## Base, head, changed files

- **Base** `74dae8d2`. **Code commits**: `03403dc8` (the repair), then the head (the ninth key,
  with this receipt's amendment and the vendored host case, one commit). The receipt and the defect
  twin landed in `a2cfb3d6`; `2ad7c1ab` and `4579c3f6` touch the receipt only. **Head**: the last
  commit on `seat/W1` (`git log -1`). Nothing pushed; no merge, checkout or reset run
  (`git merge-tree` only, which writes no ref).
- **Changed by `03403dc8`** (`git diff --numstat 74dae8d2 03403dc8`): `src/Effect4/Schema/Codec.lean`
  +50/−3, `src/Effect4/Laws/Schema/Codec.lean` +1017/−15, `src/Effect4/Schema/Bridge.lean` +517/−117,
  `Test/Codegen/SchemaGenerationContract.lean` +341/−2. No root import, no lakefile, no generated
  file, no coordinator's file.
- **Changed by the head** (the ninth key): `src/Effect4/Schema/Bridge.lean` (`erasedKeys`, docstrings),
  `Test/Codegen/SchemaGenerationContract.lean` (the controls), this receipt, and, force-added,
  `docs/research/2026-10-01-data-wave/W1/host/vendored/` `EmitIntDocs.lean`, `int-twin.ts`,
  `int-twin-red.ts`, `tsconfig.json`, `logs/emit.log`, `logs/lean-int-docs.ts`, `logs/int-twin.log`,
  `logs/int-twin-red.log` (its `node_modules` link is local and not committed).
- **Added by the receipt commit** (force-added, `docs/research` is ignored):
  `docs/research/2026-10-01-data-wave/receipt-W1.md`; `docs/research/2026-10-01-data-wave/W1/host/`
  `EmitDefectDocs.lean`, `defect-twin.ts`, `defect-twin-red.ts`, `logs/emit.log`, `logs/lean-docs.ts`,
  `logs/defect-twin.log`, `logs/defect-twin-red.log`. The `node_modules` link beside them is local
  and not committed.

