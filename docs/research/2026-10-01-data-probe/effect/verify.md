# Verifier of seat EFFECT, data probe (2026-10-01): what survives of the seat's findings

## The one thing

The seat's direction holds: records and variants are growth of `Ty` (system-map §1.1 already says
so), there is no case for a second schema carrier, and decoding fits a decision-free operation. Its
one urgent claim does not hold. The "live, unwritten" decode gap is already written down. The
owner-approved `Test/contracts/schema-codec.contract.md:25-28` says the decoder's strict field set
"is narrower than Effect's default excess-property stripping". Its half on extra keys is rc.112's
own `onExcessProperty: "error"` mode (tested). Its half on duplicate keys is the tree's written
`E4-SCHEMA-CE-012` condition (`Data/Json.lean:281-286`). Row 41 needs at most a wording fix.

Before R3 is ruled, its shapes need four repairs that the evidence forces:

1. **The census refusals are declarations, not programs.** All 2,888 refusals at a `Schema.*` head
   are top-level schema or decoder declarations; none is a program (tested). They call for DI-89's
   declaration reader into `Ty`, not a wider head table.
2. **The decode input is mostly a structured value, and decoding reads more than the shape.** In 37
   of the seat's own 40 sampled decode sites the input is an already-structured value; only 3 take
   JSON text. rc.112's result also depends on parse options and annotations, which `Ty.ofSchema`
   drops (tested).
3. **Records need a fixed field order and their own value frame.** Two records whose fields are
   permutations of each other are subtypes of each other (proved in the seat's own model). With the
   tree's proved `Ty.sub_antisymm_canonical`, the canonical form must therefore sort fields, and
   S-a1's normaliser must cover field order (reading). A record value spelled as a list of
   name/value pairs is already a member of `list (prod string τ)` (tested).
4. **The class name comes from rc.112's run-time check, not from tsgo.** tsgo is structural at
   classes: it accepts an object literal at a `Schema.Class` (tested). The class name is forced by
   rc.112's run-time identifier check, so it belongs in Σ_app with a duplicate-identifier refusal.

Base: `refactor/phase1-phase3`, HEAD `ba9783c3` (documentation-only after `bc77e97f`, `git diff
--stat` shows four doc files), so every source line read is the `bc77e97f` source. No tracked file
was edited, and no `lake build`, `make`, generator, `git add` or `git commit` was run. Everything
written is under this folder, named `verify*`. Evidence words: **proved** (a kernel theorem with
its axioms printed), **tested** (a finite check run here, log beside it), **reading** (read, not
run), **assumed**.

---

## 1. Verdicts

| id | verdict | evidence |
| --- | --- | --- |
| EFF-01 | partly | **Tested** (my own recount, `verify-counts/verify_census_heads.log`): identical to the seat's figures, 59,987 units, 4,079 unknown head, 2,888 at `Schema.*` (70.8%), `Schema.Struct` 1,513 in 12 projects. Engine 2 gives 71.0%. **Tested** (`verify-counts/verify_struct_units.log`): every one of the 2,888 is a top-level declaration. That is 2,069 schema declarations (`X = Schema.Struct(…)`), 748 decoder or encoder values (`parseX = Schema.decodeUnknownEffect(S)`), 56 other schema-valued calls and 15 type-alias or interface units. None is a program body. The recommendation's "largest refusal class" is wrong: unknown head ranks third, behind `E-PARAM-SHAPE` (26,175) and `E-IMPORT-OPAQUE` (9,002). The census is dated 2026-09-08 (reading). |
| EFF-02 | confirmed | **Tested**: an independent file walk with my own test rule (`verify-counts/verify_corpus_counts.log`) reproduces each count to within 4 (Struct 2,734/463/12, optional 2,802/288/12, decodeUnknown 931/304/11, Number 442/135/11, suspend 5/5/3). Notes: the counts are concentrated. Two projects hold 87% of the `Struct` uses, huly-mcp holds 80% of the `decodeUnknown*` calls, and alchemy holds 71% of the `Data.TaggedError` uses (reading, `counts.log`). `Schema.optional(` (2,589) outnumbers `optionalKey(` (213) 12 to 1 (tested). The recommended frequency ordering is a list of capabilities, not a theorem shape. |
| EFF-03 | confirmed | **Tested** by grep of p1–p5: 6 interfaces, 6 tagged errors with fields, 3 service records, 4 `_tag` literals, and the cast at `p1-http-cache.ts:52`. Caveat (reading): 2 of the 3 "service records" hold operations (`UserRepo.findById`, `p2:43-45`; `Ledger`, `p5:43-51`). Those belong to R5, R7 and row 118, not to R3's data records. p2's decode input is a SQL row object, not JSON text (`p2:60-66`). |
| EFF-04 | confirmed | **Tested**: the grep returns 1,643 files today, 1,635 once the 8 data-probe files are removed (the seat's 3 and my 5). Two small slips: 1,444, not 1,478, are census defect copies (the other 34 are commit-5 fidelity files and drafts), and 3 files (p2 and two p1-fold seeds) fall outside the stated split. Dogfood 6's 8 `Schema.Number` uses in 2 files are confirmed (reading). |
| EFF-05 | partly | **Tested**: there are 0 `catchTag("SchemaError")` in v4 code outside the vendored copy of Effect, 9 inside it. The formatter is called twice. But ".issue read 36 times" is a pattern overcount: only 5 of the 36 matches read a SchemaError's or SchemaIssue's issue (`verify-counts/verify_issue_reads.log`, each line read). The rest are Huly and Linear tracker issues and an app's own field. **Reading** of the seat's sample log: 32 of the 40 sampled sites are in one project (huly-mcp). Only 3 decode JSON text (sites 10, 23 and 29, each through `Schema.fromJsonString`); the other 37 decode an already-structured value. One project walks the issue tree by `_tag` (`huly-mcp src/config/config.ts:270-291`). |
| EFF-06 | partly | **Tested** (rerun, exit 0; `ProbeRed1` exit 1): the facts about the carrier and the refusals stand. **Tested** (`verify-ProbeTreeFacts.lean` §1, red control `Red7`): `ofSchema` reads a union only with exactly two members, so a foreign `Literals` of 3 or more members is refused. S-a1 ("exact modulo `stripAnn`") is insufficient for two reasons. (i) `ofSchema` drops annotations that rc.112 decodes by: `parseOptions` and `identifier` (tested, §2 and red control `Red5`; `verify-ts/verify-parse-options.log` P4–P6). (ii) Two records whose fields are permutations of each other are mutual subtypes (**proved**, `model_sub_not_antisymm`, `[propext]`). With `Ty.sub_antisymm_canonical` (proved in the tree) and DI-15 (3), the canonical form must fix field order, so the normaliser must include it. S-a3's tsgo evidence is misread (see EFF-11). "No second schema carrier" answers open decisions row 1 with option (c), against its recommended (b), without citing the row. |
| EFF-07 | partly | **Tested** (rerun; `ProbeRed2` exit 1): the decoder accepts the reordered Option object, and no exactness law exists. But the order-insensitivity is deliberate and written down: the owner-approved `schema-codec.contract.md:25-26` says "Object field order is immaterial", and the tracked guard `Test/Codegen/SchemaGenerationContract.lean:245-246` pins it. The seat cited neither. What is missing is a normaliser function and the exactness theorem, not a name for the policy. |
| EFF-08 | partly | **Tested** (bun rerun, 25 checks, ALL OK): T20 and T21 hold. **Refuted**: the claim that the refusal is unwritten. The owner-approved `schema-codec.contract.md:27-28` says "duplicates, missing fields and extra fields refuse. The decoder's strict field set is narrower than Effect's default excess-property stripping". `Data/Json.lean:281-286` says duplicate keys "must survive until the profile rejects them", and `E4-SCHEMA-CE-012` is listed in the schema-payload contract. **Too strong**: "only the encode direction". The battery decodes the 17 canonical images (`SchemaGenerationContract.lean:229-230`), and the gate equates each of them with rc.112's encoding (`harness/truth/schema-codec/check.ts`, `Emit.lean`). **Tested** (P1): rc.112 refuses the same extra key under `onExcessProperty: "error"`. Row 41's one-line summary is looser than its contract, which is a wording fix and not a live gap. |
| EFF-09 | partly | **Proved and tested** (rerun): the four model theorems hold with the same axioms, and red controls 3 and 4 fail as they should. Gaps. (i) The positional witness defeats only an exact-length carrier. A prefix carrier passes it and fails only at a permutation of the fields (`verify-ProbeModelWitnesses.lean` §2). (ii) The recommended value spelling, "a list of (name, value) pairs, the DB-15 SQL-row shape", is already a member of `list (prod string nat)` and `prod (prod …) (…)`, and the codec writes it as an array of arrays (tested, `verify-ProbeTreeFacts.lean` §4, red control `Red6`). So records need their own value frame. (iii) The model's decoder keeps the first of two duplicate keys, while rc.112 keeps the last (T7) and the tree refuses both (tested, red control `Red9`). (iv) The model's `sub` is not antisymmetric (proved), a further condition from the tree's own laws that the seat does not name. |
| EFF-10 | confirmed | **Tested**: the tsgo green and red runs reproduce, and so do T19 and `ProbeRed4`. This agrees with DI-15 ("`sub` stays sound for membership … deliberately incomplete") and with the boundary rule that a named refusal is allowed (B-accept, boundary decisions 2026-09-10, reading). Caveat: "must" holds because `hasTy_sub` keeps membership non-coercive and width subtyping is kept. The other way out is exact records. |
| EFF-11 | partly | **Tested** (`verify-ts/verify-assign-class.log`, green exit 0, red exit 1): tsgo is structural at classes. It accepts `{ name: "a" }` where a `Schema.Class` is expected. It refuses `Data.Class` only because the literal lacks a member (`pipe`). It treats two distinct tagged-error classes with the same tag and fields as mutually assignable. So "`sub (record fs) (classOf c fs) = false` … as tsgo answers" is false for `Schema.Class`; in row 68's lane it is a cut. **Tested** (`verify-ts/verify-class-runtime.log`): the class name is forced at run time instead. rc.112's encode refuses a plain object (V2) and accepts another class with the same identifier (V4). The conclusion that values print as `new C({…})` stands. |
| EFF-12 | partly | **Reading**: the precedents check out (`Native.lean:56`, `Eff.lean:336`, `Fragment.lean:28`). **Tested**: T10. Five gaps. (1) The JSON-text input fits 3 of the 40 sampled sites, and not p2. (2) rc.112 decoding also reads parse options, per call and from annotations (P1–P5; v4 application code sets `onExcessProperty` 17 times, `propertyOrder` 10 times and `errors: "all"` 11 times, tested), and the proposed row carries none of them. (3) A fourth route is not listed: a total term atom returning `except`, which is rc.112's `decodeUnknownResult` and `decodeUnknownOption` (116 uses). (4) The printed `decodeUnknownEffect` fails with a SchemaError instance, so keeping the program's error as DB-15's pair needs the prelude's `toPair` (`harness/truth/prelude.ts:278`) in the printed code. (5) DB-15's "a codec is a row" does not choose a native row over a host row. |
| EFF-13 | partly | **Tested** (rerun): the pair is admitted, `errOf` reads it as `Err.tagged`, and T16b holds. But the R3 shape is a placeholder (`supportedErrTy τ ↔ τ.isData ∧ …`). The formatter agreement it owes depends on annotations that `Ty` does not carry: `identifier` changes the message (P6), and huly's leaf hook reads `ast.annotations.message` (reading). Its support from ".issue 36" is an overcount (5 real reads). |
| EFF-14 | partly | **Reading**: `Admit.lean:59` and `Compile.lean:1354` are read correctly. But a host reply is `Completion Val …` (`Api/HostSession.lean:17`, `Answer`), not JSON. "`admitAnswer` checks `decode row.answer j`" would change the reply carrier, and "the tape stores `norm τ j`" misdescribes a journal that stores `Val` decisions. R3's path at admission is a record clause in `Val.hasTy` and `Fits` at the existing check (host-boundary §4.4). The "12 of 40" sampled sites behind it are mostly structured values, not JSON text. |
| EFF-15 | partly | **Tested** (rerun): `ofSchema Schema.number = none`, `nat` refuses 1.5 and −1, T5 and T6 hold, and `Schema.Number` has 442 uses in 135 files of 11 projects. The decision is misplaced. Row 108 is the bounded-integer profile. Binary64 belongs to row 109 (FloatLib, parked until Duration, Schedule or Random is modelled), DI-67 ("extend by one later") and the owner-ratified boundary decision T5 ("a float carrier is the first post-v0 append"). The options also omit `int`: it is in `Ty`, read from `Schema.Int` and uninhabited (tested, `verify-ProbeTreeFacts.lean` §5), it is what p5's −15 needs, and DB-15's scout E called it "the cheapest to lift". And `ofSchema` answers `Option`, so "a located refusal (what `ofSchema` does)" does not hold. |
| EFF-16 | confirmed | **Reading**: system-map §8, R3 status: "recursive types untracked". A grep of `decisions.md`, `DESIGN-ISSUES.md` and `DESIGN-BASIS.md` finds no row. Prior art the seat did not cite: recursion in the persisted carrier is covered by a contract (schema-payload contract `-013`, `-014`, `SC-DOC-02`/`-03`), and `Schema/Accepts.lean` follows `suspend` and references. |
| EFF-17 | partly | **Reading**: the AST facts are right (`SchemaAST.ts:53-74`, `:636-664`, `:401-432`, `:576-600`; `Schema.ts:1180-1199`), and T10 is tested. But the "decided" kind points at no tracked ruling; the finding is a reading of vendored source. "The pin has no ParseError" is false: `unstable/ai/McpSchema.ts:595` defines a `ParseError`, and `HttpServerError` has `RequestParseError`. What is true is that Schema has none. The exclusion list for the pure fragment P omits parse options and annotations that change behaviour. |

Totals: 5 confirmed, 12 partly, none refuted outright. The partly verdicts fall into three groups.
The facts reproduce but the framing fails (EFF-01, 07, 08, 17). The facts reproduce but a premise is
contradicted by evidence the seat did not run (EFF-06, 09, 11, 12, 14, 15). The counts reproduce but
one number or sample is skewed (EFF-05, 13).

---

## 2. What the seat missed

1. **The codec's key policy is a written, owner-approved contract clause.** It is
   `schema-codec.contract.md:25-28`, `Data/Json.lean:281-286` (the docstring above `Json`),
   `E4-SCHEMA-CE-012` in the schema-payload contract, and the guards
   `SchemaGenerationContract.lean:245-248`. On extra keys it equals rc.112's
   `onExcessProperty: "error"` (tested, P1). On duplicate keys it diverges only on the JSON-text
   route, where rc.112's `JSON.parse` keeps the last key (T7, T21), and that divergence is the written
   CE-012 condition. S3's "strip excess keys" would reverse an approved clause, and S3's "refuse
   duplicates" is the status quo. Neither is said.
2. **The census heads measure declarations.** All 2,888 refused units at a `Schema.*` head are
   top-level schema or decoder declarations (tested). Lifting them is DI-89's bounded declaration
   reader into `Ty`, or row 2's Σ_app declarations. It is not a wider program-head table.
3. **rc.112 decoding depends on more than the shape.** Parse options, given per call or as
   annotations, set the excess-key policy (`error`, `preserve`, `ignore`), the output key order and
   the error mode. `toRepresentation` persists them, and `Ty.ofSchema` drops them (tested, P1–P6 and
   `verify-ProbeTreeFacts.lean` §2). Real code sets them (17, 10 and 11 uses, tested). The pure
   fragment P, S-a1's normaliser and the decode row must each refuse them by name or carry them.
4. **Records need a fixed field order.** The tree proves `Ty.sub_antisymm_canonical`, and DI-15 (3)
   takes every schema document, codec law and printed type of the canonical form. So a record
   subtyping that ignores field order forces the canonical form to sort fields; the type-algebra
   note §1.3 already says "ascending by name". Then `schema ∘ ofSchema` reorders a foreign struct,
   which rc.112 makes observable through its output key order (T2), and S-a1 must normalise field
   order (proved in the model; red control `Red8`).
5. **Records need their own value frame.** A list of name/value pairs is already a member of
   `list (prod string τ)` and of nested pairs, and the codec writes it as an array of arrays (tested,
   red control `Red6`). Without a frame, choosing the branch of a union, the codec and the printer's
   choice between an object and an array cannot tell a record from a list of pairs.
6. **Decode mostly takes structured values.** In 37 of the 40 sampled sites, and in p2, the input is
   already structured, and only 3 sites take JSON text (reading). The natural operation decodes
   `unknown` (membership plus dropping undeclared keys) and leaves JSON parsing as a separate step.
   A fourth route is a total atom returning `except` (rc.112's `decodeUnknownResult` and
   `decodeUnknownOption`, 116 uses). It is free of decisions by construction and needs no new `Eff`
   arm.
7. **The printed decode has the wrong error type.** `decodeUnknownEffect` fails with a SchemaError
   instance. Matching DB-15's pair needs the prelude's `toPair` (DI-59) in the printed code.
   Otherwise the boundary on printed types breaks (boundary decisions, B-print) and row 68's lane
   fails the way the pass's TS2379 and TS2345 did.
8. **The class name belongs in Σ_app.** tsgo is structural at classes, while rc.112's run-time check
   identifies a class by its identifier string, and two classes sharing one identifier are
   interchangeable (tested, V4). So the name belongs in Σ_app's declaration table, with a refusal
   for duplicate identifiers (the analogue of row 113's one-code rule) and C1–C8 (row 111). The
   type-algebra note §1.3 proposes `Ty.foreign` (opaque, uninhabited, invariant) instead. The seat
   discusses neither placement.
9. **Open rows the seat did not engage.**
   - Row 1, a second schema carrier: open, with (b) recommended. The seat takes (c).
   - Row 2: "(c) annotation-carried names now, (b) `Ty.record` before the first foreign consumer".
     The seat's own positional result bears on (c), which the model probe's D10 recommends "now".
   - Row 3, `Ty.app`.
   - Row 5: one decode-iff-fits theorem is false in the total direction.
   - Row 10: four `Val → Json` images, and "the type-directed one does not" survive a change to `Ty`.
   - Row 39: `Arch/Accepts.lean` is ruled for deletion.
   - Row 109, binary64.
10. **Prior art in the Schema module.** `src/Effect4/Schema/Accepts.lean` already accepts JSON
    against a persisted schema. It handles optional keys and rc.112's default for extra keys. It
    refuses duplicate keys (CE-012), and it handles `anyOf`/`oneOf`, references and `suspend`. That
    is S3's proposed policy, already written in the tree.
11. **R3's own list of obligations is not covered.** System-map §8 names a `Fits` clause, embeddings,
    folds, assignability and inhabitance. The shapes omit inhabitance: DI-67's invariant bites at a
    record with a required field of an uninhabited type. They also omit folds: each new `Ty`
    constructor is one generated algebra field, against 17 hand edits today (traversal census §3.2),
    plus the wire and OCaml cost (error-paths scout map §7.2 (iii)).
12. **Records and variants need term forms.** Construction, field access, update by spread (p4, p5)
    and elimination on `_tag` are each a form owing a typing lemma and a behaviour law (R10, DI-89,
    C8). Equality is owed too (DI-35: `===` does not compare objects by content, so `Val.eqAt`). So
    is a policy on keys, order and duplicates for maps (machine-state §5). The model probe's R3 listed
    the last two; the seat dropped them.
13. **`Schema.optional` is not covered.** It has 2,589 uses against 213 for `optionalKey`, and it
    accepts an explicit `undefined` (T12). The model and the shapes cover only an absent key.
14. **Two problems with how needs are stated.** The shapes are stated over Σ_core's `Ty` only. Once
    nominal declarations live in Σ_app, each shape must take the signature parameter (R1). And §5's
    ranking, like EFF-02's ordering, is a list of capabilities rather than a theorem shape.

---

## 3. Probes and commands

All Lean runs used `bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`,
one at a time. The elapsed times in the logs include the wait for the lock, which was free.

| What | Command (this folder) | Result |
| --- | --- | --- |
| The seat's six Lean probes, rerun | `bash verify-rerun.sh` → `verify-rerun-<probe>.log` | identical to the seat's logs: `ProbeCodecStatus` and `ProbeRecordModel` exit 0, the four red controls exit 1 at the same guard |
| The seat's rc.112 harness, rerun | `bun run ts/rc112-schema-behaviour.ts` → `verify-rerun-rc112.log` | 25 checks, ALL OK, exit 0; identical to the seat's log except its bun-version line |
| The seat's tsgo pair, rerun | `tsgo -p ts/tsconfig.{green,red}.json` → `verify-rerun-assign-records.log` | green exit 0; red exit 1 with the same seven errors |
| Tree facts | `verify-ProbeTreeFacts.lean` → `.log` | exit 0; every `#guard` holds |
| Model witnesses | `verify-ProbeModelWitnesses.lean` → `.log` (the seat's definitions copied verbatim, lines 25-218) | exit 0; **proved** `model_sub_not_antisymm` |
| Red controls (must fail) | `verify-ProbeRed5_AnnotationsRead`, `Red6_PairsAreNotAList`, `Red7_ThreeLiteralsRead`, `Red8_PermutedRecordsEqual`, `Red9_ModelDuplicateLastWins` (`.lean`, `.log`) | each exit 1, at its intended `#guard` only |
| Class assignability | `verify-ts/`: `tsgo -p tsconfig.green.json` / `tsconfig.red.json` → `verify-assign-class.log` | green exit 0, red exit 1. Run 1 is kept as `verify-assign-class.run1-wrong-expectation.log`: I expected `Data.Class` to accept a literal, and tsgo refused it for a missing `pipe` |
| Class identity at run time | `verify-ts/`: `bun run verify-class-runtime.ts` → `.log`; red twin `verify-class-runtime-red.ts` → `.log` | ALL OK, exit 0; the red twin exits 1 |
| Parse options and annotations | `verify-ts/`: `bun run verify-parse-options.ts` → `.log` | ALL OK, exit 0. Run 1 is kept as `verify-parse-options.run1-wrong-expectations.log`, exit 1, with two wrong expectations: the order of a preserved key, and the input appearing in the text without `reportInput` |
| Census recount | `python3 verify-counts/verify_census_heads.py` | the seat's numbers exactly; engine 2 gives 71.0% |
| Census unit shapes | `python3 verify-counts/verify_struct_units.py` | 2,069 + 748 + 56 + 15 = 2,888 declarations; 0 program bodies |
| Corpus recount | `python3 verify-counts/verify_corpus_counts.py` | each count within 4 of the seat's; 0 `catchTag("SchemaError")` outside the vendored Effect repository |
| `.issue` lines | `python3 verify-counts/verify_issue_reads.py` | 36 matches, 5 of them a SchemaError's or SchemaIssue's issue |

**Axioms, verbatim** (my runs):

```text
'Effect4.Schema.Bridge.ofSchema_schema' depends on axioms: [propext]
'Effect4.Program.CTy.ofSchema_schema' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode_of_encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.decode_encode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.hasTy_decode' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_injective' depends on axioms: [propext, Quot.sound]
'Effect4.Schema.encode_sub' depends on axioms: [propext, Quot.sound]
'DataProbeEffect.RecordModel.decode_fits' depends on axioms: [propext]
'DataProbeEffect.RecordModel.encode_decode' depends on axioms: [propext, Quot.sound]
'DataProbeEffect.RecordModel.decode_encode' depends on axioms: [propext, Quot.sound]
'DataProbeEffect.RecordModel.fits_sub' depends on axioms: [propext]
'Effect4.Program.Ty.sub_antisymm_canonical' depends on axioms: [propext, Quot.sound]
'Effect4.Program.hasTy_sub' depends on axioms: [propext, Quot.sound]
'VerifyEffect.Model.model_sub_not_antisymm' depends on axioms: [propext]
```

**Bounded and host-only evidence.**

- Every count is a finite probe over one snapshot: the 2026-09-08 census file list and Foldlab's
  corpus.
- The classification of the decode-site sample and of the `.issue` lines is a reading.
- The tsgo and bun results are host-only: tsgo 7.0.0-dev.20260629.1, and bun 1.4.2 with effect
  4.0.0-rc.112 from `ts/eff/node_modules`.
- `model_sub_not_antisymm` is about the seat's model, not the tree. Its bearing on the tree goes
  through the tree's proved `Ty.sub_antisymm_canonical`, and that bearing is reading.
