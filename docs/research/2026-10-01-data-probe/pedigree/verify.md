# Verify: seat PEDIGREE of the data probe (adversarial verifier, 2026-10-01)

## The one thing

The seat's core holds. No ruling says how a program uses a schema. Records are refused by DB-15
and open in row 2 and D10. DI-08 is open, row 39's wipe is unexecuted, and a `Ty` append would
collide with Codex. These rest on reading, except row 39's state, which `ls` and `wc` confirm
(tested). The seat's probes rerun byte-identically (tested).

Two of the seat's proposed repairs are wrong at HEAD, and I tested both:

1. **The JSON codec is not exact even up to field order.** At the supported union
   `union (except nat nat) (exitOf nat nat)`, two JSON objects with different keys decode to the
   same value. `Val` is untyped: `ctor 0 [v]` is both `Exit.success v` and `Result.failure v`.
   So R3.c needs `decode` to refuse a branch image the encoder would not write. A field-order
   normaliser does not fix it, and field-order independence is deliberate.
2. **DI-67's gap is wider than never-products.** A host row answering `except never never` is
   admitted, and so is a request column `prod never nat` (tested). The sentence it breaks is in
   the frozen `foundation-wave2` contract, so this is a counterexample to register. The fix is an
   inhabitance check at admission. That check edits `Program/Admission.lean`, which Codex last
   changed on its own branch (`90df5d21`), so this repair should also wait for Codex or go ahead
   with Codex's agreement.

Two framing corrections:
- DB-15's "a codec is a row" already rules host-side decoding for data `Ty` can describe.
- "R3 after the milestone" is a recommendation in a research note, not a ruling.

## 0. Base, method, evidence words

Verifier of seat PEDIGREE. Tree `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`,
HEAD `ba9783c3` (a docs commit on top of the merge `bc77e97f`). `git diff bc77e97f ba9783c3 --
src/ Test/ AGENTS.md docs/DESIGN-BASIS.md docs/DESIGN-ISSUES.md` is empty (tested). No tracked file
was edited. I ran no `lake build`, `make`, generator, `git add` or `git commit`, and did not touch
Codex's worktree (`lean4-effect4-slice6`). Every Lean file was compiled through the lock, one at a
time: `serial.sh lake env lean -M6144 -DwarningAsError=true <file>`.

Evidence words:
- **proved**: a kernel theorem I ran, with its axioms printed.
- **tested**: a finite check I ran (`#guard`, `grep`, `git`, `wc`, `ls`).
- **reading**: read, not run.
- **assumed**: neither read nor run.

Every Lean check here is a finite probe over the tree's own definitions; none of it is host
evidence.

## 1. Verdicts

| id | verdict | evidence |
| --- | --- | --- |
| PED-01 | confirmed | **Reading:** `AGENTS.md:85-88`; `decisions.md:34` (row 13, "written … `f8c9b7fe`") and `:77` (row 36). **Tested:** `git log -S'Schema and program'` points at `f8c9b7fe`. **Nuance:** rows 13 and 36 were "do" rows with no owner ruling recorded, and "Ruling: (ii)" (`coherence-principle.md:285`) is scout F's heading. The tracked authority is AGENTS.md itself. |
| PED-02 | confirmed | **Tested:** `git show --stat b08f3b58` deletes `Schema/Transform.lean`, `Laws/Schema/Transform.lean` and `Schema/Endpoint.lean`. `git show b08f3b58^:src/Effect4/Schema/Transform.lean` shows `structure Transform (σ) (Γ) (A B E) (R)` with `program` and `typed`. `git grep` finds no Schema import under `Program/` or `Machine/`. **Reading:** `EffectfulField` imports the external `Effects.Algebra.Laws` and `Effects.Flow.Block` (`Schema/EffectfulField.lean:1-3`); `system-map.md:202` says "The laws are future work"; row 1 is open, and its own status says the transformation motive left with `b08f3b58` (`decisions.md:22`). |
| PED-03 | partly | **Confirmed (reading):** DI-08 is open (`DESIGN-ISSUES.md:80`). **Wrong in letter:** "D12 appears in tracked files only as docstrings." Tested, `git grep -w D12`: row 5 is titled "D12's shape" (`decisions.md:26`). It is a "do" row, which the register's header defines as "no decision content", so the register treats Decision 12 itself as settled. `docs/core/api-surface.md:74`, `:175` and `coherence-principle.md:220` also name it. `git grep 'Decision 12'` gives 5 hits in 3 files, not 3; the seat missed `Bridge.lean:233` and `:237`. **The real reason it is not a ruling:** the register's rule allows a module header as the tracked place of a ruling (`DESIGN-ISSUES.md:13-16`), but DI-08 never moved to "ruled", and no tracked file holds the owner's words. **Two more for the repair:** DI-08 cites a moved file (`Store/Shape.lean`, now `Store/Domain/Shape.lean`). Its second question has an answer in code: `Store/Domain/Shape` imports `Schema.Authoring`, which imports `Schema.Check` (reading). |
| PED-04 | confirmed | **Reading:** `Bridge.lean:38-59`, `:79-135`, `:140-206`, `:209-227`; the eight laws at `Laws/Schema/Codec.lean:16, 37, 50, 55, 62, 71, 82, 93`, over `CTy`; `Codec.lean:7-8`. **Tested:** `git grep schemaOf` finds only the definition at `Api.lean:137` (`RunnerBytes.schemaOf` is another function), and no S-5 gate exists under `harness/`. **Stale docstrings:** `Bridge.lean:13` says the retraction holds "for all types", and `:19` says "all 16 `Ty` constructors". The theorem needs `t.closed`, and `Ty` has 20 constructors. |
| PED-05 | confirmed, and stronger | **Tested:** T6 reruns. **New (V1a-c, tested):** three more numbers read back as `int`, each different from `schema .int`: a filter group whose id is `isInt` (its `>= 5` inner check is dropped), an aborted `isInt` filter, and an `isInt` filter with a payload. Red control VR1 fails as required. **A possible defence fails:** a check's payload sits in a record whose type is named `CheckRepresentationAnnotationOf` (`Representation.lean:773`), so someone could call T6 "modulo annotations". But a group's inner checks (V1a) and the `aborted` flag (V1b) are not annotations under any reading. So comparing payloads is not enough: the `number` arm must compare whole checks with the two the bridge mints. **Also:** the seat's cited red control R1 belongs to T1, not T6. |
| PED-06 | partly | **Tested:** T5 reruns, and red control R3 fails. **Field order is deliberate** (`Codec.lean:74-75`, "independent of object entry order"; JSON objects are unordered). So "make `decode` refuse non-canonical entry order" would break JSON semantics. **Exactness fails beyond field order (V2, tested):** at the supported union `union (except nat nat) (exitOf nat nat)`, `{"_tag":"Success","value":1}` decodes to `ctor 0 [nat 1]`, but that value encodes as `{"_tag":"Failure","failure":1}`. Red control VR2 fails. So the seat's R3.c law, with N as a field-order normaliser, is false at HEAD. |
| PED-07 | confirmed | **Reading:** `DESIGN-BASIS.md:664-667`; `decisions.md:23` (row 2, open, owner); `:204-209` (rows 111-116, "ruled 2026-10-01", owner: "D1–D6 as amended"); synthesis `:1138-1149` (D10, recommended); `system-map.md:232`. |
| PED-08 | partly | **Confirmed (reading):** three designs exist and nothing reconciles them: scout C `:690-700` and the ledger `:68`; the type algebra note `:126-185`; the charter `:458-474` and scout D `:208`. The `Ty.record` sugar's life is tested (`git show e75d9e61`, `b08f3b58`). **Too strong:** "no note decides a record's value encoding". Every generated `Canonical` image already encodes a Lean structure as `ctor 0`, fields in declaration order, with `ofVal_toVal` and `ofVal_exact` (`Api/RunnerDerived.lean:46-60`; `Store/Domain/Shape.lean:71`; reading). Under DB-11 that is the default a `Ty` record inherits. What is open is whether `Ty` records reuse it or carry names, the fork the tree seat proved. |
| PED-09 | partly | **Reading:** row 3 recommends "A with `Ty.app`" (`decisions.md:24`, a "do" row). The type algebra note says `Ty.app` "stays refused" in favour of `Ty.foreign` (`:173-182`). **But** `system-map.md:232` does not name `Ty.foreign`: it names the `Ty`/`Fields` spine and leaves the shape to the synthesis, which does (`:239-241`). Neither side is a ruling. This is a register recommendation against two force-added research notes, not two authorities in conflict. |
| PED-10 | confirmed, and wider | **Tested:** T11 and R2 rerun. **Proved:** P3 reruns at `[propext]`. **New (V3, tested):** a host-row answer `except never never` and a host-row request `prod never nat` are both admitted. **Proved:** `fits_except_never_never_empty` at `[propext, Quot.sound]` and `hasTy_except_never_never_false` at `[propext]`. Red controls VR3-VR5 fail as required. So "normalize annihilates never-products" would not close the gap. The broken sentence is also in the frozen contract `Test/contracts/foundation-wave2.contract.md:217-222` ("Inhabitation"). |
| PED-11 | partly | **Proved:** `inhabitance_needs_admission` reruns. **But** it only shows the premise is load-bearing, trivially at `int`; the synthesis clause already says "∀ admitted τ" (`:246`). **The live problem:** HEAD's admission does not establish the premise (PED-10, V3). Per-constructor refusals cannot fix that, because `prod never nat` and `except never never` are uninhabited by composition, not by constructor. **The shape needed:** a decidable `inhabited : Ty → Bool` with `inhabited τ = true ↔ ∃ w v, Fits w v τ`, refused at admission. Template parameters need their own clause: a `var 0` answer column is admitted and the use site instantiates it at `never` (V3, tested). |
| PED-12 | partly | **Confirmed:** no ruling covers decoding inside a program. Tested by grep; one extra hit, `coherence-principle.md:418`, uses `decodeUnknownSync` as a test oracle, not as a route. **But:** DB-15's "a codec is a row" (`DESIGN-BASIS.md:664-665`) is itself the ruled route (a) for data `Ty` can describe: a host row decodes and answers a declared `Ty`. What is unruled is records and in-program decoding. **Route (c) is half a route:** `Schema.decode` takes a `Json` tree, programs hold JSON text (`DESIGN-BASIS.md:603`), and `Effect4.Json` has no parser ("No … parsing … is declared", `Data/Json.lean` header, reading). **Census figures:** confirmed by reading (ingest census `:41-71`); the effect seat's recount puts `decodeUnknownEffect` at 545, in 4 of the projects (`effect/census_heads.log`, reading). |
| PED-13 | confirmed | **Tested:** `grep -i recursi` over decisions, DI, system-map, STATE, DESIGN-BASIS, machine-state, host-boundary, coherence-principle and post-Phase C finds no row for recursive data types. Row 118 (`:211`) is about service carriers; post-Phase C `:733` is a proposal. **Reading:** `Document.lean:34-56` (SC-DOC-01..07 open); `Bridge.lean` has no `reference` or `suspend` arm. |
| PED-14 | confirmed | **Tested:** T10 reruns. **Reading:** `DESIGN-ISSUES.md:134` (DI-62, amended 2026-09-12); `DESIGN-BASIS.md:649-656`. |
| PED-15 | partly | **Tested:** T7 reruns. **Reading:** DI-67, rows 108-109, and T5. **Overstated:** the two tracked timings are compatible: DI-67's "extend by one later" and row 109's "when `Duration`, `Schedule` or `Random` arithmetic is modelled". Only the untracked T5 sets another trigger. **Wrong:** "signed integers have no route at all". DB-15's recommended (not ruled) text calls `int` "the cheapest to lift" (`DESIGN-BASIS.md:669-673`), and D10's packet includes `int` (synthesis `:1139-1142`). |
| PED-16 | confirmed | **Tested:** T8 reruns; `git grep eqAt` finds only unrelated meta code (`FoldOf.lean:605`). **Reading:** `NativeAtom.lean:193-194`; `DESIGN-ISSUES.md:107`; `machine-state.md:199`. |
| PED-17 | confirmed | **Tested:** `wc -l` gives `Check` 1,499, `EffectfulField` 960, `Annotations` 1,193, `Accepts` 117 and `Image` 53. `src/Effect4.lean:52-83` imports four of them, and `Api.lean:20` imports `Image`. `schemaOf` is at `Api.lean:137` and `render` at `Shape.lean:425`. **Reading:** row 39 says "landing after that note is confirmed; nothing deleted yet" (`decisions.md:85`). |
| PED-18 | confirmed | **Tested:** T9 reruns, and V4 adds `deferredOf` and `int`. Per `git show 0a2cb898`, the commit that inverted `isSupported` ("DI-95 closed in the same commit") also added the DI-95 row reading "open". `README.md:34-35` came in at `e75d9e61`. The header at `JsonNumber.lean:12-16` cites nine modules, and all nine are missing (`ls`), not just one. |
| PED-19 | partly | **Confirmed:** "no theorem relates them" and the three pinned disagreements (`DialectContract.lean:1-19`, `:31-38`, reading). V5 re-checks that the store's `nat` reads back as `int` (tested). **Wrong in letter:** system-map §4 does list `Shape`: the value row reads "`Kind`/`Shape` classify it" (`system-map.md:147`). The gap is that `Ty` and `Shape` both classify `Val` with no connector between them. |
| PED-20 | partly | **Lineage confirmed (reading):** `DESIGN-BASIS.md:586-588`; host-rows slice `:7-8`, `:500-501`. **The inference does not follow:** "`Ty` has no sum" is the slice's reason for the error encoding only (`:198-201`). "Step 1" means dispatch order ("That is step 1, before either the memo fix or the row", `:195`), not a staged plan for records. DB-15's own reason for refusing records, "columns are pairs" (`:665`), has not gone away. **Do not** put "a staging choice whose reason has gone" to the owner as written. |
| PED-21 | partly | **Reading:** schema-at-boundaries `:4-9`; `DESIGN-BASIS.md:599-608`. **Tested (V5):** the SQL row's published answer is an array of arrays of string pairs. **Overstated:** only the SQL query row answers a record (`Packages/SqliteBun.lean:67`). The KeyValueStore rows answer `option string`, `unit`, `bool` and a handle, which D12's schema describes exactly (`KeyValueStoreMemory.lean:38-53`). D12 holds to the letter everywhere; its purpose fails only where the answer is record-shaped. |
| PED-22 | partly | **Confirmed (reading):** the record literature is marked "assumed" in the type algebra note (`:942`, `:964-969`) and the synthesis (`:741`). **Missed:** the 2026-09-09 types scout weighs Wand, Rémy, Gaster–Jones and Leijen 2005 (`docs/research/2026-09-09-design-scout-types.md:401-402`, `:445`, untracked). It calls row variables a "false friend" here, because `Eff` has no binder and `Ty` is ground. It takes Leijen 2005's label removal as the model of `catchTag`'s residual. It marks the papers neither read nor assumed. |
| PED-23 | partly | **Shapes:** (a), (b) and (f) are theorem shapes. (c)'s law with N as field order is false at HEAD (V2). (g) is a finite gate, as the seat says. (h) is a capability list, which the owner's rule excludes. **Missing:** the shapes are stated per `Σ_core` constructor, but system-map §1.1 puts nominal data declarations in `Σ_app`, where they must quantify over the declaration table. **Conflict:** (a) and (e) clash for records. The tree seat proved `positional_width_unsound` (`tree/RecordNested.log`, read, not rerun): with positional values, TypeScript's width subtyping makes `fits_sub` false. |
| PED-24 | partly | **Reading:** synthesis `:1026-1033` orders R3 after the milestone. That is a recommendation in a force-added research note; no tracked register orders it. STATE's "R3" (`:80`, `:415-422`) is a different R3 (tested by grep). **The collision is wider than stated:** the DI-67 repair edits `Program/Admission.lean`, which Codex last changed at `90df5d21` (`codex/slice6-fixes`, the row-97 handle scan; tested with `git merge-base`). It also adds a field to `AdmittedProgram`, which `Laws/Run.lean:208-219`, `Laws/Program/CheckedTyping.lean:112-115`, `Api/Built.lean:23` and `Api/HostSession.lean:85` consume (reading). The typed-state proofs under `Laws/Program/Typed/` do not use it (tested by grep). |

Tally: 11 confirmed, 13 partly, 0 refuted.

## 2. What the seat missed

1. **JSON exactness fails beyond field order (tested, V2; red control VR2).**
   - `Val` is untyped. `Exit.success v`, `Result.failure v` and every one-field structure image
     are all `ctor 0 [v]` (`Machine/Value.lean:199`, `:203`; `Api/RunnerDerived.lean:46-47`).
   - The union arm of `decodeRaw` accepts a later branch's image (`Codec.lean:209-212`).
   - So R3.c needs one of two things: a canonical-image check in `decode` (refuse `j` unless
     `encode t v` gives `j` back, modulo the unordered-object normaliser), or unions limited to
     members with disjoint images.
   - Records encoded as `ctor 0` would add more such overlaps.
2. **DI-67's gap is wider than never-products (tested, V3; proved, V3 theorems).**
   - `except never never` at a host-row answer and `prod never nat` at a host-row request are both
     admitted.
   - So the fix is an inhabitance check whose result agrees with `Fits`, or a restated DI-67;
     annihilating `never` inside `normalize` is not enough.
   - The broken sentence is in the frozen contract `foundation-wave2.contract.md:217-222`, so it
     belongs in `Test/Counterexamples/REGISTER.md`, not only beside DI-67.
3. **An answer-only template parameter (tested, V3).**
   - A host row whose answer is a template parameter that no request position binds (`var 0`) is
     admitted, and the program is typed at answer `never`.
   - The docstring at `Ty.lean:471-473` says `never` is "what TypeScript infers" here. The type
     algebra note shows TypeScript infers `unknown` (`:436-438`, `:858-861`, reading of tsgo
     lines; not run against tsgo).
   - Low impact today: no canonical row has such a parameter.
4. **More `ofSchema` exactness failures (tested, V1).**
   - A filter group, an aborted filter and an `isInt` payload all read back as `int`.
   - `schema (var i)` equals `schema (handle "effect/schema/TypeParameter")`, and that node reads
     back as the handle. This contradicts the comment at `Bridge.lean:57`.
   - The docstrings at `Bridge.lean:13` and `:19` are stale (they say "all types" and "16
     constructors").
5. **DB-15 already rules host-side decoding (reading).**
   - "A codec is a row" (`DESIGN-BASIS.md:664-665`) means decoding is a host row answering a
     declared `Ty`, for data `Ty` can describe.
   - Route (c) also needs a JSON text parser, and `Effect4.Json` declares none.
6. **A record value encoding already exists in the value carrier (reading).**
   - Every generated `Canonical` image encodes a Lean structure as `ctor 0`, fields in
     declaration order, with K2 laws (`RunnerDerived.lean:46-60`; `Store/Domain/Shape.lean:71`).
   - This is the default a `Ty` record inherits under DB-11. It is also exactly where the tree seat
     proved width subtyping unsound (`tree/RecordNested.log`, read, not rerun).
7. **R3's shapes are not over the open signature (reading).**
   - They are per `Σ_core` constructor, but nominal data declarations live in `Σ_app`
     (`system-map.md:47`).
   - Item (h) is a capability list.
   - The clash between (a) and (e) for records is already proved red by the tree seat.
8. **"D12" and "R3" each name several things in tracked files (tested, grep).**
   - "D12" is the schema-boundary Decision 12 (`Bridge.lean:10`, row 5). It is also the
     certificate protocol (`docs/STATE.md:41`; `namespace Effect4.Laws.Effects.D12`,
     `Laws/Program/Typed/ProtocolObligations.lean:8`), and the synthesis's inbound-entries
     decision (`:1161`).
   - "R3" in `docs/STATE.md:80` and `:415-422` is not system-map R3.
   - A DI-08 repair should cite "Decision 12" and rows 5, 9 and 39, never the bare "D12".
9. **DI-08's row itself is stale (tested).**
   - It cites `src/Effect4/Store/Shape.lean`, moved to `Store/Domain/Shape.lean` at `05417cc6`.
   - Its second question is answered in code. `Store/Domain/Shape` imports `Schema.Authoring`,
     which imports `Schema.Check`. `Authoring.lean` names none of the 83 named declarations in
     `Check.lean` (tested with a script), so the edge is an import only. Row 39's deletion of
     `Check.lean` must cut that import first.
10. **The seat's own standard for "ruled" is uneven (reading).**
    - It counts the S-3 amendment as ruled on module-header text (`Codec.lean:7-8`). It counts
      Decision 12 as not ruled although module headers also name it.
    - The register's rule accepts a module header (`DESIGN-ISSUES.md:13-16`).
    - Decision 12 fails for another reason: DI-08 never moved, and its text is in no tracked file.
11. **The DI-67 repair also meets Codex (tested, reading).**
    - An inhabitance scan edits `Program/Admission.lean`, last changed on `codex/slice6-fixes`
      (`90df5d21`).
    - It adds an `AdmittedProgram` field, which `Laws/Run.lean`, `CheckedTyping.lean`,
      `Api/Built.lean` and `Api/HostSession.lean` consume.
    - The typed-state proofs under `Laws/Program/Typed/` do not use that certificate (grep).
12. **The 2026-09-09 types scout already judged the row literature (reading).**
    - Its verdict, "false friend" (`2026-09-09-design-scout-types.md:401-402`, `:445`), is missing
      from the seat's pedigree.

## 3. Probes and commands

All files are in this folder.

- **The seat's probes, rerun unchanged:**
  - `verify-rerun-PedigreeProbe.log`: exit 0, byte-identical to `PedigreeProbe.log`. All five
    axiom lines match: `[propext]` twice, `[propext, Quot.sound]` three times.
  - `verify-rerun-PedigreeRed.log`: exit 1 with the same four errors R1-R4, byte-identical to
    `PedigreeRed.log`.
- **`verify-Probe.lean`:** final run exit 0 (`verify-Probe.log`).
  - Run 1 (`verify-Probe.run1.log`, exit 0) used `#eval` to discover two facts: the `var`-answer
    row is admitted, and the encoder writes the `except` image.
  - Run 2 (`verify-Probe.run2.log`, exit 1) failed on my guessed answer `var 0` and printed the
    actual answer, `some never`.
  - The final file pins both as `#guard`s.
  - Sections: V1 (`ofSchema` exactness), V2 (codec exactness at an overlapping union), V3 (DI-67
    admission gaps), V4 (DI-95's fourth constructor), V5 (the store's `nat` and the SQL row's
    schema).
  - **Proved:** `fits_except_never_never_empty` and `fits_var_empty` at `[propext, Quot.sound]`;
    `hasTy_except_never_never_false` at `[propext]`.
- **`verify-Red.lean`, the RED CONTROL:** exit 1 with exactly five errors, VR1-VR5
  (`verify-Red.log`).
- **Command, every compile:**
  `bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <absolute path>`.
  The final `verify-Probe.lean` run waited about 18 minutes for the lock.
- **Olean freshness:** all 349 `src/Effect4` modules have an olean no older than their source
  (mtime loop over `git ls-files`; tested). So the probes ran against HEAD's sources.
- **Greps and git commands (tested):**
  - `git grep 'Decision 12'`; `git grep -w D12`;
  - `grep -i recursi` over the nine register and authority files;
  - `git grep schemaOf`, `eqAt`, `inhabit` and `import Effect4.Schema`;
  - `git show --stat b08f3b58`, `e75d9e61` and `0a2cb898`;
  - `git show b08f3b58^:src/Effect4/Schema/Transform.lean`;
  - `wc -l src/Effect4/Schema/*.lean`;
  - `ls` of the nine modules `JsonNumber.lean` cites;
  - `git ls-files` for the tracked or untracked status of 25 cited notes (the seat's T/U marks are
    right).

## Working log (written as I went)

- I reran the seat's probe and red control first. Both outputs are byte-identical to the seat's
  logs.
- Reading done before the probes:
  - **AGENTS and registers:** `AGENTS.md:59-88`; decisions rows 1-13, 35, 36, 39, 56, 68 and
    108-118; DI-08, -15, -35, -47, -56, -62, -67, -78, -89, -92 and -95; DB-15
    (`DESIGN-BASIS.md:584-695`); system-map §§1.1, 4, 6 and 8; host-boundary §4.4.
  - **Code:** `Schema/Bridge.lean`, `Schema/Codec.lean` and `Laws/Schema/Codec.lean`, all three
    in full; `Program/Admission.lean:1-200`; `Program/Typed.lean:1-101`;
    `Membership.lean:60-160`; `Store/Domain/Shape.lean:50-470`; `Ty.lean:1-40` and `:460-500`.
  - **Tests and contracts:** `DialectContract.lean`; `SchemaGenerationContract.lean:115-160` and
    `:400-421`; `foundation-wave2.contract.md:210-222`.
  - **Notes:** the type algebra note (§1.3, §3.2, §5.2, §8); the synthesis (R3, §5.5, D10); the
    host-rows slice (§2.1, §7); schema-at-boundaries `:1-30`; composition synthesis §5; scout C
    P10; scout D §10; the charter (§4.4, R7); the 2026-09-09 types scout §2.2; the tree seat's
    one-thing and `RecordNested.log`; the effect seat's `census_heads.log`.
- Then V1-V5 and VR1-VR5, in three compiles of the probe and one of the red control.
