# Seat H receipt: the DESIGN-BASIS refresh (2026-10-01)

## The one thing first

The basis is refreshed and checked. It has seventeen rows, DB-16 and DB-17 new. Each row ends in
the six fields, and its status is only a link to system map §8. Three sections are retired, word
for word, to a history appendix, and one marked bibliography replaces "Primary sources". Every
citation, register id, DI number and source mark checks at `dceae006` with 0 failures (tested).

Before merging, know this: the basis's line numbers are at `dceae006`, and on
`refactor/phase1-phase3` at `e7f9756f` 41 of them point at the wrong line.
- Seat E's laws moved 38 lines in six files.
- Seat F's deletion in `Machine/Context.lean` moved 3.

Each cited text is unchanged; only its line moved. Nothing else fails there (tested), and the merge
has no conflict (tested).

My recommendation: keep `dceae006` as the stated commit, and re-pin once after wave 2, which will
move the same files again. `check_citations.py --drift <rev>` prints every new line.

## Base and head

- Base: `dceae006` on `refactor/phase1-phase3`.
- Worktree: `/Users/pooks/Dev/lean4-effect4-seat-H`, branch `seat/H`.
- Commits on `seat/H`:
  - `1efb963e`: the eight notes, force-added;
  - `240341a8`: the refreshed basis and the citation checker;
  - `1c4fa722`: the basis re-read against the seat F merge, and the checker's checks of ids, DI
    numbers and row shape;
  - the commit that adds this receipt, which is the head at hand-back. Its hash is in the
    hand-back message.
- Head of the work: `1c4fa722`. Nothing was pushed.

## Every changed path (against `dceae006`)

| Path | Change |
| --- | --- |
| `docs/DESIGN-BASIS.md` | Rewritten as described below; 824 lines become 2138 (+1496, −182). |
| `docs/research/2026-09-16-core-goals-and-end-state.md` | Force-added, content unchanged. |
| `docs/research/2026-09-07-grill-agenda.md` | Force-added, content unchanged. |
| `docs/research/2026-09-04-provision-algebra.md` | Force-added, content unchanged. |
| `docs/research/2026-09-10-config-path.md` | Force-added, content unchanged. |
| `docs/research/2026-09-05-runtime-semantics-core-math.md` | Force-added, content unchanged. Mode 100755, as on disk. |
| `docs/research/2026-09-05-effects-papers-review.md` | Force-added, content unchanged. Mode 100755, as on disk. |
| `docs/research/2026-09-07-lit-papers.md` | Force-added, content unchanged. |
| `docs/research/2026-09-16-dogfood-conclusions-review.md` | Force-added, content unchanged. |
| `docs/research/2026-10-01-design-basis-refresh/check_citations.py` | New: the citation checker. |
| `docs/research/2026-10-01-design-basis-refresh/receipt.md` | New: this receipt. |

Each note's SHA-256 is equal before and after the copy (tested, `shasum -a 256`). Each note was
untracked at `dceae006` (tested, `git ls-files --error-unmatch`).

Seat F force-added two of the same notes at `27495d51`, the provision algebra and the grill agenda.
Their blobs are identical to this branch's (tested: `798941184abf…` and `b37fa84562ce…` on both
sides), so the merge adds each once.

## The rows: amended, added, retired

### How the witnesses were re-read

Witnesses were re-read at these commits:
- `dceae006` for the tree;
- `a4ee7a14` for the `effects` package;
- `a561d604` for seat E's landings, cited as `git:a561d604:` paths.

Each pair `` `name` (`path:n`) `` was located by reading the cited line. The checker re-checks that
the name is on that line (tested).

Each row's pairs, counted by where they are read:

| Row | What changed | tree | package | seat E | earlier commit | probe | Status field |
| --- | --- | --- | --- | --- | --- | --- | --- |
| DB-01 | C1–C8 with the audit's qualifications; free sums are a coproduct of free monads (seat E), not a tensor; Hyland, Plotkin and Power by name; missing source replaced by the package pin | 3 | 18 | 7 | 0 | 20 | §8 R1, R2 |
| DB-02 | Superseded by `Eff`; its boundary rule is `AGENTS.md`'s, the pedigree of R7 | 1 | 0 | 0 | 0 | 0 | settled (superseded) |
| DB-03 | Behaviour is a function of the tape; tape action `replayEval_append`; `behaviour_unique` is the runner's uniqueness; injectivity not claimed (row 146); INV-TAPE-1/2 proposed, unruled | 14 | 0 | 2 | 0 | 0 | §8 R12, R6 |
| DB-04 | Kleene chain of the least fixed point; Elgot's laws at the limit (`conv_*`), at no single budget (`budget_not_fixpoint`); not an Elgot algebra | 22 | 0 | 5 | 0 | 0 | settled; divergence is R12's |
| DB-05 | `Point` children; algebraic in representation, operational in meaning (ALG-10); scope law `guardR_bind`, in the tree; `eraseControl_guardR_bind` (seat E) | 16 | 0 | 2 | 0 | 0 | settled |
| DB-06 | Six fields; witness claim made exact (no `wp`/`wlp` on `Eff`) | 0 | 0 | 0 | 1 | 0 | settled (a constraint) |
| DB-07 | The store handler is a comodel, lawful on live cells (`put_get`, `get_get`, `put_put`; `put_get_dead_fails` red) | 10 | 0 | 4 | 0 | 0 | §8 R11 |
| DB-08 | Six fields | 0 | 0 | 0 | 0 | 0 | settled |
| DB-09 | Six fields; the route defers to system map §1; line ranges corrected | 3 | 0 | 0 | 0 | 0 | §8 R6, R8 |
| DB-10 | Six fields; `Eff` for `Flow` (dated); a doubled line removed | 0 | 0 | 0 | 0 | 0 | settled |
| DB-11 | Paths moved to `Store/Carrier/`; row 137; value typing links DB-16 | 16 | 0 | 0 | 0 | 0 | §8 R1, R4 |
| DB-12 | Rows 104 and 105 landed; the row calculus links DB-17; `Refs` path corrected | 15 | 0 | 0 | 0 | 0 | §8 R5 |
| DB-13 | Six fields | 10 | 0 | 0 | 0 | 0 | settled |
| DB-14 | Six fields | 4 | 0 | 0 | 0 | 0 | settled |
| DB-15 | Records by row 119's ruled design; rows 120–132 by status link; Decision 12 links `host-boundary.md` §7; paths corrected | 5 | 0 | 0 | 0 | 6 | §8 R3 |
| DB-16 (new) | Typing as a protocol per operation over a world (detail below) | 45 | 0 | 7 | 0 | 20 | §8 R9 (R1, R4) |
| DB-17 (new) | One requirement row calculus (detail below) | 34 | 0 | 4 | 0 | 0 | §8 R5 |

In total there are 294 pairs: 198 in the tree, 18 in the package, 31 of seat E's, 1 at an earlier
commit and 46 in probes.

### The two new rows

**DB-16** is typing as a protocol per operation over a world.
- It records the formal pass's four findings: row 137 (ruled), rows 136 and 135, and row 134
  (ruled).
- Their counterexamples are `E4-TYPED-CE-009` to `E4-TYPED-CE-014`, on the ports at `dceae006`.
- It also records halting (row 139), M5's lemma by name (row 148) and `seq_typed` (seat E).
- Bind closure is refuted by red tests.
- It names five declared obligations and one missing witness.

**DB-17** is the requirement row calculus.
- Rows are the free bounded join-semilattice with relative complement.
- `provide` is substitution and is not associative (`provide_not_assoc`, red); `provideMerge`
  regroups (`provideMerge_assoc`).
- A row reads as a flat coeffect. Satisfaction is inclusion into `keysRow`, never an adjunction.
- Grading soundness is row 117's theorem. `build_total` is owed under R5 (row 147).

### Sections

- **Retired** to "History (retired 2026-10-01)", each under a one-line note:
  - "Semantic decomposition";
  - "Native library boundaries";
  - "Required proof graph".

  Each is word for word: every section's text is contained in the appendix (tested, a Python
  containment check against `dceae006`).
- **Replaced.** "Primary sources" becomes "Bibliography", with 61 entries:
  - 60 papers or books, each marked; by first mark, 22 read, 35 by name and 3 assumed;
  - one code source.

  "Literature names, corrected (2026-10-01)" is new, with 15 items.
- **Added:** "How to read a row".
- **Kept:**
  - "Re-review ruling", with two dated notes. Its three toolchain digests were recomputed and
    match (tested).
  - "Source and evidence rules", unchanged (tested, a diff).
  - "Designs excluded", with one line changed: a `Point` on `Eff`, a `BlockId` on the archived
    route.

## Commands and results

All were run from `/Users/pooks/Dev/lean4-effect4-seat-H`. `C` is
`python3 docs/research/2026-10-01-design-basis-refresh/check_citations.py`.

| Command | Exit | Result |
| --- | --- | --- |
| `C --self-test` | 0 | Structure control: 3 of 3 seeded defects found. Drift control: one move (`Provision.lean:69 -> 71` at `efcf1ae2`) and one unchanged line. Red control: 16 of 16 seeded defects, 1 obligation listed, 0 failures among the green lines (tested). |
| `C` (at `dceae006`) | 0 | 490 file citations, 104 commits, 5 digests, 9 tags, 904 identifiers, 294 witness pairs, 1 "witness missing" claim, 77 source marks, 56 register ids (7 registered after `dceae006`, found at `efcf1ae2`), 11 fallback ids, 30 DI numbers, 6 external pins: **0 failures**. 5 witnesses are declared obligations, each called "declared" in the text. History appendix: 1 STALE, `read_print_native`, deleted at `4e28669a` and kept as written. Structure: 17 rows, 0 failures. |
| `C --base e7f9756f` | 1 | 41 failures, every one a moved line ("name not on the cited line"); nothing else fails (tested). |
| `C --base efcf1ae2` | 1 | The same 41. |
| `C --drift a561d604` | 0 | 38 moved, 7 unchanged: seat E's merge alone. |
| `C --drift efcf1ae2` | 0 | 41 moved, 16 unchanged. |
| `C --drift e7f9756f` | 0 | 41 moved, 16 unchanged, the same list. |
| `C <the basis at dceae006>` | 1 | The old basis under the final checker: 5 citation failures and 15 structure failures (no old row had the six fields). |
| `git merge-tree --trivial-merge dceae006 e7f9756f 1c4fa722` | 0 | No path changed on both sides. The two notes both sides add are identical and resolve. 0 conflict markers (tested; this mode writes nothing). |
| `shasum -a 256` | — | Vendored `vendor/effect-4.0.0-rc.112/src/Schema.ts` at `dceae006` is `9358710e…`, DB-09's installed digest. The three toolchain files match the Re-review ruling (tested). |

The 5 citation failures in the old basis were:
- `src/Effect4/Store/Val.lean` and `src/Effect4/Store/Image.lean`, both moved under
  `Store/Carrier/`;
- `docs/research/EFFECTS-SPLIT-PLAN.md`, DB-01's only source, which was never in git (tested,
  `git log --all`);
- an ambiguous `Native.lean`;
- `read_print_native`, now in the history appendix.

There is no axiom output. No Lean file was added or changed and nothing was built, by the brief's
rule.

### The 41 moved lines (`dceae006` → `e7f9756f`; text identical at the new line)

| File | Moved | Old → new |
| --- | --- | --- |
| `src/Effect4/Laws/Program/DenoteR.lean` | 1 (cited twice) | 1380→1385 |
| `src/Effect4/Laws/Machine/Approximation.lean` | 7 | 176→185, 184→193, 756→765, 1208→1293, 1237→1322, 1403→1488, 1662→1747 |
| `src/Effect4/Laws/Api/Runner.lean` | 3 | 81→83, 157→160, 174→177 |
| `src/Effect4/Laws/Program/Iter.lean` | 4 | 30→32, 34→36, 36→38, 40→42 |
| `src/Effect4/Laws/Effects/Protocol.lean` | 10 | 30→41, 37→48, 45→56, 57→68, 66→77, 75→86, 83→94, 97→108, 108→130, 119→141 |
| `src/Effect4/Machine/Context.lean` | 3 | 72→76, 185→120, 188→123 (seat F, `7a12f485`) |
| `src/Effect4/Program/Provision.lean` | 13 | 69→71, 75→77, 85→87, 97→99, 106→108, 122→128, 137→160, 142→165, 148→171, 168→193, 246→271, 297→322, 606-607→631-632 |

The witness-pair check catches 40 of these. `Typed.inl` at `Protocol.lean:97` still passes it,
because the short name `inl` stands on line 97 at the tip. Only the drift report, which compares
text, catches it (tested).

## What changed after the seat F merge (`efcf1ae2`, then `e7f9756f`)

The worktree stayed at its base. These were read from git objects:
- **Four notes' marks, in six places.** Seat F tracked 18 notes at `27495d51`, among them four the
  basis marked untracked: the build path, the host rows slice, the timer dispatch and the timer
  semantics. The checker read tracking from the moving branch name, so 6 marks failed. It now reads
  at a fixed commit, `efcf1ae2`. The marks now say tracked, and the kept prose drops its "untracked"
  words, because the Sources field owns the mark.
- **The formal pass's register ids.** `E4-TYPED-CE-009` to `015` have been in the register since
  `66aa97d7` (tested); the basis now says so.
- **Four ids are minted in both the register and the archive.** `66aa97d7`'s header says a
  citation that needs the distinction names the file. These are `E4-SCHED-CE-004` (DB-05, the
  archive's), `E4-PROV-CE-005` and `006` (DB-12 and DB-17, the register's), and `E4-TYPED-CE-003`
  (DB-16, the register's). Each citation now names the file.
- **Decision 12 and the boundary rule** are written into `docs/core/host-boundary.md` §7
  (`0eea3cd0`). DB-15's row 122 now links there and copies nothing. The basis never wrote "D12"
  (tested, grep).
- **`Denote.ExitOk` is now `Denote.ExitHasTy`** (`32f4fabe`). The basis's `ExitOk` is the typed
  state's (`Typed/Admission.lean:30`), which keeps its name. No renamed name is cited, and
  `LoopSound.lean:306` and `:535` are unchanged (tested).
- **Row 150** (a narrower `FoldLift`, open, recommended for wave 3) is listed in DB-16's rows, with
  its probe line. Decisions rows are read at `e7f9756f`. Since `a561d604`, rows 34, 40, 56, 122,
  127, 141, 143 and 146–148 changed and row 150 is new. No status word the basis uses changed
  (reading).
- **Seat F's deletion of the unused service model** (`7a12f485`) removed nothing the basis cites
  (tested: no name failure at the tip); only the three `Context.lean` lines moved.

## Corrections not applied, and why

- **The model probe's synthesis §3.2, sixteen items.**
  - Applied, or verified as already correct: items 1–6, 10, 15 and 16. Items 2 and 3 were checked
    against the foundations review itself (reading). DB-16 now cites §7.2 item 5 as well.
  - Item 7 was already repaired at `57c93ba4`.
  - Item 9 (13 places, not ten) is not carried into the basis, which states no count.
  - Items 8, 11, 12, 13 and 14 lie outside the basis rows. Proposals for 8, 12 and 14 are below.
    For 11 and 13 the notes are history, and nothing is owed.
  - None of the sixteen turned out wrong.
- **The addendum's "Hyland, Plotkin and Power 2006, assumed"** became "by name", by the
  coordinator's later message. The bibliography and DB-01 say "by name".
- **The addendum's step-indexing reason** ("values carry no code") was replaced by the
  coordinator's wording: worlds hold syntactic types read as declarations.
- **The formal synthesis §2 attributes `guardR_bind` to this pass (P5).** It was already in the
  tree (`src/Effect4/Laws/Program/Intro/Prepare.lean:44`, read at `dceae006`), so the basis cites
  the tree. The synthesis keeps its text; a note is proposed below.
- **Withdrawn from this receipt's own draft.** The draft proposed replacing system map R1's "13
  places" with the audit's "27 sites". On re-reading the audit (§3), its 27 is a reading-based
  inventory of existing declaration sites the Σ_app slice would edit, world and order included. It
  is not the count of places pinned to the built-in signature. Those are two measures, so no R1
  change is proposed.
- **One owner per fact.**
  - Value typing is DB-16's; DB-11 links it.
  - The comodel is DB-07's; DB-05 links it.
  - The route is system map §1's; DB-09 links it.
  - C1–C8 are DB-01's. The map owns the signature and the status. `lcnf-route.md` §8 owns the
    stage rules.
  - Decision 12 is `host-boundary.md` §7's.
  - The glossary is system map §9 (row 142).

  No fact needed a second owner, so no item stopped.

## Lines proposed for the coordinator's files

Line numbers are at `e7f9756f`.

1. **`AGENTS.md:15`.**
   - Now: "the representation decisions (DB-01 … DB-15), their status and sources".
   - Proposed: "the representation decisions (DB-01 … DB-17): decision, rationale, witnesses,
     refusals, sources and literature marks; status only by link to the system map's §8".
2. **`docs/DESIGN-ISSUES.md:214`** ("Required proof graph … ten of eleven edges `Pending`"). Mark it
   resolved 2026-10-01: the section is retired to the basis's history appendix with its text kept,
   and edge status is the system map's §8.
3. **`docs/DESIGN-ISSUES.md:216`** ("Six tracked citations point at research notes that no longer
   exist …"). DB-01's instance is resolved: DB-01 cites the package pin `lakefile.toml:126-131`,
   and `docs/research/EFFECTS-SPLIT-PLAN.md` was never in git. The others it counts are not in the
   basis (tested: the checker finds every research path the basis cites).
4. **`docs/core/language-cut.md:60`.** Replace `DESIGN-BASIS.md:640` with "DB-15, *The admissible
   error image*". The citation was already wrong at `dceae006` (that text sat at line 655); line
   640 was right when the citation was written, at `696bc197` (tested).
5. **`docs/core/system-map.md` §8.**
   - **R2**, status cell. Add: "the binary sum is a coproduct of free monads (`sum_is_coproduct`,
     `Laws/Effects/Sum.lean`, merged `a561d604`), not a tensor (`sum_not_tensor`, red); C4 in both
     directions for the generic judgment (`Typed.inl_iff`, `Typed.inr_iff`); C1 vacuous for Σ_app
     (DB-01)".
   - **R3**, requirement cell. "through the `Ty`/`Fields` spine" becomes "as `Ty` growth: records
     by one constructor over a field list in canonical name order (row 119), variants with row
     130".
   - **R3**, status cell. "refused by DB-15 as written …; open as one DB-15 amendment; recursive
     types untracked" becomes "DB-15 amended 2026-10-01: records by row 119's ruled design, the
     slice after M5–M7; rows 120–132; recursive types are row 124 (open)".
   - **R5**, status cell. Add "(row 147)" after the owed restorations; add "DB-17" to the sources
     cell.
   - **R9**, sources cell. Add "DB-16".
   - **R12**, status cell. "INV-TAPE-1 and INV-TAPE-2 not yet in a tracked file" becomes "defined
     in `docs/research/2026-09-07-lit-papers.md` Q7 (tracked by seat H, `1efb963e`), recorded as
     proposed in DB-03; unruled (the model probe's D7)".
6. **`docs/core/decisions.md`.**
   - **Row 21**, recommendation cell. After "both soundness statements", add "(2026-10-01: stated
     at the empty table, they need no restatement; TREE-06, model-probe synthesis §3.2 item 8)".
   - **Row 2**. Its status reads "open", yet row 119 rules its stage (b) and supersedes (c). Close
     it into row 119, or say what stays open.
   - **A proposed "do" row.** "Re-pin the basis's line citations once after wave 2
     (`check_citations.py --drift <rev>`), moving the reading guide's commit and the seventeen
     status fields together; until then the stated commit is `dceae006`."
7. **`docs/DESIGN-ISSUES.md` DI-89.** Record the owner's 2026-09-07 ruling on the identity of
   forms: derived forms are stored expanded (grill agenda §3, call 1). The note is tracked since
   `1efb963e` and `27495d51`. Without it, the identity of forms reads as open (model-probe
   synthesis §3.2 item 12).
8. **`docs/STATE.md`, lines 271–275.** Replace "Dispatch is the owner's call." with "Landed on
   `seat/H` (2026-10-01; receipt `research/2026-10-01-design-basis-refresh/receipt.md`): DB-01 …
   DB-17 in one row shape, status by link to §8, every citation checked at `dceae006` by the
   seat's script."
9. **Force-add `docs/research/2026-09-05-reification-effhol.md`.** It is DB-06's only source and
   the last note the basis cites untracked (tested).
10. **`docs/research/2026-10-01-formal-pass/synthesis.md` §2.** Add a dated note: `guardR_bind`
    was in the tree before the pass (`Laws/Program/Intro/Prepare.lean:44`), and P5 re-proved it.
    System map §9 already says so.
11. **`docs/design/design-language.md:20` and `:89`.** They state INV-TAPE-1 and INV-TAPE-2 as
    rules. DB-03 and the model probe (D7) hold them proposed. Leave both as they are until D7
    rules, then align the one that lost.

## What remains stale

- **The 41 moved lines** (the table above), until they are re-pinned.
- **The history appendix**, which is kept as written by design: `read_print_native` (gone since
  `4e28669a`) and the proof graph's 2026-09-10 status cells.
- **Statements read at a stated commit and true there.** These are:
  - the five declared obligations;
  - `typedProg_mono_ledger`, still missing from the tree at `e7f9756f` (tested: the absence claim
    holds there);
  - decisions statuses at `e7f9756f`;
  - tracking at `efcf1ae2`.
- **The grill agenda's direction delta, item 11** ("INV-TAPE-1/2 written into DB-12"), was never
  applied. `git log -S INV-TAPE -- docs/DESIGN-BASIS.md` finds only this refresh (tested). The
  owner's 2026-09-07 ruling covered the agenda's fifteen calls (§3), not the delta (reading), so
  DB-03 records the two invariants as proposed.

## Open obligations

- **Five declared obligations**, which are not proved at `dceae006` (tested: each is a
  `ProofGraph.Obligation`): `typedProg_mono` (`Residual.lean:424`), `typedState_load`
  (`Assembly.lean:262`), `step_loop` (`:278`), `decision_preserves` (`:332`) and
  `typedState_reachable` (`:350`).
- **`typedProg_mono_ledger`**: witness missing at `dceae006`. It is proved in the port
  `docs/research/2026-10-01-landing/ports-at-dceae006/HeadTypedProgMono.lean:174`, and row 135
  carries it.
- **The re-pin decision** (above) and **the eleven proposals** (above).

## What is bounded

- **No build and no kernel check by this seat.** "Proved" in the basis means a theorem declared in
  the tree, or in the package, whose statement was re-read. The kernel check behind it is the trust
  gate's, at `[propext, Quot.sound]`, and was not rerun here (assumed from the gate).
- **The identifier check** shows a name exists somewhere: the index holds every declared name and
  each dotted component. The witness pairs show the name is on the cited line. The "Defined or
  proved" labels come from reading each line's declaration keyword (reading).
- **The drift report** compares text, so a moved line is found only if its text is unchanged. At
  `e7f9756f` every moved line was found (tested).
- **Literature marks** are the notes' marks. This seat opened no paper, and no mark was promoted.
- **External pins are recorded, not checked against their repositories** (assumed): the
  Effect-TS commit, the language service, PolyFun, lean4-effects `v0.1.0`, and the upstream
  `Schema.ts` digest `f0ecfa45…`.
- **No host evidence** was used.

## Log (the incremental record)

- **Step 1, the force-add.** The eight notes were copied from the main checkout with `cp -p`, their
  SHA-256 equal before and after, and committed by explicit path at `1efb963e`:
  - `core-goals-and-end-state`, `d2950a25…`;
  - `grill-agenda`, `2f829988…`;
  - `provision-algebra`, `1d10570e…`;
  - `config-path`, `701eb7c4…`;
  - `runtime-semantics-core-math`, `76908784…`;
  - `effects-papers-review`, `622636f8…`;
  - `lit-papers`, `9cea257f…`;
  - `dogfood-conclusions-review`, `690ee3ce…`.
- **The checker was written before the rows**, so it could find stale citations in kept text. Its
  first red control caught two defects in the checker itself, both repaired before any row was
  checked:
  - a commit hash was read as a name;
  - git grep's ERE here has neither `\b` nor `\s`, so a false absence claim passed.
- **Defects found in this refresh's own text, by the checker or on review, all fixed:**
  - seat E's short paths in prose;
  - an off-by-one range in DB-09;
  - a false absence claim for `guardR_bind`, which is in the tree;
  - "Proved" over definitions, relabelled "Defined or proved" by declaration keyword;
  - a bibliography first drafted from memory, rewritten from the notes' marks only;
  - DB-10's doubled line;
  - a wrapped code span;
  - `FoldLift`, which is not in the tree and is now cited at its probe line.
- **The coordinator's mid-task inputs:**
  - the formal synthesis;
  - seat E's merge at `a561d604`;
  - the second addendum: synthesis §2 and §5; rows 134–150; the DB-11, DB-17 and DB-03 wording;
    seat E's names and sites; seat F's rename and `host-boundary.md` §7.

  All are applied as above.
