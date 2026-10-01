Most of TREE holds, and TREE-02, -03 and -08 are now proved where the seat had reading or a row-level test, but its service-freshness rule is unsound as stated: a declaration at the machine's reserved `CurrentMemoMap` key passes it, types `yield* key` at `nat`, and the run answers a memo-map handle, so R1's lawful service table must also refuse reserved names (provision algebra §10, archived `E4-PROV-CE-007`) and should key carriers by code, as `Machine/Key.lean` already does.

# Verifier for seat TREE: verdicts on TREE-01 … TREE-16

Status: done, 2026-09-30. Research only; no tracked file edited; no commit, no `git add`.

- Seat under review: `docs/research/2026-09-30-model-probe/TREE/note.md`, `R1Probe.lean`,
  `R2Probe.lean`, `measure.py` and their logs.
- Note under review: `docs/research/2026-09-30-full-program-model-requirements.md`.
- Tree: HEAD `7cae243a` on `refactor/phase1-phase3`, clean at start.
- This folder is the seat's folder. `tree/` and `TREE/` are one directory on this Mac (same inode,
  273221468; the filesystem ignores case). Every file I wrote starts with `verify`. I edited none
  of the seat's files.
- Evidence words: **proved** (a kernel theorem I ran), **tested** (a finite check I ran),
  **reading** (read in code or notes, not run), **assumed**.

## 0. What I ran

| Check | Result |
| --- | --- |
| olean freshness | No tracked `src/**/*.lean` is newer than its `.lake/build` olean, and each has one (mtime loop over `git ls-files 'src/*.lean'`). **tested** |
| Seat's `R1Probe.lean` through the lock | exit 0, 2 s; output byte-identical to the seat's `R1Probe.log` (`verify-rerun-R1Probe.log`). **tested** |
| Seat's `R2Probe.lean` through the lock | exit 0, 4 s; output byte-identical to `R2Probe.log` (`verify-rerun-R2Probe.log`). **tested** |
| Every theorem of `R2Probe` | The seat prints 29 of 38. Its file copied unchanged plus 10 more `#print axioms` (`verify-R2Probe-allaxioms.lean`, `.log`): exit 0, all 38 at `[propext, Quot.sound]` or less (`SigExtends.refl` and `restrictCertificate_ty` were in no printed closure). **proved** |
| My probe `verify-Probe.lean` | exit 0; 15 theorems, all at `[propext, Quot.sound]` or less; 9 `#guard`s pass (`verify-Probe.log`). No `sorry`, `native_decide`, `axiom`, `partial`, `unsafe`; `decide +kernel` for finite facts. **proved / tested** |
| `measure.py` rerun | identical to `measure-designB.txt`; with comments stripped, 59 statements + **15** bodies (`verify-bodycheck.py`, `.txt`). **tested** |
| Counts | `(sig : Signature` 188 in 18 files; any binder 219 in 19 (31 implicit); `nativeSignature` 89 lines in 15 files, 2 in comments, 2 the lemma name; typed modules 1/2/3/4; rules 26+7+2+17+9+2 = 63; `FnName` in 51 tracked non-doc files (`verify-fnname-files.txt`). **tested** |

## 1. Verdicts

| Id | Verdict | Reason |
| --- | --- | --- |
| TREE-01 | **partly** | The route is real (reading): `ServicesOk` reads `nativeServiceTy` (`Typed/Admission.lean:32-34`) and is reached from `HandlesFit`'s context arm (:57), `CaptureTyped` (`Assembly.lean:47`), `preds.ServiceOk` (:56) and `fiberPre .setContext` (`Residual.lean:120`, not :121). Item E renames it to `ServicesFit`, still on `nativeServiceTy` (`2026-09-30-pass/membership/Fits.lean:89-91`; addendum 2 item E step 4). The B chain reruns clean. But "the note does not mention it" is too strong: R5's first bullet says "the context is typed by Σ's service table (row 90)", and row 90 is the ruling that created `ServicesOk` (`decisions.md:161`). What the note gets wrong is R1's "the typed state reads the signature through [`ProgramSource`]" (note :115-116) and §5 item 1, whose remedy does not reach this route. The seat does not cite row 90, which also records a rejected "world table from service keys to types"; shape A is a different object (fixed by the order, not grown per `provide`), and the coordinator should say so when ruling. |
| TREE-02 | **confirmed, strengthened** | `FlatFits` is `False` off `unit`/`nat`/`bool`/`string`/`handle` (`Fits.lean:79-86`, reading). **Proved** (`verify-Probe` §D, `servicesFit_refuses_option`): read through an open table that types K13 at `option nat`, the clause fails at every world for every context holding a value at K13. **Tested**: the honest program `provideService K13 (some 1) (service K13)` types closed at `option nat` and runs to `some 1`. So, with an open table, item E's clause refuses honest states. "Not structural on `Ty`" is right (reading); whether a measure on value and type would do is not probed. The flat-only recommendation is sound. |
| TREE-03 | **confirmed** | **Tested** by grep over all 16 typed modules for every route (`nativeSignature`, `nativeServiceTy`, `Api.typeOf`, `Checker.check`, `checkLayer`, `admitProgram`, `termEvaluatorFor`): exactly 13 places (Admission 2, Assembly 4, Residual 3, ForkSource 4). ForkSource's four are `nativeSignature` at its default empty table on `root : NativeEff` (:32, :47, :53, :68). **Proved** (`fork_source_extension_sig`): the law holds over every signature with the tree's own proof, so un-pinning it changes the statement only. Nuance: "mostly through `ProgramSource`" stays true (8 of 13 read the source's table, the two `Api.typeOf root.program root.table` premises included). The false part is R1's "through it", which 5 places do not go through. |
| TREE-04 | **confirmed** | Reading: `interpret_pinned` (`.lake/packages/effects/Effects/Algebra/Universal.lean:243`) and `Protocol.sum` (`Laws/Effects/Protocol.lean:83`) are over `RSig = StoreSig ⊕ FiberSig` (`Sched.lean:197`). A host-row perform is denoted `.async (.external op value) value` (`DenoteR.lean:235`), with no new `RSig` operation. **Proved** on rerun: `rows_append`, `prepend_not_extends`; **tested**: the three `#guard`s. Pedigree the seat missed: the mix-up starts in the charter's own status cell for *Extensible* (`2026-09-16-core-goals-and-end-state.md` §10: "true of the algebra by construction … `interpret_pinned` is stated per operation"); the note copies it. |
| TREE-05 | **confirmed, with two limits** | Rerun clean; all 38 axioms printed; 63 rules counted; the absence grep returns 0 hits, and no table-append typing lemma exists either (**tested**). Limits: it is a typing-layer result. The typed state is not table-monotone (TREE-08, now proved). `services_append`'s freshness premise is not lawfulness (missed item 1): `SigExtends` holds for the reserved-name declaration that breaks the run. |
| TREE-06 | **confirmed** | **Proved** on rerun: `meaning_typed_any`, `run_typed_any`, `meaningB_typed_any`, `run_sound_any`, `run_soundB_any`. Reading: `MeaningSound.lean:33-34` ("Scope: the empty row table") and every statement at `effTy nativeSignature []` (:518-521, :738-762; `LoopSound.lean:530-550`). Ledger 4B's "stated at `nativeSignature table`" (`2026-09-17-scout-findings-ledger.md:294-300`) is wrong. Receipt C2 (`2026-09-17-seat-author-receipt.md:318-327`) and row 21 (`decisions.md:52`) overstate the cost. `TypedProgram.run_sound`/`run_soundB` have no users beyond axiom prints (grep). The other theorems (`meaning_never_wrong`, `*_stores`, `sound`, `soundB`) follow by the same restriction lemma, which is stated at any environment (reading, not run). Qualifier: true for today's fragments, which exclude services and host rows. |
| TREE-07 | **partly** | The claim is **proved** (`shadow_not_extends` rerun) and **tested** (the two `#guard`s). The recommended rule ("refuse a declared key the built-in table types at another carrier") is not enough. The built-in table types the machine's reserved names 1–3 as `none`. So a declaration at `CurrentMemoMap`'s key ⟨3,3⟩ passes that rule and the probe's freshness premise (**proved**: `memo_entry_fresh`). It also types `provide(service(⟨3,3⟩), Layer.succeed(K4, 1))` at `nat`, and both machines finish with the memo map's handle: `Api.run` with `Val.handle 5 1`, the reference `replayR` with a kind-5 handle (**tested**, `verify-Probe` §B). The rule must also refuse names below `firstFreeName`. |
| TREE-08 | **confirmed, now proved** | The seat's evidence for the `TypedProg` claim was a row-level `#guard` plus reading. **Proved** (`verify-Probe` §A, `typedProg_not_table_monotone`): `hostCall` is the exact shape `DenoteR.lean:235` produces for a host-row perform. It is `TypedProg` under table `[]`, where every certificate passes at the placeholder, and not `TypedProg` under `[] ++ [rowB]`. So R2 for rows fails at the typed-state layer even under append, until `asyncPre` reads `dom` or an invariant confines registered rows to the table. |
| TREE-09 | **partly** | Soundness 0 (**proved**, TREE-06). Source route about 9 (reading, plausible). Shape A about 13 (reading): 13–17 if `initialWorld` gains an undefaulted parameter, which also restates `initial_valid` and its obligation (`Validity.lean:80`, :163) and two tests. Design B is 59 + **15**, not 59 + 18: three body hits are the next declaration's docstring (`restore_then_skip`, `test_settling_mask`, `forged_cell_not_live`; **tested**). "Off the M5–M7 path" holds for M5–M6, both stated over `ProgramSource` (`Assembly.lean:148-227`, reading). M7 is not declared: there is no `Typed/Transfer.lean`, and post-phase-c §I gives M7 the `TypedRun` corollaries and the exported theorem, so whether admission threading reaches M7 is open. The estimate of about 22 omits the two admission rules R1 needs (reserved names; flat carriers). |
| TREE-10 | **partly** | The inventory holds line by line (reading: `Native.lean:56-64, :90-99, :109, :154-207, :231-251, :278`; `Stores.lean:61, :243-270, :841-919`; `Rules.lean:49-66, :111-115`; `Scoped.lean:26`; `Typed.lean:45-50`; `Forms.lean:127-138`; `Styles.lean:129`; `MeaningSound.lean:297`; `profile.gen.ts:111`, which also carries the five names). Two corrections. (1) "31 files mention `FnName`" counts `src/`, `Test/` and `tools/` only; `git grep -l FnName` gives **51** tracked non-doc files: ocaml 16, ts 3 and harness 1 as well, mostly generated (**tested**). (2) "Step 3 reopens only the eight read-modify-write arms" drops the seat's own hedge. The reference machine applies `syncOpOf` (`DenoteR.lean:507, :599, :934, :947, :1203`), whose `refMake`/`deferredSucceed`/`deferredFail` decodes are `nat`-only. Rows as templates also change the checker facts that every Ref/Deferred perform arm of M5/M6 reads. So step 3 reopens more than the eight `Ψ_S` arms (reading). |
| TREE-11 | **partly** | L7 is confirmed (`2026-09-18-rows-42-43-plan.md:169`: "the six type codes … become a service table beside the program, as the row table is", depending on L6) and is absent from the note, whose §8 cites the plan's §§1, 2e only. Ledger 4B is already cited, in R1's source line (note :120). `Module.serviceTypes` is confirmed (`Authoring.lean:331-333`, R1Probe `#guard`). The L6 dependency belongs to L7's printer half ("the printer spells the tag's type from the table"), so the proof-side threading before generic cells does not contradict the plan. `Key.lean`'s frame selects a carrier by code (:337-349), which argues against the per-key table `nativeServiceTyWith` builds (missed item 2). |
| TREE-12 | **confirmed** | Reading: row 44 is "ruled 2026-09-19" (`decisions.md:91`); world at every type (`World.lean:52-57`); order laws proved (:394-406); M5, M6 `#proof_wanted` (`Assembly.lean:235-257`). |
| TREE-13 | **confirmed** | **Tested** by git: `f182d2b3` adds `theorem build_total` (`Program/Provision.lean:429` at that commit); `b08f3b58` cuts it ("Cut: … Provision's build_total/buildAll_total"); the docstring at :35-40 still says "proved once over the algebra". The provision note itself records the landing (§10: "landed as commit `f182d2b` … the workshop spike deleted"). |
| TREE-14 | **partly** | Right that R6's "exists: … the interim rule" is wrong at HEAD: there is no table scan in `Program/Admission.lean` (reading). Wrong that the reply side exists. `externalValue`'s non-allocation arm refuses only external handles (`Compile.lean:1354-1365`). The slice 6 brief, item A step 2, says that today "a live internal handle passes wherever `Val.hasTy` accepts its kind", and typed failures get no handle check. Both halves land with item A, which is in flight. |
| TREE-15 | **confirmed** | Every count reproduced exactly (§0). Additions: 2 of the 89 lines are in comments, and 10 `variable` lines bind sections, so neither count is a count of statements. |
| TREE-16 | **confirmed, with a qualifier** | Rerun exit 0, output identical; the seat's 8 `#guard`s pass. Qualifier: "every stage" means the checked stages. `Api.run` is raw by design (`Api.lean:311-318`) and runs `greetProgram` to `"hello"` (**tested**, `verify-Probe` §F). |

## 2. What the seat missed

1. **Reserved names are "fresh" and unsound.** Shown under TREE-07: **proved** that the
   declaration is fresh; **tested** that the program types at `nat` and the run answers the
   memo-map handle. The checker types `yield* ⟨3,3⟩` at the declared carrier, while the machine
   puts the memo map at that key: `addCurrentMemoMapK` and `withMemoMapThen`
   (`Compile.lean:816, :1125`). M5's premise `ClosedEff` ignores requirements (`Validity.lean:15`),
   so such a program is inside M5/M6. On the reference machine that M6's `RReachable` runs, its
   root fiber finishes with a kind-5 handle (**tested**). That exit fails `preds.exit` at `nat`,
   so the capstone would be false for it (reading). Pedigree:
   - provision algebra §10 (Deploy lane, finding 1): "a name table must skip the machine's four
     reserved keys";
   - archived `E4-PROV-CE-007` (`Test/Counterexamples/Archive/REGISTER.md:130`);
   - `ContextMap.lean:780-790` (`firstFreeName`);
   - design pass synthesis K8: an honest context under a layer carries ⟨3,3⟩.

   Today the hole is closed only by accident: `disagreeingService` compares each declaration with
   the built-in table, which types reserved names `none` (`Api/Author.lean:46-50`). No authority
   states the rule: a grep of `docs/core`, `DESIGN-ISSUES.md`, `DESIGN-BASIS.md` and `STATE.md`
   finds none, and the lane's `keyOf_ne_scopeKey` left with `Surface` (archived,
   `git:70b1571`). Opening the table removes the only guard. R1's "with its lawfulness" needs this
   clause, and `SigExtends` is not lawfulness.
2. **Per-key carriers contradict the key module's frame.** `nativeServiceTyWith` matches whole
   keys (`Services.lean:42-45`) and admits one code at two carriers (**proved**:
   `one_code_two_carriers`). `ServiceKey.Carrier` selects by code, "never by the nominal name"
   (`Machine/Key.lean:337-349`), and the built-in table is per code for free names (**proved**:
   `builtin_per_code`). The TS profile is a code-indexed table too (`profile.gen.ts:111`,
   `{"code":7,…}`). Whether the open table is keyed by code or by key is an owner decision with
   pedigree on the per-code side. The seat names per-code tables only as an alternative.
3. **M7 is not stated.** "Off the M5–M7 path" holds for M5–M6 only (TREE-09).
4. **Row 90 is the pedigree of `ServicesOk`,** and it records the rejected "world table"
   alternative (TREE-01).
5. **The *Extensible* mix-up starts in the charter** (end-state §10), not in the note (TREE-04).
6. **Item G (row 105, in flight) adds service-table reads to `checkLayer`.** Its `succeed` and
   `effect` leaves will look up `sig.serviceTy key` and refuse `serviceUnknown` (addendum 2 item G
   step 1). After G, the `memoGet` arm (`Residual.lean:52-53`) depends on the service table at
   every layer leaf. The seat's source route lists that arm, so R1 should land against G's
   checker, after G.
7. **Slips in the seat's evidence:**
   - TREE-08's `TypedProg` claim was "tested" at row level (now **proved**);
   - "29 theorems" (38, two never printed; now clean);
   - design B 18 bodies (15);
   - `FnName` 31 files (51 non-doc);
   - `Residual.lean:121` (:120);
   - `Program/Admission.lean` "10 of 16" (17 declarations; `Path` is the 17th);
   - R1Probe §B's "connectors back to the tree's judgments" exist for four of the six
     (`ServicesOk`, `HandlesFit`, `StrongValue`, `EnvTyped`), not for `StrongCause` and
     `StrongExit`. Those follow the same way (reading, not run).

## 3. Decisions at the owner's boundary (options and recommendation)

- **D-a. Reserved names in an open service table.**
  - (i) Admission refuses a declared key whose name is below `firstFreeName`.
  - (ii) Σ_core types the machine's own keys: the memo map has no `Ty` today.

  *Recommend (i)*. It is the provision lane's own rule, and it costs one decidable check
  beside TREE-07's carrier-conflict check.
- **D-b. Key the open table by code or by key.**
  - (i) Per code, as `Key.lean`, `nativeServiceTy` for free names, and the TS profile do. An
    application declares codes. Freshness is then a property of the code (not 4–9), plus D-a's
    rule on names.
  - (ii) Per key, as `nativeServiceTyWith` does today. This needs `Key.lean`'s frame and the
    profile amended.

  *Recommend (i)*. It extends the existing rule instead of adding a second one.
- **The seat's five decisions.** I agree with A (shape A, with row 90's rejected alternative
  distinguished), with flat-only carriers (made concrete by §D), and with the `asyncPre` domain
  bit (proved needed). The freshness decision needs D-a added; the append decision stands.

Proposed register rows (for the coordinator; I do not edit `decisions.md`):
- "Declared service keys: refuse reserved names (name below `firstFreeName`) and carriers that
  conflict with the built-in table" (amends TREE's freshness row).
- "The open service table is keyed by service code, as `Machine/Key.lean`'s frame is, or the
  frame is amended."

## 4. Receipt

- **Base / head:** `7cae243a` (HEAD); I read nothing in `lean4-effect4-slice6`.
- **Files written** (all `docs/research/2026-09-30-model-probe/tree/`, i.e. the seat's folder):
  - `verify.md`;
  - `verify-Probe.lean`, `verify-Probe.log`;
  - `verify-R2Probe-allaxioms.lean`, `verify-R2Probe-allaxioms.log`;
  - `verify-rerun-R1Probe.log`, `verify-rerun-R2Probe.log`;
  - `verify-bodycheck.py`, `verify-bodycheck.txt`;
  - `verify-fnname-files.txt`.

  Scratch (not evidence): `scratchpad/verify-tree/`.
- **Commands:** `bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`
  for `R1Probe.lean`, `R2Probe.lean`, `verify-Probe.lean` and `verify-R2Probe-allaxioms.lean`.
  All exit 0.
  - `python3 tree/measure.py . ServicesOk,…,CompletionStrong`: identical to the seat's.
  - `python3 tree/verify-bodycheck.py`: 59 + 15.
  - Greps as quoted in §0 and §1.
  - `git show f182d2b3:src/Effect4/Program/Provision.lean`, `git show --stat b08f3b58`.
- **Axioms:** every theorem in my two files is at `[propext, Quot.sound]`, `[propext]` or none.
- **Bounded evidence:** the `#guard`s are single-program finite tests. The capstone consequence
  in §2 item 1 is reading. The shape A count and the runtime threading counts are estimates by
  reading.
- **Open obligations:** none of the probes is landed. `verify-Probe` §A–§E are fixtures for a
  landing of R1/R2:
  - the non-monotone typed state, a red control until `asyncPre` reads `dom`;
  - the reserved-name control, red until admission refuses it;
  - the non-flat-carrier control, red until carriers are restricted;
  - one code at two carriers, red until the table is per code.
