# Coordinator log — foundation implementation, wave 1 (2026-09-09)

Tree `66ee4657`; one shared checkout; at most four seats concurrently; the coordinator (this
seat) commits one slice at a time after its battery and runs the gate sweep once per wave. The
packet is `2026-09-09-foundation-settlement-v2.md`; the rules every seat obeys are
`2026-09-09-seat-brief-common.md`.

## 18:40 — wave 1 launched (four Opus seats)

| seat | brief | note it writes | lane |
| --- | --- | --- | --- |
| core admission (S1a) | `2026-09-09-seat-brief-core-admission.md` | `2026-09-09-seat-core-admission.md` | heavy |
| error laws (S2a prep) | `2026-09-09-seat-brief-error-laws.md` | `2026-09-09-seat-error-laws.md` | light |
| host face (S1b + scout A Q3/Q5/Q6/Q7) | `2026-09-09-seat-brief-host-face.md` | `2026-09-09-seat-host-face.md`, `-probes.{ts,py,json}` | two tool runs |
| ecosystem scout E | `2026-09-09-scout-brief-ecosystem.md` (amended) | `2026-09-09-scout-ecosystem.md`, `-probes.{py,json}` | none |

Serialization points: S1a lands before S2a's cutover (shared `Typing.lean`, `Compile.lean`);
S5a's regeneration window comes after the cutover.

## 18:50 — the DI-47 baseline captured

`Test/fixtures/baseline/66ee4657/` (untracked until S0 commits): `families.json` (49 families,
none missing), `eff_manifest.txt`, `wire-manifest.txt`, `golden-digests.sha256` (136 lines),
`README.md` (provenance and the promotion rule). Command, under the lane:

```
bash docs/research/host-rows-delivery/with-lane.sh lake env lean -M4096 <scratch>/baseline/Inventory.lean
```

The reflection source (scout C's inventory list plus the alphabets S2 appends to and the
framing alphabets; a name that is not an inductive is reported, never skipped):

```lean
import Lean
import Effect4
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let names : List Name := [ …the 44 names of scout C's inventory…,
    `Effect4.Machine.Err, `Effect4.Machine.Defect, `Effect4.Store.Kind, `Effect4.Machine.HandleKind]
  let mut seen : List Name := []
  let mut rows : Array Json := #[]
  let mut missing : Array String := #[]
  for n in names do
    match env.find? n with
    | some (ConstantInfo.inductInfo ind) =>
      for fam in ind.all do
        if seen.contains fam then continue
        seen := fam :: seen
        let some (ConstantInfo.inductInfo info) := env.find? fam | throwError "not an inductive: {fam}"
        let fields : Array String :=
          if isStructure env fam then (getStructureFields env fam).map (·.toString) else #[]
        rows := rows.push <| Json.mkObj [("family", toJson fam.toString),
          ("constructors", toJson (info.ctors.map (·.getString!))),
          ("fields", toJson fields), ("mutual", toJson (info.all.map (·.toString)))]
    | _ => missing := missing.push n.toString
  logInfo (Json.mkObj [("head", "66ee465730126048ad90d99d24ce4f12f5bb2982"),
    ("families", Json.arr rows), ("missing", toJson missing)]).compress
```

Alphabets at the baseline: `Eff` 27, `NativeOp` 23, `Ty` 15, `Machine.Err` 3 (`boom`, `tag`,
`tagged`), `Machine.Defect` 5 (`notImplemented`, `asyncFiber`, `badName`, `missingService`,
`user`), `Store.Kind` 15, `Machine.HandleKind` 6 (`fiber`, `cell`, `promise`, `scope`,
`memoMap`, `external`; the bytes are `HandleKind.byte`'s, not recorded here — S5b's gate
records them). Note for the record: `src/Effect4/Machine/Context.lean:282,291` declares a
second `Err` and `Defect` in namespace `Effect4.Machine.Env` (the header at `:52` calls them
old spellings kept as patterns); a K3 duplicate to list in the docs seat's corrections.

Scout C's `Inventory.lean` failed at `Option.inductInfo` (the anonymous-constructor form under
`let some (.inductInfo ind)` resolves against `Option`); qualifying the constructor fixes it.

## 19:15 — the core seat's boundary, and how it was lifted

The core seat landed the `dom` guards, `asyncRoute` (behaviour-free for `callback`),
`checkTable` and the API certificate, then stopped at routing `perform`: the reference
denotation (`Laws/Program/DenoteR.lean`) and three compiler-head lemmas (`Intro.lean:200-208`,
`Handles.lean:380`, `Agreement.lean:593`) mirror that arm and `run_eq_ref` relates them with no
premise, so a compiler-only change is false-making for the agreement graph. The ownership list
had excluded those files. `SendMessage` is disabled in this session, so the correction went
into the seat's brief as "Coordinator amendment, 19:15" (ownership lifted for the lockstep
change; the order denotation → compiler → head lemmas → `run_eq_ref` → the DI-61 theorem; a
half-day cost guard per proof). The laws seat's note §5 shows the core seat already moving
through the laws files (Agreement green; DenoteR `:1227-1239` and Handles `:394` red at 19:13).
Lesson for later briefs: ownership lists are a coordination default, never a fence around a
change whose blast radius is unmeasured; measure the blast radius (`rg` the mirrored arms)
before writing the list.

## 19:20 — a finding from the host seat: `.scoped` keeps `Scope` in the requirement row

Verified: rc.112's `Effect.scoped : Effect<A,E,R> → Effect<A,E,Exclude<R,Scope>>`
(`vendor/effect-4.0.0-rc.112/src/Effect.ts:12815-12817`), while `effTy`'s arm is
`| .scoped body => effTy sig env body` (`Typing.lean:254`), and `acquireRelease` adds
`sig.scopeKey` (`:258`); `LayerTy.bodyRequires` already discharges it for layer bodies
(`:171-174`). Consequence: the four sqlite truth programs have a non-empty requirement row in
Lean only, and print untyped for a requirement rc.112 does not give them — DI-24's "typed
print" question is moot for them once the arm discharges `Scope`. **New register item
(DI-63, for the docs seat):** the `.scoped` arm should compute `Row.diff t.requires
(Requirement.single sig.scopeKey)`; forces the `.ty` goldens whose programs use `scoped`
(`pAcquire.ty`, `pActions.ty` carry non-empty rows today), the truth modules' printed types,
`Test/Api/PackagesContract.lean` (two `scoped` programs, requires not pinned); a `Typing.lean`
change, so the core seat's, as its own commit with the golden regeneration. Also from the host
seat: the `R` spelling for a genuinely non-empty row is the union of the service carriers in
`printKey` order (measured under `tsc`); `add`/`succ` past `MAX_SAFE_INTEGER` compute silently
wrong while both byte writers refuse the value as a thrown exception (a defect inside Effect) —
the in-program comparison that steers a branch is what DI-56's restricted profile must name.

## 19:35 — laws seat finished; slice committed as `23e5717`

`2026-09-09-seat-error-laws.md` (518 lines) with reproducer and receipt. Five files, 539
insertions, 0 deletions, 26 new declarations within the ceiling. Battery re-run by the
coordinator under the lane (exit 0, 40 jobs), then committed alone — the core seat's and host
seat's uncommitted edits stay in the working tree. Root gate reasoning: `ErrorImage.lean` is
reachable through `Laws/Program/Typed.lean:2`, and the gate accepts any source in the
`Effect4 ++ Effect4.Laws` closure (`AxiomGate.lean:572-594`). Finding for the cutover: the
`.causeOf` arm must close its membership function over the arm's own error type
(`causeAdmits (fun v _ => Val.hasTy v e allocated) e c`); the open spelling fails structural
termination. Requests carried forward: R1 (`import Effect4.Program.ErrorImage` into
`Native.lean` and drop the temporary import in `Laws/Program/Typed.lean:2` in the same commit);
R4 (the denotation packet gains the new obligations at the cutover); R5 (two citation failures
in other seats' files: `Invocation.lean:18` spells `Effect4/Api.lean` without `src/`;
`harness/truth/NOTES.md` still cited).

## 19:36 — host-spec seat launched (S6a); four seats running

core (lockstep change), host face, scout E, host-spec. Expected churn in the tree: every
`ts/eff/*.gen.ts` carries a `cut-from` stamp keyed on the Lake trace of `Tools.TsGen`'s imports,
so the core seat's `Native.lean`/`Compile.lean` edits move every stamp line until the host
seat regenerates at the final tree; the byte gate is read at the wave's end, not mid-wave.

## 19:45 — scout E finished

`2026-09-09-scout-ecosystem.md` with reproducer and receipt (13 `rg` probes, 7 derived passes,
3 bun probes; exit 0). The findings that change the plan: (1) **DI-15 can be ruled** — no
pinned package needs a payload-carrying sum; every error sum is discriminated by string
literals (19 reason unions, 114 flat classes read); `Ty.lit` with `Ty.sub` suffices; but the
sums are heterogeneous and eight families put the branched-on value outside the tag
(`UniqueViolation.constraint` inside the first package), so G1's pair loses payloads — a
widening (`error := union (prod (lit rᵢ) Xᵢ)`, no new ordinal) is a follow-on ruling (E4).
(2) **The third package is `HttpClient` over `FetchHttpClient.layer`**, hermetic on bun with
`effect` alone (probed: `tsc` and `bun run` exit 0); FileSystem ranks fifth because no
implementation ships at the pin. (3) **Row identity collides before the third table**:
`rowKey = (spelling, trailing)` with `Nodup` refuses `HttpClient.get` beside
`KeyValueStore.get`; a receiver-qualified key is needed (new row DI-64). (4) G1 is sound only
for single-outer-tag rows; `catchReason` takes both tags; four error class names are declared
twice across packages. (5) `Ty` cannot type records, `Uint8Array` (65 modules, one inside the
rowed `KeyValueStore`), `bigint`, or function arguments; `.int` is the one refusal a declared
package type contradicts. (6) DI-62's image checked against 269 package `fail` payloads: 253
tagged instances, 14 strings, 0 numbers, 0 Booleans. E1–E11 and the §8 corrections are folded
into the docs seat's brief (amendment 19:50). Correction accepted: DI-59 and DI-62 are not
register rows at `66ee4657`; the docs seat appends DI-59–DI-64.

## 19:55 — docs seat launched (S0 draft); 20:10 — the types-as-data research seat launched

The docs seat entered E's slot with the amended brief (DI-59–DI-64 appended; E1–E11 and the
§8 corrections as recommendations; the denotation packet's new obligations; the baseline
README cited). The owner then asked for a research seat on the type layer itself — model the
type requirements comprehensively, build centralized tooling, explore Lean's LCNF and IR,
treat TypeScript as data by programming over the TypeScript compiler, look at FFI — with
explicit permission to build scratch experiments. Brief:
`2026-09-09-seat-brief-types-tooling.md` (the core problem stated against the tree; six
experiments X1–X6: the TypeScript checker as the target-side oracle, a scratch LCNF→TypeScript
emitter beside `Lcnf/Translate.lean`, IR versus LCNF as the source, the type-requirements model
and the missing count guard as Lean metaprogramming, one FFI experiment — Lean → C → shared
library → `bun:ffi` — and the proposed architecture). It is the fifth concurrent seat, above the
owner's three-to-four guideline, on the owner's explicit request; it edits no tracked file and
uses the lane only for scratch compiles. Grounding facts recorded for it: `Lcnf/Translate.lean`
already translates mono-phase LCNF to OCaml with a rules table and holes; `ck.ts:3` already
imports the TypeScript compiler; the toolchain's `Lean/Compiler/LCNF/` and `IR/` are complete
at 4.33.1.

## 20:15 — owner's verdict on the parallel wave

"A failed experiment: too much conflict." Work is landing but not smoothly. Decisions for
what follows: **no further seats are launched in this wave**; the five running (core, host face,
host-spec, docs, types-as-data) finish and report; **every result of this wave is checked
carefully before any further commit** — rebuild, batteries, each touched file against its brief,
reproducers re-run, seat notes reconciled with the tree; the **next wave is scoped sequential
tasks** with the Lean restrictions eased (no per-seat ownership fences; the one-compiler rule
stays). The wave-2 briefs below are kept as task descriptions for that mode, not as parallel
launches. Causes recorded for the retrospective: unmeasured blast radius behind the ownership
lists; shared oleans red under another seat's in-flight build; generated-file stamps churning
under everyone; `SendMessage` unavailable, so a stuck seat could be steered only through its
brief on disk.

## 20:45 — docs seat finished (S0 draft, uncommitted)

`2026-09-09-seat-docs.md`. Ten tracked files, 403 insertions, 124 deletions: the register at 65
rows (DI-00 … DI-64; 48 ruled, 6 recommended — DI-15, DI-17, DI-38, DI-55, DI-63, DI-64 — 9
sequenced with an explicit S0 sentence, DI-11 amended), DB-09/DB-15 amendments, the map, the
architecture and generated documents, the README description, `known-red.txt` reasons, three
counterexample rows, the denotation packet's new ENSURES rows, one `AGENTS.md` authority row for
`Test/fixtures/baseline/<commit>/`. Eighteen Lean docstrings listed as owed with their owning
slices (two already written by the core seat). Citation check: one pre-existing failure, the
host seat's `harness/truth/NOTES.md` (DI-51, in progress there). Seven owner questions D1–D7
in the note; D7 records a concurrent edit to `docs/GENERATED.md` by another seat (the split
held). **Not committed**: per the owner's verdict, the whole wave is checked before any further
commit; S0 must land together with `Test/fixtures/baseline/66ee4657/` or four citations dangle,
and DI-50's citation waits on the host seat's `faces.contract.md`.

Still running: core (lockstep), host face, host-spec, types-as-data.

## 21:35 — host face seat finished (S1b, uncommitted); three gates green

`2026-09-09-seat-host-face.md` with `-probes.{ts,py,json}` (the runner re-derives every number
in 84 s). Gates, all through the lane: truth `PASS` with the regenerated modules type-checking
(was TS2375 on `pKv.ts`); ingest `PASS` including the new inclusion mode; ts-eff `PASS`. Nothing
under `src/Effect4/**`; `Truth.lean` touched only in the tape docstring; **no tape `.jsonl` byte
moved** — the projection is applied outside `recorded`, so the recorder keeps raw diagnostics.

Findings that correct the plan, to be checked in the review pass: (1) **DI-59 applies to the
five rows whose Lean error column is the pair, not eight** — projecting `Sql.close`/`Kv.make`
widens `never` and breaks `tsc` on five modules (`acquireRelease`'s release slot is
`Effect<unknown, never, R2>`); (2) **DI-37's inclusion claim is false as stated**: 60 of 408
printed modules are refused by the foreign contract, six of them well typed (`g75, g116, g203,
g223, g331, g393`, all `E-FAIL-NOT-DOCUMENTED` on `Effect.fail` payloads) — v2 ruled the
inclusion property as a fact; it is a measurement with counterexamples; (3) `catchTag`,
`catchTags`, `catchReason` are silent misses on a pair, only `catchIf` dispatches; the bare tuple
is the representation (the object form throws in the recorder's `wire`); (4) all four sqlite
programs have `R = never` on rc.112 — DI-24's root cause is DI-63's `.scoped` arm; (5)
`<const A, const B>` is the only DI-55 fix needing no printer change; (6) DI-40: two of the three
"stale" atom copies already had `strings`; the prelude self-test was the stale one, now under a
coverage check; (7) DI-49's corpus half is unlandable as worded — only 152 of 400 corpus
programs are well typed, so a `tsc` gate over the printed corpus must run on the well-typed
subset. Requests R-a..R-h in the note (the `.scoped` discharge; ratify the five-row DI-59; DI-37
wording and whether to pin 348/60; widen the truth `tsc` gate to `run-truth.ts`; S4b lands the
const-generic `pair`; `check-ingest.sh` edited beyond the ownership list, per step 8). Two of
its gate failures were the host-spec seat's in-flight `Profile.lean`; both passed once it
compiled. Waiting on S2 for the string case (`pairOf` refuses a string failure as a defect until
`Err.text` exists).

Still running: core (lockstep), host-spec, types-as-data.

## 21:50 — core seat finished (S1a, uncommitted); the routing half is blocked by its own choice

`2026-09-09-seat-core-admission.md` (425 lines) with reproducer, receipt (`accepted: true`) and
probe sources. **The seat never saw the 19:15 amendment**: it read its brief once, hit the
proof-graph boundary, reverted the `perform` routing, and stopped for a ruling rather than
guess — the right call under the brief it had. Landed (green on `Effect4 Effect4Laws` and the
named batteries, all through the lane): the two `Signature.dom` conjuncts (`Typing.lean:185-194,
237-246`); `asyncRoute` extracted and used by `callback` (`Compile.lean:511-552,583-598,630`);
`TableRefusal`/`checkTable` (`Native.lean:352-385`); `AdmittedProgram`, `admitProgram`,
`AdmitRefusal`, a separate `imageCertificate`, `runAdmitted`/`replayAdmitted`, raw-entry-point
docstrings (`Api.lean:257-343`); `Laws/Program/Invocation.lean` (new, five theorems including
`checkTable_none_externalRow`); `Test/Program/InvocationContract.lean` (338 lines) and its axiom
report; `Test/All.lean:98-99`; the DI-22 and DI-24/DI-51 docstrings. One edit outside its list:
`DenoteR.lean:1235`, a `simp only` argument for the extraction, no statement changed.

Measured: DI-54 changes **0 of 442** verdicts (152 → 152, 31 → 31, list-identical); the one
changed program is the counterexample, which typed only because `fail`'s answer `never`
equals the placeholder's `request := .never` — DI-54's row overstates the class (a correction
for the register). Lean and `ocaml/eff/eff_typing.ml:254,310` now agree on it.

**Not landed — the routing (DI-61 (a)):** `denoteR`'s own `perform` arm (`DenoteR.lean:592-598`),
`inlineYield`, `Handles.lean:379`, `Intro.lean:198,206` mirror the compiler's arm, and
`run_eq_ref` relates machine to denotation with no premise; the seat pinned the gap as thirteen
`THE GAP` `#guard`s with a header in `Invocation.lean`, and its note §4/§7 carries the
ready-to-apply text for a scoped task **S1a-b** (the lockstep change: denotation, compiler,
head lemmas, `run_eq_ref`, then the theorem) — exactly the 19:15 amendment, now with the seat's
own measurements. **Owner's call whether S1a-b runs as the first scoped task of the next wave.**

Requests for the review pass: (1) `src/Effect4/Laws.lean` must import
`Effect4.Laws.Program.Invocation` or the root gate refuses the unreachable source
(coordinator-owned; do at review); (2) `Test/All.lean` was edited under the brief's permission
against `AGENTS.md`'s rule that agents never edit it — a brief error to fix in the next wave's
briefs; (3) DI-24 is closed for the policy only, `printDecl` still prints two parameters; (4)
two lane hygiene facts: piping a lane command into `head` leaves a stale `.lake/LANE.lock`
(the trap does not fire when the pipe closes early), and `TestProgram` as a build glob sweeps
other seats' in-flight modules — use module names.

Still running: host-spec, types-as-data.

## 22:30 — host-spec seat finished (S6a, uncommitted); green

`2026-09-09-seat-host-spec.md` with reproducer and receipt. `Program/Profile.lean` (new, 665
lines: `ProfileData` data only; `HostSpec` four relations; `LawfulHostSpec` three laws; `rc112`;
the `Scalar` and `Resource` models, 18 theorems); `Program/Admit.lean` additions only
(`RecordedReply`, `Envelope` with `Decidable`, `acceptReply`, eight theorems, `steppedBy`,
`AcceptedOnce`); `Test/Program/HostSpecContract.lean` (477 lines, 41 ascriptions, 74 guards) and
its axiom report; `Test/All.lean:100-101`; `run_eq_ref` docstring (DI-57);
`machine-scheduler-core.contract.md` files `RunEqRefTableStatement`. Builds through the lane:
`Effect4 Effect4Laws TestProgram` exit 0 (73 s); the DenoteR/Handles reds are gone. 64
declarations, none above the ceiling (26 axiom-free, 35 `[propext]`, 3 `[propext,
Quot.sound]`); `simp` once; no `omega`, `native_decide`, `sorry`. Exit criterion met line by
line, including: an exhausted tape ends at `frontier` with the reply still acceptable, and a
malformed record in the same tape refuses at position 1. Requests: R1 flip `rc112.admittedForms`'s
`external` entry when the routing (S1a-b) lands; R2 import direction (`Profile` imports
`Native`; `Admit` imports `Profile`) inverted from the brief to keep the source reachable — the
alternative is one import in `src/Effect4.lean`; R3 DI-57's proof is its own task after S6b; R5
the pinned `Host.read` answers after release by design, so a binding that wants to satisfy
`Profile.Resource` owes that refusal.

**The tracked work of the wave is complete** (laws committed at `23e5717`; core, host-face, docs,
host-spec uncommitted in the tree). The types-as-data seat edits no tracked file. The review
pass can start now.

## 22:45 → — the review pass (coordinator, sequential, one lane)

Order followed: rebuild all five roots → gate sweep → reproducers → every diff read against its
brief → docs diffs → corrections → refresh → final gates → commit plan.

- **Full rebuild** `Effect4 Effect4Laws Test OCaml5 Tools` (detached, lane): exit 0, 338 jobs;
  root gate 100 API/utility and 38 Laws-only modules; 287 modules, 43,947 declarations;
  ceiling `[propext, Quot.sound]`; boundary 7 modules / 36 declarations unchanged. Before it,
  the coordinator added `import Effect4.Laws.Program.Invocation` to `src/Effect4/Laws.lean`
  (the core seat's request R1 — without it the new law module is unreachable).
- **Sweep (detached, serial, lane)**: roots 0, ts-eff 0, census 0, coverage 0; **generated 1**
  (`src/Effect4/Program/Derived.lean: stale provenance` — its inputs include `Native.lean`,
  which S1a changed; the family must be regenerated, bytes expected identical but the stamp);
  **truth 1** (`result.md drifted` — the differential itself passes 24/24; the drift is the
  coordinator's own citation edits to `prelude.ts`/`run-truth.ts` moving the inputs digest
  the artefacts stamp; refresh with the producer commands). Ingest, citations, internal pending.
- **Reproducers without the lane**: host-face `-probes.py` exit 0; ecosystem `-probes.py`
  exit 0 (133 error classes, 173 layer exports, 269 `Effect.fail` payloads, 4 name collisions,
  as the note says). The three Lean reproducers (core, laws, host-spec) run after the sweep.
- **Code read** (every diff, against its brief): `Typing.lean` guards; `Compile.lean`
  `asyncRoute` (behaviour-free for `callback`; the `perform` arm honestly unchanged with a
  source comment naming the mirrors); `Native.lean` `checkTable`; `Api.lean` `admitProgram` /
  `AdmittedProgram` / `imageCertificate` / `runAdmitted` / `replayAdmitted` and the raw-entry
  docstrings; `Laws/Program/Invocation.lean` (five theorems, the gap stated in its header);
  `InvocationContract.lean` (13 `THE GAP` guards); `Profile.lean` (665 lines: data / spec /
  two lawful models / the rollback refutation — sound); `Admit.lean` envelope additions (sound;
  `AcceptedOnce` proved from the unparked fact); `DenoteR.lean:1235` one `simp only` argument;
  `RuntimeR.lean` docstring; `Packages.lean`, `Print.lean` docstrings; `prelude.ts` `pairOf`/
  `toPair` (five rows, defect on unsupported shapes — matches R1a); `run-truth.ts` (one function
  for the pair; raw diagnostics kept; self-test coverage of the atom set); `Truth.lean` tape
  docstring; `check-truth.py` (tsc step), `check-ts-eff-corpus.sh` (tsc on the truth modules;
  the corpus deliberately not type-checked, reason written), `check_generated.py` (DI-44 walk),
  `generate.py`/`generate.sh` (`--all`, `readme` last), `check-ingest.sh` (inclusion mode),
  `TsGen.lean` (atom set checked by `checkAtoms` before emission), `ck.ts`/`oxc.ts` (read the
  set), `check-corpus.ts` (inclusion up to key renumbering, refusals reported by code). No
  defect found in any of them.
- **Docs read**: the register (65 rows), DB-09 and DB-15 amendments, the exclusion lines, the
  map (§L2 wording, §L3 partition and baseline, the slice order), ARCHITECTURE (faces, DI-18,
  DI-27), README, three counterexample rows, the two `known-red` reasons, the packet's rows
  36–39, AGENTS. Sound, one class of error: the register, the map and `E4-HOST-CE-004` named
  the API `Api.admit`/`Admitted` where the code, to avoid the clash with `Program.admit`,
  says `admitProgram`/`AdmittedProgram` — fixed by the coordinator; and DI-61's row now states
  what S1a landed and that the routing is pinned as the gap and is the scoped task S1a-b.
- **Corrections by the coordinator**: the three `harness/truth/NOTES.md` citations repointed
  (the file never existed; the content is the faces packet §4 and the prelude's own per-export
  comments) — this is what moved the truth artefacts' digest; the `Profile` reachability import
  moved from `Program/Admit.lean` ("for reachability, not for use") to `src/Effect4.lean`,
  the root that aggregates, with the two host-spec batteries importing `Profile` directly.

## 23:40 — refresh, regeneration, commits

Refresh phase (lane, serial): `generate.sh --only derived` 0 (stamp only); rebuild
`Effect4 Effect4Laws Test` 0 (294 jobs, audit unchanged); truth producers 0/0 (`result.md`
moved in its stamp and `pSqlOrDie`'s host die payload, now the pair; `result.json` +48; no tape
`.jsonl` moved); `check-truth.py` PASS with the modules type-checking; roots PASS; ts-eff PASS;
the laws, core and host-spec reproducers all exit 0. `check-generated.sh` red on the next stale
stamp (`eff_types.ml`), so `generate.sh --all` at the final tree: exit 0, 142 more files, every
one a stamp line (the four OCaml sources have zero non-stamp changes); ts-eff PASS again;
`check-generated.sh` then red on a third cause — `check_generated.py:17` pins the
`generated-stale` red entry's reason text, which the docs seat rewrote for DI-19. Constant
aligned; **the owner ruled no re-run for that**.

Commits, one slice each, on `23e5717`: `fdc03f7` S1a (155 files: 11 of substance, 144
stamps), `ef327ff` S6a (8), `1ac5c36` S1b (58), `3709604` S0 (15, with the baseline). Working
tree clean but for the untracked `harness/truth/node_modules`. Review:
`2026-09-09-wave1-review.md` (verdict, per seat, eleven owner decisions, the retrospective).
Still running: the types-as-data seat. Not started: S1a-b (the routing), S2's cutover, and
every other item — the next wave is sequential scoped tasks per the owner.

## 00:05 — the types-as-data seat finished; the wave is complete

`2026-09-09-seat-types-tooling.md` (1,274 lines), reproducer re-run by the coordinator: 15
runs, 0 non-zero exits. Two cures for two diseases: finish generating the Lean-side mirrors
(an LCNF→TypeScript emitter reaches the whole typing algorithm with zero holes, 20,387/20,387
vectors), and give the target side a producer — the TypeScript checker as a pinned generated
family. It found two new printed-image bugs (the `branch` head ill-typed on differing
requirement rows; `acquireRelease`'s release error dropped by `effTy`), confirmed DI-63
mechanically, answered DI-29 from generated data (24/24 answer and error; 7/24 requirement =
the DI-63 set; the tables describe the adapter), and found the blocker for DI-63's payoff
(`Host.Resource` is not a type in the printed module). Twelve rulings T-1…T-12, first slice T0
(the checker oracle as a repository tool), FFI works but is not to be built now. Folded into
the review as decisions 12–17. **All seats of wave 1 have reported; nothing is running.**

## Wave 2 briefs, kept as scoped tasks for the next (sequential) wave

`2026-09-09-seat-brief-host-spec.md` (S6a), `2026-09-09-seat-brief-docs.md` (the S0 draft),
`2026-09-09-scout-brief-census.md` (amended with B's four-count correction). The S2a cutover is
the core seat's second assignment, from the laws seat's recipe. S5a preparation and the OCaml
framing repair (S5b) wait for a slot; the regeneration window waits for the cutover.

## Commit policy

Seats stage nothing. Per slice: the seat's receipt → the coordinator re-runs the battery it
names → one commit whose message carries the measured deltas (counts, named programs, tape
bytes) → the owner pushes. S0 (docs + the baseline directory) commits after the owner reads
the docs seat's diff.
