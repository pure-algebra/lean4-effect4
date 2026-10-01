ONE THING: The seat's evidence reproduces, but most of its three omissions are already ruled or designed in sources it did not cite. The forms-identity choice was ruled on 2026-09-07 ("stored expanded"). DB-15 governs decoding. The 2026-09-10 Config route is designed. Retirement is not silent: `Run.Observation.retired` crosses the boundary. Nor does retirement touch M6, whose premise is item B's tape with no host answer, not a host relation. The one new gap, tested here: a program that uses the seat's retry form cannot be printed and read back (DI-91), so forms owe a printing-and-reading (face) obligation that R2 and R8 never state.

# Verifier for seat PROGRAMS

Status: done, 2026-09-30. Base `7cae243a` on `refactor/phase1-phase3`, clean tree. Research only.
Files are written only under `docs/research/2026-09-30-model-probe/programs/` (this file and
`verify/`); the seat's files are untouched (hashes below match the seat's receipt). No tracked
file was edited. No `lake build`, `make` or generator ran. Every Lean file was compiled through
the one-compiler lock (`serial.sh`).

**Evidence words.** **Proved**: a kernel theorem I ran, axioms printed. **Tested**: a finite
check I ran (`#guard`, type check, host run), with a red control. **Reading**: read in code or
notes, not run. **Assumed**: not checked.

**Short paths.** `Program/…`, `Machine/…`, `Laws/…`, `Api/…`, `Codegen/…` are under
`src/Effect4/`; rc.112 paths are under `vendor/effect-4.0.0-rc.112/src/`. "The note" is
`docs/research/2026-09-30-full-program-model-requirements.md`; "the seat" is
`programs/note.md` and its findings PROG-1 … PROG-15.

## 1. Reruns: what reproduces

| Check | Result | Red control |
| --- | --- | --- |
| The seat's four Lean probes, same lock, `-DwarningAsError=true` | **tested**: all exit 0 (`verify/rerun-summary.log`); `timeoutForm_scoped`, `retryForm_scoped` print `[propext, Quot.sound]`, `leaky_not_scoped` prints `[propext]` (**proved**, rerun) | `verify/RedProgram1.lean` (retired count flipped 1→0) and `verify/RedPrograms345.lean` (`[3, 2]`→`[3, 3]`, retired 2→0) each fail with exactly the flipped guards (`verify/Red*.log`), so the guards are evaluated |
| tsgo 7.0.0-dev.20260629.1 over the five programs and two capture controls | **tested**: exit 0 (`verify/rerun-typecheck.log`) | `red-control.ts` fails with the same three errors (TS2339 `forkDaemon`, TS2339 `intersect`, TS2375) |
| bun 1.4.2 host runs on the pinned rc.112 | **tested**: identical lines to the seat's `ts/hostruns.log`: p1 `42` with `"abort 1"`, 404 as `Fail(HttpError{status: 404, url})` after one call; p2 `200 bob`, `404 no user 9`, `401 bad token`, still succeeds after `ADMIN_TOKEN` is deleted mid-process; p3 close/stop order 1, 3, 2; p4 `[3,2,3]`; p5 `[-15,[10,10],"settled"]`; captures `[1,2]` and `[2,7]` (`verify/rerun-hostruns.log`) | `run-p2-noenv.ts` (fresh process, no variable) fails with `ConfigError`, as the seat says. No other `node_modules` exists above `ts/` (checked), so bun resolved the pinned package through `tsconfig.bun.json` |
| Hashes | the four `.lean` probes match the seat's receipt (`f214c1da…`, `0694ebc7…`, `118796bb…`, `c4cdde86…`); every `ts/*.ts` matches `ts/sha256.txt` | — |

So every **tested** claim the seat made reproduces as stated. The verdicts below turn on what
the claims are taken to show, and on sources the seat did not read.

## 2. Verdicts, finding by finding

| ID | Verdict | In one line |
| --- | --- | --- |
| PROG-1 forms | **partly** | R2 omits forms, as claimed. But `timeout` is not on DI-89's list, the obligation is already in tracked authorities, the identity choice was ruled on 2026-09-07, and DI-39 is missed |
| PROG-2 service code | **partly** | Both capture policies are tested and reproduce. The coupling of R5 and R7 is already stated in W2/W4 and row 82. The builder-route claim is too strong, and Cache's `requireServicesAt` is missed |
| PROG-3 host cancel | **partly** | rc.112's abort is tested. But retirement is not silent (`Run.Observation.retired`) and M6's premise is not a host relation. rc.112's notice is opt-in per call site |
| PROG-4 load inputs | **partly** | Holds against R1–R9, but the 2026-09-10 Config route already designs it. The proposed run identity drops profile and budget. The urgency holds for M5's load, not M6 |
| PROG-5 decode | **partly** | Holds, but DB-15 is the governing decision and the seat does not cite it. R3's records contradict DB-15 as written |
| PROG-6 coverage | **partly** | Right that no theorem covers a run that applies a host answer. The "only" list is incomplete, p2 is reading, and p5 also touches a host |
| PROG-7 error payloads | **partly** | The tested refusals hold. But p4 has no handler, the payloads have an owner (W1, through a DI-62/DB-15 amendment), and "common case" is already language-cut §6 |
| PROG-8 cells' types | **confirmed** | Tested, with a red control added |
| PROG-9 signed numbers | **partly** | Holds against R1–R9, now run in Lean. But it is DB-15's explicit refusal, and the row-109 remark is premature |
| PROG-10 dogfood sources | **confirmed** | The dogfood notes themselves are untracked too |
| PROG-11 R1 | **confirmed** | Rerun |
| PROG-12 dogfood 1 | **confirmed** | Rerun, and the red copy fails |
| PROG-13 cross-face | **partly** | R8 does lack the relation. "p4's outcome is set by the host's schedule" was not tested, and by reading p4's code it does not hold for the atomic limiter |
| PROG-14 pedigree | **partly** | The omission is real. The proposed pedigree reopens a ruled question, misapplies two lit-papers answers, and is mostly untracked |
| PROG-15 Ty bill | **partly** | The cited count is of definitions, not proofs. Recounted at HEAD: 25 of 63 |

### PROG-1 (forms): partly

- **Holds.**
  - The note's R2 names rows, services, cells, data types and atoms, and no forms.
  - The form table holds 19 forms and none of DI-89's list (`Codegen/Forms.lean:89-124`; count
    guard `:196`). Reading.
  - Concrete typing laws exist for 8 of them (`andThenEffect`, `andThenContinuation`,
    `andThenThunk`, `tapContinuation`, `tapEffect`, `as`, `asVoid`, `ensuring` in
    `Laws/Codegen/Forms.lean`). All 19 have scope lemmas (`Laws/Program/Authoring/Forms.lean`).
    No form has a named behaviour law. Reading.
  - `raceAll` is won by the first success (`Machine/Fibers.lean:340`). `CauseTerm` has no
    variable (`Program/Eff.lean:244-249`). `Decision` is `bool`, `option`, `tag`
    (`Program/Decision.lean:37-46`). rc.112's `raceAllFirst` forks with
    `forkUnsafe(parent, effect, true, true, false)` (the call inside `internal/effect.ts:1535-1580`;
    parameter names at `:5264-5270`). Reading.
  - The probes reproduce (tested). The form's entrants come from the authoring `fork`, whose
    default is `childOptions` = start immediately, not daemon
    (`Program/Authoring/Services.lean:129-130`). So the difference from rc.112 is the daemon flag
    and the two extra await fibers, as the seat says.
- **Wrong in detail.**
  - `timeout` is not on DI-89's named list. DI-89 names `retry`, `catchTag`, `forEach`, `all`,
    `Schedule` and the eliminators (`docs/DESIGN-ISSUES.md:161`). `timeout` belongs to W6
    ("retry/repeat/timeout composition", `docs/core/post-phase-c-synthesis.md:730`) and to the
    catalogue's slice 2 (`2026-09-19-stateful-api-catalogue.md` §4).
  - p3 also uses `catchTag` (`ts/p3-worker-queue.ts`, `Effect.catchTag("JobFailed", …)`).
  - The headline still holds. Every program uses at least one DI-89 form: p1 `retry` and
    `catchTag`; p2 `catchTag`; p3 `forEach` and `catchTag`; p4 `all`; p5 `forEach` and
    `catchTag`.
- **Already in the authorities, though not in R2.**
  - DI-89 itself.
  - `docs/core/machine-state.md:147-149`: "Each composed module therefore needs its own behavior
    law on a named profile, as DI-89 requires; typing is not enough".
  - `docs/core/system-map.md:78-80`: modules enter "by DI-89's routes".
  - The note's own §5 item 5 lists "Schedule and retry" and "Queue" as module contracts, each with
    a witness and a discriminating counterexample (post-phase-c §11.4).
  - So the gap is that R2 does not name the route, not that the obligation is unknown.
- **Refuted: "the identity choice has been open and unruled since 2026-09-07".**
  - The owner ruled it on 2026-09-07. The grill agenda's §3 says "**Ruled 2026-09-07 by the
    owner: all fifteen … as recommended**" (`2026-09-07-grill-agenda.md:74`). Call 1 is "Derived
    forms (`timeout`, `withPermits`, `transaction`)" with default (a): "store programs *expanded*
    … the address changes when an expansion changes" (`:84-88`).
  - The ruling was applied in the join dispatch: "Rulings applied (grill §3): **1** derived forms
    are stored expanded" (`2026-09-07-join-dispatch.md:43`).
  - It was challenged the next day: "store the term, not the expansion", for a corpus with
    external consumers (`2026-09-08-effectful-repository-notes.md` §6, `:278`).
  - All three notes are untracked. By the register's rule ("a ruling is made only when written
    into a tracked file"), the ruling is therefore unrecorded, not open.
  - The tracked rulings assume (a): DI-12, "everything derivable is an `Eff` to `Eff` expansion"
    (`docs/DESIGN-ISSUES.md:84`), and DI-89, "templates whose expansion is the combinator's
    meaning".
  - The action is to transcribe the 2026-09-07 ruling and say whether the 2026-09-08 challenge
    is taken up. It is not to open a fresh owner decision.
- **Missed: DI-39** (`docs/DESIGN-ISSUES.md:111`).
  - Ruled 2026-09-09: Forms rows for `catchTag`, `catchTags`, `catchIf`, `mapError`,
    `orElseSucceed` and `match`.
  - Never landed. The table has none of them; the heads sit only in the dual-dispatch data
    (`Codegen/Forms.lean:157-164`).
  - The ingest engine refuses `catchTag` as `E-HANDLER` (`ts/eff/ingest/ck.ts:938`), and the
    design-issue map lists DI-39 as "partial or owed subclauses".
  - So `catchTag`'s form status has been ruled twice and delivered never.
- **Missed: the face.** The seat's retry form cannot be printed and read back (tested, §3 X3).

### PROG-2 (a service is a record of code): partly

- **Holds.**
  - `[1, 2]` and `[2, 7]` reproduce on rc.112 (tested).
  - The Lean data capture answers `[1, 2]` (tested). My red control `captureBuiltLate` builds the
    same layer where `N` is already 2, and it answers `[2, 2]` (tested, `verify/VerifyPrograms.lean`
    §2). So the seat's guard does separate build time from call time.
  - `Ty` has no former for code (`docs/core/language-cut.md` §2, "no function types"). The note's
    R5 and R7 do not refer to each other (grep). Reading.
- **Already stated in post-phase-c §11.2,** which the note cites for R5 (W2) and R7 (W4) but
  without the dependency between them:
  - W2: "W4 for retained behavior where needed. Close construction, sharing/freshness,
    captured/invocation context … separately" (`:726`).
  - W4: "lexical captures, invocation/captured services, … Cache" (`:728`).
  - Row 82, `docs/core/machine-state.md:139-142`, and lit-papers Q1(b). The seat cites these
    three.
- **Too strong:** "the builder route reads services when a method is called".
  - The builder route captures one carrier value at build time. The seat's own capture control
    and its UserRepo-as-SQL-handle show it.
  - It departs from rc.112 when a method closes over more than one value, or over a value that
    none of the six carrier codes can hold (`Program/Native.lean:277-279`).
- **Missed: Cache's `requireServicesAt`** (`Cache.ts:199`; the type at `:200-204`).
  - It lets the program choose whether the lookup's requirement is paid when the cache is built
    or at every lookup. The run-time merge is the same either way.
  - So the capture law also has a typing half, for R5's requirement rows.

### PROG-3 (host cancellation): partly; two parts refuted

- **Holds.**
  - rc.112 aborts the signal (tested: "abort 1"; reading `internal/effect.ts:1116`, `:1135-1139`).
  - The protocol's `cancel` label is the host interrupting a fiber
    (`Api/HostProtocol.lean:21-26`, `:99-103`). Reading.
  - `retire` performs no cleanup (`Api/HostSession.lean:77-82`, `:191-199`). Reading.
- **Refuted: "the model retires the association silently; the host receives no notice".**
  - `Run.Observation` is described as "the reading that crosses a boundary". It carries
    `retired : List Key`, "the keys whose call was retired, in retirement order"
    (`src/Effect4/Run.lean:215-232`), filled from the session at `:250`.
  - The session keeps accepted but unapplied replies "available to the host cleanup driver"
    (`Api/HostSession.lean:191-193`).
  - Application at most once is proved (`applied_reply_refused`,
    `Laws/Api/HostSession.lean:219-224`; reading).
  - What is really missing is narrower:
    - the protocol's label alphabet has no retirement edge (`Api/HostProtocol.lean:16-26`), so
      `applyReply_conforms` and `advance_conforms` say nothing about it;
    - no lemma says a retired key is never applied. That is true by construction of `retire` and
      of `applyReply`'s `noCall` arm (reading), but it is not stated.
  - The seat's probes read `session.retired` themselves. That is the host driver reading the
    notice.
- **Refuted: "before M6 states its premise".**
  - M6's capstone, as ruled (row 95) and briefed (item B,
    `2026-09-30-codex-brief-slice6-and-fixes.md` §3, `:125-161`), counts reference-machine tapes
    in which no decision is a host answer.
  - At HEAD the declared statement (`Laws/Program/Typed/Assembly.lean:224-227`) still ranges over
    every tape; that is the defect item B repairs. Neither form mentions a host relation.
  - During this run, the working tree's uncommitted `docs/core/decisions.md` began recording row 95
    as "landed 2026-09-30 (Codex item B at `eca77d6a`, merged)". That commit's title is "Count M6
    over tapes with no host answer"; its contents were not read.
  - The hook the lane will use is `decision_preserves`'s `AnswerOk` premise (`:216-222`).
  - A retirement applies no answer, so it is already in scope, through the interrupt steps. Adding
    retirement to a host alphabet later restates nothing in M6.
  - The argument only bites if the owner adopts the note's own wording, "for every H the boundary
    judgment admits". Neither the note nor the seat checks that wording against item B (§3 X7).
- **Already in the authorities,** all parked by the owner on 2026-09-30:
  - host-boundary §4.2 (`:91-106`): retirement, "compensation pending", "cleanup pending";
  - §4.7: "cancellation before receipt, after receipt and after preparation" (`:202`) and
    "lost cleanup responsibility" (`:216`);
  - row 100: "cleanup ownership at every cancellation point";
  - W10's "cancellation" (`post-phase-c-synthesis.md:734`).
- **Missed: rc.112's notice is opt-in per call site.**
  - `tryPromise` creates the `AbortController` only when `try` takes the signal (`f.length !== 0`,
    `internal/effect.ts:1088`).
  - `callback` does so only when `register.length >= 2` (`:1169`), or when `register` returns a
    cancel effect.
  - Otherwise interruption abandons the call with no notice (`:1131-1133`).
  - So a host row's declaration must say whether it takes a cancellation. "H over call,
    retirement and reply" is not one shape for every row.
- **Pedigree.** lit-papers Q3(c) (Sivaramakrishnan et al. §3.2) concerns scopes left open when a
  run stops at a frontier. The grill agenda's call 9 ruled it: report them, and an abandon
  operation runs the finalizers. It does not speak about telling a host its call was dropped; the
  link is an analogy.

### PROG-4 (load-time inputs): partly

- **Holds.**
  - rc.112 reads the environment once per process (tested, with the seat's red control).
    Reading: `ConfigProvider.ts:341-343` (a `Context.Reference` whose default is `fromEnv()`),
    `:1183-1194`, and `Context.ts:1582-1589`.
  - No route from `Eff`: `Program/Config.lean` is imported only by the root, by `ConfigValue` and
    by its contract test (reading).
  - R1–R9 never mention load inputs (grep).
- **Already designed; the seat missed it.**
  - `docs/research/2026-09-10-config-path.md` (untracked), §3 route B and §4 D1: the provider's
    default is "the environment record the run was loaded with", carried "in the tape header
    beside the row table". Decisions D1–D5 are pending.
  - The header that would carry it exists: `Api/HostSession.lean:23-28` already has `profile` and
    `table`.
  - `Program/Config.lean` §6 (`:1202-1216`, `:1447-1453`) already gives a configuration's
    requirement row in the provision carrier (`Row ServiceKey`).
  - Row 51 (ruled 2026-09-20) already says "the root program's requirement row is provided at
    load". Row 83 and catalogue Q7 put the random seed "at load".
- **Incomplete.**
  - The seat's run identity is (program, table, load inputs, tape).
  - The research already has two more parts, the profile and the budget:
    `2026-09-07-cas-design.md:242` (a job is program, profile, fuel, tape) and the conclusions
    review §7 ("exact program content, row-table/profile identity, tape and budget").
- **Where the urgency does hold: at M5, not M6.**
  - M5's `typedState_load` loads by `loadR root.program fuel compileFuel` with no load inputs
    (`Laws/Program/Typed/Assembly.lean:148-150`). A configuration default read at load would
    change that statement.
  - The note's §5 item 1 already restates `ProgramSource` to carry the service table. The load
    inputs can ride in the same restatement.

### PROG-5 (decoding host answers): partly

- **Holds.** The atom alphabet (`Machine/Term.lean:146-165`, 33 atoms) has no parse and no
  number-to-text. Reading.
- **Missed: DB-15 is the governing decision.**
  - DB-15 (`docs/DESIGN-BASIS.md:584-663`, adopted 2026-09-08): host records and errors cross as
    strings; every SQL cell crosses as JSON text; errors cross as `prod string string`.
  - Its "What this basis refuses" (`:664-666`) refuses a `json` leaf in `Ty` and a record type in
    `Ty`.
  - The file the seat cites, `SqliteBun.lean:17-22`, itself cites DB-15.
- **Consequences.**
  - The seat's route (a), host rows that answer typed decoded values, is a DB-15 amendment.
  - The note's R3 ("closed under named records and variants") contradicts DB-15 as written.
    Neither the note nor the seat says so; decisions row 2 is still open.
  - Route (b), decoding as an `Eff` hole, is already W9's next deliverable: "admit needed
    parsing/transform behavior through typed Eff holes", and W9 names recursion
    (`post-phase-c-synthesis.md:733`).

### PROG-6 (what reaches the I/O programs): partly

- **Holds.**
  - No agreement theorem covers a run that applies a host answer: `run_eq_ref` takes no table
    (`Laws/Program/RuntimeR.lean:197-216`). Reading.
  - p1 and p3 are in neither fragment (tested, rerun).
- **Overstated: "only typing and the session's refusal lemmas reach them".**
  - Every program is also reached by the session's laws for the envelope, receipt commutation,
    at-most-once application and protocol conformance (`Laws/Api/HostSession.lean:12`, `:112`,
    `:219`, `:228`, `:259`), and by the runner's K5 laws (`replay_unique`,
    `Laws/Api/Runner.lean:157`).
  - `run_eq_ref` covers their runs at the empty table, and those runs stop at the first host
    call. Tested: program 1 there ends at a frontier with its root live, and the control (the
    limiter) finishes (`verify/VerifyPrograms.lean` §1b).
- **Evidence word.** p2's membership is reading: no Lean version of p2 with its SQL rows was built.
- **Count.** By the seat's own mapping, p5's `Effect.callback` timer is a host row too (note §2, the
  p5 table). So four of the five programs touch a host.
- **Already stated.** host-boundary §1 (`:32-34`) and row 99 state this cost. The finding's value
  is in putting it into R6.

### PROG-7 (structured error payloads): partly

- **Holds.** Number payloads are refused with `errorNotAdmitted`, and the 404 exit has the stated
  form (both tested, rerun).
- **Overstated: "every one of the five programs' handlers".** p4 has no handler. Four programs
  (p1, p2, p3, p5) read a payload field.
- **"No owner" is not right.**
  - Post-phase-c §11.2 W1 owns structured errors: "Arbitrary error payloads need the existing
    basis ruling amended, not silently enabled" (`:725`).
  - That basis ruling is DI-62 (`docs/DESIGN-ISSUES.md:134`), restated in DB-15
    (`docs/DESIGN-BASIS.md:655-657`).
- **"A common case, not a corner case" is already established.**
  - The language cut's §6 ranks error payloads second among the cuts that stop real programs.
  - DI-62's census of the pinned packages: 253 of 269 `Effect.fail` payloads are tagged class
    instances, and none is a number.

### PROG-8 (cells fixed at number): confirmed

- The error column `nat` reproduces (tested).
- My red control: the same pool without the deferred gate types at error `never` (tested,
  `verify/VerifyPrograms.lean` §3).
- Reading: `Program/Native.lean:205-207`. Row 42 already records `deferredAwait : nat / nat`; the
  new fact is the effect on an honest program's checked type.
- "So do its printed type annotations and boundary schemas" is reading, not tested.

### PROG-9 (signed numbers): partly

- **Holds.**
  - R1–R9 are silent (grep).
  - rc.112 answers −15 (tested, rerun).
  - In Lean, `sub 10 25` runs to 0, and the control `sub 25 10` runs to 15 (tested,
    `verify/VerifyPrograms.lean` §4).
  - The TypeScript prelude truncates (reading, `Machine/Term.lean:283-285`). OCaml not checked.
- **Missed: DB-15's refusal list keeps `.int` uninhabited.**
  - "`.int` stays uninhabited (`TYPED-FB-INT`)" (`docs/DESIGN-BASIS.md:665-666`).
  - The same section reports scout E's view that it is "the cheapest to lift" (`:668-673`).
  - host-boundary §4.4 lists `int` as "an explicit unsupported profile entry" (`:142`).
  - So the fix is a DB-15 amendment, not a new extension point.
- **Premature:** "p1 already meets row 109's condition".
  - Row 109 models binary64 once Duration, Schedule or Random arithmetic is modelled, and leaves
    `Math.pow` to the host.
  - p1 meets that only when DI-89's Schedule form exists.

### PROG-10 (the dogfood sources): confirmed

- **Reading.**
  - `docs/agents` at `f8c9b7fe^` lists four files, and none is a dogfood brief.
  - `git log --all -- Test/Dogfood` is empty, and no such file is on disk.
  - No dogfood program is in `src`, `Test` or `harness` at HEAD.
  - rc.112 exports no `Schedule.intersect`, no `Schedule.tapOutput`, no `Context.Tag` and no
    `Effect.forkDaemon` (grep of the exports; the red control's TS2339 covers two of them).
- **Added.** The two dogfood notes the note cites are themselves untracked: gitignored, not
  force-added.

### PROG-11 (R1's seventh carrier): confirmed

- Rerun (tested).
- Reading: `Api/Author.lean:46-50`; receipt C2 (`2026-09-17-seat-author-receipt.md:318-325`).

### PROG-12 (dogfood 1 at HEAD): confirmed

- Rerun (tested). The red copy flips the `[3, 2]` guard and fails.
- The dogfood-1 receipt records `pOneBatch` → `[3, 2]` and `pYielding` → `[5, 0]`
  (`2026-09-15-dogfood-1-receipt.md:44`).

### PROG-13 (the cross-face relation): partly

- **Holds.**
  - The note's R8 names no relation and no direction.
  - Row 79 (R79.1–R79.5, ruled 2026-09-20) asks for "state equality or directed behavior
    inclusion per admitted profile".
- **Not shown: "program 4's outcome [is] set by the host's schedule".**
  - It was not tested: one rc.112 run of the atomic limiter answers `[3,2,3]`.
  - With `Ref.modify`, the count does not depend on interleaving, only on the 1000 ms window
    (reading p4's code). The schedule-dependent race belongs to dogfood 1's non-atomic variant.
  - p3's order 1, 3, 2 comes from a single run.
- **Reading, not row 79's text.** The direction ("every rc.112 observation is some model
  observation") is the seat's reading. Row 79's text does not fix it.

### PROG-14 (pedigree): partly

- **Holds.** A grep of the note finds no reference to lit-papers, the catalogue, the
  effects-papers review or DI-89. It also finds no DB-15, no machine-state, no W6 and no W9.
- **But the proposed pedigree has four problems.**
  1. **It reopens a ruled question.** lit-papers Q2 and Q9 leave the identity choice open, and the
     grill agenda ruled it on 2026-09-07. Citing lit-papers without the ruling reopens it.
  2. **Two links are misapplied.**
     - Q3 (Sivaramakrishnan §3.2) supports open scopes at a frontier, not host retirement.
     - Q11's verdict is "laws only where an optimization relies on one"
       (`2026-09-07-lit-papers.md:443-444`), the opposite default to a behaviour law per form.
       DI-89 (2026-09-16) supersedes it.
  3. **Most of it is untracked.** lit-papers, the effects-papers review and the grill agenda are
     untracked. So are the note's own end-state charter, core mathematics, provision algebra and
     dogfood sources. The catalogue is tracked.
  4. **Further pedigree is missing from both.** DB-15; DI-39; DI-62's census; DI-91 and B19; the
     config-path note; rows 51 and 100; post-phase-c W6 and W9.

### PROG-15 (what a new `Ty` constructor costs): partly

- **Holds.** Adding a `Ty` constructor costs work beyond statements: row 61, and row 3's "an arm
  to each of the 16 folded `Ty` traversals".
- **But the cited count is of definitions, not proofs.**
  - The instrument reads definitions only. Its header says "What it does not see: Proofs"
    (`Laws/Auto/Exhaustive.lean:37-44`).
  - Recount at HEAD (tested, `verify/VerifyTyBill.lean`): 63 matches read `Ty`, and 25 of them
    have no catch-all. Row 61's "22 of 51" is the 2026-09-19 figure.
  - A match with a catch-all does not break, so "reaches every match" is too strong.
  - Six of the 25 are generated folds or derived instances that regenerate: `cata_ty`,
    `foldM_ty`, `foldMap_ty`, `foldMapAt_ty`, `TyC.toValTy` and `instReprTy.repr`.

## 3. What the seat missed

Numbered X1–X11, so that they are not confused with the milestones M5–M7.

**X1. The forms-identity choice has an owner ruling: stored expanded, 2026-09-07.**
- The ruling: grill agenda §3, call 1 (`2026-09-07-grill-agenda.md:74`, `:84-88`).
- Where it was applied: the join dispatch (`2026-09-07-join-dispatch.md:43`).
- A challenge the next day: the effectful repository notes §6 (`2026-09-08-…:278`), for any
  corpus with outside consumers.
- All three notes are untracked. The tracked DI-12 and DI-89 assume the expanded reading.
- What the coordinator owes: transcribe the ruling into a register, say whether the challenge is
  taken up, and state its consequence. Under it, any change to an expansion moves every digest
  and every byte of the programs that use the form.

**X2. DI-39 is ruled and owed.**
- Ruled 2026-09-09: `catchTag`, `catchTags`, `catchIf`, `mapError`, `orElseSucceed` and `match`
  become Forms rows (`docs/DESIGN-ISSUES.md:111`).
- None of them is in the table (`Codegen/Forms.lean:89-124`).
- The ingest engine refuses `catchTag` as `E-HANDLER` (`ts/eff/ingest/ck.ts:938`).
- So the most common form in the five programs was ruled twice (DI-39, DI-89) and has never been
  delivered.

**X3. Forms owe a printing-and-reading obligation, and the retry form fails it (tested).**
`verify/VerifyPrograms.lean` §1. Every result below is a `#guard`, and the red copy fails.
- **The retry form.**
  - It types: `retryAlone` types.
  - It is not readable. The reader refuses its printing at `annotation "local const"`.
  - The reason: its loop needs a cursor annotation, because the option columns are typed by no
    initial value. DI-91 (ruled 2026-09-17, `docs/DESIGN-ISSUES.md:163`) makes an annotated loop
    print `ofTy t` and "not readable", because "no reader of types exists, by design (B19)"
    (`Codegen/Read.lean:26-30`, `:433-434`).
  - So program 1 cannot be printed and read back: its round trip is refused at the same place.
- **The timeout form alone** reads back exactly.
- **Programs with no form read back:** the limiter and the capture control.
- **The pool, as the seat spelled it, does not read back.** Its workers are forked with
  `childOptions` (not daemon), and the printer drops a scoped fork's daemon flag (`Api.lean:160-162`).
  - rc.112's `Effect.forkScoped` forks a daemon (`forkScopedDefault`, `Codegen/Forms.lean:120-121`).
  - With those options the same pool reads back (tested; located in `verify/ScratchPoolRead.lean`).
  - So this one is the probe's fidelity, not a limit of the language.
- **Consequences for the requirements.**
  - The note's R8 says printing and reading are exact embeddings. That holds on the readable domain
    only, and a real program with a retry loop is outside it.
  - DI-89's forms therefore owe a sixth local obligation beside the seat's five: the expansion is
    in the readable image. Otherwise DI-91's fallback (a), a chosen representative `readTy`, is
    taken, which "needs a written amendment to B19".

**X4. DB-15 is the decision that R3 must amend, and the note contradicts it.**
- DB-15 (adopted 2026-09-08) sends host records and errors across as strings and every SQL cell as
  JSON text.
- Its refusal list (`docs/DESIGN-BASIS.md:664-666`) refuses a `json` leaf, a record type in `Ty`,
  and any inhabitant of `.int`.
- The note's R3 ("closed under named records and variants"), PROG-5's decoding, PROG-7's payloads
  and PROG-9's signed numbers are each amendments to DB-15, and to DI-62 for payloads. Neither the
  note nor the seat names DB-15.
- Decisions row 2 (names for records and sums) is still open. api-surface item 2 recommends
  annotation-carried names before `Ty.record`.

**X5. The Config route, the load and the run identity are already designed.**
- The 2026-09-10 config-path note (untracked) designs Config as `program`-kind rows over the
  context, with the environment snapshot in the tape header beside the row table. Decisions D1–D5
  are pending.
- `RowKind.program` still compiles to `frontier p` (`Program/Compile.lean:586`), so the hook the
  route needs is in place.
- Config.lean §6 already gives a configuration's requirement row. Row 51 (requirements provided at
  load) and row 83 (seed at load) already use "at load".
- The run identity in the research is program, profile, fuel and tape (`cas-design.md:242`; the
  conclusions review §7). Load inputs add to it; they do not replace it.
- The restatement this forces is M5's `typedState_load`. It can ride with the note's §5 item 1.

**X6. Retirement already crosses the boundary. What is missing is a protocol edge and a host
contract.**
- `Run.Observation.retired` (`Run.lean:215-232`, `:250`).
- At most one application is proved (`applied_reply_refused`).
- rc.112's own notice is opt-in per call site (`internal/effect.ts:1088`, `:1131-1133`, `:1169`).
  So a host row declares whether it takes a cancellation; it is not one shape for every row.

**X7. The note's R6 wording does not match M6 as planned, and the seat built on that wording.**
- The note says "the milestone says 'for every H the boundary judgment admits'".
- The capstone as ruled (row 95) and briefed (item B) is a predicate on tapes: no decision is a
  host answer. Its extension hook is `decision_preserves`'s `AnswerOk`.
- Keeping that form makes the note's §5 item 3 ("state the host premise now") unnecessary. The
  host relation can be defined with its whole event alphabet (call, reply, retirement, the
  cancellation option of X6) when the lane lands, with no restatement of M6.

**X8. The capture law has a typing half.**
- Cache's `requireServicesAt` (`Cache.ts:199-204`) moves the lookup's requirement between
  construction and use. The run-time merge is the same either way.
- So R5's requirement rows, not only R7's run-time context, must say where a code-valued service's
  requirements are paid.

**X9. The pedigree is mostly not in the tree.** The owner asked for "a consistent design basis to
refer to and build off of".
- Untracked:
  - from the note's sources: the end-state charter (the source of R2's *Extensible*), the core
    mathematics, the provision algebra and both dogfood notes;
  - from the seat's additions: lit-papers, the effects-papers review, the grill agenda (which holds
    X1's ruling) and the config-path note.
- `AGENTS.md` makes `docs/research/` history, not authority. The repository already has an owner
  for exactly this, `docs/DESIGN-BASIS.md`: "the representation decisions (DB-01 … DB-15), their
  status and sources".
- Neither the note nor the seat proposes recording R1–R9's pedigree there, or force-adding the
  notes. Either is the step that makes the pedigree durable, and it is the owner's actual request.

**X10. A stale claim in the tree that both the note and the seat repeat around.**
- `Program/Provision.lean:36-40` says `build_total` is "proved once over the algebra".
- That theorem was in the tree from `f182d2b3` until `b08f3b58` cut it (`git log -S`). No
  `theorem build_total` exists at HEAD.
- The note and the seat both say "proved in the 2026-09-04 workshop spike only". That misses the
  period in the tree, and neither flags the stale module header. R5 rests on this algebra.

**X11. Small corrections to the seat's tables.**
- p3 also uses `catchTag`.
- p4 has no error handler.
- p5's `Effect.callback` is a host row by the seat's own mapping. It could instead be modelled as
  the logical `sleep`, which would make p5 host-free. The seat does not discuss that choice.
- `timeout` is W6's, not DI-89's.
- The `Ty` bill is 25 of 63 at HEAD.

## 4. What changes for the coordinator

None of this is a ruling. The decisions register is the coordinator's, so these are proposed rows.

1. **Forms identity:** transcribe, do not reopen.
   - Record the 2026-09-07 ruling ("stored expanded") with its consequence: an expansion change
     moves every digest and every byte of the programs that use the form.
   - Ask the owner only whether the 2026-09-08 challenge is taken up (X1).
2. **The forms' obligations:**
   - typing lemma;
   - one behaviour law on a named observation;
   - scope safety (free);
   - reader admission of the idiomatic spelling;
   - the expansion lies in the readable image, or DI-91's fallback (a) is taken with a written B19
     amendment (X3);
   - land DI-39's six rows first (X2).
3. **One basis amendment for R3, DB-15:**
   - records and variants (row 2);
   - error payloads (DI-62);
   - `int`;
   - host answers decoded to typed values (or W9's typed `Eff` holes). (X4.)
4. **Load inputs:**
   - take up the 2026-09-10 Config route (D1–D5), carrying the environment snapshot in the
     session header;
   - identify a run by program, profile and table, budget, tape and load inputs;
   - restate M5's load with the `ProgramSource` change of the note's §5 item 1 (X5).
5. **Host:**
   - keep M6's premise as item B states it;
   - when the lane lands, give the host alphabet retirement, with a cancellation option declared
     per row as rc.112 has it;
   - add the retirement edge to the protocol, and a lemma that a retired key is never applied
     (X6, X7; with row 100, parked).
6. **Row 82:** add the typing half of the capture law (`requireServicesAt`, X8).
7. **Pedigree:** record R1–R9's sources in `docs/DESIGN-BASIS.md`, or force-add the notes
   (`AGENTS.md`'s authority map: "the notes that matter are force-added") (X9).
8. **Docstring:** fix `Program/Provision.lean:36-40` (`build_total`), a coordinator task (X10).

## 5. Receipt

**Base and head.** `7cae243a` (`refactor/phase1-phase3`, clean at the start). Nothing committed or
staged. The slice-6 worktree was neither read nor touched.

**Concurrent edits, not mine.** At 22:08, during this run, three tracked files changed in the
working tree: `docs/STATE.md`, `docs/core/decisions.md` and `docs/core/system-map.md` (uncommitted).
I edited none of them.
- My citations of those files were read at `7cae243a`.
- The rows I cite by number are unchanged in substance: rows 95, 96 and 110 gained "landed"
  statuses; rows 104–107 gained receipt notes; row 107 is "held" for this synthesis.
- The system map's line numbers moved by five after its line 57. The cite `system-map.md:78-80`
  ("by DI-89's routes") is at `:83-85` in the edited working copy.

**Files written** (all new, all in this folder):
- `verify.md` (this file).
- `verify/VerifyPrograms.lean` (`0f36c3a9…`), with `verify/RedVerifyPrograms.lean` (`e5600295…`,
  four guards flipped; it fails exactly at them).
- `verify/VerifyTyBill.lean` (`36f9af03…`).
- `verify/ScratchPoolRead.lean` (`e1f8d5d0…`) and `verify/ScratchRetryRead.lean` (`d73a8918…`):
  the locating probes, `#eval` only.
- `verify/RedProgram1.lean` (`832a744f…`) and `verify/RedPrograms345.lean` (`4c5aa32c…`): red
  copies of the seat's probes.
- `verify/rerun-*.log`, `verify/*.log`.

**Commands**, from the repository root through the lock:

```sh
S=/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh
D=docs/research/2026-09-30-model-probe/programs
for f in ProbeRefusals ProbeProgram1 ProbePrograms345 ProbeFormLaws; do
  bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/$f.lean; done        # all exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/verify/RedProgram1.lean     # exit 1, the flipped guard
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/verify/RedPrograms345.lean  # exit 1, the two flipped guards
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/verify/VerifyPrograms.lean     # exit 0
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/verify/RedVerifyPrograms.lean  # exit 1, the four flipped guards
bash $S lake env lean -M6144 -DwarningAsError=true $PWD/$D/verify/VerifyTyBill.lean       # exit 0; prints 63 / 25
bash $S lake env lean -M6144 $PWD/$D/verify/ScratchPoolRead.lean    # exit 0: some false, some true, some true, (false, true)
bash $S lake env lean -M6144 $PWD/$D/verify/ScratchRetryRead.lean   # exit 0: true, some "refused: annotation local const", none
# in $D/ts:
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo -p tsconfig.json       # exit 0
/Users/pooks/Dev/lean4-effect4/ts/eff/node_modules/.bin/tsgo -p tsconfig.red.json   # exit 1, three errors
bun --tsconfig-override=./tsconfig.bun.json run-p{1,2,3,4,5}.ts capture-control.ts capture-cache-control.ts
env -u ADMIN_TOKEN bun --tsconfig-override=./tsconfig.bun.json run-p2-noenv.ts
```

**Axioms.**
- The seat's theorems, rerun: `timeoutForm_scoped` and `retryForm_scoped` give
  `[propext, Quot.sound]`; `leaky_not_scoped` gives `[propext]`.
- My files state no theorem. They are `#guard`s, one `#exhaustive_gate` report, and two `#eval`
  scratch files. No `sorry`, `native_decide`, `axiom`, `partial` or `unsafe`.

**Bounded or host-only evidence.**
- Every check is a finite probe: one scripted host per program, one schedule per rc.112 run, bun
  1.4.2 on this Mac.
- The readability results are about the printer and reader at HEAD (`Api.readable`); no printed
  TypeScript was run.
- The `Ty` count is the instrument's report over `Effect4` and `Effect4.Laws` at HEAD's compiled
  libraries. It counts definitions, not proofs.

**Open obligations.** The proposed rows in §4. The OCaml face of `sub` is unchecked. The retry
form's readability under DI-91's fallback (a) is untested, because that fallback does not exist.
