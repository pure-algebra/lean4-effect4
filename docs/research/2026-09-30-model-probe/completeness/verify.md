**The one thing:** The seat's diagnosis holds (R1–R9 ask only that a full program stays typed and safe, and "lawful Σ" and "Σ ⊆ Σ'" are undefined), but three of its proposals are wrong as written: `noReason_deadlocked` is false (proved: a root parked on its own yield, with its dispatcher armed, has no frontier reason, and `Tape.Complete` holds); `finished_released` is false (tested: a release registered in a `Scope.make` scope that is never closed does not run, though the run finishes); and `build_total` was proved in the tree and cut for having no consumer, not "proved in the workshop spike only". Both the seat and the reviewed note also miss that the typed-state invariant's `ServicesOk` reads `nativeServiceTy` directly, so putting services in Σ is not a change to statements only.

# Verification of the completeness seat

Verifier of seat COMPLETENESS, 2026-09-30 model probe. Under review: the seat's note
`docs/research/2026-09-30-model-probe/completeness/note.md` and its findings C-01 to C-17,
against the reviewed note `docs/research/2026-09-30-full-program-model-requirements.md`. Read
at HEAD `7cae243a` (`refactor/phase1-phase3`, clean). Research only: nothing tracked was
edited; no build, no `make`, no generator. The seat's files were not edited. Every Lean file
was compiled through the one-compiler lock (§3).

**Method.**
- I re-read every source each finding cites. The seat's four probes were rerun unchanged, and
  each recount was redone with my own patterns.
- For each "missing" item I searched the reviewed note and the tracked authorities for a
  requirement that already covers it.
- Where a finding rests on a probe, I wrote a probe that could falsify it. Each probe has a
  red control.

**Words.** *proved*: a kernel theorem I ran. *tested*: a finite check I ran. *reading*: read in
code or notes, not run. *assumed*: taken without either.

**The probes read current code.** They load `.lake/build` oleans, so I compared timestamps.
- No source a probe imports is newer than its olean in any way that matters. `Machine/Stores.lean`
  was edited at Sep 24 01:02:42 and its olean built at 01:02:53. `Program/Checker.lean`'s olean
  was rebuilt at Sep 30 19:48, after a one-line citation edit (`a7b01358`).
- Two Laws oleans (`StoresLaws`, `LayerSharing`) are older than their sources. No probe imports
  them.

## 1. Verdicts

| id | verdict | reason |
| --- | --- | --- |
| C-01 | partly | **Confirmed: the gap.** The reviewed note contains no stream, transaction, clock, random, collection, observability, equality, finalization, deadlock or fairness term (tested by grep). Its §5 item 5 is an order item, not a requirement. 13 workstreams and 13 families summing to 137 modules (post-Phase C §11.2–11.3, reading). **Two corrections.** (1) The duty is already ruled: DI-89 asks "one behaviour law" per form, and row 79's R79.1–R79.5 are "Ruled 2026-09-20 (owner), written 2026-09-21". R79.5 fixes the default fidelity: "values relative to the decision tape; a schedule deviation is a named refusal row" (`docs/research/2026-09-20-open-design-issues-order-and-observation-packet.md:201`). So the level each module owes is not an open owner decision, except for exceptions. The seat cites catalogue §5 Q1, which predates the ruling. (2) The named proof route `Projects`/`Refines` relates one concrete step to one model step (`Laws/Machine/Refinement.lean:20-37`). A module's expansion takes many steps per contract step, and machine state §7 says stuttering simulation is "not provided automatically". The ruled shape is `Agrees profile module expansion`, with `Factors` to `Obs` (packet §2.5; R79.1, R79.5). **Minor.** R8's journal bullet names a W3 item ("commands/journal", §11.2), so "W3 has no requirement at all" is literally contestable. That bullet is itself over-claimed (C-09). |
| C-02 | confirmed | No `LawfulSig`, `Signature.Lawful` or `SigOk` (tested by grep). My wider grep of every `Lawful*` declaration under `src` finds `LawfulSpelling`, the reader-side structure over a `Signature` that the seat names, and nothing else over a signature. The checks are as cited (reading): `Api.lean:372-395`; `AdmittedProgram`'s Prop fields (`Program/Admission.lean:89-95`, whose `lawful` field is `Table.lawful`, the program-plane half of `LawfulTable`). Author receipt C3: the shipped-row guard "is not written". Rows 42–43 plan §2d: `templateAdmissible`, `Row.wellScoped`. Pass synthesis K10. The seat missed an existing located table refusal with an unproved fallback (§2, item 8). |
| C-03 | confirmed | **The probes reproduce:** `Extension.lean` exits 0, and `ExtensionRed.lean` exits 1 with one guard error, at line 72. **No transport lemma** for the row table (tested by grep with wider patterns). The tree's transport lemmas are for the world order (`Typed/Validity.lean:124-151`) and for environment weakening (`hasTy_weaken`, `Typing/Sound.lean:156`). The typed `World` holds no row table (`Typed/World.lean:52-57`). **Sharper than the seat (tested, `VerifyRun.lean` §3):** an inserted row of the same type silently changes the call: same type, lawful table, but `Host.pong()` now prints as `Host.ping()`. Appending an unregistrable row keeps the type and revokes admission. **Pedigree:** DI-47's `⊑` is defined on the world description, the language's alphabets and wire. "DI-47 applied to Σ" is the seat's extension of it, together with DI-22 and DI-64, which are the row-table rulings. **Line:** `Api.Typed` is at `Api.lean:444-446`. |
| C-04 | confirmed | All cited (reading): the fixed `World` record (`Typed/World.lean:52-57`); six `HandleKind`s, "appended, never renumbered" (`Machine/Value.lean:56-67`); `Stores` with seven fields (its structure; machine state line 39); the Latch (catalogue §3 item 6); DI-89; host boundary line 135; rows 68 and 75. **One correction.** The logical clock is already a tape decision (DB-14, `RunDecision.advance`). What is open is the custom clock and Random (row 83). **One caveat.** INV-TAPE-1 appears in no tracked file (tested by grep), so it is a recommendation from the literature note, not a rule. |
| C-05 | partly | **Confirmed: the gap.** No whole-run release theorem (grep; DESIGN-BASIS line 734, "partly discharged"). **Three corrections.** (1) "Only finite witnesses exist" understates the tree (reading). `ScopeMachine.lean` proves universal theorems for one close: `runState_complete` (:191), `runState_restore` (:217), `runState_result` (:233). `syncOpStep_scopeAdd_closed` (`StoresLaws.lean:647`) runs a finalizer added to a closed scope at once. `finalizerRuns` counts a fiber's diagnostic trace rows, not a release's, and that trace is erasable by R79.3. (2) The seat's probe cannot show "once": its release writes `1`, which reads the same after two runs. A counting release shows exactly once (tested, `VerifyRun.lean` §1). (3) **A4's `finished_released` is false as stated.** A release registered in a `Scope.make` scope the program never closes does not run, and the run finishes (tested, `unclosed`). This is rc.112's behaviour too. A4 also takes one of the six judgments of its edge (§2, item 2). |
| C-06 | partly | **Confirmed: the claim.** The probes reproduce: `Outcomes.lean` exits 0, and `OutcomesRed.lean` exits 1 at lines 51 and 91. There is no deadlock reason (`Api/Frontier.lean:22-27`); `observe` answers `parked` (`HostProtocol.lean:93-97`); there is no `Deadlocked` or `Eventually` (grep); `FairTape` is at `Scheduling.lean:432`. **The recommended `noReason_deadlocked` is false (proved, `VerifyKernel.lean`).** A root parked on its own `yieldNow` under the tape `[evaluate]` has `reasons = []`, and one `flush` finishes it. `Api.Tape.Complete` holds for that tape (`Api.lean:298-305`). All three theorems are `[propext, Quot.sound]`. The cause is a proved law: `awaitDecision_iff` (`Laws/Api/Frontier.lean:13`) says `awaitDecision` appears exactly when some fiber is unparked, so armed dispatcher owners never reach the list. The seat flagged this risk and did not test it; it is now settled. |
| C-07 | confirmed | **Confirmed by reading.** No requirement is a face theorem. LCNF route §8 has eight connections and seven rules. Typed lowering is pending (DESIGN-BASIS line 736). Row 14 is open and row 18 "not started". Pinned-surface totality is §11.1's. **Nuance.** Tracked authorities already own these duties: LCNF route §8 under row 101, system map §5, and the proof graph. So A6 copies them into the requirement list; it is not a new design. **Pedigree checked at HEAD.** The dogfood §2 disagreement the seat cites still holds on the Lean side (tested, `VerifyRun.lean` §4: `false`, where pinned rc.112 answered `true` in that note's evidence). No register row names it. |
| C-08 | confirmed | All cited (reading): `Signature`'s fields (`Typing/Rules.lean:49-69`); "No `Row.params`" (rows 42–43 plan §2b); structural records, with `Ty.foreign` as the nominal form (type algebra §1.3); `eval` stays a match (row 64); `sound_of_poly` (row 74). **One correction.** R6 already names the table-aware reference relation (DI-57's `session_eq_ref`, whose empty-table corollary is `run_eq_ref`). What R1 lacks over Σ is `run_eq_meaning` (`Agreement/Machine.lean:1922`) and `loopAgreement` (`Agreement/Loop.lean:839`). Both are stated at the empty table. |
| C-09 | confirmed | `journal_replays` is about `Run` (`Laws/Run.lean:184`). Row 98 is "open, recommended (API migration)". Host boundary line 69 says what is quoted. **Nuance.** R8's sentence is half right: the `Run` journal's action is proved; only the attribution to row 98 is wrong. R8's numbers item points at row 108, whose text is a theorem shape (equal inside the profile, refused outside). |
| C-10 | confirmed | R7 reads as a choice of representation (reading). Machine state line 139: "a digest alone does not". Row 82 is open. Literature note Q12. |
| C-11 | confirmed | All cited (reading): host boundary lines 179-180, "The converse is owed"; `runFork`/`runCallback` (`Fibers.lean:2183-2201`); `Api.load` makes one root (`Api.lean:255-260`); `Session` is indexed by one program (`HostSession.lean:84`); pass synthesis §7, "Several roots"; `HostSpec` and `LawfulHostSpec` (`Profile.lean:178`, `:198`). No `denoteRows` exists (grep). Literature note Q11. |
| C-12 | partly | **Confirmed: the omissions** (reading): 33 atoms, with no map atoms and no list removal (`Machine/Term.lean:146-164`); 20 `Ty` constructors, with no record or `fiberId` (`Program/Ty.lean:38-74`); DI-67, DI-35, DI-78; machine state line 160. **The "named records" point is weak.** "Named" follows the title of decisions row 2 ("Names for records and sums"), and §1.3's records carry named fields; nothing nominal is implied. **The real gap the seat missed.** Row 2 is open. It recommends annotation-carried names now, (c), and `Ty.record`/`Ty.variant`, (b), only before the first foreign consumer. R3 presents (b)'s spine as "the design is ready". |
| C-13 | confirmed | All cited (reading): provision note lines 107, 137, 152, 218, 244, 330, 335; papers review G5; Config D1–D5, "open proposal" (design-issue map lines 121-125); side audit line 58. **One correction from C-14:** `build_total` is to be restored, not landed. |
| C-14 | partly | **Confirmed: the header is stale.** `Program/Provision.lean:36-40` claims `build_total` is "proved once over the algebra", and no declaration exists under `src`, `Test`, `tools` or `workshop` (tested by grep). **Refuted: "the reviewed note's 'proved in the workshop spike only' is the accurate statement".** `build_total` and `buildAll_total` were proved in the tree at `f182d2b3` (2026-09-04, `src/Effect4/Program/Provision.lean:429`). They were cut at `b08f3b58` (2026-09-18) as "no consumer, 175 lines", a cut the traversal census records (`docs/core/traversal-census.md:433-436`). There is no `workshop/Provision/` at HEAD. |
| C-15 | confirmed | Reading of the note's R1, R2, R5, R9 and §4. Row 52 rules two corollaries: "never halts" and "never reaches a wrong-shape exit". R9 carries row 107's exit clause and the shape clause, and omits "never halts". |
| C-16 | partly | **Corrected.** The fidelity level per composed module has a ruled default (R79.5, C-01); only exceptions need rows. **Confirmed by reading:** several roots (pass synthesis §7, an open question); nominal or recursive types (R3: "open, no owner"); sharing (dogfood 6 F21; end state §8; none of the 25 `Eff` constructors is a procedure); a program logic (DESIGN-BASIS line 733; DI-10 deferred); durable journals (host boundary lines 105-106). **Add three:** how A4 treats scopes a program leaves open; whether the frontier alphabet names armed work; restoring `build_total`. |
| C-17 | confirmed | **Recounted (tested):** 188 explicit `(sig : Signature` binders, 173 at `Op` and 15 at `NativeOp`, plus 31 implicit, total 219. 89 `nativeSignature` occurrences on 89 lines in 15 Laws files. Typed-state uses 1 + 2 + 3 + 4 = 10. `Admission.lean:90, 108, 191`; `LoopSound.lean:298, 307`; the Ref rows at `number`. R1's seventh-carrier claim, which the seat did not check: `Api.typeOf` and `admitProgram` refuse it, and `nativeSignatureWith` types it (tested, `VerifyExplore.lean`). **But** the ten-place count misses an eleventh pin (§2, item 3). |

## 2. What the seat missed

1. **The frontier alphabet cannot see armed dispatcher work, so the empty reason list is not a
   deadlock.** Proved (`VerifyKernel.lean`) and tested (`VerifyRun.lean` §2).
   - `awaitDecision_iff` (`Laws/Api/Frontier.lean:13`) ties `awaitDecision` to unparked fibers.
     `frontierReasons` (`Api/Frontier.lean:47`) never reads `m.armed`.
   - So a root waiting on its own yield shows the same signature as a deadlock: frontier, no
     reason, host state `parked`. `Api.Tape.Complete` accepts the tape, although one `flush`
     finishes the run. The predicate excludes host replies and a runnable fiber's decision
     (`Api.lean:295-305`), not armed work, so a tape it calls complete can still owe a
     decision.
   - It also breaks INV-TAPE-2, "a frontier records what it awaits … total on frontiers"
     (literature note Q7).
   - **Fix.** The research's own definitions already exclude armed work: papers review G6
     sketches `Deadlocked` with "dispatcher idle", and core math §9 calls a state deadlocked
     when "no fair tape advances it". So A5 needs `m.armed = []` in `Deadlocked`, and the
     frontier alphabet needs a reason that names armed owners.
   - **Vocabulary to build on.** A5 should start from the existing laws: `observe_of_reasons`
     (`Laws/Api/Frontier.lean:82`) and `Sched.reasons_eq_ref` (`Laws/Program/ReasonsR.lean:223`).
     The seat cites neither.
2. **A4 is the wrong size.** Tested and read.
   - **Too strong.** `finished_released` fails on a scope the program makes and never closes
     (`VerifyRun.lean` §1, `unclosed`). That is the program's own leak, and rc.112 behaves the
     same way.
   - **Too narrow.** The edge it cites requires "state retention on failure, finalizer order
     and exactly-once execution, delimiter laws, interruption behavior, fiber ownership, and
     disposal" (DESIGN-BASIS line 734). DB-07 asks for "finalizer registration and order,
     exactly-once close, interruption masking, fiber ownership, scheduler decisions, and
     managed-runtime disposal" (DESIGN-BASIS lines 288-291).
   - **Shape to propose.** State release over closed scopes and structured regions (`scoped`,
     a layer's scope, a race), in close order. Include ownership of forked fibers. Treat a
     scope a finished run leaves open as an observation, not a violation.
3. **The service-table pin inside the typed-state invariant.** Reading.
   - `ServicesOk` (`Laws/Program/Typed/Admission.lean:32-34`) is stated against
     `nativeServiceTy` itself. It feeds `HandlesFit`'s context arm (:57), the assembly
     predicates (`Typed/Assembly.lean:47`, `:56`, row 51's `ServiceOk`) and the residual
     `setContext` arm (`Typed/Residual.lean:120`).
   - Neither the reviewed note's "ten places" (its §4) nor the seat's C-17 counts it: a grep
     for `nativeSignature` cannot see it. The note's plan (§5 item 1) names `ProgramSource`
     and `PointTyped` and omits it.
   - Its docstring says "a service value's own nested handles are not re-checked here". With
     a handle-typed carrier in Σ, that becomes a `HandlesFit` obligation or a named refusal.
     Contexts also need validation at the runtime bridge (side audit line 58).
   - So the threading is not a change to statements only, as the note's §5 item 1 claims.
4. **`build_total` is a cut to restore, not a gap to fill.** Tested by `git show`.
   - It was proved in the tree at `f182d2b3:src/Effect4/Program/Provision.lean:429`, with
     `buildAll_total`.
   - It was cut at `b08f3b58` with no reason in the commit message. The traversal census
     records the reason: "no consumer, 175 lines" (`docs/core/traversal-census.md:435`).
   - Restoring it gives R5 its consumer. This is the forgetting the owner asked the probe to
     catch.
5. **The composed-module rulings already exist.** Reading.
   - R79.1–R79.5 (row 79) already rule the shape of the module requirement: "Profiles are data
     in one place; a composed module's law names its profile; the default fidelity is values
     relative to the decision tape".
   - A3 should cite and instantiate that ruling, not reopen it.
   - A3's proof route must be a stuttering relation, not `Projects`/`Refines` (C-01).
6. **Insertion is silent, and admission is not monotone.** Tested (`VerifyRun.lean` §3).
   - **Same bytes, different call.** `Api.bytesOf` takes no table (`Api.lean:175`), so the
     same bytes under a reordered table call a different row and still check. The cure is the
     recorded default of DI-01, which is still open: bytes published together with their link
     table (DI-05, DI-22). An order on Σ alone is not enough.
   - **Admission can be lost.** Appending a lawfully named, unregistrable row revokes
     admission of every program at that table. That is DI-47's separate "execution
     permission" comparison. A2's lemma list (`typeOf_mono`, `replay_mono`, `read_mono`)
     omits it, and covers it only if Σ' must itself satisfy A1.
7. **R2's appeal to the algebra has no row object yet.** Reading and grep.
   - "Rows: additive by construction … `interpret_pinned` and `Protocol.sum` are per
     operation" needs rows to be an `Effects.Signature`.
   - At HEAD the denotation's signature is `StoreSig`, store operations only
     (`Laws/Program/Denote.lean:41`). DI-69's `RowFamily`/`RowSig` and `denoteRows` do not
     exist.
   - The seat cites DI-69 only under R6.
8. **Lawful tables already have a located refusal, with an unproved fallback.** Reading.
   - `Table.checkLawful` and `LawfulRefusal` (`Program/Table.lean:76-97`) give the refusal by
     key. A1's `admitSig` should extend them.
   - `admitProgram` has a fallback arm, `| none => .error (.duplicateKey ("", []))`
     (`Program/Admission.lean:123`). It invents a key when `Table.lawful` is false but
     `checkLawful` finds nothing. No theorem ties the two checks (grep: no `checkLawful`
     theorem). A1's "located and complete" `admitSig_ok_iff` has to close this first.
9. **Divergence has no requirement.** Reading.
   - DESIGN-BASIS line 732 marks "divergence adequacy: pending". DB-03: divergence "is
     witnessed by an infinite run or by compatible finite prefixes, not by running out of
     fuel".
   - The seat marks it uncovered and proposes nothing. Programs that run until stopped
     (servers, event loops) are full programs in the owner's sense. For them, a frontier at
     every budget must be told apart from divergence.
10. **Two authorities were not enumerated.** Tested by grep.
    - `Test/Counterexamples/REGISTER.md` has 153 live rows: 135 `SEEDED`, 6 `PINNED`, 10
      `REPAIRED`, 1 `RETIRED`. A `SEEDED` row's forced repair is still owed.
    - `Test/contracts/` has 32 frozen packets. One, for example, files the table-aware
      `RunEqRefTableStatement` (DI-57).
    - AGENTS.md lists both as authorities. The seat's method enumerates neither.
11. **INV-TAPE-1 and INV-TAPE-2 are not rules yet.** Tested by grep: they appear in no tracked
    file. A2's decision-source clause and A5 cite them as if they were rules; they need a
    decisions row first ("a ruling is not made until it is written into a tracked file",
    DESIGN-ISSUES header).
12. **Smaller points.** Reading.
    - Row 2 is open, with a staged recommendation (C-12).
    - R8 touches W3 (C-01).
    - R6 already carries `run_eq_ref`'s generalization (C-08).
    - The clock is already a tape decision (C-04).
13. **Incidental, out of scope.** Tested.
    - `syntax (name := daemonFork_) "daemon " term …`
      (`Program/Authoring/Services.lean:151`) makes `daemon` a keyword in every module that
      imports `Effect4.Api.Author`.
    - After that import, `{ startImmediately := …, daemon := …, maskMode := … }` for
      `ForkOptions` no longer parses: `VerifyDaemonToken.lean` exits 1 at 10:30, and its
      control exits 0.

## 3. Probes

Every file below is in this folder, compiled from the repository root, each through the lock
(`F` is the file):

```sh
bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh \
  lake env lean -M6144 -DwarningAsError=true /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-30-model-probe/completeness/F
```

| file | exit | what it shows |
| --- | --- | --- |
| `Outcomes.lean` (seat's, rerun) | 0 | as the seat states |
| `OutcomesRed.lean` (seat's, rerun) | 1 | exactly two guard errors, at lines 51 and 91 |
| `Extension.lean` (seat's, rerun) | 0 | as the seat states |
| `ExtensionRed.lean` (seat's, rerun) | 1 | exactly one guard error, at line 72 |
| `VerifyKernel.lean` | 0 | **proved**: `yielding_reasons` (no frontier reason after `[evaluate]`), `yielding_tape_complete` (`Api.Tape.Complete` holds), `yielding_flush_finishes` (one `flush` finishes the run); each by `decide +kernel`, each `[propext, Quot.sound]` |
| `VerifyKernelRed.lean` | 1 | `yielding_reasons` flipped to `≠ []`: `decide` proves the flip false (line 18). Its dependent fails (line 22), with five unused-`simp`-argument linter errors that follow from that failure |
| `VerifyRun.lean` | 0 | **tested.** §1: a counting release runs once and only once; two setter releases read as one; `unclosed` (finished run, release never run, one scope left). §2: the yielded root (no reason, `parked`, armed, finished by `flush`) beside a true deadlock (no reason, nothing armed). §3: silent re-pointing by insertion; admission revoked by appending an unregistrable row. §4: the dogfood §2 program answers `false` at HEAD |
| `VerifyRunRed.lean` | 1 | exactly six guard errors, at lines 110, 129, 153, 184, 195, 214, the six guards marked `[red]` |
| `VerifyDaemonToken.lean` | 1 | one parse error at 10:30, "unexpected token 'daemon'; expected '}'" (the incidental item) |
| `VerifyDaemonTokenControl.lean` | 0 | the same file importing `Effect4.Api` instead |
| `VerifyExplore.lean` | 0 | exploration, printed values only (`#eval`), with no red control. Two small claims rest on its output: R1's seventh carrier (C-17: `false`, `true`, `false`), and forked work behind a parked root being reported (`awaitDecision`, because the child is unparked). Everything else it printed is guarded in `VerifyRun.lean` |

What the probes do not show: anything about all programs. `VerifyKernel.lean` proves facts
about one program and one tape. That is enough to refute the universal statement
`noReason_deadlocked`, and to show that `Tape.Complete` can hold while a decision is still
owed. It shows nothing more.

## 4. Receipt

- **Base and head.** `7cae243a` (`refactor/phase1-phase3`). No commit, no checkout, no
  `git add`. `git status --short` prints nothing (`docs/research` is gitignored). The Codex
  worktree was not read.
- **Files written** (this folder): `verify.md`, `VerifyKernel.lean`, `VerifyKernelRed.lean`,
  `VerifyRun.lean`, `VerifyRunRed.lean`, `VerifyDaemonToken.lean`,
  `VerifyDaemonTokenControl.lean`, `VerifyExplore.lean`. The seat's four probe files are
  unchanged (their digests match the seat's receipt), and its `note.md` was not edited.
- **Commands.**
  - The compiles of §3, through the lock.
  - Reads and greps (`grep`, `sed`, `awk`, `shasum`), plus `git show` and `git log -S` for
    `build_total`'s history.
  - No `lake build`, no `make`, no generator.
- **Digests (sha256).**
  - `41c30bbe922eb009c8db51a64b0999bbb2e1becbe57ad519570a4100876734ee  VerifyKernel.lean`
  - `cd097f91257725725198f5c507859f89d06f2ea88cb74acd3f050104b4bb2fb0  VerifyKernelRed.lean`
  - `b1684687b0e87dd62aa9e1e5e47e8521965d70ec9939f9148e2915e93a55711a  VerifyRun.lean`
  - `67d248319f214f2d549c1f100275228ba78d367ea4b3ab61bd7959298f1f0fc3  VerifyRunRed.lean`
  - `9eb1cd08c3c18c8bc2d48ef3184f6518b50833cc0d3a4a68e902c8290d441116  VerifyExplore.lean`
  - `d4f09d7aa3ae76858e35dd8b1fa84193650135dc604089ef93bf1b33857ca836  VerifyDaemonToken.lean`
  - `0f1cd54da9452f80e57861ee0c2238360c990cda553fadcc03924fbbcffdf77b  VerifyDaemonTokenControl.lean`
  - The seat's four: unchanged (`55d1fabe…`, `21cb85ef…`, `d3cd1bb3…`, `29e3f7e1…`).
- **Axioms.** `yielding_reasons`, `yielding_tape_complete` and `yielding_flush_finishes`:
  `[propext, Quot.sound]`. No other theorem was stated.
- **Evidence classes.**
  - Verdicts on cited text are *reading*. Every grep is *tested*, bounded by its patterns.
  - The run checks are *tested*, on one program each. The three kernel facts are *proved*,
    for one program and one tape.
  - rc.112's side of the dogfood §2 disagreement (`true`) is *reading*, from that note's
    evidence folder.
  - rc.112's side of the unclosed scope is *reading* of the vendored source. Finalizers run
    only in `scopeCloseUnsafe`, which returns at once on a closed scope
    (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts:3779-3797`). `scopeMake` links no
    parent (`:3915-3926`). The only closers are an explicit `close`, a parent's close for a
    forked scope (`:3841`), and `scoped`/`scopedWith` (`:3958`, `:3967`).
  - No host run was made here.
- **Open.**
  - Whether the frontier alphabet should gain a reason for armed owners, or `awaitDecision`
    should cover them. This is an API and protocol change, and so the owner's.
  - Whether A4 treats a scope left open by the program as a leak to observe or a refusal.
  - Whether `ServicesOk` re-checks nested handles in service values, or refuses
    handle-typed carriers by name.
  - The register's 135 `SEEDED` rows and the 32 contract packets are not mapped to R1–R9 here;
    that mapping is owed by whoever restates the requirements.
