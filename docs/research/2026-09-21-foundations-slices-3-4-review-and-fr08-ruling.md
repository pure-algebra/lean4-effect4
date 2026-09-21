# Foundations slices 3 and 4: the once-over, and the FR-08 ruling

Codex landed four commits on `codex/foundations-slices-3-4` from base `641a0fea`:
`cd769650` (slice 3 statements), `5d63f91d` (slice 3 proofs and the preflight
counterexamples), `5a9611c4` (the approved independent D12 and C2–C4 subset) and
`ef38bf11` (the M3a residual). This note is the coordinator's once-over of those landings,
the fast-forward of `refactor/phase1-phase3` onto `ef38bf11`, and the ruling on the one
design question they left open: FR-08, the interrupt-delivery contract that blocks slice 5.
The checked evidence is in `2026-09-21-foundations-fr08-evidence/`; the counterexample is
`Test/Counterexamples/Machine/Semantics/InterruptEscape.lean` (`E4-SCHED-CE-008`); the
dispatch that follows is `2026-09-21-codex-brief-foundations-slice-5.md`.

## 0. The once-over

| landing | what it claims | verdict |
| --- | --- | --- |
| slice 3 (`cd769650`, `5d63f91d`) | `WorldValid` with every clause the brief listed (exact support, token bound and targets, `state`, `wf`, the four closedness clauses, `root`); the three freshness corollaries and `ref_completion_live`; `leHost` a preorder projecting to `World.le`; value, completion (C1), heap, promise and exit transport; `initialWorld` with `initial_world_valid`; `park_extension` closed; `M2Validity` 0 open / 15 proved; the negatives (ghost next-index declarations, unbounded tokens, changed spelling under bare `le`, a dangling cell keeping `leHost` and breaking `WF`, a dangling `ofRefGet` excluded by valid coverage, the two coarse false positives retained) and the mixed Nat/Bool allocation through actual `syncOpStep` | as briefed. `Validity.lean` and `TypedWorldValidity.lean` read against the brief clause by clause; nothing weakened, nothing global claimed under `leHost` |
| independent slice 4 (`5a9611c4`) | D12 certificates on `Protocol` with all seven generic laws re-proved under certificate binders and the unit adapter; C2 `indexed_ref_step_preserves`; C3/C4 `projects_compose` and `projects_induces_refines`; the vendor probe distinguishing `getCont`, the failure evaluator and the run loop | as briefed and as approved. The disposition's correction that C2 does not cover allocation (`refMake.refKernel = none`) is right and is carried into the settling case |
| M3a (`ef38bf11`) | `HandlesLive`/`HandlesFit`/`StrongValue`/`StrongCause`/`StrongExit`; D13 `EnvTyped`/`PointTyped`/`BodyTyped`; `ControlAdmitted` with `unguard_payload_inv` and `finishFinalizer_payload_inv`; `Ψ_S` over 31 rows with `StoreCert`; `Ψ_F` over 40 rows with `FiberCert`; concrete `TypedProg`; `#answer_gate`; the two settling cases at ceiling 0; ledger 342 / 333 / 9 | the proved part is as briefed and honest; the receipt says what is thin. Four gaps against the brief, listed below, none of them a false claim |

Gaps in `ef38bf11`, all carried into the slice 5 brief:

1. **`Ψ_F` rows.** Categories 1–3 of the brief's table mostly landed with `pre := True` and
   `post := True` (`raceAll`, `async`, `suspend`, the `interrupt*` family, `runIn`,
   `awaitNewChildren`, `guard_`, `construction`, `closeScope`, `foreignRelease`,
   `closeWalk`, `closeIter`, the race/iterator bookkeeping rows). `await`, `fork`, `mask`,
   `unguard`, `finishFinalizer`, `scopeExit`, `closeScope` and `closeIter` carry real posts.
   `forkIn`, `forkScoped` and `scoped` have `PUnit` certificates with an existential type,
   so their continuations cannot name the child's type; `memoBuild` has a `Ty × Ty`
   certificate its post never reads. The manifest is complete as an inventory, and the
   receipt says so; it is not delivery adequacy.
2. **No M6 adequacy obligations.** The brief asked for a named actual-delivery obligation per
   answered row. None was declared. Slice 5 declares them (`Typed.M6Adequacy`, zero proved).
3. **`frameProtocols` is `True`** in all three fields. `popR_typed` cannot be proved against
   it. Slice 5 fills it under `HookLaws` (§2 R5).
4. **`#answer_gate`** counts constructors (31 and 40) and prints their names. It does not
   inspect the manifest's clauses; Lean's exhaustiveness already guarantees one clause per
   constructor, and the wildcard arms hide which rows are trivial. Slice 5 extends the table
   to say per row whether the post is non-trivial and which obligation covers it.

Codex's preflight refutations (`E4-SCHED-CE-006/007`, `E4-TYPED-CE-003`) are correct and are
retained unchanged. The preflight stopped the dependent stack work as §2 of the brief
required, and the receipts never counted the held part as done.

The fast-forward discarded two uncommitted files in the coordinator's checkout (the older
copies of the brief and `STATE.md`); the branch's versions are strict supersets.

## 1. FR-08: what is actually true

The refuted proposal tried to state, at a frame, when `popR` may skip a catch. Codex's
counterexamples are universal equations on saved states; the amendment said their state
had not been reproduced as a decision tape. It has now, and the answer settles the design.

**The vendor rule.** rc.112 `internal/core.ts:540-545`: evaluating a failure takes the next
failure continuation and then, while `fiber.interruptible && fiber._interruptedCause &&
cont`, discards it and takes the next. `internal/effect.ts:4312-4319`: the frame that
restores interruptibility returns, on the success path only, a continuation that fails
with the recorded cause; on the failure path that continuation is discarded by the same
loop. `interruptUnsafe` (`effect.ts:574-595`) records the cause on a masked fiber and does
nothing else. So: an interrupt recorded while a fiber is masked, followed by a failure
leaving the masked region, restores the mask, skips every interruptible catch above it,
and lets the original failure reach the fiber's exit. The reference machine's `popR`
(`EvaluateR.lean:72-89`) is this rule exactly.

**Reachable, on three machines** (`E4-SCHED-CE-008`):

| program | checker | tape | frame machine | term evaluator | rc.112 (bun) |
| --- | --- | --- | --- | --- | --- |
| `catchAll(uninterruptible(await >> fail 42), _ => succeed 0)` | answer `nat`, error `never` | `[evaluate, answerAsync]` | `success 0` | `success 0` | `Success 0` |
| the same | the same | `[evaluate, interruptFrom root, answerAsync]` | `Fail 42` | `Fail 42` | `Failure Cause([Fail(42)])` |
| `uninterruptible(catchAll(interruptible(catchAll(uninterruptible(await >> fail "boom"), _ => 0)) >> fail 7, e => add e 1))` | answer `nat`, error `never` | `[evaluate, answerAsync]` | `success 8` | `success 8` | not run |
| the same | the same | `[evaluate, interruptFrom root, answerAsync]` | `die badName` | `die badName` | not run |

The third program is the contagion: after the escape, `interruptible`'s restoration
re-masks the walk, the outer `nat`-typed catch is no longer preempted, its handler binds
the string, and `add` on a string is the machine's bad-shape defect. A defect-free,
checker-typed program dies. `escaped_exit_does_not_fit` proves the delivered exit fits no
world at the checked type; `escaped_exit_fits_region` proves it fits the masked region's
own type, so the skipped catch was the only frame that could have removed it.

**Consequences.** No invariant of the form "every reachable delivery fits its declared
error column" holds on the reference machine, and no per-fiber "interrupted" flag repairs
it: the escaped exit is an ordinary `Fail`, a joiner typed at `never` receives it, and the
contagion is unbounded. No frame-level correlation can be right either, which is what
Codex's counterexamples showed from the other side. A tape restriction does not help:
scope closes, race losers and `interruptChildren` interrupt masked fibers without any tape
decision.

## 2. The ruling (R1 and R2 overruled the same day; see §4)


- **R1. Faithful model, no runtime change.** The escape is rc.112's semantics. Slices 3–6
  change no runtime source, evaluator or generated predicate. Whether to report it upstream
  is the owner's call; `2026-09-21-foundations-fr08-evidence/VendorEscapeProbe.ts` is a
  minimal reproduction against the pinned source.
- **R2. Escape-free runs.** The typed-state theorem is stated for runs whose stack walks
  are `skipsClean`: a Bool computed by `popR`'s own recursion over the data `popR` already
  reads, true unless a resume arm is skipped under preemption while the exit carries a
  `Fail` reason. It is interpreter-free because every arm that consults the interpreter
  ends the walk. `NoEscape root fuel cfuel tape` is the run-level form: at every prefix of
  the replay, every fiber's next delivery (`.pure`, `.unguard`, `.finishFinalizer`: the
  three `deliverR` call sites in `EvaluateR.lean`) is clean. This is a trace observation and
  a premise, not a runtime tag and not a clause of the invariant. `E4-SCHED-CE-008` is why
  it is necessary.
- **R3. Guard-miss-only skipping.** `FrameAccepts.resume.skip` drops the all-failures
  disjunct and both `resume` and `answer` read strong exits and typed programs. The old
  disjunct rejected every error-removing catch; it was standing in for preemption, which
  R2 now carries where it belongs.
- **R4. Provenance stays.** The causes `popR` and `deliverR` inject on success paths are the
  recorded interrupt, all-interrupt by `InterruptProvenance`, and an interrupt-only failure
  fits every effect type (`strongExit_of_clean`).
- **R5. Hooks under `HookLaws`.** `frameProtocols` is filled with the real arrows for the
  async finalizer, iterator and loop slots; `popR_typed` is generic in the interpreter under
  a `HookLaws` record; the concrete `interpR` instance is a named open M5 obligation.

**Checked before ruling** (`SkipsCleanProbe.lean`, `skips-clean.log`): `cleanExit`,
`skipsClean` and `strongExit_of_clean` at `[propext, Quot.sound]`; the amended frame and
stack contracts elaborate; the slice 5 `popR_typed` statement elaborates; on the
`E4-SCHED-CE-006` state the amended contract accepts the stack (`masked_stack_accepted`,
the Nat-removing catch typed through `recovery_typed` and the guard-miss `catch_skip`), the
walk is not clean (`masked_walk_not_clean`, by `rfl`), and the same walk with an
interrupt-only failure is clean and fits the output type. That is the shape of the ruling:
the contract admits ordinary catches; the run premise excludes the escape.

**What this does not settle.** `popR_typed` is a statement here, not a proof; the hook
laws, delivery, capture lookup and the `Keeps` ladder are slice 5's. The M7 corollaries
(no bad shape, no halting) are stated under `NoEscape`; the third program above is the
checked reason the first of them needs it. Whether the escape-free scope is acceptable as
the milestone's statement is the owner's decision (recorded in `STATE.md`); the coordinator's
recommendation is yes, because it is the only true statement about this machine, and the
premise is observable on every run.

## 3. Verification

- `lake build` of the landed modules after the fast-forward: exit 0 (380 jobs).
- `lake build Test.Counterexamples.Machine.Semantics.InterruptEscape`: exit 0, both theorems at
  `[propext, Quot.sound]`, every `#guard` green (`interrupt-escape.log`).
- `bun docs/research/2026-09-21-foundations-fr08-evidence/VendorEscapeProbe.ts`: exit 0,
  `vendor-escape.json`; the six vendor files pinned in `vendor-sha256.json`.
- `lake env lean -DwarningAsError=true …/SkipsCleanProbe.lean`: `skips-clean.log`.
- `make check` (build with its axiom audit, 705 jobs; fresh root elaboration; generated-file
  drift): exit 0, log `make-check.log.gz`.
- The fresh unique ledger audit (`final-audit.log`, the slice 4 driver rerun at this head):
  **342 total; 333 proved; 9 open**, the nine historical names unchanged. This landing adds
  no obligation and closes none; it adds one registered counterexample and one ruling.

## 4. Amendment (2026-09-21, owner): the machine diverges from rc.112 and strips

The owner overruled R1 and R2: the reference machine does not adopt the vendor's escape.
It is a **noted divergence**, the first row of `docs/UPSTREAM-BACKLOG.md` (`U-01`), and the
typed-state theorem is stated unconditionally. R3, R4 and R5 stand.

**The rule.** At a preempted skip of a resume arm that would otherwise have run (a failure,
the frame interruptible, a cause recorded), the walk passes on the sanitized failure
`Cause.combine (stripFail cause) ic` in place of `ex`: the original failure without its
`Fail` reasons, combined with the recorded interrupt `ic`. Defects and interrupts of the
original failure are retained; only what the skipped handler was typed to remove is removed.
This is Effect 3's rule (`stripFailures` at the skipped handler, the interrupt appended at
the mask restore, `fiberRuntime.js:974-1000`), applied at the one site that matters. Nothing
else in either walk changes: the success-path injections, guard misses, `onExit false`,
answer glue, hooks and the deferred interception are as they were.

**Checked** (`DivergenceProbe.lean`, `divergence.log`, `[propext, Quot.sound]`): a copy of
`popR` with only that branch changed ends the `E4-SCHED-CE-006` walk with the interrupt-only
failure (`diverged`), which fits the catch's output type at every world (`diverged_fits`);
with a defect in the original failure the defect is retained and the `Fail` is not
(`diverged_keeps_defect`); the sanitized cause is `Fail`-free for every input
(`sanitize_clean`, through the cause module's `mem_combine`). The proposal that prompted the
amendment replaced the cause by the recorded interrupt outright; that drops defects
(`proposal_drops_defect`) and is not adopted. Its claim that `skipsClean` becomes true by
definition is also wrong for the predicate as defined; the correct consequence is that the
premise is unnecessary and is deleted.

**Consequences.** The walk lives in two machines and both escaped: `popR` in the term
evaluator and `popFrom`/`passPushed` in the compiled frame machine
(`Machine/Frames.lean:1482, 1533`). Both change identically; the frame machine is what LCNF
compiles to OCaml, so the generated faces regenerate. `skipsClean`, `DeliveryClean` and
`NoEscape` are never landed; `cleanExit` and `strongExit_of_clean` remain as the lemma the
sanitized branch uses. The coverage row `checkpoint.exit-failcause-skip` becomes a signed
divergence. `E4-SCHED-CE-008` becomes the divergence's positive witness. The truth harness
gains the escape program as a fixture with a signed host exception, because printed programs
on rc.112 still deliver `Fail 42`; that is the cost, and the reason `U-01` should be reported.
The divergence is dispatched first, as its own slice
(`2026-09-21-codex-brief-foundations-divergence-slice.md`); slice 5 then proves `popR_typed`
unconditionally (`2026-09-21-codex-brief-foundations-slice-5.md`, retargeted).
