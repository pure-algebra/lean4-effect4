# Model-probe plan audit

**The one thing first.** Keep the proposed three-argument exit judgment, but do not approve the
whole H2 plan as a local eight-body repair. Part two has a checked saved-frame counterexample:
the current loop contract accepts a frame that transports `missingService` from a nonempty
requirement row to an empty one. The cited context condition supplies no missing presence
premise. D1–D4 and D6 remain reasonable choices with the amendments below; D5 needs a contract
over the fully assembled table, not a reversal of `Package.install`'s append operands. The
22–26 declaration estimate is stale after E. R11 and R12 also need corrected theorem shapes.

Reviewed base and head: `f437b066e5d716713d5603e18d9ccf8f78f93077`, branch
`codex/slice6-fixes`, worktree `/Users/pooks/Dev/lean4-effect4-slice6`. The checkout was clean.
The audit writes only this directory. No source, test, register, generated file, build, make,
generator, or push was part of the review. The independent readers were `h2_review`, `rulings`,
and `coverage_basis`; the coordinating seat compiled all probes sequentially.

Evidence words: **proved** means the named Lean theorem was accepted with printed dependencies
within `[propext, Quot.sound]`; **tested** means a finite guard, command, or text count;
**reading** means an inspection of the named source; **assumed** means not established here.
An unproved proposed statement remains owed. In particular, no finite run below establishes a
whole-run theorem, and the saved-frame witness is not claimed reachable from checked source.
Short source paths below are under `src/Effect4/`; `synthesis` means
`../2026-09-30-model-probe/synthesis.md`. All source line references are at the reviewed head.

## 1. H2 and the eight measured bodies

**Reading: the proposed interface survives.** With a static service interpretation in `World`,
`ExitOk w ty ex := FitsExit w ty ex ∧ NoShapeDefect ty ex` needs no new signature argument.
`Fits` reaches service interpretation only through the context branch and `ServicesFit`
(`Laws/Program/Typed/Membership.lean:73–104`). The defect exclusion reads the core defect
alphabet and `ty.requires`. None of R1–R13 forces another argument. This is an interface
assessment, not a proof of the strengthened stack walk or of all future extensions.

**Proved: part two needs a stronger saved-frame contract.**
`probes/SavedFrameTransport.lean` retains the old helper diagnostic and adds a current-tree
saved-stack witness. `AuditH2.loop_admitted` accepts one loop frame from
`⟨never, never, single nativeScopeKey⟩` to `EffTy.pure unit`. The current `LoopProtocol.step`
requires equal error columns and a successful-value continuation; that continuation is
vacuous at answer `never` (`Residual.lean:286–291`). The incoming failure satisfies `ExitOk`;
`output_eq` proves that `popR` returns that same failure; `output_bad` proves it is excluded
at the outer type. `provenance` supplies the existing interrupt-provenance premise. These
five theorems pass at the ceiling (`logs/saved-frame.log`). No reached-run premise was used.

**Reading: the proposed presence argument does not supply the missing premise.**
`preds.ServiceOk` is exactly `ServicesFit w ctx.services` (`Assembly.lean:56`). It says that
present services fit their static carriers; it does not require any service to be present.
This matches decisions row 51, and contradicts synthesis R5's stronger description at
lines 316–319. `satisfies_iff_subset_keysRow` (`Program/Provision.lean:169`) converts a
presence claim into a subset claim; it cannot manufacture either from value typing.
The witness above also has no context among the stack-walk premises.

**Reading: the repair must cover more than loops.** Iterator hooks have the same
error-column-only transport. The preempted-catch helper (`Stack.lean:163–165`) produces a
sanitized cause at an arbitrary destination type; sanitization retains a `die missingService`.
Requirement-discharging operations also need a positive admission control: the checker drops
the scope requirement at `.scoped` (`Checker.lean:198–200`), while its residual certificate
types the body and its post types the exit at that certificate (`Residual.lean:135,158–159`),
which the generated continuation passes through (`DenoteR.lean:657–659`). A mechanical
replacement by requirement-sensitive `ExitOk` does not by itself discharge that obligation.
These additional observations are readings, not additional reached counterexamples.

**Tested: eight remains the original lower bound.** The original `H2/Baseline.lean` reruns
with exit 0; `H2/PartOne.lean` reruns with exit 1 in the same eight theorem bodies. The retained
mapper report is `logs/h2-error-map.json`. The bodies are Admission's `strongExit_success`,
`strongExit_of_clean`, `cleanExit_of_never`; Residual's `strongExit_bool`, `settling_fork`,
`strongExit_mono`; Stack's `strongExit_failure_of_error`, `popR_typed`. Two error locations
inside `popR_typed` count once. This measures part one's unrepaired harness, not the final
cost. The original receipt explicitly makes that distinction at lines 462–495. Shape A
avoids a service parameter but does not prove that repairing these bodies reveals no further
failures. For example, adding failure-transport fields to the named protocols would also
repair `hookLaws_interpR` (`Stack.lean:300–325`); another placement may cost differently.

**Smallest amendment, H2/row 107 and D2:** retain `ExitOk(w,ty,ex)` and signature-free
`NoShapeDefect`. Authorize part one's eight named repairs, the explicit clean-failure premise,
and local exclusion lemmas, with another measured report if further failures appear. Hold
part two until an explicit frame/operation contract amendment covers the cases above and
admits the scoped/provision positive controls. Do not silently add a reachability premise to
the frozen stack theorem or weaken its conclusion. H2 remains held until the coordinator's
addendum; this audit implements none of these amendments.

## 2. D1–D6: choices, costs, and breakage

| Row | Verdict and smallest amendment | Evidence and what it changes |
| --- | --- | --- |
| D1 | Keep Σ_app as the row and service tables and core growth under DI-47. Say C1–C8 are conservativity **obligations**, with the qualifications in §4. | **Reading:** the machine alphabets are concrete. Parameterizing all of them is a larger change. The concrete extension result is not yet proved. Core and per-face lawfulness must remain distinguished. |
| D2 | Keep a static service interpretation in `World`, fixed by its order and tied to the source in `TypedState`. | **Reading:** this avoids adding a service argument to every value predicate. It also changes `servicesFit_map` and `fits_map` after E, not just `ServicesFit`; §3 records the omitted cost. Equality is needed during a run; cross-signature projection is a separate extension theorem. |
| D3 | Keep carriers per service code; reject conflicting declarations of the same application code, and preserve the reserved-key exception. | **Proved/tested:** `one_code_two_carriers` survives in `VerifyTreeCurrent.lean`. **Reading:** `Machine/Key.lean:337–349` owns code-selected carriers; `Program/Native.lean:271–293` handles the reserved Scope key before free-name codes. Built-in conflict checking alone does not check two new declarations sharing a code. |
| D4 | Keep reserved-name, carrier-conflict, and non-flat-carrier refusal. Include application-code consistency and enforce lawfulness at the typed-source boundary too. | **Reading:** merely replacing `Api/Author.disagreeingService` leaves arbitrary `ProgramSource` admitted to M5/M6. Structured carriers still require their own rule and recursive service-membership work. |
| D5 | Require append of the **fully assembled link table**, and retain the complete table with published programs and sessions. | **Tested:** `PackageAppend.lean` refutes the proposed two-field append repair. The authoring representation needs a separately designed assembly/linking change. The cheapest safe interim is to pin complete artifacts to their original table and make no append claim. |
| D6 | Add the row-domain bit before proving general extension. Describe its demonstrated necessity as an extension issue. | **Proved:** `typedProg_not_table_monotone` survives E in `VerifyTreeCurrent.lean`. **Reading:** the fixed-root M6 parking route does not inspect it; no necessity result for M6 follows from that counterexample. |

**Reading: D4's reserved range is correct.** `firstFreeName = 4`; machine keys use names 0,
1, 2, and 3 (`Machine/ContextMap.lean:660–670,780–790`). The declaration at the memo-map name
3 is covered, not only the built-in Scope service. Reserved-name declaration refusal applies
regardless of the proposed code. Built-in service use without an application declaration
continues to be a separate case. An agreeing explicit Scope declaration passes today's guard
but would be intentionally refused by D4. No production `ServiceDef` fixture using a reserved
name was found. Flat means exactly the admitted scalar and non-context-handle carriers,
not every `Ty` that happens to contain no ordinary data recursion.

**Tested: D5's overlooked insertion.** `Module.rowDefs` is
`m.rows ++ m.services.flatMap (·.ops)` (`Program/Authoring.lean:322–326`). Even when both
`install` fields append, new package rows precede the old module's service operations.
`PackageAppend.lean` checks an old service call at index 0 moving to index 1, and checks
that the new table differs from the old table followed by the package table. This is finite
evidence against that implementation prescription, not a proposed replacement representation.

**Reading/text search: D5's affected fixtures.** The only non-research caller of
`Package.install` is `Test/Program/AuthorContract.lean:118–133`. Its recipient has no own
rows/services, so its assertions stay unchanged under the simple append reversal. No
production corpus or golden caller was found. Tracked research has real affected entries:

- `model-probe/programs/ProbeProgram1.lean:95`, `programs/verify/RedProgram1.lean:95`,
  `VerifyPrograms.lean:81`, and `RedVerifyPrograms.lean:81`: HTTP moves from index 5 to 0;
  KV indices 0–4 move to 1–5. Their elaborated programs and bytes change. The positive
  script uses `b.positionOf` (`ProbeProgram1.lean:130–138`), so behavior should remain;
  this audit did not execute a mutated installer.
- `model-probe/pedigree/VerifyGuards.lean:82,94,99,104`: the second SQL installation changes
  from SQL-before-KV to KV-before-SQL; the three order/retyping guards need new expectations.
  `VerifyGuardsRed.lean:37`'s old intentionally false equality becomes true. Preserve a
  frozen-original witness when moving these controls, rather than erasing their history.

**Reading: D6 and M6.** `StepPreserves` fixes one `root` (`Assembly.lean:99–103`), and
`RReachable` excludes host-answer decisions (`:74–82`). External registration returns
`(state, none)` without reading the row table (`InterpR.lean:330–337`;
`Simulation/Evaluate.lean:412–415`, `registerAsyncR_foreign`). The async arm then parks
(`EvaluateR.lean:213–231`). Thus the domain bit is not required by that parking argument.
No concrete external-async constructor proof to repair was found under `Typed/`; generic
`TypedProg.fiber` takes the precondition as a premise. This is not a claim that all M6 proofs
are now possible: they remain owed. Adopt the bit now to avoid changing the protocol later.

## 3. The Σ_app slice: recount and order

**Reading: keep the slice after G and before dependent M5/M6 proofs.** G adds service-table
reads to layer checking, including the `memoGet` premise. Keep H2's unresolved part-two contract
separate. `MeaningSound`, `LoopSound`, and `TypedRun` need no existing statement rewrite on
their current fragments: the R2 probe's five transport corollaries rerun (**proved**). M7 has
no declaration yet, so its exact cost is open.

**Reading-based recount: 27 existing declaration sites**, under the candidate choice of a
source-carried lawfulness certificate and a generalized initial-world constructor. This is
not a compiled edit count and not 27 changed theorem statements:

| Group | Existing sites | Kinds of change |
| --- | ---: | --- |
| Source route | 9 | `ProgramSource`, `PointTyped`, `CaptureTyped`, `storePre`, `asyncPre`; both ForkSource declarations; M5 `typedState_load` and M6 `typedState_reachable` checking premises |
| World and order | 8 | `World`, `World.le`, `order_refl`, `order_trans`, `park_extension`, `fork_extension`, `refMake_extension`, `promise_extension` |
| Membership | 4 | `ServicesFit` body; two new agreement premises in `servicesFit_map` and `fits_map`; `fits_mono` caller body |
| Initialization | 3 | `initialWorld`, the obligation and proof both named `initial_world_valid` |
| Source/world tie | 1 | `TypedState` definition |
| Existing tests | 2 | `Test/Audit/TypedStateDecl.lean:294`; `Test/Counterexamples/Machine/Semantics/ValueMembership.lean:987` |
| Total candidate inventory | 27 | Before new helpers, admission work, further H2 repairs, or extension lemmas |

`deferredMake_extension` and `memoBuild_extension` already call `promise_extension`
(`World.lean:708,724`), so the original six direct extension-proof edits are four.
Conversely, E added `servicesFit_map` (`Membership.lean:721–723`) and `fits_map` (`:729–732`):
their current allocation/table premises do not constrain a new service interpretation.
A previously untyped key could acquire an incompatible carrier in the destination world.
Add equality or the appropriate reverse lookup-agreement premise; `fits_mono` (`:829–831`)
obtains it from the new order. `FlatFits` and `flatFits_map` do not themselves read that table.
Defaulting the new `initialWorld` argument does not generalize the existing validity theorem;
both its obligation and proof (`Validity.lean:79,162`) must cover the nondefault case, or a
new general helper must be budgeted.

**Reading: lawfulness must reach the ledger.** `ProgramSource` currently contains only program
and table (`Admission.lean:27–29`), while M5/M6's initialization/reachability statements accept
successful checking plus closed columns (`Assembly.lean:154–156,241–243`). An authoring guard
cannot constrain this input. Put admitted signature evidence on the source, or add explicit
lawfulness premises. With source-carried evidence, the 18 command statement spellings and
`decision_preserves` can remain unchanged while their predicates strengthen. With separate
arguments, count the extra ledger changes. None of those currently open obligations becomes a
proved theorem merely by restating its predicate.

**Tested text count: the extension family needs a selected inventory.** `R2Probe.lean` contains
46 declarations: 38 theorems, 2 structures, and 6 definitions. Its C3 core through line 310 is
25 declarations; `pointTyped_rows_append` makes 26. Witness/red-control material adds 10;
fragment restriction and soundness corollaries add the other 10. “About 30” can describe a
selected family but not the whole file plus controls. C3 reflection, concrete C4, service
lawfulness, and G-sensitive adaptations remain additional work. The current probe is
pre-G and its check-layer cases need review after G changes that judgment.

**Smallest amendment, D1/D2/D4 and the next brief:** replace 22–26 mechanical statements with
this named candidate inventory, distinguish definition/body/premise changes, state how lawful
signatures enter `ProgramSource`, and select the extension declarations and red controls.
Keep a fresh compilation measurement as the slice's first check. Item E's recursive `Fits`
stays; only its static-service interpretation and transport assumptions change at this stage.

## 4. C1–C8: status and completeness

**Tested:** all four required original probes were rerun. `Conservativity.lean`,
`VerifyConservativity.lean`, and `R2Probe.lean` pass. `TREE/verify-Probe.lean` fails because E
retired `HandlesFit` and `StrongExit`, and its old conjunction projection no longer fits.
The original failure is retained; it was discovered on the first rerun and is an expected negative only in the replay runner. `probes/VerifyTreeCurrent.lean` replaces only that string
membership helper with production `Fits`/`fits_sub` and removes the obsolete projection;
it passes with all printed theorems at the ceiling. Its non-flat-service subsection remains
the original explicitly copied model, not a newly generalized production judgment.
`TREE/verify-R2Probe-allaxioms.lean` also reruns at the ceiling. Failed elaborations and their
recovery placeholders are never used as proof evidence.

| Condition | Audited status and smallest amendment |
| --- | --- |
| C1 syntax | **Proved** for binary injections. Generic `along_bind` proves bind transport, not injectivity of every morphism. `MorphismCollapse.lean` proves two distinct programs have the same image and the map is not injective. State general injectivity only under a separately proved embedding contract; operation injectivity alone also need not recover unobserved answer branches. D1. |
| C2 meaning | **Proved** generic handler restriction, including `interpret_along`. Host-row operational extension remains owed; the synthesis's one-run check is finite. Name the observation and related host specification/tape. No RowSig result exists before DI-69. D1. |
| C3 checker | **Proved** successful-typing preservation under `SigExtends`, including the six judgments and source-point append. Full checker-result equality/reflection on old programs is owed. A fresh per-key-service probe is not yet the D3 per-code implementation. D1/D3. |
| C4 protocol | **Proved** generic iff for the exact pulled-back old protocol and result predicate, with monotone projection and back condition. **Owed** for concrete `TypedProg`. One-way refinement does not give iff: `RefinementNotIff.lean` proves forward demand/backward promise refinement while typing exists only in the new protocol. Require exact old-operation protocols or a proved two-way relation for iff. D1. |
| C5 world | **Proved** red controls for the listed missing premises, not a completed concrete world-extension construction. Keep order/lookup stability, projection and back condition distinct from one-way protocol transport. D1/D2. |
| C6 lawfulness | **Owed shape.** Include every core R1 clause: table laws, registration, type/template closure and scope, service requirements, integer and internal-handle policy, D3/D4. Freshness includes compatibility with old declarations. Do not substitute the shorter conjunction in synthesis line 205 for full lawfulness. D1/D3/D4. |
| C7 representation | **Owed/conditional.** Pin the complete program table, profile and session; append of installer fields is insufficient (§2). Add target admission and artifact/header/call/reply/journal compatibility to the named face obligation. G alone is not a theorem about all those surfaces. D1/D5. |
| C8 forms | **Owed per form**, over the declared readable domain. The retained annotated-loop refusal remains deliberate under DI-91; any fallback requires its ruling. Link this condition to R10's behavior law; a readable expansion alone proves no behavior claim. D1 and the existing forms decisions. |

**Reading: one lawfulness check must not erase a boundary.** R1 includes reader
`LawfulSpelling` in the universal admission check (synthesis line 147), but
`Program/Table.lean:11–13` deliberately keeps name safety in codegen so program admission
does not import it. `Codegen/Read.lean:1940–1944` distinguishes the two. The cheapest amendment
is core `LawfulSig` plus per-face lawfulness/profile checks, joined at that face. Moving the
boundary instead needs an explicit decision and shared-predicate design.

**Reading: sessions and OCaml are not covered by raw table append.** `HostSession.start`
compares header tables exactly (`Api/HostSession.lean:129–135`); `bindCall` compares the
call's table exactly (`:145–150`). An old call is refused by a session using an extended
table. Pin sessions with their original complete signature/profile, or state a migration
relation for headers, calls, replies and journals. C2 must also relate the host contract and
tape. C7/R8 must include each selected target's admission/refusal and artifact/profile
binding; OCaml's stages remain those of `lcnf-route.md:183–204`. Generic proofs and DI-47's
finite gate do not establish these connections. No ninth condition is necessary if these
scopes are explicit; an assertion that C1–C8 already establish all concrete faces is false.

## 5. R10–R13 and coverage

**Reading: R10 has the right form.** It relates an expansion to a module specification on a
named profile, with the observation and stuttering obligation identified (synthesis:495–525).
Keep the profile/observation and progress premise in the eventual statement. Amend “scope
safety is free” to **lexical well-scoping**: `authoring_scoped` proves `Src.Scoped`, not
resource cleanup or lifetime safety. No general behavior law is established by that lemma.

**Tested: R11's closed-scope premise is insufficient if it means the runtime closed bit.**
`ClosedBeforeCleanup.lean` constructs a typed program with two sequential finalizers. The
later registration is still awaiting a deferred at fuel 500; the earlier would increment a reference.
At fuel 500 the result is a frontier, the scope is marked closed, and the reference is still
zero. This matches the source order: state is marked closed before cleanup code is returned
(`Machine/Stores.lean:1905–1923`) and installed (`Machine/Fibers.lean:1487–1494`).
`ScopeMachine.runState_complete` has a sufficient bound and a total callback; it is not a
whole-run cleanup theorem. **Amend R11/D8:** count registration identities, distinguish
close-started from cleanup-completed, use a completed-cleanup receipt for exactly-once, and
retain pending cleanup even when the owning scope already has its closed bit. Prefix
at-most-once is a separate safety statement. If `closedIn` was intended to mean completed
cleanup, define it so explicitly; the current name and text do not supply that condition.

**Proved/tested: R12's whole-machine fixed-point shape is false.** `DeadlockMutation.lean`
checks a Deferred-waiting frontier with all fibers exited or parked, no armed work, no host
reason and no timer reason. `machine_changes` proves `installMiddleware` changes that machine;
it is not an interruption. `yieldVerdict` and `advance` also mutate state
(`Machine/Fibers.lean:2089–2109`, **reading**). Existing `obs` includes stores and clock,
so it does not solve unrestricted time advancement. **Amend R12/D7:** define the allowed
internal decisions and a named control/exit progress observation before freezing a stability
law. `FairTape` services armed dispatchers (`Laws/Machine/Scheduling.lean:429–440`); it alone
promises neither host answers nor time advancement nor row termination. `row_live` needs
row-specific enabling, environment and sufficient-work assumptions. Divergence needs a
compatible-prefix or infinite-run statement, as DB-03 already requires.

**Reading: R13 is still an input list, not a theorem shape.** It names program, profile/table,
budgets, tape and load inputs, but gives no congruence or admission law. **Smallest amendment,
R13/Config decision:** name the load-input carrier; require supplied values to fit the
admitted load requirements; and require equality of recorded program/signature/profile,
budgets, tape and inputs to imply equality of the named replay observation. Hidden host
inputs must be represented by the selected host relation/tape assumptions. Freeze the
concrete law when Config's route is ruled. Its status stays designed/owed.

**Reading: coverage is broad, not exhaustive.** The stateful catalogue's primitive needs map
to R3/R4/R7; composed behavior to R10; dogfood readability, identity, host connection and
inputs to R8/R10/R6/R13. A remaining omission is the exported surface's total disposition:
`post-phase-c-synthesis.md:706–711` includes aliases, type-only entries and initialization,
not only runnable programs. Add an R8/R10 pointer to that existing owner, quantifying over
the selected `(module, export/overload, profile)` inventory, with unreviewed distinct from
refused. Local replay laws do not discharge the distributed persistence work in W10/W12.
An exhaustive mapping of every counterexample and contract packet to R1–R13 remains owed;
the synthesis itself leaves that mapping open (lines 713–714). This audit does not replace
the register or claim that a broad requirement heading closes any registered gap.

## 6. Basis refresh and ownership

**Reading/proved where indicated: keep the principal pedigree corrections.**
`interpret_pinned` is uniqueness, while the rerun injection/transport laws supply the actual
limited extension evidence. Concrete `TypedProg` is its own inductive. `fiberRefusal` is
explicitly not control semantics (`Sched.lean:32–42,216–218`). The direct source supports
separate `denoteB`, the current world fields, and the Effects pin `v0.8.0`. The service
soundness corollaries rerun (**proved**). `build_total` was introduced at `f182d2b3` and cut
at `b08f3b58`; the current header is stale. Scope-key discharge exists in the checker and
typing laws, but that does not establish all cleanup obligations. The basis already lists
Xia and Chappe (`DESIGN-BASIS.md:808–810`). These corrections should survive.

**Reading: do not inherit new inaccuracies from the corrections.** The 13 pinned reads are
a pre-E inventory, not the current edit budget (§3); synthesis's `ServicesOk`/unread-landed-E
discussion is superseded by `Membership.lean`. Addendum 4 is now tracked, so the synthesis's
tracking list must be refreshed at landing. The local proof distinction behind the Hazel
correction is right: world-order weakening is not result/protocol monotonicity. A fresh
validation of every external paper, section, and attribution was not performed here;
those literature claims retain the named historical readers' evidence status, not this
audit's proof label.

**Reading: two refresh steps would duplicate ownership unless amended.**

1. Synthesis asks every basis row for a status line (line 815), then says current status lives
   only in the system map (line 850). Basis rows should own the settled decision, rationale
   and **dated** evidence receipt; their current-status field should be a link to the system
   map. Do not create another live proof/workstream ledger.
2. DB-01 receives C1–C8, the system map receives the signature definition/requirement index,
   and `lcnf-route` receives readable-domain stage details. Keep each as the named owner of
   that fact, linking across them. DB-17 owns the row-calculus rationale and links to DB-12
   and current service contracts. “Carry each cited claim into the basis” must mean its
   decision-relevant conclusion, not copying status or the host/stage contract wholesale.

**Smallest amendment, D1 and the refresh brief:** fix those two ownership boundaries in the
write plan; keep force-added research visibly dated history. Corrections to historical notes
should be pointers or dated annotations. Current rulings still land in the coordinator's
registers. The read-only audit records the proposed repairs instead of changing any owner.

## Verification and remaining work

The finishing criteria were six reviewed parts, explicit ruling amendments, retained probe
results with axiom evidence, and a research-only commit. `verify.py` is the exact sequential
runner; `logs/results.json` records each command, worktree, source hash, exit and expected
exit. Commands run with `LEAN_NUM_THREADS=1` and Lean `v4.33.1`:

```sh
cd /Users/pooks/Dev/lean4-effect4-slice6
python3 docs/research/2026-09-30-codex-review-model-probe/verify.py
```

Each entry invokes only `lake env lean -DwarningAsError=true <path>`. The expected negative
runs are the original TREE verifier after E and the unrepaired H2 part-one harness. The
successful TREE adapter and every new named counterexample theorem have axiom output at
the ceiling. Initial audit-harness errors for the morphism argument order and saved-stack
construction remain in `*.failed.log`; they carry no proof claim. Final positive evidence
contains no recovery axioms. The negative H2 log is mapped by:

```sh
python3 docs/research/2026-09-30-seat-codex-slice6-evidence/H2/map_errors.py PartOne docs/research/2026-09-30-codex-review-model-probe/logs/h2-part-one.log
```

Static checks used `git status --short --branch`, `git rev-parse HEAD`,
`git diff 3c2609f4..HEAD -- src Test generated tools ocaml ts`, and searches including
`git grep -n 'Package.install\|install \['`, `rg -n 'nativeSignature|nativeServiceTy|initialWorld|fits_map|servicesFit_map' src/Effect4/Laws/Program/Typed`, and declaration counts over
`R2Probe.lean`. Production source/tests/generated outputs have no change since the merged
receipt; the intervening tool changes are architecture-report code. No full trust gate,
runtime target run, generator, or rebuild was authorized for this review.

Still open: H2's part-two contract and full repair count; a compiled Σ_app migration count;
core/face lawfulness separation and its admission theorem; concrete C3 reflection/C4 and
session/target extension; the corrected R11/R12/R13 universal statements; exhaustive
counterexample-to-requirement coverage; fresh external-literature verification. These limits
do not block the separately authorized A, C, F, G, H1 queue. H2 and D1–D6 implementation stay
with the coordinator's next ruling/addendum.
