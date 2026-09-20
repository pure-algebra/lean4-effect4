# Deep-dive review of the state refinement plan: slices, simpler abstractions, proof infrastructure

Reviewed at `a96051a6` on `refactor/phase1-phase3` against the paused tooling worktree
`/private/tmp/effect4-typed-state-tooling` (branch `codex/typed-state-tooling`, base `23e668b0`,
one commit `f6f9f793`, the rest uncommitted). Every file and line below was read at those
revisions. The plan under review is `docs/research/2026-09-19-state-refinement-plan.md`; its
§14 now carries the slice table this note derives. Nothing here rules a decisions row.

## 0. Verdict

The plan is right about what it refuses and thin about what to build. Its D0–D7 rows are
stages, not slices: no row names a Lean file, a theorem statement, a deletion or a red control,
so the next implementer has to re-derive all of it. The tooling worktree already supplies most
of what D3 asks for, built green today (§1), and should land first as five tooling slices. Three
abstractions get simpler before any proof is written, and one owner question dissolves:

1. **One world, one order.** The world is `⟨Γ, Π, Ρ, s⟩`; its order is table extension paired
   with `Stores.le`, which already has `le_refl`/`le_trans`
   (`src/Effect4/Laws/Machine/StoresLaws.lean:46-60`). Layer 0 (`Laws/Effects/Protocol.lean`)
   needs exactly a `WorldOrder`; nothing else is owed for weakening.
2. **Columns over data, not decoders.** D2 (the map's R1+R2) is the first machine change and it
   is a deletion: two `Program`-typed positions leave the store, `denoteStored`'s partial arm
   goes, and the promise column is stated on `Completion` data. It must precede layer 1's
   `PromiseTable`, not the whole milestone.
3. **The store kernel is already the storage interface.** `refStepOf` reads one cell, computes,
   writes back, and its laws are proved once (`src/Effect4/Laws/Machine/RefKernel.lean`). D5 is
   "make the kernel generic over an arena", not "an efficient Lean implementation" — which the
   plan's own §8 says would not speed up OCaml, since the translator lowers `Array` to a list.
4. **Row 80 is moot for a first transaction profile** if admitted bodies are the straight
   fragment: a straight body under prevented yields is one `sync` step and cannot reach a fuel
   frontier, so there is no budget to own across (§3, F9).

*Corrections (2026-09-19, after the landed-architecture review, §9): item 1 is amended (the
order also needs typed-cell compatibility; `Stores.le` alone is refuted) and item 4 is withdrawn
(a straight body compiles to continuation frames; a sufficient budget must be proved). F5 and
F7 are amended there too.*

## 1. What was checked

Facts the slices stand on; each was read, not recalled.

| fact | where |
| --- | --- |
| The tooling tree built green after its last edit: every `.olean` is newer than its source (`TypedStateDecl` 13:35:30 → 13:35:40; `Frames`, `State`, `Typed/Frames`, the four audit tests 13:40–13:41; `AxiomGate` 13:43:51), so the trust-gate exemptions it adds are not stale | `.lake/build/lib/lean/**` in the worktree |
| Main differs from the tooling base by documentation only: 39 files, all under `docs/`, since `23e668b0` | `git diff --stat 23e668b0 a96051a6` |
| The tooling diff: 18 tracked files (+162/−710), 12 new files (945 lines): `tools/ProofGraph/{Proof,Ledger,Search}.lean` (209), `Laws/Auto/{TypedStateDecl,Frames,Obligations}.lean` (518), `Typed/Frames.lean` (10), five tests (208). It deletes `Laws/Auto/TypedStateGen.lean` (402), `scripts/lean/TypedStateEmit.lean` (18), the generated body of `Typed/State.lean` (170 → 26) and 66 lines of `tools/Conform/Core/Proof.lean` | `git status --short --untracked-files=all` |
| `ProofGraph` imports `Lean` and Batteries only; `Conform.Core.Proof` is a four-line shim over it; `Laws/Auto/Census.lean` reuses `ProofGraph.search` and `axiomsOf` | `tools/ProofGraph/*.lean`, `tools/Conform/Core/Proof.lean`, `src/Effect4/Laws/Auto/Census.lean` |
| `#typed_state` generates `Preds` from the source table, one `Ok` per owner, the aesop registrations into the named bank `Effect4.TypedState`; the red control `TypedStateRulesRed` proves the bank is what closes `saved_from_clauses` | `Laws/Auto/TypedStateDecl.lean:202-355`, `Typed/State.lean`, `Test/Program/TypedStateRulesRed.lean` |
| `#frame_rules` fills the invariant constructor with old projections where the type still matches and abstracts the rest; **one rule per single field** | `Laws/Auto/Frames.lean:21-35` (`fill`), `:59-72` (per field) |
| `#typed_state_obligations` collects `Obligation p` declarations by name prefix, searches each with the given tactic, publishes `<goal>.checked` through the kernel, and checks placeholders and a ceiling; **the goal set is the authored declarations** | `Laws/Auto/Obligations.lean:38-48` |
| Layer 0 exists, 125 lines, no axioms: `Typed`, `mono`, `bind`, `widen`, `inl`, `inl_inv`, `inr_inv`, `pure_inv` | `src/Effect4/Laws/Effects/Protocol.lean` |
| Layer 1 does not exist; `Laws/Machine/Keeps.lean` does not exist; Move 1 (`EvaluateR.lean`) landed | `ls src/Effect4/Laws/{Machine,Program,Program/Typed}` |
| The store's heap column and the store progress theorem: `Stores.HeapNat` (`Progress.lean:71`), `progress` with hypotheses `WF`, `HeapNat`, `.sync`, request typing and validity, conclusion answer typing, validity, `WF`, `HeapNat` (`:346-352`); `answer_typed` (`:259`) | `src/Effect4/Laws/Program/Progress.lean` |
| `Stores.WF` excludes completions (`STORES-FB-COMPLETION`); a Deferred cell holds `Option Program` and the owed resumes hold `Program`; the reference decodes with `denoteStored`, whose catch-all is `pending .unsupported` | `StoresLaws.lean:11-19`, `Stores.lean:1079-1096`, `InterpR.lean:133-137` |
| `MemoEntry.effect : Program` duplicates the cell (`Deferred.await` until the build exits, then the exit) | `Stores.lean:551-562` |
| `WakeList` is a lawful ordered-work interface already: `register_phase`, `cancel_pending`, `cancel_owed_iff`, `schedule_posts`, `schedule_coalesces`, `runBatch_clears`, `sweep_keeps_order` and eight more; Latch is named there as the `Unit`/broadcast/scheduled instance | `src/Effect4/Machine/Wake.lean` header |
| The OCaml property tests compare the store carrier with Lean's list operations law by law | `ocaml/engine/test/prop_store.ml:1-8` |
| The STM scout's admitted fragment includes `iterate`/`gen` ("never park by themselves") and notes that a loop that never ends inside a transaction reaches a fuel frontier | `docs/research/2026-09-19-stm-scout.md:516-520` |
| `Simulation/*` is 6,008 lines across eight files; the scout's S2 count is 65 arms | `wc -l src/Effect4/Laws/Program/Simulation/*.lean` |
| A `lake serve` and two `lean --worker` processes are open on the tooling worktree (an editor), no `lake build` anywhere | `pgrep -fl 'lean\|lake'` |

## 2. Findings on the plan

**F1. Stages, not slices.** D1–D7 (`plan §11`) name work and acceptance in prose. None names a
file, a statement, a deletion or a red control, which is what every landed slice of this
estate has carried (`Tier 3` of the tooling plan, the atoms receipt). §14 of the plan now holds
the slice table of §4 below.

**F2. D1 is three things.** "Structural contract" bundles (a) the observation projections of
plan §3, which are two definitions and one factorization lemma already proved in the critique
packet (`docs/research/2026-09-19-critique/Contracts.lean`: `Factors`, `transfer_safety`);
(b) the completion and memo contract, which is D2's statement; (c) the wake protocol, Latch and
the replay-versus-suspension choice, which belong to D6 and to row 80. Only (a) and (b) are
Lean-shaped now. The rest is reserved with `theorem_wanted` when its first consumer appears,
which is the plan's own §9 rule.

**F3. D2 first, and it is a deletion.** R1 changes `DeferredCell.completion : Option Program`
to `Option (Completion Val Err Defect FiberId Ann)` and `DeferredStore.due : List (Owed Program)`
to `List (Owed (Completion …))`; R2 deletes `MemoEntry.effect`. The position census then loses
two `Program` positions (`DeferredCell.completion`, `MemoEntry.effect`) and `Owed.code`'s carrier
changes; the map (`stores-and-event-log-map.md:328-346`) lists what dies with it:
`CompletionShaped`, the first conjunct of `DeferredOk`, `StoredCodeNoRace`, `DeferredCodes`, the
partial arm of `denoteStored` (it becomes `denoteCompletion`, already total at
`InterpR.lean:128`), and `Stores`' dependence on the compiled code type. The twelve
`deferred.*` census witnesses re-spell at `Completion`. Radius about twenty files. The
totality gate forces the source-table edit. Nothing in S1's fiber arms or in `Keeps` depends on
it, so those can run beside it; layer 1's `PromiseTable` column and the deferred store arms
wait for it.

**F4. D3 is three things too.** It bundles the generic language work rows 42–43 still owe
(binder-term rows, `hasTyWith`, the `Ρ` column), layer 1 (the `Preds` instance), and the
ledger. They have different owners and different blockers: binder terms change one kernel
line per `refUpdate` row (`RefKernel.lean`, tooling 3.1) and are needed only when S2 reaches
those rows; layer 1 needs D2; the ledger needs the coverage join of F5. Split them (§4, M2 and
M6).

**F5. The "independent goal producer" is over-specified.** *(Amended in §9: the holder join is
the inventory; each holder's statement is fixed by a per-transition-shape adapter, so an
`Obligation True` cannot pass.)* Plan §9 asks that the ledger derive
"the required goal set" from the invariant and the actual transitions so that a deleted
declaration cannot vanish. A goal *statement* per definition cannot be synthesized: `driveStep`
returns a pair, `popR` a step result, `exitFiber` takes an exit, `fireObserver` a fiber and an
observer; each preservation statement is hand-shaped. What can be derived is the *set of
definitions that must carry one*: the holders of the write census closure
(`#write_census f closure over R…`, `Positions.writeSites`, with matcher-arm provenance
already carried). So the join is a coverage check: every holder with a write site on a typed
position must have an `Obligation` declaration named after it under the ledger's scope, and
every such declaration must name a holder. Deleting a declaration then fails the build.
About forty lines on top of `Laws/Auto/Obligations.lean`. Counts stay a report.

**F6. Frames per field are not the frames S2 uses.** A step writes a field *set*
(`exitFiber` writes `exit`, `frame`, `pending`, …), and the write census reports that set per
site (`Site.fields`). A single-field frame chain needs every intermediate record to satisfy the
invariant, which a record with a fresh `exit` and a stale `frame` does not. `Frames.fill`
generalizes without change of shape: replace several projections at once, keep the rest, fill
what still matches. Generate frames per `(owner, written-field set)` found by the census, which
is what decisions row 50 already says.

**F7. Two of the eleven hand predicates are derivable, and five `Expect` constructors are
unused.** *(The two deletions are withdrawn in §9: a resume answer is typed at the saved
continuation's input, not the fiber's final type, and an interrupt cause is provenance, not
admission at one type. The pruning of the unused `Expect` constructors stands.)* `Task.resume.answer` and `Cmd.resume.answer` are sourced as `.custom "ResumeOk"`; the
generator binds constructor fields by name (`TypedStateDecl.lean:228-233`), so
`.program (.fiber "target")` elaborates to `P.program w (.fiber target) answer` and `ResumeOk`
goes. `RSaved.interruptedCause : Option CauseV` is `.custom "InterruptOnly"`; `.cause .inherited`
generates `∀ v0, x.interruptedCause = some v0 → P.cause w e v0`, and an interrupt cause is
admitted by every column, which is what `InterruptOnly` would have said. `Expect` carries
`promise`, `refColumn`, `row`, `checker`, `const`; no row uses them (per-cell typing goes through
the `column` escape because a cell's index is not in scope at its position). Prune them: every
hand predicate of layer 1 matches on `Expect`, so each unused constructor is an arm in nine
definitions.

**F8. Two expectation vocabularies.** `Expected` (strings, `Typed/Vocabulary.lean`) and `Expect`
(typed, `Typed/State.lean`) are the data and the elaborated form of one thing. The split is
necessary; the near-identical names are not. Low priority; rename when `Expect` is pruned.

**F9. The transaction profile's first cut should be the straight fragment.** *(Corrected in §9:
"one `sync` step" is false, since Straight admits `bind` and `suspend` and the driver's budget
is independent of prevented yields; the profile needs a proved sufficient budget or row 80's
contract. Row 84's rationale is amended.)* Plan §7 keeps
finite replay and driver suspension both open (row 80) because an admitted body might reach a
fuel frontier. The scout admits `iterate` and `gen` and names that hazard
(`stm-scout.md:516-520`). If the first profile admits `TxBody ∩ Straight` (no `iterate`, no
`gen`), a body under `PreventSchedulerYield` is one `sync` step: no frontier, no budget, no
ownership across budgets, and the isolation lemma is the scout's §2.1 argument without the
loop case. Loops inside a transaction become a named refusal until row 80 is ruled. This is a
proposal for the owner (plan §14, decisions row 84); it removes nothing the plan requires and
lets D6 start without row 80.

**F10. D5's "efficient Lean implementation" buys nothing where speed is wanted.** Plan §8
records that `translateClosure` lowers `Array` to `List` and `Array.push` to append
(`src/OCaml5/Lcnf/Types.lean`, `Translate.lean`), and D5's acceptance says "verify actual
target operations". So a Lean `Array` arena changes no OCaml artifact. What D5 needs is the
*interface*: a structure `Arena` with `peek`, `poke`, `alloc`, `size`; the dense-arena laws of
plan §5 as its fields; `refStepOf` and `refStepOf_keeps`, `refStepOf_length` restated over it;
the `List Val` instance is today's `RefHeap` and is the reference. The OCaml `E4_store`
already implements those operations and `prop_store.ml` already checks each law against
Lean's list operation, so the OCaml instance is the trusted edge plan §8 names, with its
evidence in place. No Lean `Array` instance until the translator can emit one. Decisions row 85
records the re-scope as a proposal.

**F11. The ordered-work interface exists.** Plan §5's table lists "ordered work sequence" as
an interface to expose. `WakeList` is that interface, with fifteen proved laws and the
cancellation clause the plan worries about (`Wake.lean` header). Latch is already named there
as the `Unit`/broadcast/scheduled instance. D6's "Latch contract first" is therefore: one
`DeferredCell`-shaped store, the four controls (cancel in pending versus captured batch,
coalescing, snapshot versus live drain, opener dispatcher) as instances of `cancel_pending`,
`schedule_coalesces`, `runBatch_clears` and a new owner clause. Say so in §5 rather than
re-deriving it.

**F12. Observations as definitions.** Plan §3's three views should be two Lean definitions
(`Obs.semantic`, `Run.holder`) with the `Factors` lemma from the critique packet promoted into
`Laws/Machine/Behaviour.lean`, and R3 of the map (`parent`/`daemon` on `RunFiber`, set at
`spawn`) as the one machine change that makes holder supervision a state projection rather
than a trace read. Small; independent of the milestone; it is the concrete content of D1.

**F13. The aesop bank and its red control already exist.** Plan §9 asks for "small named banks
with positive and omitted-bank controls". `Effect4.TypedState` is declared
(`Laws/Auto/RuleSets.lean`), `#typed_state` registers into it, `TypedStateRulesRed` is the
omitted-bank control. The next banks are `Effect4.World` (the order facts, `Typed.mono`,
the three inversions as `safe forward`) and `Effect4.Store` (`progress`, `answer_typed`,
`refStepOf_keeps`).

**F14. A totality gate for the fiber alphabet.** The position census makes the *state*
invariant total by construction; nothing does the same for the residual protocol's forty
`OpOk`/`AnswerOk` arms. A `#answer_gate FiberOp using answerSources` that walks `FiberOp`'s
constructors, reads `FiberOp.answer` per constructor, and refuses a constructor without a row
or a row without a constructor is sixty lines on the `PositionGate` pattern. It is the
instrument that ends the "which operation did we forget" class of surprise for M3.

**F15. `STORES-FB-COMPLETION` retires with layer 1.** Once `PromiseTable` is stated on
`Completion` data (after D2), `Stores.WF`'s refusal of completions is subsumed; delete the
refusal row and the docstring at that slice, not later.

**F16. Register.** About forty percent of the plan is restatement of what is not claimed. That
was the right answer to an audit; it is the wrong shape for the implementer. §14 is the short
form; the rest stays as the evidence record.

## 3. The abstractions, simplified

| abstraction | today | after | what it deletes |
| --- | --- | --- | --- |
| the world | `W` abstract in `Preds`; layer 1 unwritten | `World := ⟨Γ : FiberId → Option EffTy, Π : DeferredKey → Option (Ty × Ty), Ρ : RefKey → Option Ty, s : Stores⟩`; `WorldOrder` = pointwise table extension ∧ `Stores.le` ∧ typed-cell compatibility (every cell keeps the type its column declares; `Stores.le` alone is refuted, §9) | nothing; it is the missing piece |
| the promise column | `Option Program` decoded by a partial `denoteStored`; `WF` refuses completions | `Option Completion`; `PromiseTable w s := ∀ i c, s.deferreds.cells[i]? = some c → ∀ x, c.completion = some x → CompletionOk w (Π ⟨i⟩) x` | `CompletionShaped`, `DeferredOk.1`, `StoredCodeNoRace`, `DeferredCodes`, `denoteStored`'s catch-all, `STORES-FB-COMPLETION`, `MemoEntry.effect` |
| the store interface | `RefHeap := List Val` with `refPeek`/`refPoke`; kernel laws proved on it | `Arena` (peek/poke/alloc/size + five laws); `refStepOf` over any `Arena`; `RefHeap` its list instance | no new code path; the OCaml instance keeps `prop_store.ml` as its evidence |
| the hand predicates | eleven (`program`, `exit`, `StackOk`, `InterruptOnly`, `PendingOk`, `ResumeOk`, `ServiceOk`, `RaceOk`, `HeapNat`, `PromiseTable`, `CaptureOk`) | nine: `ResumeOk` and `InterruptOnly` derived from the table | two arms in every layer-1 definition |
| `Expect` | eight constructors, three used | `root`, `fiber`, `hook` (add one when a row uses it) | five arms in nine definitions |
| the frames | one theorem per field, 60 rules | one theorem per `(owner, written-field set)` the census reports | the single-field rules nothing applies |
| the ledger | authored `Obligation` declarations, searched and checked | the same, plus a coverage join from the write census closure to the declarations by name | the "a deleted goal disappears" hazard |
| the residual protocol | forty arms to be written by reading | the same forty, under an `#answer_gate` | the forgotten-operation surprise |
| transactions v1 | `TxBody` with `iterate`/`gen`; row 80 open | `TxBody ∩ Straight`; loops refused by name | the across-budget ownership clause, for v1 |

## 4. The slices

Every slice names its files, its statement or instrument, its deletion, its red control and its
build. Tooling slices T0–T5 land first; they touch no runtime root. M-slices are the milestone.
P-slices are independent and may run beside any M-slice.

### Tooling, from the paused worktree

| slice | files | statement / instrument | deletes | red control | build |
| --- | --- | --- | --- | --- | --- |
| T0 checkpoint | the worktree's 12 new and 18 modified files, as three commits on `codex/typed-state-tooling` (ProofGraph; the typed-state tooling with its wiring; docs) | preserve the work as commits before anything else touches the worktree | nothing | — | none (built green 13:40–13:43 today) |
| T1 ProofGraph | `tools/ProofGraph/{Proof,Ledger,Search}.lean`, `lakefile.toml`, `tools/Conform/Core/Proof.lean` (shim), `Laws/Auto/Census.lean`, `Test/Audit/ProofGraph.lean` | `ProofRef.validate` (name, universes, proposition by `isDefEq`, axioms ⊆ `[propext, Quot.sound]`); `search` (rolled back, closed term or refusal); `addTheorem`; `Ledger.check` (exact set, dependencies acyclic, ceiling) | 66 lines of `Conform/Core/Proof.lean`, 15 of `Census.lean` | the nine `#guard_msgs` of `Test/Audit/ProofGraph.lean` (wrong proposition, non-theorem, extra axioms, stale, missing, ceiling, cycle) | `lake build ProofGraph Conform.Core.Proof Effect4.Laws.Auto.Census Test.Audit.ProofGraph` |
| T2 declarations | `Laws/Auto/TypedStateDecl.lean`, `Typed/State.lean` (26 lines), `Typed/Vocabulary.lean`, `Typed/Sources.lean`, `Laws/Auto/TypedSources.lean` (`readRows table`), `Laws/Auto/Positions.lean` (the two refusals, the arms), `Test/Audit/{TypedStateDecl,PositionAnalysis}.lean`, `Test/Program/TypedStateRulesRed.lean` | `#typed_state R… using sources columns Stores` elaborates `Preds` and one `Ok` per owner in place; registers the bank | `Laws/Auto/TypedStateGen.lean` (402), `scripts/lean/TypedStateEmit.lean` (18), the generated body of `State.lean` (150) | collision, missing-source and the omitted-bank control | `lake build Effect4.Laws.Program.Typed.State Test.Audit.TypedStateDecl Test.Audit.PositionAnalysis Test.Program.TypedStateRulesRed` |
| T3 frames | `Laws/Auto/Frames.lean`, `Typed/Frames.lean`, `Test/Audit/FrameRules.lean` | `#frame_rules Inv…`: one kernel-checked theorem per field today; **amend to per written-field set** (F6) before M6 uses it | — | the two-field fixture (`Fits.frame_value` needs both clauses) | `lake build Effect4.Laws.Program.Typed.Frames Test.Audit.FrameRules` |
| T4 ledger | `Laws/Auto/Obligations.lean`, `Test/Audit/Obligations.lean` | `Obligation p`, `#proof_wanted`, `#typed_state_obligations S ceiling n using tac`; **add the coverage join** (F5): `#typed_state_coverage <step roots> over <state roots> ledger S` | — | missing, stale, solved-with-placeholder, ceiling; new: a holder without a declaration | `lake build Effect4.Laws.Auto.Obligations Test.Audit.Obligations` |
| T5 wiring | `Effect4/Laws.lean`, `Test/All.lean`, `Test/Audit/AxiomGate.lean` (three exemptions), `Makefile` (`check-typed-state`), `docs/{ARCHITECTURE,GENERATED,STATE}.md` | the group has no generated file; `make check-typed-state` is the focused build | the `TypedStateGen` exemption | the gate's bidirectional staleness check | `lake build Test.Audit.AxiomGate` then `make check-typed-state` |

T0 is done in this review (§6). T1–T5 merge as one branch merge once `docs/STATE.md` and
`docs/ARCHITECTURE.md` are reconciled by hand (both sides changed them).

### The milestone

| slice | files | statement | deletes | red control | build |
| --- | --- | --- | --- | --- | --- |
| M1 = D2 (R1+R2) | `Machine/Stores.lean` (cell, `due`, three writers, `memoBuild`/`memoComplete`), `Machine/Completion.lean`, `Laws/Program/InterpR.lean`, `Simulation/Hooks.lean`, `Laws/Machine/{StoresLaws,Handles}.lean`, `Typed/Sources.lean`, the OCaml regeneration, twelve `deferred.*` witnesses | `DeferredCell.completion : Option Completion`; `due : List (Owed Completion)`; `answerCode`/`dueResumes` mint code at the consumer; `MemoEntry.effect` gone | `CompletionShaped`, `DeferredOk.1`, `StoredCodeNoRace`, `DeferredCodes`, `denoteStored`, `STORES-FB-COMPLETION` | the position gate (two positions fewer, one carrier changed); `#guard` that `dueResumes` still delivers `Completion.ofRefGet` as a deferred read | `lake build Effect4.Machine.Stores Effect4.Laws.Program.InterpR Effect4.Laws.Program.Simulation.Hooks Effect4.Laws.Machine.StoresLaws Test.Audit.PositionCensus`; OCaml `make gen-lcnf` |
| M2 layer 1 | `Typed/World.lean` (new) | `World`, `WorldOrder`, `Γ`/`Π`/`Ρ` extension, the columns `HeapNat` (reuse `Stores.HeapNat`) and `PromiseTable` on data, the nine hand predicates, `instance : Preds World`; `ResumeOk`/`InterruptOnly` retired by table edit (F7); `Expect` pruned | two source rows' `custom` names; five `Expect` constructors | `TypedStateRulesRed` still red without the bank; a `#guard` that `RStateOk P₁ w (loadR e fuel)` is stated | `lake build Effect4.Laws.Program.Typed.World` |
| M3 residual | `Typed/Residual.lean` (new), `Laws/Auto/AnswerGate.lean` (new, F14), `Typed/AnswerSources.lean` | `Ψ_S := ⟨progress's hypotheses, its conclusion⟩`; `OpOk`/`AnswerOk` forty arms under `#answer_gate`; `TypedProg w ty p := Typed order (Ψ_S.sum Ψ_F) w (ExitOk ty) p`; `HandlesFit` | — | the gate: a `FiberOp` constructor without a row | `lake build Effect4.Laws.Program.Typed.Residual` |
| M4 keeps and stack | `Laws/Machine/Keeps.lean` (new, imports `Machine/Fibers` only), `Typed/Stack.lean` (new) | the unary ladder; existential `StackOk` (row 48); `popR_typed`, the first hard witness | — | `popR_typed` at `[propext, Quot.sound]` | `lake build Effect4.Laws.Machine.Keeps Effect4.Laws.Program.Typed.Stack` |
| M5 = S1 | `Typed/Denotation.lean`, `Typed/Hooks.lean` (new) | `denoteR_typed` by the weight induction of `code_intro_aux`; `InterpTyped (interpR root)` for the fourteen hook fields | — | the 51 hook rows `proved` in the ledger | one module at a time |
| M6 = S2 | `Typed/Ledger.lean` (the `Obligation` declarations, one per write-census holder, named `Ledger.<holder>`), `Typed/Step/{Frame,Deliver,Operations}.lean` | `#typed_state_coverage` green before the first proof; the ceiling pinned **here**, after M1 and M2; frames per written set first, then the nine delivery sites, then the operation arms by family | — | coverage; ceiling decreasing | per module |
| M7 = S3 | `Typed/Transfer.lean` (the only `Typed/*` module importing `RuntimeR`), `TypedRun.lean` | `TypedProgram.run_typed` through `replay_rel`/`BMeans.exitOf`; no `badShape`; DI-17 | — | `Test/Program/TypedStateContract.lean` on the dogfood programs | `lake build Effect4.Laws.Program.Typed.Transfer` |

Binder-term rows (rows 42–43 step 3) are needed when M6 reaches the `refUpdate` family; they
change one kernel line per row (`SyncOp.refKernel`) and one `progress` arm. Land them before
that family, not before M2.

### Independent

| slice | files | statement | deletes | red control |
| --- | --- | --- | --- | --- |
| P1 observations (D1's Lean content) | `Laws/Machine/Behaviour.lean`, `Run.lean` | `Obs.semantic`, `Run.holder`, `Factors`, `transfer_safety` promoted from the critique packet; R3 (`parent`, `daemon` on `RunFiber`) | the trace read in `forkedOf` (it becomes a check) | the equal-`Obs`/different-supervision fixture stays a refutation of the unrestricted claim |
| P2 arena (D5 re-scoped) | `Laws/Machine/Arena.lean` (new), `RefKernel.lean` | `Arena`, its five laws, `refStepOf` and `refStepOf_keeps` over it, `instArenaList`; the OCaml `E4_store` as the trusted instance with `prop_store.ml` | nothing in Lean; the plan's Lean `Array` instance | a lawless arena (poke that drops) fails `refStepOf_keeps`' premise by construction |
| P3 identities (R5) | `Machine/Stores.lean`, `Machine/Fibers.lean` | `ScopeKey`, `FinKey`, `Token`, `RaceId` as one-field structures | numeric coincidences no clause reads | `DecidableEq` derives; the join's counter unchanged |
| P4 transactions v1 (D6, after M7) | per the scout §3 items 1–8, with `TxBody ∩ Straight` (F9) | isolation lemma; transaction meaning as `run_eq_meaning` on a run segment | versions, journal handle, conflict path (the scout's "what not to add") | the finite `probe.ts` wake controls; `iterate` inside `tx` refused by name |
| P5 Latch (D6) | `Machine/Stores.lean`, `Machine/Wake.lean` | the `Unit`/broadcast/scheduled instance and its owner clause | — | the four controls of F11 |

## 5. Proof infrastructure and structure

Three instruments to add (each is a chore done by hand once already):

1. **Field-set frames** (`Frames.generate invariant fields`): the same `fill`, several
   projections replaced; `#frame_rules Inv from #write_census root…` reads the sets from the
   census. Red control: a two-field write whose single-field chain is unprovable.
2. **Coverage join** (`#typed_state_coverage`): `writeSites` closure over the step roots →
   holder set; the ledger scope → declaration set; the difference either way is an error with
   the name. Red control: delete one declaration in a fixture scope.
3. **Answer gate** (`#answer_gate FiberOp using answerSources`): totality over the fiber
   alphabet's constructors, same vocabulary as `Sources`. Red control: a constructor without a
   row.

Banks: `Effect4.TypedState` (exists), `Effect4.World` (order, `Typed.mono`, the inversions),
`Effect4.Store` (`progress`, `answer_typed`, `refStepOf_keeps`). Each bank lands with the slice
whose proofs it closes and with an omitted-bank control.

Where things live, so no `Typed/*` module imports `Simulation` or `Book` before `Transfer`:

| module | slice | imports |
| --- | --- | --- |
| `tools/ProofGraph/*` | T1 | `Lean`, Batteries |
| `Laws/Auto/{Positions,PositionGate,TypedSources,TypedStateDecl,Frames,Obligations,AnswerGate}` | T2–T4, M3 | `Lean`, `ProofGraph`, the vocabulary; trust-gate exemptions |
| `Laws/Effects/Protocol` | exists | the pinned `Effects` only |
| `Laws/Program/Typed/{Vocabulary,Sources,State,Frames}` | T2–T3 | `EvaluateR`, the generators |
| `Laws/Program/Typed/World` | M2 | `State`, `StoresLaws`, `Progress` |
| `Laws/Program/Typed/Residual` | M3 | `World`, `Protocol`, `Sched` |
| `Laws/Machine/Keeps`, `Typed/Stack` | M4 | `Machine/Fibers`; `Residual` |
| `Typed/{Denotation,Hooks}` | M5 | `Stack`, `DenoteR` |
| `Typed/{Ledger,Step/*}` | M6 | `Hooks`, `Frames` |
| `Typed/Transfer` | M7 | `RuntimeR` |
| `Laws/Machine/{Arena,Behaviour}` | P1–P2 | `RefKernel`; `Approximation` |

## 6. Done in this review

- The tooling worktree's uncommitted work is checkpointed on `codex/typed-state-tooling` as
  three commits by explicit paths (ProofGraph; the typed-state tooling with its wiring, since
  the root imports cannot be split without a broken intermediate; docs), so T0 is closed and
  the worktree can be retired after the merge.
- The plan gained §14 with the slice table above; `docs/STATE.md` points at this note;
  decisions rows 84–85 record F9 and F10 as proposals (`74f2ddf0`).
- T1–T5 merged into `refactor/phase1-phase3` as `de27095d` (one hand-resolved paragraph in
  `docs/STATE.md`: main's rows 44–45 approval kept, the branch's 87-position and retired-writer
  facts taken). The narrow build on the merged tree, in the main checkout:

      lake build ProofGraph Conform.Core.Proof Effect4.Laws.Auto.Census \
        Effect4.Laws.Auto.TypedStateDecl Effect4.Laws.Auto.Frames Effect4.Laws.Auto.Obligations \
        Effect4.Laws.Program.Typed.State Effect4.Laws.Program.Typed.Frames Effect4.Laws \
        Test.Audit.ProofGraph Test.Audit.Obligations Test.Audit.FrameRules Test.Audit.TypedStateDecl \
        Test.Program.TypedStateRulesRed Test.Audit.PositionAnalysis Test.Audit.PositionCensus \
        Test.Audit.AxiomGate

  532 jobs, exit 0. Receipt lines: `Typed/State.lean:25` "87 positions from 4 roots, 95 source
  rows"; `:28` "typed state: 16 predicates, 11 carrier predicates, 2 refusals";
  `Typed/Frames.lean:8` "frame rules: 60 checked theorems, 159 reused clauses, 40 explicit
  premises"; `saved_from_clauses` at `[propext]`; the axiom gate rebuilt with the three new
  exemptions and the retired one removed. No whole-tree or host sweep was run.
- The tooling worktree keeps an editor session open (`lake serve`); retire it with
  `git worktree remove` once that is closed. The design worktree's branch is fully merged and
  can go now.

## 7. Owner decisions surfaced

- **Row 84** (F9): the first transaction profile admits `TxBody ∩ Straight`; loops inside
  `tx` are a named refusal; row 80 waits.
- **Row 85** (F10): D5 is the `Arena` interface and its list instance; no Lean `Array`
  instance; the OCaml instance is the trusted edge with `prop_store.ml`.
- Merge T1–T5 now (recommended; nothing runtime moves, the tree is green, the plan's §9 already
  says to retain every piece).
- F7's pruning of `Expect` and the two derived predicates needs no ruling; it lands with M2.

## 8. What the map measured (2026-09-19, after the merge)

`docs/core/architecture-map.html` is now generated from the tree by `tools/Tools/Architecture.lean`
(`make gen-architecture`, 17 s): every import header through the compiler's parser, declaration
counts from the loaded roots, the estates by file walk, the groups from GENERATED.md and the
pins from the lakefile, against the role register `tools/Tools/ArchitectureRoles.lean`, which
is total both ways. At this measurement: 541 modules, 195,403 lines, 8,570 theorems in the
tree, 26 imports against the declared direction (2 accepted by a document), 10 area pairs that
import each other. The organization questions it puts to the plan review:

1. **The fold connectors live in the runtime root and import upward.** `Program/Folds/{Term,
   Ty, Representation}`, `Machine/Folds/Stores` and `Store/Folds/Val` reach Schema, Codegen
   and Program: eleven of the twenty-six. They are `fold_of` connectors, proof material beside
   a hand definition; they belong under Laws beside `Laws/Program/Folds`, or in one `Folds`
   area declared above Codegen. Moving them clears three of the ten cycles at once (Machine ↔
   Program, Program ↔ Schema, Program ↔ Codegen in part).
2. **`tools/Tools` and `src/OCaml5` import each other.** The descriptions (`ProgramStructure`,
   `WireTags`, `ProfileJson`, `GeneratedStamp`) are read by `OCaml5.Eff.World`; the drivers
   (`TsGen`, `Corpus`, `ForeignCorpus`, `Styles`, `ProgramStructureCheck`) read `OCaml5.Eff`.
   One library holds both. Split it: the descriptions below OCaml5, the drivers above.
3. **`Laws/Auto` and `Laws/Program` import each other.** The position gate and the table
   reader (`PositionGate`, `TypedSources`) read `Typed/Vocabulary` and `Typed/Sources`, which
   sit in the area the gate serves. M3's answer gate would repeat the shape. Put the typed-state
   tables and their readers in one place before M3: either the vocabulary and tables move to
   `Laws/Auto/Typed*` as data, or the gates move under `Typed/`.
4. **Store is two things.** `Machine/Value` reads `Store.Image`, so the register puts Store
   beneath Machine; but `Store/AnnotationsCanonical` reads `Machine.Value`, `Store/Shape` reads
   `Schema.Authoring` (row 39's `render` move, already ruled) and `Store/Folds/Val` reads
   Program. The value carrier (`Val`, the codec, `Image`) is beneath Machine; the store proper
   (nodes, words, shapes) is above Program. The prose in ARCHITECTURE lists Store beside Schema,
   which matches neither half.
5. **Arch is two things.** `Arch/JsonNumber` is a leaf; `Arch/Accepts` reads
   `Schema.Document`. Two files, two heights.
6. **One file each:** `Laws/Codegen/ModuleReadable` reads `Laws/Api/Codegen` (the
   Api ↔ Codegen cycle in the proof graph); `OCaml5/Tools/CasGoldens` reads
   `Test.Store.NodeContract`; `Tools/RowTypes` reads `Test.Api.AcquireHandleContract` and
   `Laws.Program.Template`. Each is a move or a documented acceptance.
7. **Leftovers:** `src/Effect4/Program/Agreement` and `src/Effect4/Program/Simulation` are
   empty directories; `tools/conform-red` is unbuilt by design and should say so in a README or
   go. The twelve largest modules top out at `Laws/Machine/Handles.lean` (6,428 lines) and
   `Laws/Program/Guard/Core.lean` (3,766); `Machine/Fibers.lean` holds 365 definitions and one
   theorem, which is what the milestone's S2 has to walk.

None of these changes a slice's statement; 1, 3 and 4 change where M2–M6's files should go and
belong in the plan review before M2 starts.

## 9. The landed-architecture review, addressed (2026-09-19)

`docs/research/2026-09-19-landed-architecture-review.md` (`f4404923`) checked this note and the
merged tooling against the tree, with witnesses under
`docs/research/2026-09-19-landed-architecture-review/`. Each finding, and its disposition:

| finding | disposition |
| --- | --- |
| P1 §1: the generator silently weakens for three shapes (a field that is both a position and an edge; a single-constructor inductive that is not a structure; a nested column owner) | **Fixed** in `src/Effect4/Laws/Auto/TypedStateDecl.lean`: the census's naming rule is shared (a single constructor's arguments are the owner's fields); a field's direct positions and its child edges each contribute a clause, never one instead of the other; a nested column owner is relevant; and `#typed_state` ends with an accounting pass in which every censused position and edge is stated, deliberately omitted (`journal`, `hook none`) or under a covered subtree, and every column a row names was emitted by a column owner, else it fails by key. The three shapes and the ownerless column are controls in `Test/Audit/TypedStateDecl.lean`. On the real roots the skeleton is unchanged (16 predicates, 2 refusals), as the review's scope probe predicted. The review's `Skeleton.lean` and `Scope.lean` witnesses no longer elaborate: the weakened statements do not exist. |
| P1 §2: allocation growth does not license weakening | **Withdrawn** (§0.1, §3). `Typed.mono` needs monotone demands and result predicates; `Stores.le` orders allocation, not contents; `heapNotMonotone` is checked. M2's order is allocation growth *and* typed-cell compatibility, and the store's own invariants are handler-preservation premises, not part of the protocol's monotone demand. |
| P1 §3: Straight is not one `sync` step | **Withdrawn** (F9; row 84 amended). Straight admits `bind` and `suspend`, which compile to continuation frames, and the driver's budget is independent of `preventYield` (the probe leaves a straight bind unfinished at fuel 1). A straight-first profile needs a proved sufficient budget, the fold `Agreement.steps` being the candidate bound the `tx` wrapper must supply, or row 80's contract. |
| P1 §4: the two predicate deletions | **Withdrawn** (F7). `ResumeOk` types the resume answer at the saved continuation's input, which is not the fiber's final type; `InterruptOnly` is provenance. Both stay; eleven predicates. The `Expect` pruning stands. |
| P1 §5: the store protocol must cover every `SyncOp` | **Accepted** (M3 amended in plan §14). `Ψ_S` is stated over `SyncOp`, internal operations included; `progress` is the adapter theorem for the public rows. |
| P2 §6: name coverage is not statement coverage | **Accepted** (T4 and M6 amended). The holder join is the inventory; a per-transition-shape adapter fixes each holder's full preservation type, with a weakened-statement control. |
| P2 §7: order world, protocol, predicate assembly | **Accepted** (plan §14 re-cut): M2 is the world's data, order and columns, `HeapNat` a specialization of the per-cell column; M3 the operation protocol and `TypedProg`; M3b the `Preds` instance and the stack assembly. |
| P2 §8: a parameterized stale placeholder vanishes from the ledger | **Fixed** in `src/Effect4/Laws/Auto/Obligations.lean`: a marker is recognized under binders, so a parameterized leftover is reported stale; control `Parameterized` in `Test/Audit/Obligations.lean`. The review's `Boundaries.lean` ledger line now fails as it should. |

What the review confirms stands: ProofGraph as the one evidence seam, the frames with the
field-set amendment, in-place generation and the named bank, completion data, `WakeList`, the
Ref kernel, and `Arena` as a law interface with the OCaml tests as finite host evidence.

## 10. The M1 specification review, addressed (2026-09-19)

`docs/research/2026-09-19-state-refinement-deep-dive-and-m1-specification.md` (another session,
22:12) rules on rows 84 and 85, resolves §8's placement questions and specifies M1 in six
steps. Every checkable claim was checked against the tree; the probes are recorded here, the
witness for the fuel claim is `FuelProbe.lean` in the session scratchpad (four programs,
`driveState` least fuel against `Agreement.steps` and the proved bound).

| claim | disposition |
| --- | --- |
| §1: the proof-shape ratchet counted `first` in `let some proof ← attemptProof … first \| return none` (`Laws/Auto/Census.lean:59`) as a tactic; renaming the binder cleared it | **Confirmed; the instrument rebuilt, not the binder renamed around it.** The gate's source scan (`Test/Audit/AxiomGate.lean`, `scanSource`) now parses each source as the compiler did: `Parser.parseCommand` under the frontend's scope (`Lean.Elab.Frontend.processCommand`), `namespace`/`section`/`end`/`open` elaborated so scoped syntax resolves, the token table of the source's own import closure (the whole audit environment's table refuses 32 of 450 sources — `daemon`, `eff`, `ceiling` are names in one module and keywords in another — which is why the earlier reading tokenized), the source's own tokens reserved as the commands declaring them are parsed, and the counted tactics read by syntax kind (`Lean.Parser.Tactic.first`, `simpAll`, `tacticTry_` and the `conv` twins). A binder, a pattern or a `do` block's `try` is not a node of those kinds, and a `first` whose next token is a splice is one: the token count over-counted `try` 7 → 4 in `Laws/Program/Decision.lean`, 35 → 14 in `Laws/Program/TypeAlgebra.lean` and 1 → 0 in `Program/FoldOf.lean`, `first` 4 → 0 in `TypeAlgebra`, 2 → 0 in `Laws/Machine/LiveStack.lean` and 3 → 2 in `Schema/Annotations.lean`, and under-counted `first` 11 → 14 in `Laws/Machine/Handles.lean` (three `first $[| …]*` in the `close_mem` macro, where the next token is `$[`). The ceilings are re-pinned to the exact counts: 668 over 91 sources, 0 below the ceiling (`lake build Test.All`, 652 jobs). The scanner reads the compiled environment, in which a `local` syntax declaration does not exist, so the gate refuses one by line and the tree's five `local macro` tactics (`DenoteR`, `ReferenceTyping`, `Codegen/Read`, `Schema/Check`) are `scoped`. The rename to `startLine` stays as the better name. |
| §2: `Agreement.steps` is not a driver budget (5 fuel for `succeed`, 8 for `bind`); a driver-level fold `c₁·steps + c₀` is needed; attempts at a frontier replay, never resume | **Confirmed, with the bound already in the tree.** Measured least `driveState` fuel: 5 for `succeed` (steps 0), 7 for `bind` (steps 2; the review says 8), 19 for three nested binds (14), 8 for `suspend bind` (3). The bound the review asks for is `straight_sufficient` / `TypedProgram.run_sound` (`Laws/Program/RuntimeR.lean:304`, `TypedRun.lean:85`): `depth e ≤ fuel ∧ 2·steps e + 6 ≤ fuel`, proved, and `Api.run` finishes at `max depth (2·steps + 6)` = 6, 10, 34, 12 for the four probes. Row 84 amended: the `tx` wrapper's budget is that bound, no new fold. The zombie fiber is the decision boundary's: `stepDecisionState` drops the command residue, `driveState` keeps it and the witness's own second half resumes it to the exit — row 80's "resumption contract retaining all necessary driver work" is exactly a contract at that level, so replay is one of row 80's options, not the only one; under the proved bound a straight body needs neither. |
| §3: row 85 as proposed; `Array → list` in the LCNF route; the OCaml store is native and property-tested against the Lean lists | **Confirmed.** `src/OCaml5/Lcnf/Types.lean:34`, `Translate.lean:241` (`Array.push` → `@ [x]`; the review's `:574-577` is `listFact?`), `ocaml/engine/e4_store.ml` (not `engine/src/`), `ocaml/engine/test/prop_store.ml` ST1–ST8 against `Stores.lean`'s list operations. The five law names are the review's proposal. Row 85 unchanged; the ruling is the owner's. |
| §4.1: fold connectors move under Laws | **Accepted with one constraint.** `Program/Typing/Agreement.lean` imports `Folds/Checker` and `Api.lean` imports `Typing/Agreement` for `explain_none_iff` (DI-86), so the API root reaches that connector. Nine of the ten move freely (their importers are the umbrella and Laws); `Folds/Checker` moves with the fold half of `Typing/Agreement`, the projection law staying. |
| §4.2: split `tools/Tools` around `src/OCaml5` | **Accepted.** The cheaper cut moves the five drivers up (`TsGen`, `Corpus`, `ForeignCorpus`, `Styles`, `ProgramStructureCheck`: 7 Makefile, 2 lakefile, 3 GENERATED.md, 3 script references) rather than the four descriptions down (22 import lines); the library keeps its name and its register row. |
| §4.3: `PositionGate` and the answer gate under `Typed/` | **Accepted, widened.** `TypedSources` reads `Typed/Vocabulary` and `TypedStateDecl` imports `TypedSources`, so all three typed-state instruments go under `Laws/Program/Typed/` with M3's answer gate; the generic instruments (`Positions`, `Census`, `Frames`, `Obligations`, `Exhaustive`, `Inversion`, `RuleSets`, `Traversals`) stay in `Laws/Auto`. |
| §4.4: bisect Store into `Carrier` and `Domain` | **Accepted** as the proposal. By imports the carrier half is `Val`, `Utf8`, `Digits`, `Image`, `Digest`, `Kind`, `Fold` (Store-only imports; `Machine/Value` reads `Image`); the domain half is `Node`, `Canonical`, `Word`, `Store`, `Traits`, `Genesis`, `Shape` (reads `Schema.Authoring`), `AnnotationsCanonical` (reads `Machine.Value`), `RowCanonical`, `Pin`, `PinDerived`, `Cascade`, `Folds/Val`. |
| §4.5: `Arch/JsonNumber` under `Effect4.Format`, `Arch/Accepts` beside Schema | **Amended.** There is no `Effect4.Format`. `JsonNumber` imports `Data.Json` and is read by `Schema/Codec` and `Store/Shape`, so its home is `Data/`; `Accepts` beside Schema; `Arch/` then goes. |
| §4.6: the one-file cross-imports | **Amended.** `Laws/Codegen/ModuleReadable` composes a Codegen law with the Api face (`Api.printModule`), so it is a `Laws/Api` module, not a new `Codegen.Syntax`; `OCaml5/Tools/CasGoldens` → `Test.Store.NodeContract` as listed; the review omits `Tools/RowTypes` (reads `Test.Api.AcquireHandleContract` and `Laws.Program.Template`). |
| §4.7: delete the two empty directories | **Done** (`src/Effect4/Program/Agreement`, `src/Effect4/Program/Simulation`); the map's audit is clean of them. |
| §5.1: the three type changes | **Accepted.** `Completion` derives `DecidableEq` (`Machine/Completion.lean:28`), `Owed κ` is parametric (`Machine/Wake.lean:97`), the instantiation `Completion Val Err Defect FiberId Ann` is already `Stores.lean:279`'s. `MemoEntry.effect` is the await program from `memoBuild` (`:2003`) until `memoComplete` writes the exit (`:2021`) and is read only for keys (`Laws/Machine/Handles.lean:747`): the stores map's "not read by execution" holds. |
| §5.2: DI-97 preserved; code minted at consumers | **Confirmed** (`Program/Native.lean:150`; `completionPrim` at `Stores.lean:1083`, `denoteCompletion` at `InterpR.lean:128`, `answerCode := denoteCompletion` at `:352`). One correction: `poll` answers `Option (Option Program)` (`:1115`), not `Option Bool`; after M1 it answers `Option (Option Completion)` and the sync row keeps `Val.bool slot.isSome` (`:1945`). |
| §5.3: the deletions | **Accepted, one corrected.** `DeferredOk`'s two conjuncts are both `CompletionShaped` (`Simulation/Hooks.lean:33-35`), so the whole predicate goes and `StoresOk` keeps `ScopeKeysFresh` alone; plan §14's "`DeferredOk.1`" is corrected. `denoteStored`'s five uses (`InterpR.lean:348,355,359`; `Simulation/Drive.lean:81,192`) go with it; `E4-STORES-CE-003` (`Test/Machine/Runtime/StoresLawsContract.lean:80`, `Test/Counterexamples/REGISTER.md:131`) is retired with `STORES-FB-COMPLETION`. |
| §5.4: six steps, six files, `make gen-lcnf` | **Amended: the radius is 38 files, measured.** Every file naming a deleted or retyped artifact: the six named plus `Guard/{RaceSites,FrameOwned,Core,NativeState,Settle}`, `Simulation/{Drive,Evaluate,Deliver,Actions}`, `Handles/Hooks`, `Laws/Run`, `Laws/Api/HostSession`, `Api/HostSession`, `Program/{Admit,Compile}`, `Laws/Machine/{Witnesses}`, `Laws/Program/{LayerSharing,Typed/Frames}`, `OCaml5/Lcnf/{Externs,Types}`, `OCaml5/Tools/CasGoldens`, seven Test files and the counterexample registers — the stores map's "about twenty" was itself low. Step 5 is three census rows, not two (`Sources.lean:59-61`, all `.column "PromiseTable"`): row 61 goes with the field, rows 59–60 keep their column over a `Completion` carrier, and `#position_gate`'s count lines and the `#typed_state` skeleton change with them, so T5's controls re-pin. There is no `make gen-lcnf`; the OCaml regeneration is the `lcnf` and `cas` groups of `docs/GENERATED.md`. The stores map's two conditions on the memo deletion (cell-based replacement witnesses; the representation connector, `docs/core/machine-state.md` §4) are not in the review and are part of the slice. |

What the review adds and stands: the driver-level reading of a budget (now named as the proved
bound), the `Straight`-only refusal at `tx` admission, the carrier/domain cut of Store, and the
order of M1's steps (types, denotation, laws, simulation, census, generation).
