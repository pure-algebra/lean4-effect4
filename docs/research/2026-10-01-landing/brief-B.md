# Seat B brief: frames closed under world growth, posts that the handlers fulfil, the walk

Written 2026-10-01 by the coordinator. Base: `bb269fde` on `refactor/phase1-phase3`. Worktree
`/Users/pooks/Dev/lean4-effect4-seat-B`, branch `seat/B` (created; `.lake` current). Read
`docs/research/2026-10-01-landing/plan.md` (§0 items 2 and 4, §2, §4) and decisions rows 87, 106,
117, 133, 135, 136, 137 first. The pass's material: `docs/research/2026-10-01-formal-pass/algebra/`
(`note.md` A1, §2.6; `verify.md` §1 and "what the seat missed" 1–5; `probes/P2KripkeTyping.lean`,
`verify-StepLoop.lean`, `verify-WrapWalk.lean`) and `.../proofs/` (`note.md` G2, G6, §4;
`verify.md` items 4 and 8, `CONF-1`; `probes/{FrameCategory,StorePostAdequacy,AwaitValuePost,
CloseScopePost,PostScout}.lean`, `verify-probes/VerifyPosts.lean`). The main checkout holds them;
read by absolute path; never edit or build there.

**The one thing.** Two statement defects block every M6 proof: the saved-stack judgment is typed
at one world, so a step that allocates breaks it (`M6Ledger.step_loop` is false at a concrete
typed state; `E4-TYPED-CE-012`), and six protocol posts contradict what the machine answers, one
of them making M5 false on the typed corpus's own `awaitFiber.value` (`E4-TYPED-CE-010`, `-013`).
You own `src/Effect4/Laws/Program/Typed/{Contracts,Stack,Residual,Frames}.lean` and their
batteries. Seat A owns `Membership.lean`, `TypeAlgebra.lean`, `Typed.lean`, `World.lean`,
`Program/Admission.lean`; seat C owns `Assembly.lean`, `Sources.lean`, `Scheduler.lean`,
`State.lean`, `TypedStateDecl.lean`, `Laws/Machine/Lift.lean`. Do not edit theirs; write the
exact lines they need in your receipt. Statements only for the eighteen command goals: this seat
proves no `step_*`.

## The work, in order

1. **Re-establish the counterexamples on this tree** as batteries under `Test/Program/` (imported
   from `Test/All.lean` beside `TypedStack`): `FramesNotKripke.lean` from `P2KripkeTyping.lean`
   and `verify-StepLoop.lean` (`stackAccepts_not_mono`, `step_loop_refuted`, `step_loop_good`,
   `evaluate_keeps`, `bad_not_kripke_initial`), `ProtocolPosts.lean` from `StorePostAdequacy`,
   `AwaitValuePost`, `CloseScopePost` and `VerifyPosts` (every `*_post_excludes`,
   `store_step_leaves_typing`, `await_code_refused`, `close_code_refused`, the `memoRelease`,
   `refModify` and `closeIter` controls, the frontier-arm control). Commit red. After steps 2–4
   these become historical controls under local copies of the old definitions (as
   `ValueMembership.lean` does), and the positive forms are proved beside them.
2. **Row 135: the Kripke closure.** In `Contracts.lean`, `FrameAccepts`'s `run`/`skip` arms and
   its three hook premises quantify over later worlds (`∀ w' ≥ w, ∀ ex, ExitOk w' … ex → …`, the
   shape `TypedProg`'s continuations already use, `Residual.lean:189-216`, and the vocabulary's
   `continuation` source, `Vocabulary.lean:31-32`); in `Residual.lean`, `IteratorProtocol.step.next`,
   `LoopProtocol.step.next` and `frameProtocols.asyncFinalizer`'s cancellation clause close over
   later worlds in their definitions, with their `resume`/`continue` tails at the answer's world
   (wrapping at the frame is refuted by `verify-WrapWalk.lean`'s `output_not_kripke`; keep it as a
   red control). Keep the names: the closed judgment replaces the one-world one, and
   `stackAcceptsK_now`-style lemmas give today's judgment at the current world so existing users
   (`popR_typed`, `saveAnswerR_typed`, `deliver_active`, `deliver_stale`) are restated with Kripke
   premises and conclusions rather than duplicated. Prove `frameAccepts_mono`,
   `stackAccepts_mono`, `savedOk_mono` (the last may need `SavedOk`'s shape from `Sources.lean`:
   if so, state it on the unfolded shape and give seat C the one-line declaration), and land
   `typedProg_mono` (proved in `P2KripkeTyping.lean`: `storePre_mono`, `fiberPre_mono`,
   `envTyped_mono`, `pointTyped_mono`, `bodyTyped_mono`, `asyncPre_mono`) so that
   `M3bWorld.typedProg_mono` closes; declare `savedOk_mono` and `stackAccepts_mono` as `M3bWorld`
   goals if they are not provable here and say why. The frame category laws
   (`stackAccepts_append`, `_split`, `_id`, `_push`, `FrameCategory.lean`) land in `Contracts.lean`
   under the closed judgment. `HookLaws` and the walk (`Stack.lean:253-289`) are restated over
   Kripke stacks; `hookLaws_interpR` is re-proved (the verifier says "reading, not probed": it is
   your proof to finish or to report exactly).
3. **Row 136: the posts.** In `Residual.lean`: the await-by-value post at
   `∃ ty, w'.Γ target = some ty ∧ Fits w' ans (.exitOf ty.answer ty.error)` (the checker's rule,
   `Program/Checker.lean:196`; row 106's token rule); the close-scope post and `closeIter`'s post at
   "a success or a clean failure" (`Scope.close` answers `void`; `InterpR.lean:166-169`; the
   verifier's `closeSeq_done`, `closeIter_post_excludes`); `scopeRemove` and
   `deferredAwaitCleanup` at `ans = Val.unit`; `scopeAdd` at `ans = Val.unit ∨ ∃ ex, ans =
   reifyExitVal ex ∧ FitsExit w' ⟨unknown, unknown, ∅⟩ ex`; `refModify`/`refModifySome`'s pre
   strengthened so the `nat` post is adequate (`Residual.lean:41-43`); `memoRelease`'s post at the
   machine's answer; the frontier arm (store frontiers answer `unit` while the scope rows' pre is
   `True`: give the scope rows a pre carrying scope liveness, which row 139 needs anyway). For each
   row, a positive control: the machine's actual answer satisfies the post on the sample store
   (`PostScout.lean` lists them). Then the generic adequacy statement: in `Laws/Effects/Protocol.lean`
   is seat E's (it lands `Typed.inr`/`Typed.refine` there); you declare `Implements` beside the
   protocol tables in `Residual.lean` (or a new `Laws/Program/Typed/Adequacy.lean`): "if
   `syncOpStep op st = some (st', ans)` and `storePre w op cert` (and the world conditions), then
   `∃ w' ≥ w, storePost w' op cert ans`", one per store row through `syncOpStep`, and the fiber-row
   analogue through the `FiberAction` helpers, as `#proof_wanted` goals in a new ledger scope
   `M3bAdequacy` (the proofs are wave 2); prove the ones that are a few lines (the store rows whose
   answers you just fixed are candidates) and leave the rest declared.
4. **TY-16 `fiber_inv`** beside `guard_inv` in `Residual.lean` (proved in
   `types/M5CounterProbe.lean`); `guard_inv`'s docstring "exactly" corrected (algebra verify, stale
   texts). **Row 137's entries in your files**: after seat A's `Ty.subN` lands (watch the main
   checkout's `refactor/phase1-phase3` for the merge of `seat/A`; until then use
   `sub (normalize a) (normalize b)` inline), `asyncPre`'s deferred arm, `fiberPre`'s
   `awaitAll`/`raceAll` and the completion entries compare in the checker's order.
5. **The red controls flip**: every `*_post_excludes` becomes `*_post_admits` on the real answer;
   `step_loop_good` stays green; `stackAccepts_not_mono` is retained on the local old judgment
   and `stackAccepts_mono` is proved on the new one.

## Checks

Per step: `LEAN_NUM_THREADS=4 lake build` of the touched module and its direct dependents
(`Assembly.lean`, `Scheduler.lean` and the batteries import yours: build them; if seat C's
`Assembly.lean` breaks on your change, repair it minimally there, list the hunk for seat C, and
do not otherwise edit it); the batteries by `lake env lean -DwarningAsError=true`; `#print axioms`
for every theorem landed; `#auto_census` on `Residual` and `Stack` before rewriting any proof
against a bank. At the end `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` once; `make
check-cases` if you added a match on a policy family. No generator.

## Receipt

`docs/research/2026-10-01-landing/receipt-B.md` (force-added): the one thing first; base and
head; every changed path; per step the statements with old and new text, the theorems (name,
file:line, axioms), the controls (red retained, positive proved); the exact hunks for seats A and
C; the lines for rows 87, 106, 117, 135, 136, 137; what is owed (the adequacy instances left
declared, with their count).

## Amendments (2026-10-01, after the synthesis and the owner's ratification; these win over the text above)

1. **Step 1 uses the tracked ports** at `ports-at-dceae006/`: `HeadStepLoop.lean`,
   `HeadKripkeWalk.lean`, `HeadTypedProgMono.lean`, `HeadStorePostAdequacy.lean`,
   `HeadCloseScopePost.lean`, `HeadAwaitValuePost.lean`, `HeadVerifyPosts.lean`, with their axiom
   logs. Copy from them; do not re-port.
2. **Row 136, made exact:** the close-scope and `closeIter` posts are
   `ExitOk w' (EffTy.pure .unit) ans`; `refModify`/`refModifySome`'s pre is at the native row's
   declared cell type; `memoRelease`'s post is what the store answers (the last release answers the
   layer's scope handle).
3. **Step 4's "completion entries" are not this seat's files:** `World.lean:81` is seat A's and
   `Assembly.lean:40` is seat C's. With `fits_normalize` available, `Residual.lean`'s
   derivation-chosen certificates (`asyncPre`'s deferred arm, `fiberPre`'s `awaitAll`/`raceAll`)
   need not change: review them and record the verdict.
4. **Plan §5 (Codex's observation):** the generic handler-adequacy theorem is proved, not only
   declared, and instantiated at least for the rows whose posts this seat fixes and for
   await-by-value; the remaining instances stay declared as `M3bAdequacy` goals for wave 2. The
   receipt reports which per-row arguments the generic theorem replaced and how many instances
   remain open.
5. Row 137 is ruled (a). Seats E (`a561d604`) and F (`efcf1ae2`) are merged on
   `refactor/phase1-phase3`; E's `Laws/Program/Typed/Seq.lean` imports `Residual.lean`, so the
   coordinator re-checks it at this seat's merge.
