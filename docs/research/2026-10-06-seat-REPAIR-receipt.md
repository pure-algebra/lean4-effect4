# 2026-10-06 seat REPAIR receipt: the Queue's typing through the wrapper's rules, and two general statements in the lift module

Status: receipt (history, not authority). Brief:
`docs/research/2026-10-05-claude-lead/briefs/seat-repair-brief.md`, with the dispatch message
and the coordinator's two later messages (item 2).

**The one thing to know before merging:** `admittedReplay_true` has no statement in
`src/Effect4/Laws/Machine/MaskRuns.lean` any more. Its statement named the mask's invariant, so
it could not move byte for byte. The general statement is `Lift.admittedReplay_true`
(`src/Effect4/Laws/Machine/Lift.lean`), and the coordinator ruled the cut of the mask's copy.
So the brief's acceptance 1 holds for three names, and the fourth has nothing to compare.

Four more facts stand beside it.

- **`Waiter.Typed` served both forms with no change, and the answer form adds no premise.**
  `waitAnswer_answers` takes the module's part at the hint's type, and it answers that type.
  One helper stands beside it: `HintTy.canonical`, which the coordinator kept.
- **Three statements are unchanged**: `take_types`, `offer_types` and
  `flushRootState_maskRuns`. `git diff` shows each as context, and each elaborates to the type
  that it had at the base (tested).
- **One battery changed, on the coordinator's word.** `Test/Program/SemaphoreWrapper.lean`
  gains two axiom pins and one proved control. No battery of the Queue changed.
- **`generated/semantics.md` needs `make gen-semantics` again at step B's merge.** The
  coordinator regenerated it at step A's merge. Item 8 names what step B moves.

## 2. Base, head, commits and messages

Branch `seat/repair`, in the worktree `/Users/pooks/Dev/lean4-effect4-mask`. The base is
`ae082907`. The head is the commit that adds this receipt, and its parent is `8de7aa4b`.
Nothing is pushed. The coordinator merged step A on the main line as `1504ae65`. The main line
is at `42492024` as I write. `git merge-tree --write-tree` of the two heads reports no conflict
(tested). I ran no second merge, and I ran no gate of a merged tree. Outside `MaskRuns.lean`,
no file of the main line, of `seat/poolops` or of `seat/workq` names the cut name. One
`git grep` over `src`, `Test`, `tools` and `harness` tested it.

| Commit | Step | Content |
| --- | --- | --- |
| `09f34e1e` | A | `HintTy.canonical` and `waitAnswer_answers`; `take_types` and `offer_types` through the wrapper's two rules |
| `849cfe59` | B | `Lift.FoldLift.flushRootState_lift` and `Lift.admittedReplay_true`; the mask's copy cut; `flushRootState_maskRuns` as the instance |
| `8de7aa4b` | A | two axiom pins and one proved control in the wrapper's battery |

Message 1 rules part B's point 1: the general statement in `Lift.lean`, the mask's copy cut,
and `replayEval_maskRuns` at the general one. Message 2 keeps the helper, and it asks for the
two pins in section 4 of the wrapper's battery. The proved control is my addition.

## 3. Changed files

| File | What changed |
| --- | --- |
| `src/Effect4/Laws/Modules/Waiting.lean` | `HintTy.canonical` and `waitAnswer_answers`, directly after `waitRetry_answers`; one bullet of the typing header; nothing at the file's end |
| `src/Effect4/Laws/Modules/Queue/Ops.lean` | the proofs of `take_types` and `offer_types`; one paragraph of the typing header |
| `src/Effect4/Laws/Machine/Lift.lean` | `FoldLift.flushRootState_lift` after `FoldLift.flushAllState_lift`; `admittedReplay_true` after `replayEval_lift` |
| `src/Effect4/Laws/Machine/MaskRuns.lean` | `admittedReplay_true` cut; the proofs of `replayEval_maskRuns` and `flushRootState_maskRuns`; two docstrings |
| `Test/Program/SemaphoreWrapper.lean` | two axiom pins, one proved control, item 4 of the header |
| `docs/research/2026-10-06-seat-REPAIR-receipt.md` | this receipt |

I edited no file under `src/Effect4/Machine/`, no file of another seat and none of the
coordinator's six files. `Waiter.Typed` and each landed statement of `Waiting.lean` are as the
base has them.

## 4. Commands and results

`SLOT` is `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`. Each result is tested. A
scratch file is in the session's scratch folder, which no later session holds.

| Command | Result |
| --- | --- |
| `SLOT lake build`, at the base | `Build completed successfully (1026 jobs).`, with no gate line: Lake restored `Test.All` |
| `SLOT lake env lean -M6144 -DwarningAsError=true Test/All.lean`, at the base | exit 0, with the base's gate lines |
| `SLOT lake build Effect4.Laws.Modules.Waiting Effect4.Laws.Modules.Queue.Ops Effect4.Laws.Modules.Semaphore.Ops Effect4.Laws.Modules.Pool.Ops Effect4.Laws Test.Program.PoolSteps Test.Program.QueueOps Test.Program.SemaphoreWrapper`, at step A | `Build completed successfully (694 jobs).` |
| `SLOT lake build Effect4.Laws.Machine.Lift Effect4.Laws.Machine.MaskRuns Effect4.Laws.Machine.ForkLedgerInvariant Effect4.Laws.Program.Guard.Core Effect4.Laws.Machine.MaskBracket Effect4.Laws.Program.MaskRuns Test.Machine.MaskRuns Test.Program.GuardFoldLift Test.Counterexamples.Machine.Semantics.StaleCode Effect4.Laws.Program.Typed.Assembly`, at step B | `Build completed successfully (481 jobs).` |
| `SLOT lake build Effect4.Laws Test.Audit.ProofStyle Test.Program.SemaphoreWrapper`, at step B with the pins | `Build completed successfully (708 jobs).`; the ratchet reports no finding |
| `SLOT lake build`, at `8de7aa4b` | `Build completed successfully (1026 jobs).`, with the head's gate lines |
| `SLOT make -o build -o ts/eff/node_modules -o harness/truth/node_modules check-docs` | `PASS check-docs: every path, link, citation and make target in 76 documents resolves` |
| `python3 scripts/check-language.py --strict` on this receipt | `PASS`, no finding |

| Gate | The base `ae082907` | The head of the code `8de7aa4b` |
| --- | --- | --- |
| Library roots | 177 API and utility modules, 317 Laws-only modules | 177 and 317 |
| Modules and axioms | 776 modules and 90717 declarations | 776 modules and 90720 declarations |
| Planned goals | 24 goals; 11 declarations rest on goals | 24 goals; 11 declarations rest on goals |
| Proof style | not read at the base; at step A, 1911 recorded uses and 52 unread commands in 1161 entries | 1911 recorded uses and 52 unread commands in 1161 entries |

Each run of the axiom gate reads: "semantic/test axioms are [propext, Quot.sound]; exact
implementation boundary (17 module(s), 23 declaration(s)) additionally allows Classical.choice".

**Not run:** `make check-gen`, `make check-slow`, `make check-corpus`, `make check-target`,
`make check-truth`, the conservativity script and `make gen-semantics`, as the brief lists.
Also not run: `make check`, `make check-full`, `make check-semantics` and `make check-cases`.
No TypeScript compiler, no OCaml build and no host ran.

## 5. Axiom output, and the new statements

Each statement of this list is at `[propext, Quot.sound]` (tested: `#print axioms` in a scratch
file, and the axiom gate). The list: `HintTy.canonical`, `waitAnswer_answers`,
`Queue.take_types`, `Queue.offer_types`, `Lift.FoldLift.flushRootState_lift`,
`Lift.admittedReplay_true`, `flushRootState_maskRuns`, `replayEval_maskRuns` and
`runSyncExit_maskRuns`.

```lean
theorem HintTy.canonical {H : Ty} (hint : HintTy table H) : H.normalize = H

theorem waitAnswer_answers {w : Waiter} {s : TypedScope} {F : Ty}
    (hw : w.Typed table (s.push .restore Ty.maskRestore) w.hint F) :
    Answers (nativeSignature table) (waitAnswer w) s w.hint
```

`Lift.FoldLift.flushRootState_lift h fuel root` has the statement of
`FoldLift.flushAllState_lift`, at `flushRootState interp fuel root`.
`Lift.admittedReplay_true J interp fuel` has the mask's former statement, at every `J`, every
evaluator and every code type of the lift module.

## 6. The lines of each proof, before and after

One script counts the lines after each statement, in the base's text and in the head's.

| Proof | Base | Head |
| --- | --- | --- |
| `Queue.take_types` | 62 | 35 |
| `Queue.offer_types` | 38 | 32 |
| `flushRootState_maskRuns` | 18 | 3 |
| `admittedReplay_true` | 2, in `MaskRuns.lean` | 3, in `Lift.lean` |
| `replayEval_maskRuns` | 3 | 4 |
| `waitAnswer_answers`, `HintTy.canonical`, `Lift.FoldLift.flushRootState_lift` | — | 15, 5 and 16 |

Each of the Queue's two proofs is one application of a rule to the Queue's part. The part is
a structure literal of `Queue.take` and of `Queue.offer`, so each proof types it in place.
`flushRootState_maskRuns` is written as one alternative, so no line of its statement changes.

## 7. Evidence, choices and placement

- **Proved:** each theorem of item 5, at every row table, typed scope, invariant, fuel and tape
  that its statement names. Each rests on no planned goal.
- **Tested:** the pins, and the comparison of the elaborated statements at the base and at the
  head. No evidence is host-only. The bounded evidence is the pins and the scratch files.
- **The rule's form (tested: one scratch file holds three forms).** The general fact answers
  `Ty.join w.hint R` at any result type `R`, and the landed rule is its use at `R := w.hint`.
  The join of a type with itself is its normal form (`Ty.join_self`). The row check answers a
  normal form, and the await's row answers the hint's type: that is `HintTy.canonical`. A form
  with that fact as a premise compiles too.

| Statement | Concept; requirement; claim | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| `HintTy.canonical` | `store-typing`; R4; a step of `waiting-wrapper-typed` | every row table, and every type with a hint's three rows | that a type in normal form has the three rows | `waitAnswer_answers` |
| `waitAnswer_answers` | the same | the checker's judgment `effTy` at every typed scope, where the module's part is typed at the hint's type under the mask's saved state | a run; a law of the mask; a delivery of a wake | `Queue.offer_types` |
| `take_types`, `offer_types`, proved again | `store-typing`; R4 | unchanged | unchanged | `Api.Author.build` of a client |
| `Lift.FoldLift.flushRootState_lift` | `reactive-scheduling`; R11; a step of `saved-mask-chain-runs` | every invariant that a `FoldLift` carries, at every fuel, root and count of rounds | an invariant of its own; an invariant is not progress | `flushRootState_maskRuns`, then `runSyncExit_maskRuns` |
| `Lift.admittedReplay_true` | the same | every invariant, interpreter, evaluator, fuel and tape, where the lift asks no condition of a decision | a lift that asks one | `replayEval_maskRuns` |

## 8. Proposed text for the coordinator's files (proposals only)

- **`docs/core/semantics.md`, the property `waiting-wrapper-typed`.** After the sentence on the
  result type's normal form, add:

  > The wrapper with no loop answers its hint's type at every typed scope, when the module's
  > part is typed at that type (`waitAnswer_answers`). It asks no normal form of the hint's
  > type: a type with a hint's three rows is its own normal form (`HintTy.canonical`).

- **`tools/Tools/SemanticsRegistry.lean`, the title of `waiting-wrapper-typed`.** The pointer
  stays, and the users gain "the Queue's take and offer". After the clause on the withdrawal,
  add:

  > ; the wrapper with no loop answers its hint's type from the same part, with no premise on
  > that type (waitAnswer_answers, HintTy.canonical)

- **`generated/semantics.md` (reading: I did not run the producer).** Step B removes one tagged
  theorem of `MaskRuns.lean`, and it adds two theorems to the default module `Lift.lean`. The
  counts of the rows that rest on them may change.
- **`docs/STATE.md`.** The seat's entry gains its second part: the two general statements of
  `Lift.lean`, and the cut of the mask's copy of `admittedReplay_true`.

## 9. The requirements R1 to R13

The slice serves R4 and R11, and it closes no open part of either. R4 gains one rule and one
helper under the claim `waiting-wrapper-typed`, both proved. Two of its placed nodes are proved
again through the shared rules, with their statements unchanged. R11 gains two general
statements under `saved-mask-chain-runs`, and one of its steps becomes an instance. R4 and R11
keep their planned goals and their open parts as they are. R10 and R12 gain no theorem: the
slice states no run, no delivery and no budget. R1 to R3, R5 to R9 and R13 have no relation to
the slice. It changes no language signature, no data, no service, no host law, no face and no
journal. No planned goal is added, and none is closed.

## 10. Open obligations, and proposed decisions rows (proposals only)

No obligation of the brief's table is open. Two candidates stay, and no one has ruled them.

1. Three other statements walk `flushRootState` by hand (reading):
   `flushRootState_minted_of_evaluator` (`src/Effect4/Laws/Machine/Handles.lean`),
   `flushRoot_extends` (`src/Effect4/Laws/Machine/Approximation.lean`) and
   `book_flushRootState` (`src/Effect4/Laws/Machine/Book.lean`). None has a `FoldLift` today.
2. A name for each of the Queue's two parts would let the typing and the batteries share one
   text. `Test/Program/SemaphoreWrapper.lean` writes the taker's part again as `takePart`.

| Row | Proposal |
| --- | --- |
| 278, point 5 | Landed. `admittedReplay_true` is general in `Lift.lean`, and the mask's copy is cut. The lift of the root's flush is `Lift.FoldLift.flushRootState_lift` |
| 279, point 5, the first candidate | Landed. The two forms are typed over one structure, `Waiter.Typed`. A rule asks for the module's part, and for no fact that the part implies |
