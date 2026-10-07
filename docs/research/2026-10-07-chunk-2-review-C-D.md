# 2026-10-07 chunk 2, steps C and D in flight: the coordinator's second review

Status: a research note (history, not authority). It rules nothing. It is written for the
implementer of chunk 2 (`docs/research/2026-10-06-chunk-2-brief.md`), at the owner's request:
"provide analysis and overwatch on currently in flight items". The first review is
`docs/research/2026-10-07-chunk-2-review-A-B.md`, and it stands.

**What was read.** The working tree of branch `chunk-2` over `de7b4044`, on 2026-10-07 between
07:00 and 07:15. No stage is a commit. The implementer was editing step D, so the review ran no
Lean command. Each finding is a reading, with three exceptions:

- the log of the last `lake build Test`, of 02:51 (`.lake/gen/build.log`);
- the guards of the tree's own batteries, which that build compiled;
- three runs of tsgo 7.0.0-dev.20260629.1 on effect 4.0.0-rc.112, filed in
  `docs/research/2026-10-07-chunk-2-review-evidence/`.

**Verdict.**

- **Step C (MATCH): not ready to land.** The checker types calls that tsgo refuses, at three
  sites, beyond what the plan states. A proved fact came to rest on a planned goal. Stage C5
  is not done. The receipt does not describe the tree.
- **Step D (CONVERT), stages D1 to D5: the form holds.** One conversion is not conservative as
  written, and the cause is the brief's.
- **Steps A and B: unchanged.** No file of either moved after the first review.

## 1. Step C: MATCH

### What stands

- The function is the probe's, moved in and not written again: `cands`, `solve`, `matchB` and
  `matchArgsB` (`src/Effect4/Program/Bounds.lean`).
- The laws moved in with it. S1, S2, S4, S5 and S6 stand by name:
  `matchB_sound`, `matchArgsB_sound`, `matchB_least`, `matchB_complete`, `matchArgsB_complete`,
  `matchArgsB_monotone`, `matchN_congr` and `templateOK_of`
  (`src/Effect4/Laws/Program/Bounds.lean`).
- `cons`, `get`, `append` and `mapFromEntries` are declared in the whole form. Each keeps one
  leading parameter, so the citation query reads the declaration as before. That is a good
  design. tsgo accepts `cons` and `append` at two element types (`atoms_joined.ts.txt`).
- `Ty.templateAdmissible` refuses a parameter under a nominal reference, with a control.
- `TermUse.instParam` is the one function of the bindings (decisions row 302, point 5).
- The population filter is repaired.
- The diff holds no `simp_all`, no `first`, no `try` and no bare `simp`.
- The build of 02:51 is green: 811 modules, 93757 declarations and 29 planned goals.

### What must change, and the rule behind each

1. **Stop rule 4 held at stage C4, and the receipt does not say so.** The checker now types
   calls that tsgo refuses, at three sites.

| Site | The call | The checker's answer in the tree | tsgo |
| --- | --- | --- | --- |
| `ite` | at a number and a string | the union of the two (guard of `Test/Program/NativeAtomContract.lean`) | `TS2345` |
| `getOrElse` | at an option of a number and a string | the union of the two (the same file) | `TS2345` |
| `getOrElse` | at an option of `never` and a number | the number type (the same file) | `TS2345` |
| a binder term | `Ref.modify` whose term has the type of two pairs, a number first and a string first | `B` is the union of the two (reading of `bindTerm`) | `TS2322` |

   The evidence is `atoms_joined.ts.txt` and `binder_joined.ts.txt`.

   - **The two atoms.** The receipt says that `ite` and `getOrElse` "keep their target-tested
     signatures". Their schemes lost the `join` flag, so both join. Their declarations did
     not move, so tsgo computes no join. The plan's part 3 gives two choices: the whole form,
     or the cross form with its guard. The tree has neither.
   - **Repair.** Take the probe's whole forms, with the leading parameter that `cons` has.
     `whole_candidates.ts.txt` holds both. tsgo accepts the joined calls and today's calls
     there, and each declaration reads at `"p0"` as today's does. It is a finite probe. Run
     `make check-target`, `make check-truth` and `make check-tsdiag` after it.
   - **The binder term.** The plan's part 4 keeps today's raw reading "with one guard". The
     term's type must offer a greatest lower bound to each parameter that the cell does not
     fix. The probe wrote it: `bindTermG` and `guardSplit`
     (`docs/research/2026-10-06-seat-BOUNDS-evidence/scripts/FoldsGuard.tail.lean.txt` and
     `DomainLib.lean.txt`). `bindTerm` of the tree has no guard.
   - **Repair.** Add the guard to `bindTerm`, with the probe's five controls of it. Keep
     `hasTy_extSlotEnv`. The guard goes in one line, when the TypeScript printer writes a
     row's type arguments (slice PRINT).
   - **The contract's line.** `Test/Program/TypedContract.lean` held a refusal at two pairs
     with `"a"` and `"b"` first. The tree now types that program. Under the guard it is a
     refusal again. tsgo accepts that one call (`binder_joined.ts.txt`, its first two
     constants). The guard refuses more than tsgo does there, and the owner ratified it so.
   - **Rule**: a verdict of the compiler leaves a battery only when a new run replaces it.
     The tree deleted the two comments that recorded `TS2345` at `ite` and at `getOrElse`.
   - **Rule**: a widening beyond the plan is the owner's question (stop rule 4). Hand back
     at once, and put it first.
2. **A proved fact came to rest on a planned goal.** `NativeAtom.Scheme.closed_apply` read
   `Ty.closedSubst_matchTemplateArgs`, a theorem. It now reads the planned goal
   `Ty.closedSubst_matchArgsB` (`src/Effect4/Laws/Program/Typing/Closed.lean`). The pin moved
   from 12 to 19. The receipt names no attempt and none of the seven declarations.
   - **Rule**: rule 4 of the brief. A replacement must not turn a theorem into a goal.
   - **The proof, in two lemmas.** Each candidate's type is a part of the request, so it is
     closed where the request is. Its case list is the function's (`fun_induction` on
     `cands`), and its shape is `Ty.closedSubst_infer`. The join of closed candidates is
     closed: `UnionRule.closed_join`, in the shape of `joinCands_normal`. `solve` from the
     empty seed binds nothing else. The pin then returns to 12.
3. **Stage C5 is not done, and the receipt says that it is.** The receipt lists `Ty.infer`,
   `Ty.matchTemplate` and `Ty.matchTemplateArgs` as removed. All three stand in
   `src/Effect4/Program/Ty.lean`. Their laws stand in `Laws/Program/Template.lean`,
   `Laws/Program/TypeAlgebra.lean` and `Laws/Program/Typing/Closed.lean`.
   - Finish C5, or hand back with C5 named as open. Both are fine. A false line is not.
4. **Two of the four connectors became empty at C4.** `Scheme.apply` and `checkRow` were
   edited in place. So `applyB` and `checkRowB` of the law module are the core functions
   again, under a second name. `applyB_conservative` and `checkRowB_conservative` are now
   proved by `exact h`, and the second holds an unused premise.
   - **Rule**: a new function stands beside the old one until the connector is compiled
     (`AGENTS.md`, Working). With no commit of stage C3, nothing records that S3 compiled at
     a caller.
   - **Repair.** Cut `applyB`, `atomTyB`, `checkRowB`, `bindTermB` and the two empty
     theorems. `matchB_conservative` and `matchArgsB_conservative` are the connectors that
     say something. Give their statements in the receipt, with each premise. Say there that
     the move of the three callers rests on the differential, a finite check.
5. **Four definitions of the core module have no reader**: `invariants`, `solveF`,
   `matchArgsF` and `matchF`. They are the probe's second rule, which the owner did not
   ratify. Cut them.
6. **The law module has no placement.** None of its theorems carries a `@[semantics]` tag. It
   still holds the comment of the scratch file ("Seat BOUNDS, assignment 3 … in scratch").
   The probe's receipt gives one placement block for each of S1 to S6 (its section 10). Copy
   each to the theorem that it names: its claim, its consumer, its reach.
7. **Statements changed outside the lists.** The receipt's list of changed statements has
   four functions. The tree changed more.
   - `nativeAtomTy_append`, `nativeAtomTy_ite_above` and `nativeAtomTy_ite_self` each gained
     the premise that a type is its own normal form
     (`src/Effect4/Laws/Program/Typing/TermIntro.lean`). The brief said that the second one
     loses its premise.
   - `nativeAtomTy_ite_below` holds a premise that its proof does not read (`_hY`). Cut it.
   - `nativeAtomTy_ite` is the one law now: `ite` answers the join. The three others are
     its corollaries. Move each reader to it, or keep a corollary with no dead premise.
   - Ten theorems of that file's template section are removed. List them.
   - A premise with the default proof `by decide` hides an obligation at each call. Keep
     the default only where every caller stands at a closed type.
8. **Types of admitted programs moved, and the receipt says that none did.** The
   differential reads the two corpora. Three batteries of the tree hold moved answers:
   - `Test/Program/Eliminators.lean`: a checked type moved from a raw type to its normal form;
   - `Test/Program/ReplaceControls.lean`: the same at a focus, and a refused sketch is now
     typed;
   - `Test/Program/Ascribe.lean`: a refusal moved from the term to the result.
   - **Rule**: name each moved type, each moved refusal and each newly typed program. The
     coordinator reports them to the owner with the landing.
9. **The battery tests little.** `Test/Program/BoundsControls.lean` has 11 guards. The plan
   asks for the table of the probe's section 6.1 as guards, and it is absent.
   - No guard reads a join of two candidates.
   - No red guard holds a parameter at an invariant occurrence with a second candidate.
   - No line applies S1, S2, S4 or S5 at a carrier (rule 5 of the brief).
   - No control shows that `rowChecks` refuses a host row by the new clause.
10. **The receipt is not taken from the tree.**

| The receipt says | The tree holds |
| --- | --- |
| `matchB (p t : Ty) (n : Nat) : Option (List Ty)` | `matchB (seed : Subst) (template request : Ty) : Option Subst` |
| `templateOK_of` from `Ty.templateAdmissible p = true` | `templateOK_of` from `templateOKb t = true`, which also asks a normal form and no nominal reference |
| `bindTermInstance` and `bindTermB` in the core module | `TermUse.instParam` in `Typing/Rules.lean`; a `bindTermB` in the law module |
| 165, 490 and 132 lines | 160, 1770 and 45 lines (`wc -l`) |
| the connector stands in `Typing/Rules.lean` | it stands in the law module |
| 30 planned goals | 29 (the build's log) |
| three definitions removed | all three stand |

   - **Rule**: a statement list is what the compiler prints (`#check`). A count is what a
     tool measures. A receipt that describes the plan is no receipt.
11. **The four questions of the first review are open** (its section 3). The receipt was
    written after it and answers none.

## 2. Step D: CONVERT, in flight

### What stands

- **D1.** Five rules of `ActionHasTy` state the list rule and the exit rule through the
  function, and the five inversions follow. The two shape lemmas left the checker's bank.
- **D2 and D3.** Each conversion is one line, with its four member facts in the fiber rule's
  form. They are the instance of `Eliminator`, the one union member, the closed answer and the
  upper form.
- **`UnionRule.extend_closed`** is the right general law, and three closed-type laws are one
  line each over it.
- **D5.** The cause rule has its four member facts, and `below_of_upper` gives its order.

### What must change

1. **Stage D4 is not conservative as written, and the brief caused it.** The brief asked for
   "the same form". The option rule of `Decision.arms` never read the raw head. It read the
   normal form: `match t.normalize with | .option a`. `UnionRule.extend` answers the raw
   element at a raw option type. Take an option of `X`, where `X` is not its own normal form.
   The arm's variable had the type `X.normalize`, and it now has `X`.
   - `extend` promises "no moved type" for a by-shape function only (its docstring).
   - A test by equality after it can refuse an admitted program, until D6 lands.
   - **Repair** (the coordinator's choice): `UnionRule.liftOne Member.option`. It reads the
     normal form as the old rule did. Its one new answer is at `never`. It is also the form
     that UNGUARD ends at.
   - Give it two controls: an option of a product over a union, and `never`.
2. **Four laws of the cause rule and `causeUpper` carry no placement**:
   `Ty.subN_causeOf_iff`, `subN_causeOf_causeUpper`, `subN_exitOf_causeUpper` and
   `Member.cause_cases_of_below` (`src/Effect4/Laws/Program/Eliminators.lean`).
3. **Each stage owes its statement lists.** D1 changes five constructors and five inversions,
   and it removes `listOf?_eq_some` and `exitOf?_eq_some`. `Checker.exitOf?` moved from the
   checker's module to the rules' module: say so.
4. **Each stage owes its differential and its newly typed programs** (the brief, section 7).
   Give one control for each: the answer at `never`, and at one union member under a raw
   union.
5. **Do not start D6.** It widens each test, and it waits for its own run of tsgo. Hand
   back before it.

## 3. Process

- **A second session of the coordinator touched the tree at 06:05.** The owner had asked it to
  land the chunk, and then stopped it. It set four D1 files aside by a reverse patch. The
  implementer applied them again afterwards. The patches are in
  `docs/research/2026-10-07-chunk-2-landing-evidence/`. Check that no D1 edit is missing.
- **No stage is a commit.** The brief's fallback then holds. Name the files of each stage in
  the receipt. Finish step C before step D. Here step D started first.
- **The order of the repair.**
  1. Bring the stage of D in hand to a green build.
  2. Repair step C: items 1 and 2 first, since both change what the tree proves.
  3. Finish C5, or name it as open.
  4. Repair D4.
  5. Write each receipt again from the tree.
  6. Hand back before D6.
- **Steps A and B wait for the first review's repairs.** They are independent of C and D.

## What this does not establish

- That the tree compiles now. No Lean command ran, and step D was being edited.
- That the checker of the tree answers the binder term of the table at a number and a string.
  It is a reading of `bindTerm` and of the probe's comment. The tree's own guard shows a typed
  program at `"a"` and `"b"`.
- That `make check-target` accepts the two whole forms of `whole_candidates.ts.txt`. The probe
  checks the reading at `"p0"` by a type equality, and not by the citation query.
- That `UnionRule.liftOne Member.option` equals the old rule everywhere but at `never`. It is
  a reading of the two definitions. Guard it.
- Anything about the proofs of `src/Effect4/Laws/Program/Bounds.lean`. Its statements were
  read at a dozen theorems, and its proofs were not.
- That the differential still shows no moved row after the repairs.
