# 2026-10-07 chunk 3: the coordinator's review at the landing

Status: a research note (history, not authority). It is written for the implementer of the next
chunk. Decisions row 306. The brief is `docs/research/2026-10-07-chunk-3-brief.md`, and the
probe of stage E3 is `docs/research/2026-10-07-tests-by-order-probe.md`.

**Verdict: landed, with five small repairs.** The chunk kept the rules of its brief, and it is
much better than chunk 2.

- Stages E1 and E2 are commits. Stage E3 stopped before its commit, and the hand-back says why
  first.
- Each changed line of a contract battery stands first in the hand-back, with its old form.
- The probe came before the rule changed, with one evidence file for each form.
- Each refusal keeps its reason, and `hasTy_extSlotEnv` keeps its statement.
- The chunk removes 1,127 lines of the sources net (`git diff --shortstat` against chunk 2).

## 1. What the landing changed, and the rule behind each

1. **A registry claim pointed at a removed theorem.** Stage E1 removed
   `Ty.matchTemplate_complete_anchored`. The claim `template-match-anchored` kept that name as
   its pointer (`tools/Tools/SemanticsRegistry.lean`), and `docs/core/semantics.md` kept its
   paragraph. A pointer is a name literal, so the build does not see it. The landing retired
   the claim and its paragraph. The brief did not name the claim: that omission is the
   coordinator's.
   *Rule: when a theorem goes, search the semantics registry and the authority documents for its
   name,
   and list each hit in the hand-back.*
2. **Four guards pinned a list of bindings with repeated entries**
   (`Test/Program/TypeAlgebraContract.lean`). `Bounds.solve` enters a parameter once for each
   of its candidates, so the list `[(0, .string), (0, .string), …]` is an accident of the walk.
   The guards now read the binding by `lookup`, as the checker does.
   *Rule: a guard reads what a caller reads. It pins no shape that no caller sees.*
3. **One green control was no raw union** (`Test/Program/TypingCheckContract.lean`). The
   second control of `catchIf` tested the literal `true`. It now tests a slot of the type
   `.union .bool .never`, and the red control tests a slot of the type `.string`.
4. **Two compiler lines tested a plain Boolean** (`harness/truth/term-rows.typecheck.ts`).
   The green lines of `catchIf` and of `iterate` now hold a function that answers `never`.
   tsgo 7.0.0-dev.20260629.1 accepts both.

5. **One row of the corpus index moved, and the receipt reported none.** The program g85 is
   `Effect.catchIf(body, (a0) => a0, handler)`, and its body cannot fail. So the test has the
   type `never`, and the converted test accepts it. The checker refused g85 at the root with
   `predicateNotBool`. It refuses it now at the address `1.0`, with the same reason. That
   address is the test `7` of an inner loop. tsgo reports its one error there (TS2322). So the move is right, and
   it is the first corpus program that a converted test reads differently. The landing named
   the row in the compatibility policy and promoted the two generated tables.
   *Rule: after a change of a checker rule, run `make corpus` and read
   `git diff generated/corpus-index.tsv`. The corpus check compares verdicts, and it does not
   see an address.*

The receipt held two more statements that the tree does not hold. It counts 56 placements, and the
file holds 68 theorems with 68 tags. It calls the bindings of `Bounds.matchB` deduplicated, and
they are not.

## 2. What the coordinator checked

- **Every changed file under `Test/`, in full**, against chunk 2: four batteries and one
  fixture.
- **The three core files, line by line.** Eleven tests changed, and nothing else. Nine rules of
  `HasTy` state the premise in the form of the brief.
- **The printed form of `restore`.** The probe tests `pipe(body, saved)`. That is the form
  that the printer writes (`src/Effect4/Codegen/Templates.lean`, decisions row 245).
- **The case policy.** The site of `Ty.infer` is gone, and the 22 hand notes stand.
- **The wide gates**, with the differential of the two corpora against chunk 2. Section 4 has
  the list.

## 3. What the landing hands on

1. **The helpers of the retired claim.** Sixteen lines of docstrings name `template-match-anchored` as
   the claim that their theorem is a step of (`src/Effect4/Laws/Program/Template.lean`,
   `src/Effect4/Data/Constructive.lean`). Some of them have a caller in the laws of the match
   by bounds, and some may have none. `Ty.anchored` and `Ty.bottomFree` have no caller outside
   their file. The next chunk measures the callers of each, from the environment and not from
   the text. It names the claim that a live helper serves now, and it cuts each other one.
2. **Three guards read the helpers of item 1** (`Test/Program/TypeAlgebraContract.lean`:
   `anchored` once and `bottomFree` twice). They go with the helpers.
3. **The typed print is next**, after the coordinator's design note. The interim guard at a
   binder term stands until it lands.

## 4. The gates of the landing

The coordinator ran them on the working tree of stage E3, with its repairs. The base of the
differential is chunk 2. Twenty gates ran. Seventeen passed at once.

- `make check-docs` failed where this note was not yet written, and it passes with the note.
- `make check-conservativity` refused the move of g85, and it passes with the policy's name.
- `make check-tsdiag` asked for the promotion of its table, and it passes after
  `make gen-tsdiag`.

The commit message of the landing holds the result of each gate.

## What this does not establish

- No theorem of the tree. The review is a reading of a diff and a run of gates.
- That each helper of item 1 of section 3 is dead. The count needs the environment.
- That tsgo accepts a form that the probe did not print. The probe covers the eleven tests at
  `never` and at a raw union.
