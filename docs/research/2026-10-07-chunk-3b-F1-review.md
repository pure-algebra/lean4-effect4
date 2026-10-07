# 2026-10-07 chunk 3b, stage F1: the coordinator's review

Status: a research note (history, not authority). It is written for the implementer of stage
F2. The brief is `docs/research/2026-10-07-chunk-3b-brief.md`.

**Verdict: landed, with two repairs.** The seventeen cuts are right, the three guards turned
as the brief asked, and the hand-back came in its order.

## 1. What the landing changed

1. **A docstring named a concept where a claim belongs.** Thirteen docstrings said "a step of
   `subtyping-algebra`". That is a concept of `docs/core/semantics.md`. A helper names the
   claim that it is a step of (`AGENTS.md`, the placement rule). The claim is
   `template-match-complete`, and each docstring names it now.
2. **Seven docstrings named a reader that does not read the helper.** The hand-back gave
   `Bounds.matchB_sound` as the reader of five helpers. The environment gives other callers:
   `Bounds.below_args`, `Bounds.cands_below`, `Bounds.covers`, `Bounds.cands_args` and
   `Bounds.above_args`. The landing listed the direct callers of each helper with the script
   of the measure, and each docstring names them.
   *Rule: a reader in a docstring is a line of the measure's output, and no reading of a
   proof.*
3. **One more declaration had no caller after the cuts**: `Ty.anchoredFrom`. Its three callers
   were among the seventeen. The brief said that it stays, and the brief was wrong: the
   coordinator read the measure before the cuts. The landing cut it, so eighteen declarations
   are gone.
   *Rule: run the measure again after a cut, and read what joined the list.*
4. **Two pieces of prose named the retired premise** in
   `src/Effect4/Laws/Program/Template.lean`: a section head, and one sentence on its
   completeness. The landing rewrote both.

## 2. What stays in the list of the measure

The measure gives 25 declarations of the two modules with no caller chain from another module.
None served the retired claim. Fourteen are laws of `Template.lean` that are an end of their
own, and eleven are lemmas of `src/Effect4/Data/Constructive.lean`. The coordinator decides
about them at a later cleanup. Stage F2 leaves them.

## What this does not establish

- That each of the 25 has a use. The measure reads callers in proofs, and it sees no use by an
  attribute.
- No theorem of the tree. The stage removes text, and it changes docstrings.
