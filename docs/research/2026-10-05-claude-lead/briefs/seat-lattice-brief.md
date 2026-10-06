# 2026-10-06 brief for seat LATTICE: the generic theory of slices

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is the first groundwork slice of R14 (decisions row 282): the owner authorized the
type slicing line and the gap with holes as first-class work on 2026-10-06, with no
shortcut.

## The slice

The paper "Bidirectional Type Slicing" proves that every type query has a minimal slice, that
a one-step descent finds one, that refining a query shrinks a minimal slice, and that slices
are closed under joins (its Theorems 4.5, 4.6 and 4.7, pages 9 to 12). Each proof uses two
facts only: the slices of one program are a finite lattice, and the map from a slice to its
type is monotone. **State and prove those consequences once, for any such map.** No
statement of the module names `Eff`, `Ty` or the checker. Every later slice view, under
candidate A, N or G, is then an instance that owes its monotonicity and nothing else.

## Read first

1. `AGENTS.md`, in full.
2. The plan `docs/research/2026-10-06-type-slicing-plan.md`, sections 2, 4.2 and 6, and its
   sketch `Sliced`.
3. The paper's pages 7 to 12, and its page 23 for the meet that is not preserved
   (`/Users/pooks/Dev/lean4-effect4/vendor/papers/program-graphs/bidirectional-type-slicing-2607.12197v1.pdf`).
   Take each statement from its page.
4. How the tree states an order today: `Ty.sub` and its laws (`src/Effect4/Program/Ty.lean`),
   the world's order (`src/Effect4/Laws/Program/Typed/World.lean`), the path orders of
   `src/Effect4/Program/Refs.lean`. The tree has no Mathlib: the module states the order
   that it needs.

## The assignment

1. **A design note first** (`docs/research/2026-10-06-seat-LATTICE-design.md`): the
   interface as Lean elaborates it. Decide these, each with its reason:
   - how the module asks for a finite lattice of slices with no Mathlib: a carrier with a
     decidable order and a list of all its elements, or a concrete carrier of masks (a set
     of folded addresses of one tree, ordered by what is kept). The paper's own carrier is
     the lower set of a term under precision, and a mask is its image for a derived view;
   - what the type side needs: a preorder is enough for validity; a join is needed for
     Theorem 4.7 only;
   - that a query is valid for a slice when the slice's type is at or above the query, and
     that an exact slice need not exist (the paper's Counterexample 4.2).
   Send its path and the statements, and go on.
2. **State each consequence as a planned goal, placed, and prove it in place**: validity is
   upward closed; a minimal valid slice exists below each valid slice (4.5); the one-step
   descent, as an executable function, ends at a minimal valid slice, with its termination
   and its cost in calls of the check; a refined query has a minimal slice below a minimal
   slice of the wider query (4.6); the join of two valid slices is valid for the join of
   their queries (4.7), and so the join of all minimal slices is valid: the contribution
   slice.
3. **The descent is a real function**, and its choice is fixed: among the slices one step
   below, it takes the first in a stated order, so two runs give one answer. State that it
   returns one minimal slice and not the smallest: a minimum-size slice is NP-hard in the
   paper's calculus (its section 10).
4. **Controls** in a battery (`Test/Program/SliceLattice.lean`): an instance over a small
   tree with a monotone toy check. Render the paper's two examples in it: the four
   incomparable minimal slices of its page 18, and the two slices of its page 23 whose meet
   loses the type. Red controls: a check that is not monotone, on which the descent stops
   at a slice that is not minimal; and a query above the full type, which no slice serves.
5. **Think about speed and about Lean's own tools, and write it down.** The descent as
   written costs one check for each step and each candidate. Say what an instance could
   give to make it cheaper (a check of a slice from the check of its neighbour), and whether
   a decision procedure or a tactic of Lean serves a finite instance. Implement nothing of
   it that has no consumer; file the note for the slice that has one.

**Not in this slice:** any instance at `Eff`; a mask of a real program; the sliced check;
graduality of the checker; the structural calculus of the paper's section 8.

## Placement

| Statement | Concept; requirement | Reach | It does not establish | Consumer |
| --- | --- | --- | --- | --- |
| Each consequence above | `subtyping-algebra`; R14, the proposed claim `slice-lattice-minimal` | every monotone map from a finite lattice of slices to a preorder of types | that any real check is monotone; a least slice; a minimum-size slice | each slice view: error and requirement provenance first (the plan's slice 4) |
| The descent's law | the same | the same, with a decidable validity | a bound better than the stated one | the same |

## The files, and the rules

- New files: one law module, `src/Effect4/Laws/Slice/Lattice.lean`, with any executable
  definition that a tool will call in a core module beside it only if the design note shows
  that the `Effect4` root needs it; and `Test/Program/SliceLattice.lean`. Root anchors: at
  the end of the imports of `src/Effect4/Laws.lean`, and after the last `Test.Program`
  import of `Test/All.lean`.
- Tag each theorem `@[semantics "subtyping-algebra" (requirement := R14)]`. R14 is in the
  registry since the base.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md` or `tools/Tools/SemanticsRegistry.lean`.
  Propose their text in the receipt: the claim's row and title, and the required property.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an
  error. A planned goal is allowed only for a statement of the table, and none stays open at
  the hand-back unless the receipt names its missing fact first.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]`. The controls pass, each red
one red for its stated reason. Narrow builds after each step; the default `lake build` once
at the end, with the gate lines; `make check-docs`. Not run, and listed so: `check-gen`,
`check-slow`, `check-corpus`, `check-target`, `check-truth`, the conservativity script,
`gen-semantics`.

The receipt is `docs/research/2026-10-06-seat-LATTICE-receipt.md`, in the handoff form of
`AGENTS.md`: the one thing to know before merging; base, head and commits; changed files;
commands with results; the statements as compiled, with axioms and plan status; what an
instance owes; the note on speed; the proposed registry text. One paragraph accounts for R1
to R14. Your last message gives the head, the receipt's path and its first item.
