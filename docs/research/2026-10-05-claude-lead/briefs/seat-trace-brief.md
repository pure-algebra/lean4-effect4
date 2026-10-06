# 2026-10-06 brief for seat TRACE: the type at each address, and every refusal in one pass

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is stage 3 of the plan of the study of a gap with holes (decisions rows 282, 288).
The owner brought it forward on 2026-10-06 (row 292, point 2).

## The slice

The checker answers one type for a whole program, or its first located refusal. Three
consumers need more than that, and they need the same thing: **the environment and the type at
each address of a program**.

- **The TypeScript printer.** A converted eliminator at a proper union needs its type arguments
  written at the join, or tsgo refuses the printed call
  (`docs/research/2026-10-06-uniform-eliminators-landing-probe.md`). The printer reads no type
  today. A guard keeps the checker's refusal at a proper union until it does (row 292).
- **A tool at a hole**: what stands at this address, in which environment, at which type.
- **A slice view**: member provenance checks a program once and then walks down with the types.

The study's section 9.7, "Slice TRACE", is this brief's body
(`docs/research/2026-10-06-seat-GAP-study.md`), with its section 9.4 on what is generic. It has
two halves, and they land in this order.

1. **The traced check**: a second algebra beside the checker's, which keeps the environment
   and the type of each address. Its result is the checker's (`traced_check`), and each kept
   pair is a typing of the sub-program at that address (`focusAt_typed`).
2. **Total marking**: a checker that goes on past a local refusal and answers every refusal.
   Its first mark is `explain`'s refusal (`mark_first`), and it has no mark exactly where the
   program is admitted (`mark_none_iff`).

Hand back after the first half, with its receipt, and go on with the second on the same branch.

## Additions to the study's brief

1. **A design note first, one page** (`docs/research/2026-10-06-seat-TRACE-design.md`):
   - The traced check as one generic function over an algebra, not a second checker written by
     hand: the study names `EffAlgebra.ofLayer` and `ArgF` (`src/Effect4/Program/LayerView.lean`)
     and a function `EffAlgebra.traced`. Say what it is as Lean elaborates it, and whether it
     serves every fold of the program syntax or the checker's alone.
   - The agreement theorem as a fusion (`hom_eq_cata_eff`, or the monadic fold's naturality),
     with no induction of its own.
   - What the trace holds at a term address. The printer needs the type of an eliminator's
     scrutinee, which is a term. Say whether the trace keeps term types, or the environment
     alone with `termTy` run again, and what each costs.
   - The trace's size for a program of `n` addresses, and what a tool reads from it in one step.
   Send the note's path and the statements, and go on.
2. **Organization.** One core module for each half, each with a head comment that a reader new
   to the work understands. One law module for each. No definition without a statement or a
   control that uses it.
3. **A check of the first consumer, in the battery**: for one program with a join of two fiber
   types under a `join`, the trace answers the scrutinee's type with its two members. The
   checker refuses that program today (`notFiber`), so state the control at the address above
   the refusal, or on a program of the same shape that is admitted (two list types under
   `length`). Do not print anything: the printer's change is a later slice.
4. **Root anchors.** In `src/Effect4/Laws.lean`, directly after
   `import Effect4.Laws.Program.Typing.Check`. In `Test/All.lean`, directly after
   `import Test.Program.BlameContract`. In `src/Effect4.lean`, directly after
   `import Effect4.Program.Typing.Agreement`.
5. Tag each theorem `@[semantics "initial-algebras-folds" (requirement := R14)]`.

**Not in this slice:** any change of `Checker.check`, of `explain` or of a refusal; the printer;
a gap; a term hole; the conversion of an eliminator; a type slice view.

## The rules

- Three other seats edit near you. Seat UNION writes `Record.fieldType` through a combinator
  (equal by `rfl`). Seat FORM adds a clause to `Formation.HeadFormed`. Seat SKETCH proves the
  replacement law over `HasTy`. Read none of their branches. If a proof must look inside the
  field read, use `change` to its explicit shape, not `unfold` then `rw`.
- A new core module opens with `module`, `public import` and `@[expose] public section`
  (decisions row 200), unless one of its imports is a specialization site of row 202: say so.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md`, `docs/core/controlled-english.md` or
  `tools/Tools/SemanticsRegistry.lean`. Propose their text in the receipt.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
  State each theorem as a planned goal, placed, and prove it in place. No planned goal stays
  open at a hand-back unless the receipt names its missing fact first.
- The dictionary forbids "partial program", "placeholder", "stub" and "todo". A program with
  holes is a sketch.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]`. The controls pass, each red one
red for its stated reason. Run narrow builds after each step. Run the default `lake build` once
before each hand-back, with the gate lines, then `make gen-fixtures`, `make check-cases` and
`make check-docs`. Not run, and listed so: `check-gen`, `check-slow`, `check-corpus`,
`check-target`, `check-truth`, the conservativity script, `gen-semantics`, `gen-architecture`.

The receipt of the first half is `docs/research/2026-10-06-seat-TRACE-receipt.md`, in the
handoff form of `AGENTS.md`: the one thing to know before merging; base, head and commits;
changed files; commands with results; the statements as compiled, with axioms and plan status;
**what the printer reads from the trace at an eliminator**, as the next slice's input; the
proposed registry and dictionary texts. One paragraph accounts for R1 to R14. Your last
message gives the head, the receipt's path and its first item.
