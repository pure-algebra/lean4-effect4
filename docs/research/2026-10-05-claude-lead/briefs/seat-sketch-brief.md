# 2026-10-06 brief for seat SKETCH: a program with its hole table

Status: a brief (history, not authority). One page. Base: the head that the dispatch message
names. It is stage 1 of the plan of the study of a gap with holes, and a groundwork slice of
R14 (decisions rows 282 and 288). The seat that wrote the study has it.

## The slice

The study's section 9.7, "Slice SKETCH", is this brief's body
(`docs/research/2026-10-06-seat-GAP-study.md`). Its files, its four statements, its controls and
its placement table stand as written. This page adds what the coordinator ratified and the
rules of a code seat.

**The goal.** A sketch is data: a program with its hole table. A hole is a host row with a
declared type, and the hole table is appended after the row table. The checker admits a sketch
modulo its holes. The four theorems say that this language is a conservative extension of ours,
and they are the scratch proofs of the study's section 5.7, landed as theorems of the tree.

## What is ratified (row 288)

- The hole table stands beside the row table. `Row` and the wire stay as they are.
- A hole declares three columns by default: an answer, an error and a requirement.
- The words: sketch, hole, hole row, hole table, omit, "admitted modulo its holes". Propose
  each dictionary entry in the receipt, with the anchor that this slice lands. The coordinator
  enters them at the merge.
- No constructor of `Eff`, `Term` or `Ty` is added, and no rule of `HasTy`.

## Additions to the study's brief

1. **A design note first, half a page** (`docs/research/2026-10-06-seat-SKETCH-design.md`): the
   types as Lean elaborates them, and three decisions with their reasons.
   - What `Sketch` holds, and what its check answers. A program with an empty hole table is a
     program: say how the type shows it.
   - How a hole is named. A position in the table shifts when an earlier hole is filled, and a
     row has a name (the study's section 9.8). Choose, and state what an edit keeps.
   - The request of a hole row: a unit, or the tuple of the variables in scope (the same
     section). Choose for this slice, and say what the other choice would change.
   Send the note's path and the statements, and go on.
2. **Organization.** One core module with a head comment that a reader new to the work
   understands: what a sketch is, the parallel with a planned goal and where it stops (the
   study's section 10.3). One law module. One battery. No definition that this slice's
   statements or controls do not use.
3. **Lean's own tools, as a design input.** The parallel with `proof_goal` is exact enough to
   ask it: could a term-level notation write a hole in an authored program, and the elaborator
   collect the hole table? Write the answer in the design note. Implement it only if the
   battery's controls already pay for it.
4. **Root anchors.** In `src/Effect4/Laws.lean`, directly after
   `import Effect4.Laws.Program.Signature`. In `Test/All.lean`, directly after
   `import Test.Program.SignatureControls`. In `src/Effect4.lean`, directly after
   `import Effect4.Program.Typing.Blame`. Other seats use other anchors.
5. Tag each theorem with its concept and `(requirement := R14)`, as the study's table places it.

**Not in this slice:** the replacement law (the next slice, REPLACE, which you take when this
one is handed back); a gap; a term hole; a run of a sketch; any change of `Row`, `Eff`, `Ty`,
`Term`, the checker or the wire tags.

## The rules

- A new core module opens with `module`, `public import` and `@[expose] public section`
  (decisions row 200), unless one of its imports is a specialization site of row 202: say so.
- Do not edit `docs/core/decisions.md`, `docs/STATE.md`, `lakefile.toml`,
  `generated/semantics.md`, `docs/core/semantics.md`, `docs/core/controlled-english.md` or
  `tools/Tools/SemanticsRegistry.lean`. Propose their text in the receipt: each claim's row and
  title, each required property, each dictionary entry, the architecture rows.
- No `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`. No
  `simp_all`, `first` or `try`. A hand `simp` is `simp only [...]`. Every warning is an error.
  A planned goal is allowed only for a statement of the study's table, and none stays open at
  the hand-back unless the receipt names its missing fact first.
- The shell's rules are in the dispatch message.

## Acceptance, and the receipt

Each landed statement is a theorem at `[propext, Quot.sound]`. The controls pass, each red one
red for its stated reason. Run narrow builds after each step. Run the default `lake build` once
at the end, with the gate lines, then `make gen-fixtures`, `make check-cases` and
`make check-docs`. Not run, and listed so: `check-gen`, `check-slow`, `check-corpus`,
`check-target`, `check-truth`, the conservativity script, `gen-semantics`, `gen-architecture`.

The receipt is `docs/research/2026-10-06-seat-SKETCH-receipt.md`, in the handoff form of
`AGENTS.md`: the one thing to know before merging; base, head and commits; changed files;
commands with results; the statements as compiled, with axioms and plan status; the proposed
texts. One paragraph accounts for R1 to R14. Your last message gives the head, the receipt's
path and its first item.
