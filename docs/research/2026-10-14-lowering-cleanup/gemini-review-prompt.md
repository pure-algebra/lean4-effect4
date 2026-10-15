# Gemini: review the OCaml side of the lowering cleanup

## The one thing to know first

The owner wants your view of the OCaml side before the lowering cleanup runs. The owner ruled
(decisions row 391): the lowering carries no proof obligations for now. OCaml made from the
machine's Lean definitions through LCNF stands for the machine. The priorities:

- a clean, deep OCaml estate and Lean compiler code;
- faster code generation;
- focused tests that each catch a real fault;
- clean data structures;
- interop: the to-do in OCaml, the session from LCNF, a C face.

Review as a senior OCaml and compiler engineer. Give concrete, ranked recommendations, each
checked against the tree.

## Read first

- `AGENTS.md`, all of it.
- `docs/research/2026-10-14-lowering-cleanup/prompt.md`: the brief you review, slices LC-1 to
  LC-9.
- `docs/research/2026-10-14-lowering-collation/README.md`, §2.5, §3, §4, §6, §7 and §8: the
  evidence behind the brief.
- Decisions row 391, in `docs/core/decisions.md`.
- `ocaml/README.md`, `ocaml/STANDARDS.md`, `docs/core/lcnf-route.md` §8 and §9.

Then read the estate itself:
- `ocaml/engine/`: the hand modules, `externs.txt`, `tools/api_engine_prelude.ml`,
  `api_engine_inst.ml`, `api_engine_ref.ml`, `e4_program.ml`, the tests;
- the generated files: `ocaml/gen/*_gen.ml`, `ocaml/engine/api_engine.ml`, `ocaml/gen/roots.json`;
- `ocaml/eff/`, `ocaml/clock/`, `ocaml/tools/`, the dune files;
- `src/OCaml5/Ml/*.lean`, `src/OCaml5/Lcnf/*.lean`, `src/OCaml5/Tools/LcnfGen.lean`;
- the `Makefile` rules `gen-lcnf`, `check-compiler`, `check-native` and `check-ocaml`.

## The questions

1. **The estate's target shape.** After LC-9, the estate holds an engine and a session made from
   LCNF, thin host drivers and a C face. Are the libraries, the dune layout and the module
   boundaries right for that end? Give the target tree, and the moves from today's tree to it.
2. **The generated OCaml.** Judge `api_engine.ml` and `api_gen.ml` as OCaml: readability, run time
   and `ocamlopt` compile time. Which translator changes make the output idiomatic and faster?
   Examples: integer and list forms, `a @ [x]`, tail calls, match shapes, exceptions against
   results, standard library use. Rank them by effect, and measure where you can.
3. **The carriers and the extern seam** (finding N7, slice LC-8). Choose the OCaml data structures
   for the machine's families: the Ref arena, the ordered work, the trace, the views. Say how each
   meets its Lean interface: a functor, a first-class module, or plain code made from a Lean
   definition. Recommend one design.
4. **Focused tests** (slice LC-5). Which OCaml tests catch a fault that no other test catches?
   Describe the focused suite: goldens, property tests, the differential, lane S. Name what to
   cut.
5. **OCaml 5 and the host.** Give the host loop for the to-do face (LC-6). Say whether `e4_sched`
   and its modules suit the host that serves many sessions. Weigh effects, domains, Eio and a
   plain loop.
6. **Interop.** Weigh the C face over Lean's compiled library against the OCaml face, and
   js_of_ocaml and wasm_of_ocaml under node. Name a better byte boundary if there is one.
7. **The brief.** From the OCaml side, what is wrong, missing or misordered in LC-1 to LC-9? Give
   each edit as text the coordinator can apply.

## The rules

- Propose no proof, planned goal, validator or stage law (row 391).
- Report only material findings, with no wording or style notes.
- Every item of the brief is wanted, and its users are known. Never propose dropping or deferring
  one. Say what an item needs to reach its users.
- Check each claim against the tree. Cite a declaration or file by its name and path, never by a
  line number.
- Edit no source file. Write one file: `docs/research/2026-10-14-lowering-cleanup/gemini-review.md`.
- You may run read-only commands. Inside `ocaml/` you may also run
  `opam exec --switch=effect4 -- dune build` and `dune test`, sparingly.
- Run no `lake` and no `make`. Never write `2>/dev/null`.
- Commit only the review, by its path: `git add -f` it, then `git commit`. Do not push.

## The review's sections

1. The one thing to know first.
2. The estate's target shape and the moves to it.
3. The generated OCaml: findings, ranked, with measurements.
4. The carriers and the extern seam: the recommended design.
5. Focused tests: what to keep, what to cut.
6. OCaml 5 and the host.
7. Interop.
8. Edits to the brief, as text.

Stop when the review is committed.
