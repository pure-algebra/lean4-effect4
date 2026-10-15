# Working standard for the OCaml estate (2026-09-04, user ruling; restated 2026-10-15)

The estate is reusable, library-level software, not one-off scripts. Every lane, agent or
person, follows four rules. `AGENTS.md` summarizes the same four.

1. **Libraries first, drivers thin.** Reusable code lives in a dune `library` (OCaml) or a
   namespaced Lean module (`OCaml5.<Area>.<Module>`). An executable or a `--run` tool is a thin
   driver that parses its arguments and calls the library. Files are snake case, and an engine
   module carries the `E4_` prefix. No program uses `Obj`, `Marshal` or polymorphic comparison
   on an abstract type.
2. **One component per file, a property list at its head.** Each file opens with a header.
   The header says what the file is, what it depends on, and the behaviours it holds itself to.
   Such behaviours are delivery, ordering, bounds, one-shot and termination under fuel. Each
   behaviour is marked `by construction` or `tested`, and a tested one names its test. Tests
   live beside their code, in a dune `test` stanza.
3. **Generated is generated.** A file derived from Lean or from data carries a
   `GENERATED … do not edit` header and the rule or the documented command that regenerates
   it (`docs/GENERATED.md`). No hand edit of a generated file is allowed. The OCaml made from
   LCNF is the machine; hand OCaml under `ocaml/engine` is host code or a carrier that LCNF-made
   code replaces (decisions row 391).
4. **Every number in a report behind a command.** A report says what changed, what was
   decided and why, what was measured and what was not done. It cites a declaration by its name
   and its path (`docs/core/controlled-english.md`, rule W25), and each number has the command
   that reproduces it.

Building follows `ocaml/README.md`: dune through `opam exec --switch=effect4`, one Lean process
at a time, and commits by the rules of `AGENTS.md`.
