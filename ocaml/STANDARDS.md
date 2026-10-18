# Working standard for the OCaml estate (2026-09-04, user ruling; second edition 2026-10-17)

The estate is reusable, library-level software, not one-off scripts. Every lane, agent or
person, follows nine rules. The first four govern form, and the other five govern how code
models meaning. `AGENTS.md` summarizes them. The second edition adds rules 5 to 9 from the
refactor plan (`docs/research/2026-10-17-ocaml-estate-review/plan.md`, §2).

## Form

1. **Libraries first, drivers thin.** Reusable code lives in a dune `library` (OCaml) or a
   namespaced Lean module (`OCaml5.<Area>.<Module>`). An executable or a `--run` tool is a thin
   driver that parses its arguments and calls the library. Files are snake case, and an engine
   module carries the `E4_` prefix. No program uses `Obj` or `Marshal`.
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

## Modeling

5. **Interfaces once, and small.** Every library module has an `.mli`; a module without one
   gains it when it next changes. Two kinds need none: an `_intf.ml`, and a module that only
   applies a functor whose result an interface already checks (`api_engine_inst.ml`). A module type is
   written once, in an `_intf.ml` that the `.ml` and the `.mli` include. A public interface
   holds the roots its callers use; helpers stay hidden. A value that exists only after a check
   has an abstract or `private` type, made only by its checker. A checked package is abstract as
   a whole, so no caller can update one field and keep the others' certificate.
6. **A refusal is a value.** A domain error is a typed `result`, never an exception that
   escapes and never a status that reads as success. A function that raises on an ordinary
   input ends in `_exn`. A decoder answers `option` or `result`. `Or_error` serves only a caller
   that needs diagnostic text. Fuel exhaustion and an unanswered call are live frontiers, never
   errors. A host's exception is no answer: it is never turned into a typed failure. An error
   path carries `[@inline never] [@local never] [@specialise never]`.
7. **Numbers are exact, and comparison is by type.** A Lean `Nat` or `Int` is exact (Zarith)
   wherever it carries meaning. A bounded `int` appears only with a stated domain and a checked
   conversion. Its name states the conversion's class: `_exn` refuses, `_trunc` truncates,
   `_wrap` wraps. Each type compares through its own `equal` and `compare`. Polymorphic
   comparison serves `int`, `char`, `bool` and `string` only. `tools/typed_lint` checks this
   on each hand library's typed tree under `dune test`; a generated unit is skipped. A string
   length says whether it counts bytes or scalars.
8. **Mutation behind pure interfaces.** Mutable state is a choice of implementation, never of
   meaning. An implementation may mutate where speed needs it, under three conditions. Its
   interface's meaning is a pure function in the Lean model. One owner holds the state at a
   time, inside an owned builder. To share or to snapshot, the owner freezes it to a value,
   deeply, so every retained snapshot and sibling keeps its observations after later updates.
9. **Outside libraries by contract.** Jane Street's libraries (Base first) are welcome in hand
   and generated code. Each use is qualified, never a blanket `open Base`. In generated code,
   each operation enters through the target-library catalogue (`OCaml5.Lcnf.Builtins`) with its
   contract and its consumer. A ppx enters a build only with its measured cost. An Incremental
   callback never raises: it returns a refusal as a value and does no input or output.

Generated code holds two more checks. Each LCNF join point is `let[@local always]`, and
warning 55 is an error, so a jump that cannot be static fails the build. Each check's red control
sits beside its positive case.

Building follows `ocaml/README.md`: dune through `opam exec --switch=effect4`, one Lean process
at a time, and commits by the rules of `AGENTS.md`.
