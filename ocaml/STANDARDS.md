# Working standard for the OCaml lanes (2026-09-04, user ruling)

We are building reusable, library-level software, not one-off mega scripts. Every lane,
agent or human, follows this.

1. **Libraries first, drivers thin.** Reusable code lives in a dune `library` (OCaml) or a
   namespaced Lean module (`OCaml5.<Area>.<Module>`); executables and `--run` tools are thin
   drivers that parse arguments and call the library. No 600-line `main`.
2. **One component per file, one property list per component.** Each file opens with a
   header: what it is, what it depends on, and the behaviours it holds itself to (delivery,
   ordering, bounds, one-shot, termination under fuel), each marked `by construction` or
   `tested`, as `server/README.md` §0 does.
3. **Generated is generated.** Anything derived from Lean or from data carries a
   `GENERATED … do not edit` header and a rule (dune `rule`, or a documented command) that
   regenerates it. Hand-edited copies of generated things are not allowed.
4. **Names and layout.** snake_case files, `E4_`/`e4_` prefixes for daemon modules, `Lib/`
   carriers reused before new ones are written (`Deque`, `Map`, `Set`, `Sexp`, `Stream`,
   `Eio`, `Picos`). Representability: every OCaml construct we rely on has a Lean carrier or
   a refusal row (`docs/research/2026-09-04-ocaml-packages-plan.md` §4); no `Obj`, no
   `Marshal`, no polymorphic compare on abstract types.
5. **Tests beside code.** dune `test` stanzas or `%expect` tests where cheap; the corpus and
   witnesses as the differential; every claim in a report is backed by a command that
   reproduces it.
6. **Reports are precise and honest.** What changed (file:line), what was decided and why,
   what was measured (numbers in a table), what was not done and why. No claims without a
   run behind them.
7. **Build hygiene.** One `lean` process at a time, always `-M4096`; dune in WSL from the
   workspace root `ocaml`; never edit files another lane owns; never commit.
