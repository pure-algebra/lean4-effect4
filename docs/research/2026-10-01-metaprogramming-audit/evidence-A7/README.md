# A7 source import and use measurement

Base: `198dd5331eb6607e1e94f3abad39ebbda90c86dc`.

The retained script reads Git blobs at the exact base and writes only this temporary review directory. It does not run Lean, Lake, generators, or external-package code. The captured command exited 0 and its assertions reproduced the reported counts.

- `measure.py`: reproducible source-only census.
- `command.txt` and `run.log`: exact command and result.
- `summary.json`: counts, root boundaries, and explicit limitations.
- `project-modules.json`: all 475 module paths, base Git blob IDs, and SHA-256 hashes.
- `imports.json`: every measured import edge with its source path and line.
- `root-closures.json`: sorted project closure lists for `Effect4` and `Effect4.Laws`, plus external frontier names.
- `direct-lean-importers.json`: the five direct `src/Effect4` Lean importers with exact import locations and full direct/transitive dependent lists.
- `fold-sites.json`: all 62 `fold_of` sites in 13 Laws modules, with exact source lines.
- `sugar-dependents.json`: Sugar's five direct and twenty transitive project dependents, classified by roots.
- `authoring-block-sites.json`: zero source/tool block applications and 21 blocks in three explicitly named Test files; one of those is the existing intentional refusal control.
- `runtime-meta-sites.json`: runtime-reachable macro/syntax declarations, including `Codegen.Read.close_arm`, `daemon`, and `eff`.
- `obligation-command-sites.json`: source command-site lists and counts relevant to the cost of moving all metaprogramming out of the library.

## What the counts mean

The project graph contains tracked `.lean` files under `src/` and `tools/`. Root counts include the root itself: 135 project modules under `Effect4`, 351 under `Effect4.Laws`. Reverse dependent counts exclude the subject module and exclude Test and downstream applications. Direct `Lean` imports mean explicit imports of `Lean` or a `Lean.*` module, not proof that a declaration uses elaboration APIs.

External packages are **frontier nodes**, not traversed. For example, TypeScript, Hash, Std, Aesop, and Batteries are named where imported, but their internal import graphs are not read. Consequently, the simulated removal of the `Effect4 → Effect4.Program.FoldOf` edge yielding 134 project modules and zero direct project Lean importers does **not** establish a Lean-free full package closure.

The parser is a bounded lexical census that blanks nested comments and strings while preserving line numbers. It is not Lean's import parser and does not load `.olean` files. No compiler result, axiom gate result, rebuilt-module count, compilation time, or memory figure is claimed.

## Interpretation after the owner's DI-18 amendment

The owner has dropped the blanket import ban in favor of keeping program representations first-order. The measurements therefore support discretionary organization choices; they do not require a move or justify holding idiomatic parser API use. The earlier alternatives below describe costs, not the current requirement:

- Moving FoldOf into Laws would change 13 Laws import sites, remove one runtime-root import, and update its named audit admission. Its 62 command applications could keep their generated declaration names by preserving declaration namespaces.
- Moving all metaprograms to a generator root entails much more: 181 explicit obligation commands, 74 obligation-search/check commands, and 20 placeholder commands, plus census, tactic and authoring syntax APIs. Generated proofs and source provenance would need a design; this is not a file relocation.
- Sugar combines ordinary authoring functions and macro helpers. Splitting its syntax API need not force the five direct importers of its ordinary functions to import a tooling root. The first-order representation boundary is separate from where these build-time conveniences reside.

No architecture change has been made by this census.
