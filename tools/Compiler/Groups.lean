import Compiler.Main
import Test.Dogfood.Scenario.Todo.HostLane

/-!
# Compiler.Groups — the tree's own groups, which `lake exe effect4` runs over

    lake exe effect4 check --group NAME [--json]
    lake exe effect4 emit --group NAME --target ts [--out DIR] [--emit=KIND,…]
    lake exe effect4 describe --group NAME --target ts [--out DIR] [--emit=KIND,…]
    lake exe effect4 run --group todo [--text | --typed | --json] [--script FILE] [--budget N]

The compiler's command line (`Compiler.mainOver`) over the tree's groups, imported statically as a
project's executable imports its application (decision E1; the entry point's second slice,
`docs/research/2026-10-20-compiler-entry/README.md`). The executable is `Compiler.Exe`; the
groups stand here, so the battery `Test/Codegen/CompilerEmit.lean` reads what it runs.

- `corpus`, the wire corpus (`Effect4.Program.Wire.Corpus.all`): eight programs, each admitted at
  the empty application. `emit --group corpus` writes each program's files under its name, the
  prelude's import closure once, and one manifest (`Compiler.emitGroup`). It has no host, so
  `run` refuses it, as a usage error.
- `todo`, the dogfood to-do (`Test.Dogfood.Scenario.Todo.application`): one application, emitted
  as a project's executable emits its own (`Compiler.emitTs`), and run over its reference
  repository on the host lane's script (`todoHosted`, `todoScript`).
-/

namespace Compiler.Groups

open Test.Dogfood.Scenario.Todo in
/-- The dogfood to-do's host as `run` takes it: the reference repository (`repository`), from no
to-do (`HostLane.start`), its state shown as the host lane shows it (`Host.repoVal`). -/
def todoHosted : Hosted :=
  { σ := Repo, initial := HostLane.start, reactor := repository, view := Host.repoVal }

/-- The host lane's script (`Test.Dogfood.Scenario.Todo.HostLane.script`) as requests, each
argument a literal (`Tools.RunChecks.literal`); empty when an argument is none. -/
def todoScript : List Request :=
  ((Test.Dogfood.Scenario.Todo.HostLane.script.mapM fun (entry, args) =>
    (args.mapM Tools.RunChecks.literal).map fun lits => ⟨entry, lits⟩ : Option (List Request))).getD []

/-- **The tree's groups**, by name: the wire corpus, and the dogfood to-do with its host and its
script. -/
def all : List Source :=
  [.programs "corpus" Effect4.Program.Wire.Corpus.all,
   .application Test.Dogfood.Scenario.Todo.application (some todoHosted) todoScript]

end Compiler.Groups
