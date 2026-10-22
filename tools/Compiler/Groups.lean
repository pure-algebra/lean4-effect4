import Compiler.Main
import Test.Dogfood.Scenario.Todo.HostLane
import Test.Api.PackagesContract

/-!
# Compiler.Groups — the tree's own groups, which `lake exe effect4` runs over

    lake exe effect4 check --group NAME [--json]
    lake exe effect4 emit --group NAME [--target ts|ocaml] [--check] [--out DIR] [--emit=KIND,…]
    lake exe effect4 describe --group NAME [--target ts|ocaml] [--out DIR] [--emit=KIND,…] [--pretty]
    lake exe effect4 inspect --group NAME --what types|rows|surface|graph|manifest [--json]

The compiler's command line (`Compiler.mainOver`) over the tree's groups, imported statically as a
project's executable imports its application (decision E1; the entry point's second slice,
`docs/research/2026-10-20-compiler-entry/README.md`). The executable is `Compiler.Exe`; the
groups stand here, so the battery `Test/Codegen/CompilerEmit.lean` reads what it runs.

- `corpus`, the wire corpus (`Effect4.Program.Wire.Corpus.all`): eight programs, each admitted at
  the empty application. `emit --group corpus` writes each program's files under its name, the
  prelude's files its modules reach once, and one manifest (`Compiler.emitGroup`). No module of
  it has a SQL row, so the folder imports `effect` alone.
- `sql`, the SQLite package's programs (`Test.Api.PackagesContract.sqlitePrograms`): the truth
  corpus's five, each admitted at the package's table (`Packages.sqliteBun`). Each module imports
  `Sql` from the prelude's adapter (`Compiler.adapters`), which the folder copies, so the folder
  imports `@effect/sql-sqlite-bun` too.
- `todo`, the dogfood to-do (`Test.Dogfood.Scenario.Todo.application`): one application, emitted
  as a project's executable emits its own (`Compiler.emitTs`), with the native roots of its host
  lane (`todoLowered`).
-/

namespace Compiler.Groups

/-- The dogfood host's native roots, named once for the compiler. -/
def todoLowered : Lowered :=
  { imports := [`Test.Dogfood.Scenario.Todo.HostLane]
    roots := [`Test.Dogfood.Scenario.Todo.repository,
      `Test.Dogfood.Scenario.Todo.HostLane.start, `Test.Dogfood.Scenario.Todo.HostLane.script,
      `Test.Dogfood.Scenario.Todo.Host.serveBuiltVal, `Test.Dogfood.Scenario.Todo.Host.resultVal] }

/-- **The tree's groups**, by name: the wire corpus, the SQLite package's programs at its table,
and the dogfood to-do with its native roots. -/
def all : List Source :=
  [.programs "corpus" Effect4.Program.Wire.Corpus.all,
   .programs "sql" Test.Api.PackagesContract.sqlitePrograms { rows := Effect4.Program.Packages.sqliteBun },
   .application Test.Dogfood.Scenario.Todo.application todoLowered]

end Compiler.Groups
