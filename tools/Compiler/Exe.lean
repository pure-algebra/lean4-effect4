import Compiler.Main
import Test.Dogfood.Scenario.Todo.Data

/-!
# Compiler.Exe — `lake exe effect4`, the compiler over the tree's own groups

    lake exe effect4 check --group NAME [--json]
    lake exe effect4 emit --group NAME --target ts [--out DIR] [--emit=KIND,…]
    lake exe effect4 describe --group NAME --target ts [--out DIR] [--emit=KIND,…]

The compiler's command line (`Compiler.mainOver`) over the tree's groups, imported statically as a
project's executable imports its application (decision E1; the entry point's second slice,
`docs/research/2026-10-20-compiler-entry/README.md`). Two groups stand here:

- `corpus`, the wire corpus (`Effect4.Program.Wire.Corpus.all`): eight programs, each admitted at
  the empty application. `emit --group corpus` writes each program's files under its name, the
  prelude's import closure once, and one manifest (`Compiler.emitGroup`).
- `todo`, the dogfood to-do (`Test.Dogfood.Scenario.Todo.application`): one application, emitted
  as a project's executable emits its own (`Compiler.emitTs`).
-/

/-- The tree's groups, by name: the wire corpus and the dogfood to-do. -/
def groups : List Compiler.Source :=
  [.programs "corpus" Effect4.Program.Wire.Corpus.all,
   .application Test.Dogfood.Scenario.Todo.application]

def main (args : List String) : IO UInt32 :=
  Compiler.mainOver groups args
