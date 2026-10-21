import Compiler.Groups

/-!
# Compiler.Exe — `lake exe effect4`, the compiler over the tree's own groups

The compiler's command line (`Compiler.mainOver`) over the groups of `Compiler.Groups`: `check`,
`emit`, `describe` and `inspect` over `--group corpus`, `--group sql` and `--group todo`, and `run`
over `--group todo`, the group with a host. Its module closure and the declared names of its keys
are this module's elaboration's (`Compiler.Elaborated`).
-/

def main (args : List String) : IO UInt32 :=
  Compiler.mainOver Compiler.Groups.all args
