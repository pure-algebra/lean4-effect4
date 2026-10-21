import Compiler.Groups

/-!
# Compiler.Exe — `lake exe effect4`, the compiler over the tree's own groups

The compiler's command line (`Compiler.mainOver`) over the groups of `Compiler.Groups`: `check`,
`emit` and `describe` over `--group corpus` and `--group todo`, and `run` over `--group todo`, the
group with a host.
-/

def main (args : List String) : IO UInt32 :=
  Compiler.mainOver Compiler.Groups.all args
