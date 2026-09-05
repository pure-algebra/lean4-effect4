/-
RenderDeep — print the generated block of one avatar part (`OCaml5.Avatar.parts`):

    lake env lean --run src/OCaml5/Tools/RenderDeep.lean stores|layer|context|forkflow|fibers

`ocaml/avatar/render-deep.sh` runs it and diffs the block against the one the avatar file
carries (`--write` replaces it). A thin driver: the descriptions are `OCaml5.Avatar.*`.
-/
import OCaml5.Avatar
open OCaml5.Ml

def main (args : List String) : IO Unit := do
  let name := args.getD 0 "stores"
  match OCaml5.Avatar.find? name with
  | some p => IO.println (moduleText p.generated)
  | none => throw (IO.userError s!"RenderDeep: no avatar part named {name}; \
the parts are {OCaml5.Avatar.parts.map (·.name)}")
