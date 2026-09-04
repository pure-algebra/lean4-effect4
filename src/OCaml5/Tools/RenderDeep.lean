/-
Seat W1's render driver: `OCaml5.Ml.Deep.*` → the generated carrier block of one avatar
module. Run through `render-deep.sh`, which also diffs the result against the block the
avatar file carries, exactly as `tools/fuzz.sh avatar` diffs `deep_fibers.ml`.

Not a lake module: `ocaml/avatar` is not a `srcDir` of any `lean_lib`
(`lakefile.toml`), so this file is only ever run with `lake env lean --run`.
-/
import OCaml5.Render
open OCaml5.Ml

def main (args : List String) : IO Unit := do
  match args.getD 0 "stores" with
  | "stores" => IO.println (moduleText Deep.Stores.generated)
  | "layer" => IO.println (moduleText Deep.Layer.generated)
  | "context" => IO.println (moduleText Deep.Context.generated)
  | "forkflow" => IO.println (moduleText Deep.ForkFlow.generated)
  | other => throw (IO.userError s!"seat W1: no description set named {other}")
