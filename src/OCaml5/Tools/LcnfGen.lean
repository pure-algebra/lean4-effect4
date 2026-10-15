import Lean
import OCaml5.Lcnf.Gen

/-!
# LcnfGen — Lean definitions to OCaml modules, through the mono-phase LCNF

A thin driver over `OCaml5.Lcnf.Gen`. With `--recipe <path>` it makes every artifact of the recipe
(`ocaml/gen/roots.json`, `make gen-lcnf`) in one process: each set of modules is imported once,
and each artifact gets its own run over it. With an artifact's own arguments it makes that
artifact alone; that is the command each artifact's header carries.

    lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean --recipe ocaml/gen/roots.json
    lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean \
      --out ocaml/gen/api_gen.ml --import Effect4.Api --cap 2000 \
      Effect4.Api.run Effect4.Api.replay …

An artifact's options: `--out <path>` (required), `--import M` (a module whose environment the
roots are looked up in; required, repeatable), `--cap <n>` (default 60), `--types A,B,…` (types
to emit in full even when no translated code destructs them), `--externs <file>` and
`--prelude <file>`.

## The seam (`--externs`, `--prelude`)

With `--externs <file>` the run reads an `OCaml5.Lcnf.Externs` table (its format is that
module's docstring) and the output becomes

```
[@@@warning …]
<the six carrier module types, verbatim>
module Make (M : TABLE) (T : TRACE) (L : LAYERS) (D : DISPATCHER) (P : PPATH) (E : PENV) (F : FIBERS) = struct
  <the type group>                (* it mentions M.t / T.t / L.t / D.t, so it moves inside *)
  <--prelude, verbatim>           (* the hand rows: they need the record types above *)
  <the declarations>
end
```

A functor body type-checks with **no instance**, and that is the proof the table is closed
(`docs/research/2026-09-08-engine-a1-state.md` §1.3): any generated site that still treats a
carrier field as a list is an `ocamlopt` type error. The run **fails** when a `fn` row (as
opposed to `fn?`), a `type` row or a `field` row was never hit — a stale row is a stale ledger.

Without `--externs` the file is the flat structure, so `ocaml/gen/api_gen.ml` has no seam.

This is a tool (`IO`, `MetaM`); it is not part of any audited library.
-/

open Lean OCaml5.Lcnf

/-- The recipe at `path`, as JSON. -/
def readRecipe (path : System.FilePath) : IO Json := do
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure j
  | .error e => throw (IO.userError s!"{path}: {e}")

def main (argv : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  -- The artifacts to make, each as its argv, and the recipe's outputs (they place the manifests).
  let (runs, recipeOuts) ← match argv with
    | ["--recipe", path] => do
      let recipe ← readRecipe path
      let runs ← IO.ofExcept (Gen.recipeArgvs recipe)
      pure (runs, Gen.recipeOutsOf recipe)
    | _ => do
      let path : System.FilePath := "ocaml/gen/roots.json"
      let outs ← if ← path.pathExists then
          pure ((Gen.recipeOutsOf <$> (Json.parse (← IO.FS.readFile path)).toOption).getD [])
        else pure []
      pure (#[argv], outs)
  -- One environment for each set of imports, in the order the artifacts first name it.
  let mut envs : Array (Array Name × Environment) := #[]
  for run in runs do
    let args := Gen.Args.parse run {}
    let cached := envs.find? (·.1 == args.imports)
    let t0 ← IO.monoNanosNow
    let env ← match cached with
      | some (_, env) => pure env
      | none => importModules (args.imports.map fun m => { module := m }) {} 0
    let t1 ← IO.monoNanosNow
    if cached.isNone then
      IO.println s!"imported {args.imports} in {(t1 - t0) / 1000000} ms"
      envs := envs.push (args.imports, env)
    IO.println s!"== {args.out}"
    -- One `MetaM` run spells every type of the closure, and Lean's heartbeat budget counts the
    -- whole run. The default (200000 thousand) stopped the `api_gen` cut once the error payload
    -- carrier (decisions row 120) grew its closure; the budget is five times that, still finite,
    -- so a runaway cut stops deterministically.
    let ctx : Core.Context :=
      { fileName := "<lcnf-gen>", fileMap := default, maxHeartbeats := 1000000 * 1000 }
    let _ ← ((Gen.run run recipeOuts).run' {}).toIO ctx { env := env }
