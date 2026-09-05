/-
TranspileDeep — render the named `Fibers.lean` defs through `OCaml5.Transpile` and print the OCaml,
or the residue table with `--residue`:

    lake env lean --run src/OCaml5/Tools/TranspileDeep.lean insert enqueue drain arm disarm countdownWalk
    lake env lean --run src/OCaml5/Tools/TranspileDeep.lean --residue insert enqueue …
    lake env lean --run src/OCaml5/Tools/TranspileDeep.lean stepDecision.fire            # a `where`-local
    lake env lean --run src/OCaml5/Tools/TranspileDeep.lean --file path/to/File.lean insert

The file defaults to `src/Effect4/Machine/Fibers.lean`, relative to the repository root, which
is where `ocaml/avatar/transpile-deep.sh` runs it. A thin driver: the tables and the translation
are `src/OCaml5/Transpile.lean`.
-/
import OCaml5.Transpile

open Lean OCaml5.Ml OCaml5.Transpile

/-- `--file <path>`, when given. -/
def pathArg : List String → Option String
  | "--file" :: p :: _ => some p
  | _ :: rest => pathArg rest
  | [] => none

/-- The arguments without `--file <path>`. -/
def dropPath : List String → List String
  | "--file" :: _ :: rest => dropPath rest
  | a :: rest => a :: dropPath rest
  | [] => []

unsafe def main (args : List String) : IO Unit := do
  Lean.enableInitializersExecution
  let path := (pathArg args).getD "src/Effect4/Machine/Fibers.lean"
  let wantResidue := args.contains "--residue"
  let names := (dropPath args).filter (· != "--residue")
  let found ← collect path
  let mut residues : List (String × List String) := []
  let mut decls : List Decl := []
  for n in names do
    -- `outer.local` addresses a `where`-local of `outer`; `outer` alone renders it with its locals
    let (outer, only) := match n.splitOn "." with
      | [o] => (o, none)
      | [o, l] => (o, some l)
      | _ => (n, none)
    match found.find? (·.name == outer) with
    | none => IO.eprintln s!"transpile-deep: no def named {outer} in {path}"
    | some f =>
      let ((main, locals), st) := (trDef f.name f.sig f.val).run {}
      let binds := match only with
        | none => main :: locals
        | some l => locals.filter (·.name == globalName (outer ++ "." ++ l))
      let isRec := true
      decls := decls ++ [.letD isRec binds]
      residues := residues ++ [(n, st.residue)]
  if wantResidue then
    for (n, r) in residues do
      IO.println s!"{n}\t{r.length}\t{", ".intercalate r}"
  else
    IO.println (moduleText decls)
