import Tools.GeneratedStamp
import Lean
import Conform.Lcnf.Validity
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Check
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate

/-!
# LcnfGen — Lean definitions to an OCaml module, through the mono-phase LCNF

A thin driver over `OCaml5.Lcnf.Translate` and `OCaml5.Lcnf.Types`: import
`Effect4.Machine.Fibers`, translate the named constants and everything they call (up to
`--cap`), generate the types they destruct or construct (plus `--types`), render one `.ml`
file, and print a report of what was and was not covered.

    lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean \
      --out ocaml/gen/machine_gen.ml --cap 60 \
      Effect4.Machine.Dispatcher.insert Effect4.Machine.Dispatcher.enqueue …

Options: `--out <path>` (default `ocaml/gen/machine_gen.ml`), `--cap <n>` (default
60), `--types A,B,…` (types to emit in full even when no translated code destructs them),
`--import M` (the module whose environment the roots are looked up in; default
`Effect4.Machine.Fibers`, repeatable — every existing regeneration command is unchanged).

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

Without `--externs` nothing changes: the file is the flat structure it has always been, so
`ocaml/gen/api_gen.ml`'s regeneration command produces the same bytes.

This is a tool (`IO`, `MetaM`); it is not part of any audited library.
-/

open Lean OCaml5 OCaml5.Lcnf

structure GenArgs where
  out : String := "ocaml/gen/machine_gen.ml"
  types : Array Name := #[]
  cap : Nat := 60
  roots : Array Name := #[]
  /-- Modules to import before looking the roots up. Empty means the default. -/
  imports : Array Name := #[]
  /-- The `Extract Constant` table (`--externs <file>`). None means the flat, unseamed output. -/
  externs : Option String := none
  /-- Hand OCaml spliced verbatim inside the functor, after the type group (`--prelude <file>`).
  It is where a row whose Lean body applies a builtin to a carrier field lives, because only
  there can it see both the carrier parameters and the generated record types. -/
  prelude : Option String := none

/-- The import list actually used: `--import`s, or `Effect4.Machine.Fibers` when none was given,
so every command written before `--import` existed generates exactly what it did before. -/
def GenArgs.importModuleNames (a : GenArgs) : Array Name :=
  if a.imports.isEmpty then #[`Effect4.Machine.Fibers] else a.imports

partial def parseArgs : List String → GenArgs → GenArgs
  | "--out" :: p :: rest, a => parseArgs rest { a with out := p }
  | "--types" :: ts :: rest, a =>
    parseArgs rest { a with types := a.types ++ ((ts.splitOn ",").map String.toName).toArray }
  | "--cap" :: n :: rest, a => parseArgs rest { a with cap := n.toNat! }
  | "--import" :: m :: rest, a =>
    parseArgs rest { a with imports := a.imports ++ ((m.splitOn ",").map String.toName).toArray }
  | "--externs" :: p :: rest, a => parseArgs rest { a with externs := some p }
  | "--prelude" :: p :: rest, a => parseArgs rest { a with prelude := some p }
  | r :: rest, a => parseArgs rest { a with roots := a.roots.push r.toName }
  | [], a => a

/-- One row of the closure manifest: the Lean constant, the OCaml name it became, whether the
emitted binding is recursive, the twenty-six mono-LCNF construct counts of its body
(`Conform.Lcnf.constructs`, in that order) and `DeclHash`'s hash of the whole `Decl` — the
identity of the *code*, stable across runs of one build.

The mono declaration is read the way `translateClosure` reads it, out of `monoExt`'s module
entries (`Conform.Lcnf.persistedMonoIndex`), never through `getMonoDecl?`: the module system's
export filter makes the two disagree, which is the finding `Conform/Lcnf/Validity.lean` records
at its "the answer is read out of `monoExt`'s local state" section. A declaration the closure
translated and the index cannot find is fatal, not a blank row. -/
private def manifestRow (env : Environment) (mono : Conform.Lcnf.MonoIndex)
    (t : Translated) : MetaM String := do
  let some d := mono.findIn? env t.leanName
    | throwError s!"closure manifest: no mono declaration for {t.leanName}"
  let census := Conform.Lcnf.Census.ofDecl {} d
  return "\t".intercalate
    ([toString t.leanName, t.ocamlName, toString t.recursive]
      ++ Conform.Lcnf.constructs.map (fun k => toString (census.get k))
      ++ [toString (hash d)])

private def checkpoint (label : String) : MetaM Unit := do
  let ctx ← readThe Core.Context
  let current ← IO.getNumHeartbeats
  IO.println s!"STAGE {label}: current={current} init={ctx.initHeartbeats} used={(current - ctx.initHeartbeats) / 1000} max={ctx.maxHeartbeats / 1000}"

def main (argv : List String) : IO Unit := do
  initSearchPath (← findSysroot)
  let args := parseArgs argv {}
  let ex : Externs ← match args.externs with
    | none => pure {}
    | some path => do
      match Externs.parse (← IO.FS.readFile path) with
      | .ok e => pure e
      | .error msg => throw (IO.userError s!"{path}: {msg}")
  let preludeText : Option String ← match args.prelude with
    | none => pure none
    | some path => pure (some (← IO.FS.readFile path))
  let mods := args.importModuleNames
  let env ← importModules (mods.map fun m => { module := m }) {} 0
  let ctx : Core.Context := { fileName := "<lcnf-gen>", fileMap := default }
  let act : MetaM Unit := do
    -- Two Lean type constants can share a short name (`Effect4.Api.Outcome` and
    -- `Effect4.Machine.Outcome` are both `outcome`). Renaming one *after* the annotations and
    -- constructors are rendered makes them disagree, so the collisions are discovered on a
    -- first pass and fed back as `TypeNames` before anything is written; the loop repeats in
    -- case a fallback name collides in its turn.
    checkpoint "start"
    let mut tn : TypeNames := {}
    let handEx := ex
    let (closure0, ex0, inferred0) ← translateClosureInferring args.roots args.cap tn handEx
    checkpoint "translation first"
    let mut closure := closure0
    let mut ex := ex0
    let mut inferred := inferred0
    let mut gen ← generate (closure.realTypes ++ args.types) closure.mentioned tn ex
    checkpoint "types first"
    let mut renamed : Array (String × Name × Name) := #[]
    for _ in [:4] do
      if gen.collisions.isEmpty then break
      renamed := renamed ++ gen.collisions
      for (_, _, n) in gen.collisions do tn := tn.insert n (fullTypeName n)
      let (closure1, ex1, inferred1) ← translateClosureInferring args.roots args.cap tn handEx
      checkpoint "translation collision"
      closure := closure1
      ex := ex1
      inferred := inferred1
      gen ← generate (closure.realTypes ++ args.types) closure.mentioned tn ex
      checkpoint "types collision"
    let cmd := "lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean " ++ " ".intercalate argv
    let header := "GENERATED by OCaml5.Lcnf (src/OCaml5/Lcnf/*.lean) from the mono-phase LCNF "
      ++ "of " ++ ", ".intercalate (mods.toList.map toString)
      ++ ", Lean " ++ Lean.versionString ++ ". Do not edit. Regenerate with:\n   " ++ cmd
    let emitted ← match emit closure.decls with
      | .ok items => pure items
      | .error message => throwError message
    checkpoint "emission"
    let body : List Ml.Decl :=
      [gen.item, .blank]
        ++ (match preludeText with | none => [] | some t => [.rawD t, .blank])
        ++ emitted
    -- Without a table the file is what it always was; with one, the type group mentions the
    -- carrier parameters, so the whole body moves inside the functor (A1 §1.5).
    -- The seamed file adds warning 30 (a record label claimed by two of the ~80 generated
    -- record types) because the engine library compiles with `-w +a` and dune's dev profile
    -- makes 30 fatal; `ocaml/gen` builds with `-warn-error -a` and its list is left alone, so
    -- `ocaml/gen/api_gen.ml` regenerates byte for byte.
    let items : List Ml.Decl :=
      if args.externs.isNone then
        [.floatingAttrD "warning \"-8-26-27-30-32-33-35-37-39-69\"", .blank] ++ body
      else
        [.floatingAttrD "warning \"-8-26-27-30-32-33-35-37-39-69\"", .blank,
         .rawD carrierSignatures, .blank,
         .moduleD "Make" carrierParams none body]
    let modName := (System.FilePath.mk args.out).fileStem.getD "machine_gen"
    let m : Ml.Module := { name := modName, header := some header, items := items }
    -- The closure as DATA (tooling plan 4.1). What stood here was a line per translated
    -- declaration on a terminal nobody reads; the manifest is beside the artefact and inside
    -- GENERATED_PATHS, so a declaration entering or leaving the engine's closure, or a body
    -- whose shape changed, is a diff at review time. One file per artefact, all four in
    -- `ocaml/gen/`, named after the artefact's own stem. It is BUILT here and WRITTEN with the
    -- artefact, below every fatal check: a manifest beside an artefact the run never wrote
    -- would be the drift it exists to catch.
    let env ← getEnv
    let monoIndex := Conform.Lcnf.persistedMonoIndex env
    let stem := (System.FilePath.mk args.out).fileStem.getD "closure"
    let manifestPath := s!"ocaml/gen/closure-{stem}.tsv"
    let manifestHeader := "\t".intercalate
      (["lean", "ocaml", "recursive"] ++ Conform.Lcnf.constructs ++ ["declHash"])
    let manifestRows ← closure.decls.mapM (manifestRow env monoIndex)
    checkpoint "manifest"
    let manifestText := String.intercalate "\n" (manifestHeader :: manifestRows.toList) ++ "\n"
    IO.println s!"closure: {closure.decls.size} of --cap {args.cap} \
      ({args.cap - closure.decls.size} of headroom); manifest {manifestPath}"
    IO.println s!"missing (no mono decl): {closure.missing}"
    IO.println s!"wrapper referenced directly: {closure.wrapperRefs}"
    IO.println s!"todos ({closure.todos.size}):"
    for t in closure.todos do IO.println s!"  {t}"
    IO.println s!"types in full: {gen.full}"
    IO.println s!"types as abbreviations: {gen.aliases}"
    IO.println s!"types as placeholders: {gen.placeholders}"
    IO.println s!"requested but not inductive: {gen.notInductive}"
    IO.println s!"field types not spelled: {gen.unknown}"
    IO.println s!"type-name collisions renamed to their full path: {renamed}"
    IO.println s!"type-name collisions left unresolved: {gen.collisions}"
    -- A non-empty frontier means the artefact calls a declaration the cap stopped at: the
    -- emitted file names a function it does not define, and only `ocamlc` would say so. The
    -- headroom is printed above, so raising the artefact's `cap` in `ocaml/gen/roots.json` is
    -- the repair. All four close today, so this costs nothing until something stops closing.
    unless closure.frontier.isEmpty do
      throwError s!"closure did not close at --cap {args.cap} (fatal): {closure.frontier}"
    unless closure.missing.isEmpty do
      throwError s!"missing mono declarations (fatal): {closure.missing}"
    unless closure.todos.isEmpty do
      throwError s!"todos remaining in closure (fatal): {closure.todos}"
    unless gen.collisions.isEmpty do
      throwError s!"unresolved type-name collisions (fatal): {gen.collisions}"
    -- The module's own well-formedness, FATAL (tooling plan 4.3), for all four artefacts and
    -- not only the three without a prelude. It was an informational count nobody read, and the
    -- count was 27/59/24/244 — every one of them a defect of the checker, not of the generated
    -- file: it reported unused type parameters, which OCaml accepts, missed the unbound ones it
    -- rejects, did not know `Ok`/`Error`, and called the names a top-level `rawD` binds unbound.
    -- With those four repaired the count is zero everywhere and the check can refuse.
    let diags := Ml.checkModule m
    unless diags.isEmpty do
      throwError s!"Ml.checkModule (fatal): {diags.length} diagnostic(s)\n  " ++
        "\n  ".intercalate (diags.map Ml.Diag.toLine)
    IO.println "Ml.checkModule: PASS (0 diagnostics)"
    checkpoint "Ml.checkModule"
    -- G10: the extern ledger. Every row is reported; a row nothing hit is fatal, because a
    -- stale row is a claim about the generated file that the generated file does not make.
    if args.externs.isSome then
      let fnRows := ex.fns.toList
      let tyRows := ex.tys.toList
      let fieldRows := ex.fields.toList
      let elemRows := ex.elems.toList
      IO.println s!"extern rows: {fnRows.length} fn, {tyRows.length} type, \
        {fieldRows.length} field, {elemRows.length} elem"
      IO.println s!"fn rows used ({closure.usedExterns.size}):"
      for n in closure.usedExterns do IO.println s!"  {n} -> {(ex.fn? n).get!.head}"
      IO.println s!"type rows used ({gen.usedTys.size}): {gen.usedTys}"
      IO.println s!"field rows used ({gen.usedFields.size}): {gen.usedFields}"
      IO.println s!"elem rows used ({gen.usedElems.size}): {gen.usedElems}"
      IO.println s!"ops rows: {ex.ops.size}, used ({closure.usedOps.size}): {closure.usedOps}"
      IO.println s!"carg rows: {handEx.cargs.size} stated, used ({closure.usedCargs.size}): \
        {closure.usedCargs}"
      IO.println s!"carg rows inferred from the call sites ({inferred.size}):"
      for row in inferred do IO.println s!"  {row}"
      -- Every place a carrier had to be copied back into the Lean list. It is correct and it
      -- is O(depth); the list is printed so that a missing `carg` row is visible here rather
      -- than only in a bench.
      IO.println s!"carrier to_list sites ({closure.toLists.size}):"
      for t in closure.toLists do IO.println s!"  {t}"
      let mut stale : Array String := #[]
      for (n, row) in fnRows do
        unless row.optional || closure.usedExterns.contains n do stale := stale.push s!"fn {n}"
      for (n, _) in tyRows do
        unless gen.usedTys.contains n do stale := stale.push s!"type {n}"
      for (n, _) in fieldRows do
        unless gen.usedFields.contains n do stale := stale.push s!"field {n}"
      for (n, _) in elemRows do
        unless gen.usedElems.contains n do stale := stale.push s!"elem {n}"
      for (n, _) in ex.ops.toList do
        unless closure.usedOps.contains n do stale := stale.push s!"ops {n}"
      for (n, _) in handEx.cargs.toList do
        unless closure.usedCargs.contains n do stale := stale.push s!"carg {n}"
      unless stale.isEmpty do
        throwError "extern rows no declaration hit (a stale ledger): {stale}"
    let rendered := Ml.render m
    IO.println s!"NO OUTPUT: rendered {rendered.utf8ByteSize} bytes, manifest {manifestText.utf8ByteSize} bytes"
    checkpoint "render"
  let _ ← (act.run' {}).toIO ctx { env := env }
