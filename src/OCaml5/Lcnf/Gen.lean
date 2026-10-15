import Lean
import OCaml5.Lcnf.Index
import OCaml5.Lcnf.Census
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Check
import OCaml5.Lcnf.Externs
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate

/-!
# OCaml5.Lcnf.Gen

**What it is.** One LCNF artifact made from its command's arguments: the closure translated
(`translateClosureInferring`), the types generated (`generate`), the declarations emitted, the
module checked (`Ml.checkModule`, `hygieneProblems`, the extern ledger), rendered and written, with
its closure manifest. The recipe (`ocaml/gen/roots.json`) lists the artifacts, and
`argvOf` turns each entry into the command its header carries. The driver
`OCaml5.Tools.LcnfGen` runs one artifact, or every artifact of the recipe in one process.

**Depends on.** `OCaml5.Lcnf.Translate`, `OCaml5.Lcnf.Types`, `OCaml5.Lcnf.Externs`, `OCaml5.Ml`,
`OCaml5.Lcnf.Index` and `OCaml5.Lcnf.Census` (the mono index and the construct census of the manifest).

**Properties.**
* **The header is the command.** An artifact's header carries the command that makes it alone
  (`commandOf`), whether the run made it alone or with the recipe's others. The recipe's argv
  order is fixed (`argvOf`), so the two runs write the same bytes — *by construction*; *tested*
  by `make gen-lcnf`, which runs the recipe and refuses no byte.
* **A run that fails writes nothing.** Every refusal (the frontier, a missing declaration, a
  translation or clock refusal, a type-name collision, a module diagnostic, a capture, a stale
  extern row) is raised before the artifact or its manifest is written — *by construction*.
* **Each artifact starts from the imported environment.** A recipe run imports each set of
  modules once and gives each artifact a fresh `MetaM` state over it, as a run of its own
  would — *by construction*.
-/

namespace OCaml5.Lcnf.Gen

open Lean

/-- One artifact's arguments, as its command spells them. -/
structure Args where
  /-- The artifact's path; a run without one is refused. -/
  out : String := ""
  types : Array Name := #[]
  cap : Nat := 60
  roots : Array Name := #[]
  /-- Modules to import before looking the roots up; a run without one is refused. -/
  imports : Array Name := #[]
  /-- The `Extract Constant` table (`--externs <file>`). None means the flat, unseamed output. -/
  externs : Option String := none
  /-- Hand OCaml spliced verbatim inside the functor, after the type group (`--prelude <file>`).
  It is where a row whose Lean body applies a builtin to a carrier field lives, because only
  there can it see both the carrier parameters and the generated record types. -/
  prelude : Option String := none
  /-- An OCaml module that declares some of this artifact's types (`--open <Module>`): the
  artifact opens it and declares none of them. -/
  opens : Option String := none
  /-- The types the opened module's own artifact requests (`--open-types A,B,…`). This run
  generates them as that artifact does, so the two agree on every name. -/
  openTypes : Array Name := #[]

/-- The arguments of one artifact's command. Every word that is no option is a root. -/
def Args.parse : List String → Args → Args
  | "--out" :: p :: rest, a => Args.parse rest { a with out := p }
  | "--types" :: ts :: rest, a =>
    Args.parse rest { a with types := a.types ++ ((ts.splitOn ",").map String.toName).toArray }
  | "--cap" :: n :: rest, a => Args.parse rest { a with cap := n.toNat! }
  | "--import" :: m :: rest, a =>
    Args.parse rest { a with imports := a.imports ++ ((m.splitOn ",").map String.toName).toArray }
  | "--externs" :: p :: rest, a => Args.parse rest { a with externs := some p }
  | "--prelude" :: p :: rest, a => Args.parse rest { a with prelude := some p }
  | "--open" :: m :: rest, a => Args.parse rest { a with opens := some m }
  | "--open-types" :: ts :: rest, a =>
    Args.parse rest { a with openTypes := a.openTypes ++ ((ts.splitOn ",").map String.toName).toArray }
  | r :: rest, a => Args.parse rest { a with roots := a.roots.push r.toName }
  | [], a => a

/-- The format of the recipe this module reads. -/
def recipeFormat : String := "effect4-lcnf-roots-v2"

/-- The command an artifact's header carries: the driver run on this artifact alone. -/
def commandOf (argv : List String) : String :=
  "lean -M4096 --run src/OCaml5/Tools/LcnfGen.lean " ++ " ".intercalate argv

/-- One recipe entry's argv, in the recipe's fixed order: `--out`, one `--import` per module,
`--cap`, `--types` (comma-joined, when any), `--externs`, `--prelude`, `--open` and
`--open-types` (when the entry opens another artifact's module), the roots in the order listed,
then the coverage roots. It is the text of the artifact's header. `typesOf` gives an artifact's
requested types by its `out`, so an `open` names the artifact once and its types are read from it. -/
def argvOf (typesOf : String → Option (List String)) (entry : Json) :
    Except String (List String) := do
  let out ← entry.getObjValAs? String "out"
  let imports := (entry.getObjValAs? (List String) "import").toOption.getD []
  let cap ← entry.getObjValAs? Nat "cap"
  let types := (entry.getObjValAs? (List String) "types").toOption.getD []
  let roots ← entry.getObjValAs? (List String) "roots"
  let coverage := (entry.getObjValAs? (List String) "coverage").toOption.getD []
  let flag (name : String) : List String :=
    match entry.getObjValAs? String name with
    | .ok value => if value.isEmpty then [] else ["--" ++ name, value]
    | .error _ => []
  let opens ← match entry.getObjVal? "open" with
    | .error _ => pure []
    | .ok spec => do
      let m ← spec.getObjValAs? String "module"
      let from_ ← spec.getObjValAs? String "artefact"
      let some ts := typesOf from_
        | throw s!"{out} opens the module of {from_}, which is no artefact of the recipe"
      pure ["--open", m, "--open-types", ",".intercalate ts]
  return ["--out", out] ++ imports.flatMap (fun m => ["--import", m]) ++ ["--cap", toString cap]
    ++ (if types.isEmpty then [] else ["--types", ",".intercalate types])
    ++ flag "externs" ++ flag "prelude" ++ opens ++ roots ++ coverage

/-- The recipe's artifacts, each as its argv, in the recipe's order. Another format is refused. -/
def recipeArgvs (recipe : Json) : Except String (Array (List String)) := do
  let format ← recipe.getObjValAs? String "format"
  unless format == recipeFormat do
    throw s!"unsupported LCNF recipe format {format}; this generator reads {recipeFormat}"
  let entries ← recipe.getObjValAs? (Array Json) "artefacts"
  let typesOf (out : String) : Option (List String) :=
    entries.findSome? fun e =>
      if (e.getObjValAs? String "out").toOption == some out then
        some ((e.getObjValAs? (List String) "types").toOption.getD [])
      else none
  entries.mapM (argvOf typesOf)

/-- The `--out` paths of the recipe's artifacts, whose closure manifests are data in
`GENERATED_PATHS` at `ocaml/gen/closure-<stem>.tsv` (decisions row 70). -/
def recipeOutsOf (recipe : Json) : List String :=
  match recipe.getObjVal? "artefacts" with
  | .ok (.arr rows) => rows.toList.filterMap fun r => (r.getObjValAs? String "out").toOption
  | _ => []

/-- Where a run writes its closure manifest: in `ocaml/gen/` for one of the recipe's artifacts
(row 70, all of them in one folder, named after the artifact's stem), and beside `--out` for any
other run, so a probe that redirects its output never writes into the tree (decisions row 174
(i)). -/
def manifestPathFor (out : String) (recipeOuts : List String) : String :=
  let stem := (System.FilePath.mk out).fileStem.getD "closure"
  if recipeOuts.contains out then s!"ocaml/gen/closure-{stem}.tsv"
  else ((System.FilePath.mk out).parent.getD "." / s!"closure-{stem}.tsv").toString

/-- One row of the closure manifest: the Lean constant, the OCaml name it became, whether the
emitted binding is recursive, the twenty-six mono-LCNF construct counts of its body
(`constructs`, in that order) and `DeclHash`'s hash of the whole `Decl`, the
identity of the *code*, stable across runs of one build.

The mono declaration is read the way `translateClosure` reads it, out of `monoExt`'s module
entries (`persistedMonoIndex`), never through `getMonoDecl?`: the module system's
export filter makes the two disagree (`tools/Conform/Lcnf/Validity.lean`, the section on reading
`monoExt`'s local state). A declaration the closure translated and the index cannot find is
fatal, not a blank row. -/
private def manifestRow (env : Environment) (mono : MonoIndex)
    (t : Translated) : MetaM String := do
  let some d := mono.findIn? env t.leanName
    | throwError s!"closure manifest: no mono declaration for {t.leanName}"
  let census := Census.ofDecl {} d
  return "\t".intercalate
    ([toString t.leanName, t.ocamlName, toString t.recursive]
      ++ constructs.map (fun k => toString (census.get k))
      ++ [toString (hash d)])

/-- Milliseconds between two readings of `IO.monoNanosNow`. -/
private def millis (a b : Nat) : Nat := (b - a) / 1000000

/-- One artifact, made from its argv and written with its closure manifest; the report goes to
standard output, the last line its phases' times. `recipeOuts` places the manifest
(`manifestPathFor`). -/
def run (argv : List String) (recipeOuts : List String) : MetaM Unit := do
  let args := Args.parse argv {}
  if args.out.isEmpty || args.imports.isEmpty then
    throwError "LcnfGen: `--out <path>` and at least one `--import <module>` are required"
  let handEx : Externs ← match args.externs with
    | none => pure {}
    | some path => do
      match Externs.parse (← IO.FS.readFile path) with
      | .ok e => pure e
      | .error msg => throwError s!"{path}: {msg}"
  let preludeText : Option String ← match args.prelude with
    | none => pure none
    | some path => pure (some (← IO.FS.readFile path))
  let t0 ← IO.monoNanosNow
  -- Two Lean type constants can share a short name (`Effect4.Api.Outcome` and
  -- `Effect4.Machine.Outcome` are both `outcome`). Renaming one *after* the annotations and
  -- constructors are rendered makes them disagree, so the collisions are discovered on a
  -- first pass and fed back as `TypeNames` before anything is written; the loop repeats in
  -- case a fallback name collides in its turn. A renaming pass translates the declarations
  -- again (`retranslate`): the walk, the carrier rows and the clock boundary read no name.
  -- The opened module's types, generated as its own artifact generates them (no table, the same
  -- renaming loop), so every name agrees. A placeholder there would hide a type this run must
  -- declare in full, so the opened artifact must declare each of its types in full.
  let mut tn : TypeNames := {}
  let mut provided : NameSet := {}
  let mut openedDecls : Array Ml.TypeDecl := #[]
  if args.opens.isSome then
    let (og, otn) ← generateInFull args.openTypes
    tn := otn
    provided := (og.full ++ og.aliases).foldl (·.insert ·) {}
    openedDecls := og.decls
  let (closure0, ex, inferred) ← translateClosureInferring args.roots args.cap tn handEx
  let t1 ← IO.monoNanosNow
  let mut closure := closure0
  let mut gen ← generate (closure.realTypes ++ args.types) closure.mentioned tn ex provided
  let t2 ← IO.monoNanosNow
  let mut renamed : Array (String × Name × Name) := #[]
  for _ in [:4] do
    if gen.collisions.isEmpty then break
    renamed := renamed ++ gen.collisions
    for (_, _, n) in gen.collisions do tn := tn.insert n (fullTypeName n)
    closure ← retranslate closure tn ex
    gen ← generate (closure.realTypes ++ args.types) closure.mentioned tn ex provided
  let t3 ← IO.monoNanosNow
  let header := "GENERATED by OCaml5.Lcnf (src/OCaml5/Lcnf/*.lean) from the mono-phase LCNF "
    ++ "of " ++ ", ".intercalate (args.imports.toList.map toString)
    ++ ", Lean " ++ Lean.versionString ++ ". Do not edit. Regenerate with:\n   " ++ commandOf argv
  let emitted ← match emit closure.decls with
    | .ok items => pure items
    | .error message => throwError message
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
  let opened : List Ml.Decl :=
    match args.opens with | none => [] | some m => [.openD m, .blank]
  let items : List Ml.Decl :=
    if args.externs.isNone then
      [.floatingAttrD "warning \"-26-27-30-32-33-35-37-39-69\"", .blank] ++ opened ++ body
    else
      [.floatingAttrD "warning \"-26-27-30-32-33-35-37-39-69\"", .blank] ++ opened ++
      carrierSignatures ++ [.blank, .moduleD "Make" carrierParams body]
  let modName := (System.FilePath.mk args.out).fileStem.getD "lcnf_gen"
  let m : Ml.Module := { name := modName, header := some header, items := items }
  let t4 ← IO.monoNanosNow
  -- The closure as DATA (tooling plan 4.1): one manifest per artifact, all of them in
  -- `ocaml/gen/`, named after the artifact's own stem, so a declaration entering or leaving the
  -- engine's closure, or a body whose shape changed, is a diff at review time. It is BUILT here
  -- and WRITTEN with the artifact, below every fatal check: a manifest beside an artifact the
  -- run never wrote would be the drift it exists to catch.
  let env ← getEnv
  let monoIndex := persistedMonoIndex env
  let manifestPath := manifestPathFor args.out recipeOuts
  let manifestHeader := "\t".intercalate
    (["lean", "ocaml", "recursive"] ++ constructs ++ ["declHash"])
  let manifestRows ← closure.decls.mapM (manifestRow env monoIndex)
  let manifestText := String.intercalate "\n" (manifestHeader :: manifestRows.toList) ++ "\n"
  IO.println s!"closure: {closure.decls.size} of --cap {args.cap} \
    ({args.cap - closure.decls.size} of headroom); manifest {manifestPath}"
  let t5 ← IO.monoNanosNow
  IO.println s!"missing (no mono decl): {closure.missing}"
  IO.println s!"wrapper referenced directly: {closure.wrapperRefs}"
  IO.println s!"todos ({closure.todos.size}):"
  for t in closure.todos do IO.println s!"  {t}"
  IO.println s!"clock refusals ({closure.clockRefusals.size}):"
  for t in closure.clockRefusals do IO.println s!"  {t}"
  IO.println s!"types in full: {gen.full}"
  IO.println s!"types as abbreviations: {gen.aliases}"
  IO.println s!"types as placeholders: {gen.placeholders}"
  IO.println s!"requested but not inductive: {gen.notInductive}"
  IO.println s!"field types not spelled: {gen.unknown}"
  IO.println s!"type-name collisions renamed to their full path: {renamed}"
  IO.println s!"type-name collisions left unresolved: {gen.collisions}"
  -- A non-empty frontier means the artifact calls a declaration the cap stopped at: the
  -- emitted file names a function it does not define, and only `ocamlc` would say so. The
  -- headroom is printed above, so raising the artifact's `cap` in `ocaml/gen/roots.json` is
  -- the repair.
  unless closure.frontier.isEmpty do
    throwError s!"closure did not close at --cap {args.cap} (fatal): {closure.frontier}"
  unless closure.missing.isEmpty do
    throwError s!"missing mono declarations (fatal): {closure.missing}"
  unless closure.problems.isEmpty do
    throwError s!"todos remaining in closure (fatal): {closure.problems}"
  unless gen.collisions.isEmpty do
    throwError s!"unresolved type-name collisions (fatal): {gen.collisions}"
  -- The module's own well-formedness, FATAL (tooling plan 4.3), for every artifact. The opened
  -- unit's interface is its types, as its own artifact declares them: the `open` reads as a
  -- scope, and the value names past it are checked.
  let units : List Ml.Interface := match args.opens with
    | none => []
    | some m => [{ name := m, types := openedDecls.toList }]
  let diags := Ml.checkModule m units
  unless diags.isEmpty do
    throwError s!"Ml.checkModule (fatal): {diags.length} diagnostic(s)\n  " ++
      "\n  ".intercalate (diags.map Ml.Diag.toLine)
  IO.println "Ml.checkModule: PASS (0 diagnostics)"
  -- The names, FATAL. `Ml.checkModule` decides that every name is bound; it cannot decide
  -- that a name is bound by the declaration the translator meant. `hygieneProblems` reads
  -- each translated declaration against the names its body leaves free.
  let captures := hygieneProblems closure.decls
  unless captures.isEmpty do
    throwError s!"name hygiene (fatal): {captures.length} problem(s)\n  " ++
      "\n  ".intercalate captures
  IO.println "name hygiene: PASS (0 problems)"
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
    for k in closure.usedExterns do
      IO.println s!"  {k} -> {(ex.fns[k]?.map (·.head)).getD "?"}"
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
  let t6 ← IO.monoNanosNow
  let text := Ml.render m
  IO.FS.writeFile args.out text
  -- An artifact with no roots declares types only: it translates nothing, so it has no closure
  -- to record.
  unless args.roots.isEmpty do IO.FS.writeFile manifestPath manifestText
  let t7 ← IO.monoNanosNow
  IO.println s!"wrote {args.out} and {manifestPath}"
  IO.println s!"time (ms): closure {millis t0 t1}, types {millis t1 t2}, renaming {millis t2 t3}, \
    emission {millis t3 t4}, manifest {millis t4 t5}, checks {millis t5 t6}, \
    rendering {millis t6 t7}"

end OCaml5.Lcnf.Gen
