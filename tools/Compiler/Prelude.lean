import Effect4.Codegen.Checked

/-!
# Compiler.Prelude — the prelude's import closure, beside a printed module

A printed module imports from its prelude each name it uses outside `effect` (`preludeNames`,
`src/Effect4/Codegen/Checked.lean`), and the prelude imports its helper files. So a folder that
holds a printed module holds, beside it, the import closure of the module's own imports: every
file of the prelude that the module reaches by a relative import or re-export, each once, at its
path under the prelude's folder (`closureOf`, from `importedBy`).

- **The closure starts at the module**, not at `prelude.ts`: its roots are the files that the
  folder's own files import (`importedBy`). A module that uses no prelude name imports no
  prelude file, and its folder holds none.
- **The closure is read off the files' imports** (`relativeImports`), never named by hand. From
  `prelude.ts` it is five files on 2026-10-20. A file that imports outside the prelude's folder is
  refused (`resolve`), since the copy would break its import.
- **A file no import reaches is not copied.** `sql.ts`, the SQLite package's adapter, is the one
  file of the prelude that imports `@effect/sql-sqlite-bun`, and `prelude.ts` does not import it.
  A module reaches it only by importing `Sql` for a SQL row (`Compiler.hostImports`), so a folder
  with no SQL row needs no SQL package.
- **The packages a folder imports** are read off the same scan: each bare specifier's package
  (`packages`), which the manifest names with the library's pin (`Compiler.Inputs`).
- **The scan is lexical**: each `from` and `import` followed by a quoted specifier (`specifiers`).
  A specifier inside a comment counts too, so the closure may hold a file, and the manifest name a
  package, that no import needs; a dynamic `import(…)` is not read.
- **The source** is the library's prelude folder, under its checkout (`source`). The compiler
  reads the whole folder (`folder`) and copies the closure of each module's imports
  (`Compiler.emitTs`). The code generator's folder (`tools/Drivers/Emit.lean`) copies the closure
  from `prelude.ts`, which every one of its modules imports (`closure`, `write`).
-/

namespace Compiler.Prelude

/-- The library's prelude folder, under its checkout. -/
def source : System.FilePath := System.FilePath.mk "ts" / "prelude"

/-- The prelude's root file, which a printed module imports. -/
def root : String := "prelude.ts"

/-- The content of a quoted specifier: the text before the closing quote, if one follows. -/
def upToQuote (quote : String) (rest : String) : Option String :=
  match rest.splitOn quote with
  | specifier :: _ :: _ => some specifier
  | _ => none

/-- The specifiers that follow each `opener` in a text, up to their closing `quote`. -/
def after (opener quote : String) (text : String) : List String :=
  ((text.splitOn opener).drop 1).filterMap (upToQuote quote)

/-- **The specifiers of a TypeScript text**: each one after `from "`, `import "`, `from '` or
`import '`, up to its closing quote. -/
def specifiers (text : String) : List String :=
  after "from \"" "\"" text ++ after "import \"" "\"" text ++ after "from '" "'" text ++
    after "import '" "'" text

/-- Whether a specifier is relative: it starts with `./` or `../`. -/
def relative (specifier : String) : Bool := specifier.startsWith "./" || specifier.startsWith "../"

/-- **The relative specifiers of a TypeScript text** (`specifiers`). -/
def relativeImports (text : String) : List String := (specifiers text).filter relative

/-- **The package a bare specifier names**: a scoped package's scope and name
(`@effect/sql-sqlite-bun`), else its first segment (`effect` of `effect/unstable/persistence`). -/
def packageOf (specifier : String) : String :=
  match specifier.splitOn "/" with
  | scope :: name :: _ => if scope.startsWith "@" then scope ++ "/" ++ name else scope
  | _ => specifier

/-- **The packages a TypeScript text imports**: the package of each specifier that is not
relative (`packageOf`), once each. -/
def packages (text : String) : List String :=
  ((specifiers text).filter fun s => !relative s).map packageOf |>.eraseDups

/-- One step of a path: `.` and an empty step stay, `..` leaves the last folder, and a name enters
one; `none` once a step leaves the prelude's folder. -/
def step (dirs : Option (List String)) (segment : String) : Option (List String) :=
  dirs.bind fun ds =>
    if segment == "." || segment == "" then some ds
    else if segment == ".." then (if ds.isEmpty then none else some ds.dropLast)
    else some (ds ++ [segment])

/-- **A specifier resolved** against the folder of the file that imports it, both relative to the
prelude's folder; `none` when it leaves that folder. -/
def resolve (importer specifier : String) : Option String :=
  ((specifier.splitOn "/").foldl step (some (importer.splitOn "/").dropLast)).map ("/".intercalate ·)

/-- At most this many files in a closure: the bound of `closure`'s loop. -/
def bound : Nat := 64

/-- **The prelude's import closure** from the files `from_`, each file read by `read` at its path
relative to the prelude's folder: each file's path and its bytes, each once, in byte order of the
paths (`Codegen.bytesLe`). Refused, with what and where, when a file is not UTF-8, when an import
leaves the folder, or past `bound` files; `read` refuses a missing file. From no file, it is
empty. -/
def closureOf {m : Type → Type} [Monad m] (read : String → ExceptT String m ByteArray)
    (from_ : List String := [root]) : ExceptT String m (List (String × ByteArray)) := do
  let mut found : List (String × ByteArray) := []
  let mut pending : List String := from_.eraseDups
  for _ in [0:bound] do
    match pending with
    | [] => break
    | path :: rest =>
      let bytes ← read path
      let some text := String.fromUTF8? bytes
        | throw s!"the prelude's {path} is not UTF-8"
      let next ← (relativeImports text).mapM fun s => match resolve path s with
        | some p => pure p
        | none => throw s!"the prelude's {path} imports {s}, outside its folder"
      found := found ++ [(path, bytes)]
      pending := ((rest ++ next).filter fun p => !found.any (·.1 == p)).eraseDups
  unless pending.isEmpty do
    throw s!"the prelude's import closure holds more than {bound} files"
  return found.mergeSort fun a b =>
    Effect4.Codegen.bytesLe a.1.toUTF8.data.toList b.1.toUTF8.data.toList

/-- **The prelude's import closure** under `dir`, from `root`: `closureOf`, each file read from
the disk. -/
def closure (dir : System.FilePath) (from_ : List String := [root]) :
    IO (List (String × ByteArray)) := do
  match ← (closureOf (fun path => ExceptT.lift (IO.FS.readBinFile (dir / path))) from_).run with
  | .ok files => pure files
  | .error why => throw (IO.userError why)

/-- The folder an emitted folder holds the prelude's files under. -/
def under : String := "prelude/"

/-- **The prelude's files that a folder's own files import**: each relative import of a file at
the emitted folder's root, resolved there (`resolve`), that falls under the prelude's folder
(`under`), with that prefix dropped; once each, in the order of first import. A printed module and
its surface stand at the root, so these are the roots of their closure (`closureOf`). -/
def importedBy (texts : List String) : List String :=
  (texts.flatMap fun text => (relativeImports text).filterMap fun s =>
    (resolve "" s).bind fun p => if p.startsWith under then some (p.drop under.length).toString
      else none).eraseDups

/-- The file a closure's path names in `files`, the prelude's folder read as data (`folder`);
refused when the folder holds none. -/
def lookup (files : List (String × ByteArray)) (path : String) : ExceptT String Id ByteArray :=
  match files.lookup path with
  | some bytes => pure bytes
  | none => throw s!"the prelude has no file {path}"

/-- **The prelude's folder as data**: every file under `dir` but those under a `node_modules`
folder, each with its path relative to `dir` and its bytes, in byte order of the paths. The
compiler reads it once, and each module's closure is computed from it (`closureOf`). -/
def folder (dir : System.FilePath) : IO (List (String × ByteArray)) := do
  let paths ← dir.walkDir fun p => pure (p.fileName != some "node_modules")
  let mut files : List (String × ByteArray) := []
  for path in paths do
    unless ← path.isDir do
      let relative := "/".intercalate (path.components.drop dir.components.length)
      files := files ++ [(relative, ← IO.FS.readBinFile path)]
  return files.mergeSort fun a b =>
    Effect4.Codegen.bytesLe a.1.toUTF8.data.toList b.1.toUTF8.data.toList

/-- Write each file at its path under `out`, creating its folders. -/
def write (out : System.FilePath) (files : List (String × ByteArray)) : IO Unit := do
  for (path, bytes) in files do
    let file := out / path
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeBinFile file bytes

end Compiler.Prelude
