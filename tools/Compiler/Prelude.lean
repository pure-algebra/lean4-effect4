import Effect4.Codegen.Checked

/-!
# Compiler.Prelude — the prelude's import closure, beside a printed module

A printed module imports from its prelude each name it uses outside `effect` (`preludeNames`,
`src/Effect4/Codegen/Checked.lean`), and the prelude imports its helper files. So a folder that
holds a printed module holds the prelude's import closure beside it: `prelude.ts`, and every file
that it reaches by a relative import or re-export, each once, at its path under the prelude's
folder (`closure`).

- **The closure is read off the files' imports** (`relativeImports`), never named by hand. On
  2026-10-20 it is five files. A file that imports outside the prelude's folder is refused
  (`resolve`), since the copy would break its import.
- **The scan is lexical**: each `from` and `import` followed by a quoted specifier that starts with
  `./` or `../`. A specifier inside a comment counts too, so the closure may hold a file that no
  import needs; a dynamic `import(…)` is not read.
- **The source** is the library's prelude folder, under its checkout (`source`). The compiler
  (`Compiler.Main`) and the code generator's folder (`tools/Drivers/Emit.lean`) copy the same
  closure through `closure` and `write`.
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

/-- **The relative specifiers of a TypeScript text**: each one after `from "`, `from '`,
`import "` or `import '` that starts with `./` or `../`. -/
def relativeImports (text : String) : List String :=
  (after "from \"" "\"" text ++ after "import \"" "\"" text ++ after "from '" "'" text ++
    after "import '" "'" text).filter fun s => s.startsWith "./" || s.startsWith "../"

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

/-- **The prelude's import closure** under `dir`, from `root`: each file's path relative to `dir`
and its bytes, each once, in byte order of the paths (`Codegen.bytesLe`). Refused, with what and
where, when a file is missing or is not UTF-8, when an import leaves the folder, or past `bound`
files. -/
def closure (dir : System.FilePath) (from_ : String := root) : IO (List (String × ByteArray)) := do
  let mut found : List (String × ByteArray) := []
  let mut pending : List String := [from_]
  for _ in [0:bound] do
    match pending with
    | [] => break
    | path :: rest =>
      let bytes ← IO.FS.readBinFile (dir / path)
      let some text := String.fromUTF8? bytes
        | throw (IO.userError s!"the prelude's {path} is not UTF-8")
      let next ← (relativeImports text).mapM fun s => match resolve path s with
        | some p => pure p
        | none => throw (IO.userError s!"the prelude's {path} imports {s}, outside its folder")
      found := found ++ [(path, bytes)]
      pending := ((rest ++ next).filter fun p => !found.any (·.1 == p)).eraseDups
  unless pending.isEmpty do
    throw (IO.userError s!"the prelude's import closure holds more than {bound} files")
  return found.mergeSort fun a b =>
    Effect4.Codegen.bytesLe a.1.toUTF8.data.toList b.1.toUTF8.data.toList

/-- Write each file at its path under `out`, creating its folders. -/
def write (out : System.FilePath) (files : List (String × ByteArray)) : IO Unit := do
  for (path, bytes) in files do
    let file := out / path
    if let some dir := file.parent then IO.FS.createDirAll dir
    IO.FS.writeBinFile file bytes

end Compiler.Prelude
