import Compiler.Groups
import Effect4.Author
import Test.Api.PackagesContract

/-!
# The compiler's emission and readings, read: corpus programs' folders, the dogfood to-do, and their controls

Readers and controls over `Compiler.emitProgram`, `Compiler.emitTs`, `Compiler.emitGroup`,
`Compiler.check` and `Compiler.reading` (`tools/Compiler/`; the entry point's slices,
`docs/research/2026-10-20-compiler-entry/README.md` §5, E3 and E6). A battery reads no file, so the
prelude's folder and the inputs are data here; the IO that reads them is `Compiler.Main`'s.

- **The folder of the wire corpus's first program**, `p42`, admitted at the empty application:
  its files and their kinds, the manifest read back from its own bytes, the address, the
  canonical bytes and their tagged print, and the certificate. `p42` uses no prelude name, so its
  folder holds no prelude file. `pBind`'s module imports the prelude, so its folder holds the
  closure of that import, and no import leaves the folder.
- **The red control**: an application whose literal is one above rc112's `natBound`. `check`
  admits it, since profile support is no part of the build, and its emission refuses at the
  profile. Its twin at `natBound` emits, and its module imports the prelude beside it.
- **The command's controls**: an entry that the checker refuses is named, `--emit` selects, an
  unknown kind is refused, and an import that leaves the prelude's folder resolves to nothing.
- **The packages a folder imports**: the manifest's pins name each package that the folder's
  files import, with the library's pin, and tsgo's. The prelude's closure, over a folder shaped
  as the library's, does not reach the SQLite package's adapter from the root that a module
  imports. So the wire corpus's folder names `effect` alone. The red control: a folder whose root
  reaches the adapter, as the root imported the package before 2026-10-20, names
  `@effect/sql-sqlite-bun`.
- **The tree's groups** (`Compiler.Groups.all`): the wire corpus, the SQLite package's programs and
  each example of `Examples.all`, and the to-do alone lowers native roots.
- **A program with a SQL row** (`Test.Api.PackagesContract.pSqlite`, at `Packages.sqliteBun`): its
  module imports `Sql` from the copied adapter (`Compiler.hostImports`), the reading boundary
  admits it, and its folder holds the adapter and names the SQL package. The red control: the file
  without that import, which the base's emission read, is refused at the reading boundary, by the
  name `Sql`. Every program of the group `sql` emits so.
- **The inputs** (`Compiler.Inputs`): the address is the SHA-256 of the modules' digests in
  order, so the same sources give the same address, and one changed source changes it. The
  executable's closure (`elaborated%`, here the battery's own) holds the module itself and the
  compiler, no toolchain module, in byte order, and the declared names of its literal keys.
- **The readings** (`Compiler.reading`, `inspect`): over the dogfood to-do, each through one query
  of the tool protocol. `rows` is the certificate's rows, `types` holds the program's type at the
  root, `graph` is the program's public JSON and its indented text reads back to it, and `surface`
  is the service's four methods. The command's reader of `--what`, and its refusals.
- **The defaults**: `ts` is the target when none is named, `describe --pretty` describes the same
  `emit`, and `check` names a key's declaration beside its spelling.
- **A group**: the wire corpus emitted as one folder with one manifest. The manifest names each
  program with its address and every file with its SHA-256, and each module is the one its
  program's own emission writes. The red controls: two programs of one name, and one program above
  the profile's bound, each refuse the group, by name.
- **A service module's read-back**: the dogfood to-do's file. Read as the envelope that a host
  wraps, with no services, the reading boundary refuses it at its first row service. With the
  table's row services read first, as `Api.readFile` reads them, it admits the file, and the
  to-do emits.

Every check is a `#guard`, so the rendered bytes stay inside them.
-/

namespace Test.Codegen.CompilerEmit

open Effect4 Effect4.Program Effect4.Program.Authoring Compiler

/-- The pins of the battery's emissions, as data: the library's TypeScript package's pins, and no
module closure. -/
def inputs : Inputs :=
  { lean := "leanprover/lean4:v4.33.1", library := none,
    pins := [("@effect/sql-sqlite-bun", "4.0.0-rc.112"), ("effect", "4.0.0-rc.112"),
      ("@typescript/native-preview", "7.0.0-dev.20260629.1")] }

/-- A prelude's folder of two files given as data: its root re-exports the other. -/
def prelude : List (String × ByteArray) :=
  [("prelude.ts", "export * from \"./a.ts\"\n".toUTF8), ("a.ts", "export const a = 1\n".toUTF8)]

/-- What `emit --target ts` asks for a module's name, with the kinds given. -/
def specOf (name : String) (kinds : List Compiler.Kind := Compiler.Kind.selectable) : Spec :=
  { name, command := ["emit", "--target", "ts"], kinds, prelude, inputs }

/-- A prelude folder shaped as the library's (`ts/prelude/`): its root imports `effect` and
re-exports a helper. Beside them, the SQLite package's adapter imports the root and
`@effect/sql-sqlite-bun`, and no file of the root's closure imports the adapter. -/
def folder : List (String × ByteArray) :=
  [("prelude.ts", "import { Option } from \"effect\"\nexport * from \"./a.ts\"\n".toUTF8),
   ("a.ts", "export const a = 1\n".toUTF8),
   ("sql.ts", ("import { SqliteClient } from \"@effect/sql-sqlite-bun\"\n" ++
     "import { a } from \"./prelude.ts\"\nexport const Sql = { a }\n").toUTF8)]

/-- A file of `folder` read by its path, as `Prelude.closure` reads the disk; refused when none. -/
def readIn (path : String) : ExceptT String Id ByteArray :=
  match folder.lookup path with
  | some bytes => pure bytes
  | none => throw s!"no file {path}"

/-- The wire corpus's first program, with its name. -/
def first : String × NativeEff := Wire.Corpus.all.head?.getD ("", .succeed (.lit .unit))

/-- The wire corpus's program `pBind`, whose module imports the prelude. -/
def bound : String × NativeEff := ("pBind", Wire.Corpus.pBind)

/-- An application whose one entry adds a literal to its parameter. -/
def offset (literal : Nat) : Application NativeOp :=
  { name := "offset"
    entries := [{ name := "shift", params := [("n", .nat)], body := succeed (Atom.add (var "n") (nat literal)) }] }

/-- An application whose one entry adds a string to a natural. -/
def mixed : Application NativeOp :=
  { name := "mixed", entries := [{ name := "mix", body := succeed (Atom.add (nat 1) (str "x")) }] }

#guard first.1 == "p42"

/-! ## The folder of `p42` -/

-- The files in the order `emit` writes them: the module, the prelude's files its imports reach,
-- the canonical bytes and their tagged print, the certificate, then the manifest. `p42` uses no
-- prelude name and declares no data service, so it has no prelude file and no surface; `pBind`'s
-- module imports the prelude's root, so its folder holds the root's closure, in byte order.
#guard match emitProgram (specOf first.1) first.2, emitProgram (specOf bound.1) bound.2 with
  | .ok e, .ok f => (e.files Kind.selectable).map (fun (a : Artifact) => (a.path, a.kind)) ==
      [("p42.gen.ts", .module), ("p42.eff", .canonical), ("p42.eff.json", .canonical),
       ("certificate.json", .certificate), ("manifest.json", .manifest)] &&
    (f.files Kind.selectable).map (fun (a : Artifact) => (a.path, a.kind)) ==
      [("pBind.gen.ts", .module), ("prelude/a.ts", .prelude), ("prelude/prelude.ts", .prelude),
       ("pBind.eff", .canonical), ("pBind.eff.json", .canonical), ("certificate.json", .certificate),
       ("manifest.json", .manifest)]
  | _, _ => false

-- The manifest, read back from its own bytes, names every other file with the SHA-256 of its bytes,
-- and not itself.
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e =>
    let files := e.files Kind.selectable
    match files.find? (fun (a : Artifact) => a.kind == .manifest) with
    | some m =>
      match NatJson.parse (m.bytes.data.toList.map UInt8.toNat) with
      | .ok t =>
        match t.at? [.key "artifacts"] with
        | some (.arr rows) => rows.length + 1 == files.length &&
            (files.filter fun (a : Artifact) => a.kind != .manifest).all fun a =>
              rows.any fun r => isStr a.path (r.at? [.key "path"]) &&
                isStr (sha256Hex a.bytes) (r.at? [.key "sha256"])
        | _ => false
      | .error _ => false
    | none => false
  | .error _ => false

-- The address, read back from the manifest, is the SHA-256 of the canonical bytes, and those bytes
-- decode to the program; the tagged print reads back to it too.
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e =>
    let files := e.files Kind.selectable
    match files.find? (fun (a : Artifact) => a.path == "p42.eff"),
      files.find? (fun (a : Artifact) => a.path == "p42.eff.json"),
      files.find? (fun (a : Artifact) => a.kind == .manifest) with
    | some canonical, some json, some m =>
      match NatJson.parse (m.bytes.data.toList.map UInt8.toNat) with
      | .ok t => isStr (sha256Hex canonical.bytes) (t.at? [.key "program", .key "address"]) &&
          sha256Hex canonical.bytes == Tools.Code.addressOf first.2 &&
          decide (Wire.decodeProgram canonical.bytes.data.toList = some first.2) && readsBack json.bytes first.2
      | .error _ => false
    | _, _, _ => false
  | .error _ => false

-- The certificate file is the certificate's JSON text and a newline, and the manifest holds the
-- same certificate. Its fields, for `Effect.succeed(42)`: a natural, no error, no key, row, service or
-- definition.
#guard match emitProgram (specOf first.1) first.2, Api.Built.ofProgram {} first.2 with
  | .ok e, .ok b =>
    let files := e.files Kind.selectable
    match files.find? (fun (a : Artifact) => a.kind == .certificate),
      files.find? (fun (a : Artifact) => a.kind == .manifest) with
    | some c, some m =>
      match NatJson.parse (m.bytes.data.toList.map UInt8.toNat) with
      | .ok t =>
        let held := ((t.at? [.key "certificate"]).map NatJson.render).getD []
        c.bytes.data == (jsonBytes (certificate b)).data &&
          held ++ [10] == c.bytes.data.toList.map UInt8.toNat &&
          jsonText (certificate b) == "{\"answer\":{\"_tag\":\"nat\"},\"error\":{\"_tag\":\"never\"}," ++
            "\"requires\":[],\"rows\":[],\"services\":[],\"declarations\":[]}"
      | .error _ => false
    | _, _ => false
  | _, _ => false

-- The manifest records the module's checks the slice owes (formation, typing, the literal profile,
-- the reading boundary's admission of the structured module), and that no target compiler and no
-- run were performed.
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e =>
    match e.manifest.at? [.key "checks", .key "performed"], e.manifest.at? [.key "checks", .key "notPerformed"] with
    | some (.arr performed), some (.arr skipped) =>
      (performed.filter fun c => isStr "module" (c.at? [.key "kind"])).map
          (fun c => match c.at? [.key "check"] with | some (.str s) => s | _ => "") ==
        ["formation", "typing", "profile", "readBack"] && skipped.length == 2
    | _, _ => false
  | .error _ => false

-- The prelude's files stand under `prelude/`, byte for byte, and every relative import of every
-- file resolves to a file of the folder: nothing leaves it.
#guard match emitProgram (specOf bound.1) bound.2 with
  | .ok e =>
    let files := e.files Kind.selectable
    prelude.all (fun (path, bytes) => files.any fun (a : Artifact) =>
        a.path == "prelude/" ++ path && a.kind == .prelude && a.bytes.data == bytes.data) &&
      files.all fun (a : Artifact) => match String.fromUTF8? a.bytes with
        | some text => (Prelude.relativeImports text).all fun s =>
            match Prelude.resolve a.path s with
            | some p => files.any (·.path == p)
            | none => false
        | none => a.kind == .canonical
  | .error _ => false

-- `--emit=module` writes the module and the prelude its imports reach, and no manifest.
#guard match emitProgram (specOf bound.1 [.module]) bound.2 with
  | .ok e => (e.files [.module]).map (fun (a : Artifact) => a.kind) == [.module, .prelude, .prelude]
  | .error _ => false

/-! ## The red control: the profile is the emission's -/

-- One above rc112's bound: `check` admits the application, and its emission refuses at the profile,
-- with the literal.
#guard match check (offset (safeBound + 1)) with
  | .ok b =>
    match emitTs (specOf "offset") b with
    | .error (.emission (.outsideProfile r)) => decide (r.reason = .aboveBound (safeBound + 1))
    | _ => false
  | .error _ => false

-- At the bound itself it emits: the module imports the prelude beside it, and the surface imports
-- the module.
#guard match check (offset safeBound) with
  | .ok b =>
    match emitTs (specOf "offset") b with
    | .ok e =>
      let importsOf (path : String) : List String :=
        match e.artifacts.find? (fun (a : Artifact) => a.path == path) with
        | some a => ((String.fromUTF8? a.bytes).map Prelude.relativeImports).getD []
        | none => []
      importsOf "offset.gen.ts" == ["./prelude/prelude.ts"] &&
        importsOf "offset.surface.gen.ts" == ["./offset.gen.ts"]
    | .error _ => false
  | .error _ => false

/-! ## The command's controls -/

-- An entry that the checker refuses is named, with the checker's located refusal.
#guard match check mixed with
  | .error ⟨some "mix", .typing _⟩ => true
  | _ => false

-- `--emit` reads the kinds it names, and refuses one that is no kind.
#guard Kind.parse "surface,module" == some [.surface, .module] && (Kind.parse "module,bogus").isNone
#guard match Options.read ["--emit=bogus"] {}, Options.read ["--target", "ts", "--out", "ts"] {} with
  | .error _, .ok o => o.target == some "ts" && o.out == some "ts" && o.kinds == Kind.selectable
  | _, _ => false

-- `--group NAME` is read wherever it stands, and the other arguments keep their order; without it
-- there is no group. A `describe` records the `emit` that it describes.
#guard takeGroup ["emit", "--target", "ts", "--group", "corpus", "--out", "o"] ==
    (some "corpus", ["emit", "--target", "ts", "--out", "o"]) &&
  takeGroup ["emit", "--target", "ts"] == (none, ["emit", "--target", "ts"]) &&
  asEmit ["describe", "--group", "corpus", "--target", "ts"] == ["emit", "--group", "corpus", "--target", "ts"]

-- The scan reads re-exports, imports and both quotes, and keeps only relative specifiers; an import
-- that leaves the prelude's folder resolves to nothing, so `closure` refuses it.
#guard Prelude.relativeImports
    "export * from \"./a.ts\"\nimport { b } from './b.ts'\nimport \"./c.ts\"\nimport { Effect } from \"effect\"\n" ==
  ["./a.ts", "./c.ts", "./b.ts"]
#guard Prelude.resolve "prelude.ts" "../outside.ts" == none && Prelude.resolve "sub/x.ts" "../y.ts" == some "y.ts"

/-! ## The packages a folder imports -/

-- A bare specifier names its package: a scoped package by its scope and name, any other by its
-- first segment. A relative specifier names none.
#guard Prelude.packageOf "effect/unstable/persistence" == "effect" &&
  Prelude.packageOf "@effect/sql-sqlite-bun" == "@effect/sql-sqlite-bun" &&
  Prelude.packages "import { a } from \"./a.ts\"\nimport { Ref } from \"effect\"\nimport { K } from 'effect/unstable/persistence'\n" ==
    ["effect"]

-- The manifest's inputs: the toolchain, the provenance, the address and the modules, then each
-- package that the folder's files import with the library's pin, and tsgo's. `p42`'s module imports
-- `effect`; no module closure is given here, so the address is the SHA-256 of no byte.
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e => (e.manifest.at? [.key "inputs"]).map jsonText ==
      some ("{\"lean\":\"leanprover/lean4:v4.33.1\",\"library\":null,\"address\":" ++
        "\"e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855\",\"modules\":{}," ++
        "\"packages\":{\"effect\":\"4.0.0-rc.112\"},\"tsgo\":\"7.0.0-dev.20260629.1\"}")
  | .error _ => false

-- The closure from the root that a module imports holds the root and its helper, never the SQLite
-- package's adapter; the closure from the adapter holds all three; from no file, it is empty.
#guard (Id.run (Prelude.closureOf readIn ["prelude.ts"]).run).toOption.map (·.map (·.1)) ==
    some ["a.ts", "prelude.ts"] &&
  (Id.run (Prelude.closureOf readIn ["sql.ts"]).run).toOption.map (·.map (·.1)) ==
    some ["a.ts", "prelude.ts", "sql.ts"] &&
  (Id.run (Prelude.closureOf readIn []).run).toOption.map (·.length) == some 0 &&
  (Id.run (Prelude.closureOf readIn ["missing.ts"]).run).toOption.isNone

-- The roots of a folder's closure are the prelude's files that its own files import: a module's
-- relative imports under `prelude/`, and nothing that the surface imports from the module.
#guard Prelude.importedBy ["import { a } from \"./prelude/prelude.ts\"\nimport { Sql } from \"./prelude/sql.ts\"\n",
    "import { TodoApp } from \"./todo.gen.ts\"\nimport { b } from \"./prelude/prelude.ts\"\n"] ==
  ["prelude.ts", "sql.ts"]

/-- The library's folder as it stood before 2026-10-20: its root reaches the SQLite package's
adapter, here by a re-export. -/
def folderBefore : List (String × ByteArray) :=
  [("prelude.ts", "export * from \"./a.ts\"\nexport * from \"./sql.ts\"\n".toUTF8)] ++
    folder.filter (·.1 != "prelude.ts")

-- So the wire corpus's folder, whose modules import the root alone, names `effect` and no SQL package.
-- red: over the folder whose root reaches the adapter, the same group names `@effect/sql-sqlite-bun`
-- with its pin.
#guard
  let packagesOf (prelude : List (String × ByteArray)) : Option String :=
    ((emitGroup { specOf "corpus" with prelude } Wire.Corpus.all).toOption.bind
      (·.manifest.at? [.key "inputs", .key "packages"])).map jsonText
  packagesOf folder == some "{\"effect\":\"4.0.0-rc.112\"}" &&
    packagesOf folderBefore == some "{\"@effect/sql-sqlite-bun\":\"4.0.0-rc.112\",\"effect\":\"4.0.0-rc.112\"}"

/-! ## A group: the wire corpus, with one manifest -/

-- The group's files: the prelude's files that its modules reach, once, in byte order, then each
-- program's module, canonical bytes, their tagged print and its certificate under its name, then
-- one manifest. No program of the wire corpus declares a data service, so none has a surface.
#guard match emitGroup (specOf "corpus") Wire.Corpus.all with
  | .ok e => (e.files Kind.selectable).map (fun (a : Artifact) => (a.path, a.kind)) ==
      [("prelude/a.ts", .prelude), ("prelude/prelude.ts", .prelude)] ++
        Wire.Corpus.all.flatMap (fun (name, _) =>
          [(s!"{name}.gen.ts", .module), (s!"{name}.eff", .canonical), (s!"{name}.eff.json", .canonical),
           (s!"{name}.certificate.json", .certificate)]) ++ [("manifest.json", .manifest)]
  | .error _ => false

-- The manifest, read back from its own bytes, names the group and each program in order, with the
-- SHA-256 of that program's canonical bytes as its address. It names every other file with the
-- SHA-256 of its bytes, and not itself.
#guard match emitGroup (specOf "corpus") Wire.Corpus.all with
  | .ok e =>
    let files := e.files Kind.selectable
    match files.find? (fun (a : Artifact) => a.kind == .manifest) with
    | some m =>
      match NatJson.parse (m.bytes.data.toList.map UInt8.toNat) with
      | .ok t =>
        match t.at? [.key "programs"], t.at? [.key "artifacts"] with
        | some (.arr programs), some (.arr rows) =>
          isStr "corpus" (t.at? [.key "group"]) && programs.length == Wire.Corpus.all.length &&
            (programs.zip Wire.Corpus.all).all (fun (entry, name, _) =>
              isStr name (entry.at? [.key "module"]) &&
                (files.find? (fun (a : Artifact) => a.path == s!"{name}.eff")).any fun canonical =>
                  isStr (sha256Hex canonical.bytes) (entry.at? [.key "address"])) &&
            rows.length + 1 == files.length &&
            (files.filter fun (a : Artifact) => a.kind != .manifest).all fun a =>
              rows.any fun r => isStr a.path (r.at? [.key "path"]) &&
                isStr (sha256Hex a.bytes) (r.at? [.key "sha256"])
        | _, _ => false
      | .error _ => false
    | none => false
  | .error _ => false

-- Each program's module in the group is its own emission's module, byte for byte: the group places
-- the programs' emissions side by side, and one manifest stands for theirs.
#guard match emitGroup (specOf "corpus") Wire.Corpus.all with
  | .ok e => Wire.Corpus.all.all fun (name, program) =>
      match emitProgram (specOf name) program with
      | .ok single => (single.artifacts.find? (fun (a : Artifact) => a.kind == .module)).any fun m =>
          (e.artifacts.find? (fun (a : Artifact) => a.path == s!"{name}.gen.ts")).any
            (·.bytes.data == m.bytes.data)
      | .error _ => false
  | .error _ => false

-- red: two programs of one name refuse the group, since their files would share paths.
#guard match emitGroup (specOf "pair") [("p", Wire.Corpus.p42), ("p", Wire.Corpus.pBind)] with
  | .error (.duplicate "p") => true
  | _ => false

-- red: one program above rc112's bound refuses the whole group at the profile, by its name, with
-- the literal; the program inside the bound beside it writes nothing either.
#guard match emitGroup (specOf "bound")
    [("inside", Wire.Corpus.p42), ("above", .succeed (.lit (.nat (safeBound + 1))))] with
  | .error (.member "above" (.emission (.outsideProfile r))) =>
    decide (r.reason = .aboveBound (safeBound + 1))
  | _ => false

/-! ## The read-back of a service module -/

-- The file is the structured module that the dogfood to-do's emission lays out. Each guard builds
-- it, so its rendered bytes stay inside the guard.

-- red: read as the envelope that a host wraps, with no services, the reading boundary refuses the
-- file at its first row service, which names no layer path.
#guard match check Examples.Todo.application with
  | .ok b =>
    match b.typed.emit declaration with
    | .ok e =>
      match e.file preludeImport with
      | .ok file =>
        match Api.admitModule declaration file b.table (Tools.Code.originsAt preludeImport) with
        | .error (.read (.shape "module")) => true
        | _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

-- green: with the table's row services read first, as `Api.readFile` reads them, it admits the
-- file, to exactly the built program; and the to-do emits.
#guard match check Examples.Todo.application with
  | .ok b =>
    match b.typed.emit declaration with
    | .ok e =>
      match e.file preludeImport with
      | .ok file =>
        match Api.admitModule declaration file b.table (Tools.Code.originsAt preludeImport) [] b.table with
        | .ok reading => decide (reading.program = b.program) && (emitTs (specOf "todo") b).toBool
        | .error _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

/-! ## The tree's groups -/

-- The groups of `lake exe effect4`: the wire corpus, the SQLite package's programs, then each
-- example of `Examples.all` under its application's name; only the to-do lowers native roots.
#guard Groups.all.map Source.name == ["corpus", "sql"] ++ Examples.all.map (·.name) &&
  Examples.all.map (·.name) ==
    ["todo", "cachedTodo", "boundedBuffer"] &&
  (Groups.all.filterMap fun
    | .application app lowered => if lowered.roots.isEmpty then none else some app.name
    | .programs .. => none) == ["todo"]

/-! ## A program with a SQL row: the adapter, imported and copied -/

/-- `pSqlite`, the SQLite package's fixture, built at the package's table. -/
def sqlBuilt : Except CheckRefusal Api.Built :=
  checkProgram Test.Api.PackagesContract.pSqlite { rows := Packages.sqliteBun }

-- The module of a program with a SQL row imports `Sql` from the adapter beside it, after the
-- prelude's root, and the reading boundary admits it. Its folder holds the adapter with the root's
-- closure, and the manifest names the SQL package with its pin.
#guard match sqlBuilt with
  | .ok b =>
    match emitTs { specOf "pSqlite" with prelude := folder } b with
    | .ok e =>
      let importsOf (path : String) : List String :=
        match e.artifacts.find? (fun (a : Artifact) => a.path == path) with
        | some a => ((String.fromUTF8? a.bytes).map Prelude.relativeImports).getD []
        | none => []
      importsOf "pSqlite.gen.ts" == ["./prelude/prelude.ts", "./prelude/sql.ts"] &&
        (e.artifacts.filter (·.kind == .prelude)).map (·.path) ==
          ["prelude/a.ts", "prelude/prelude.ts", "prelude/sql.ts"] &&
        (e.manifest.at? [.key "inputs", .key "packages"]).map jsonText ==
          some "{\"@effect/sql-sqlite-bun\":\"4.0.0-rc.112\",\"effect\":\"4.0.0-rc.112\"}"
    | .error _ => false
  | .error _ => false

-- red: the file without the adapter's import, the one the base's emission read, is refused at the
-- reading boundary, by the name `Sql`.
#guard match sqlBuilt with
  | .ok b =>
    match b.typed.emit declaration with
    | .ok e =>
      match e.file preludeImport with
      | .ok file =>
        match Api.admitModule declaration file b.table (Tools.Code.originsAt preludeImport) [] b.table with
        | .error (.unbound "Sql" _) => true
        | _ => false
      | .error _ => false
    | .error _ => false
  | .error _ => false

-- Every program of the group `sql` emits at the package's table: each module imports `Sql` from the
-- adapter, and the group's folder holds the adapter once. control: over the same folder, the wire
-- corpus's group, with no SQL row, holds no adapter.
#guard match emitGroup { specOf "sql" with prelude := folder } Test.Api.PackagesContract.sqlitePrograms
      { rows := Packages.sqliteBun },
    emitGroup { specOf "corpus" with prelude := folder } Wire.Corpus.all with
  | .ok e, .ok c =>
    (e.artifacts.filter (·.kind == .prelude)).map (·.path) ==
        ["prelude/a.ts", "prelude/prelude.ts", "prelude/sql.ts"] &&
      (e.artifacts.filter (·.kind == .module)).length == 5 &&
      (e.artifacts.filter (·.kind == .module)).all (fun a =>
        (((String.fromUTF8? a.bytes).map Prelude.relativeImports).getD []).contains "./prelude/sql.ts") &&
      (c.artifacts.filter (·.kind == .prelude)).map (·.path) == ["prelude/a.ts", "prelude/prelude.ts"]
  | _, _ => false

/-! ## The inputs: the module closure and its address -/

/-- Two modules' sources, as data. -/
def sources : List (String × ByteArray) := [("A", "def a := 1\n".toUTF8), ("B", "def b := 2\n".toUTF8)]

/-- The inputs over some sources: each module with its source's SHA-256. -/
def inputsOver (sources : List (String × ByteArray)) : Inputs :=
  { inputs with modules := sources.map fun (m, bytes) => (m, Store.sha256 bytes.data.toList) }

-- The address is the SHA-256 of the modules' digests, concatenated in the closure's order. red: one
-- changed byte of one source changes it.
#guard (inputsOver sources).address ==
    Store.sha256 (sources.flatMap fun (_, bytes) => (Store.sha256 bytes.data.toList).bytes) &&
  (inputsOver sources).address != (inputsOver [("A", "def a := 1\n".toUTF8), ("B", "def b := 3\n".toUTF8)]).address

-- The manifest writes the inputs in this order, each module by its name with its source's digest.
#guard match (inputsOver sources).json [] with
  | .obj fields => fields.map (·.1) == ["lean", "library", "address", "modules", "packages", "tsgo"] &&
      ((NatJson.obj fields).at? [.key "modules", .key "B"]).map jsonText ==
        some ("\"" ++ (Store.sha256 ("def b := 2\n".toUTF8.data.toList)).hex ++ "\"")
  | _ => false

/-- What this battery's own elaboration knows of its environment (`elaborated%`). -/
def here : Elaborated := elaborated%

-- The closure holds the module itself and the compiler, and no module that the toolchain ships;
-- its names are in byte order.
#guard here.modules.contains "Test.Codegen.CompilerEmit" && here.modules.contains "Compiler.Groups" &&
  here.modules.contains "Compiler.Elaborated" &&
  !here.modules.any (fun m => m.startsWith "Init." || m.startsWith "Lean." || m.startsWith "Std." ||
    m.startsWith "Lake.") &&
  here.modules == here.modules.mergeSort fun a b =>
    Effect4.Codegen.bytesLe a.toUTF8.data.toList b.toUTF8.data.toList

-- The declared names of the closure's literal keys: the dogfood to-do's repository key and the SQL
-- layer's. `check` names a key's declaration beside its spelling, and a key no declaration states
-- prints alone.
#guard here.namesOf ⟨⟨30⟩, ⟨6⟩⟩ == ["Examples.Todo.todoRepoKey"] &&
  here.namesOf ⟨⟨8⟩, ⟨4⟩⟩ == ["Test.Api.PackagesContract.kSql"] &&
  keyLine ⟨⟨1⟩, ⟨9⟩⟩ (here.namesOf ⟨⟨1⟩, ⟨9⟩⟩) == "k1_9" &&
  (match check Examples.Todo.application with
    | .ok b => (certificateLines "todo" b here.namesOf).contains
        "services  TodoRepo k30_6 (Examples.Todo.todoRepoKey)"
    | .error _ => false)

/-! ## The readings: one query of the tool protocol each -/

-- Each guard builds the dogfood to-do (`check`): the service's name is rendered text, so the build
-- stays inside the guards.

-- `rows` is the certificate's rows: the inspection at the root holds the application's table in
-- its signature context, one line a row.
#guard match check Examples.Todo.application with
  | .ok b =>
    match reading b .rows with
    | .ok r => jsonText r.json == jsonText (tree b.table) && (r.text.splitOn "\n").length == 4
    | .error _ => false
  | .error _ => false

-- `types` is the address table: its first line is the root, at the program's type.
#guard match check Examples.Todo.application with
  | .ok b =>
    match reading b .types with
    | .ok r => (r.text.splitOn "\n").head? == some ("[] " ++ Tools.Code.effTyText b.ty)
    | .error _ => false
  | .error _ => false

-- `graph` is the program's public JSON, the bytes of `<name>.eff.json` without their newline, and
-- its indented text reads back to the same tree.
#guard match check Examples.Todo.application with
  | .ok b =>
    match reading b .graph with
    | .ok r => (jsonText r.json).toUTF8.data.toList ++ [10] == (programJson b.program).data.toList &&
        (match NatJson.parse (NatJson.codes r.text) with
          | .ok t => jsonText t == jsonText r.json
          | .error _ => false)
    | .error _ => false
  | .error _ => false

-- `surface` is the service's four methods, as its Schemas state them.
#guard match check Examples.Todo.application with
  | .ok b =>
    match reading b .surface with
    | .ok r => (r.text.splitOn "\n").map (fun l => (l.splitOn "(").headD "") ==
        ["TodoApp.add", "TodoApp.list", "TodoApp.complete", "TodoApp.remove"]
    | .error _ => false
  | .error _ => false

-- control: a program with no service has an empty surface, and the manifest is `describe`'s, no
-- reading.
#guard match checkProgram first.2 with
  | .ok b => (match reading b .surface with
      | .ok r => r.text == "" && jsonText r.json == "[]"
      | .error _ => false) && (reading b .manifest).toOption.isNone
  | .error _ => false

-- The reader of `inspect`'s options: `--what` names a reading, and what is left is `describe`'s.
-- red: a word that names no reading, and no `--what`, are refused. The manifest's command is the
-- `emit` it describes. `--json` is the report's flag, read before the command (`takeFlags`).
#guard What.all.all (fun w => What.parse w.name == some w) && (What.parse "bogus").isNone &&
  (readInspect ["--what", "manifest", "--out", "ts"] none []).toOption ==
    some (.manifest, ["--out", "ts"]) &&
  (readInspect ["--out", "ts"] none []).toOption.isNone &&
  (readInspect ["--what", "bogus"] none []).toOption.isNone &&
  inspectAsEmit ["inspect", "--group", "todo", "--what", "manifest", "--out", "o"] ==
    ["emit", "--group", "todo", "--out", "o"]

/-! ## Relation document forms -/

-- reader: every document form and graph selection has its command spelling.
#guard InspectDocument.Form.all.all (fun f => InspectDocument.Form.parse f.name == some f) &&
  [What.relations, .boundary, .calls, .layers].all What.isDocument &&
  !What.graph.isDocument

-- controls: unknown forms, conflicting forms, missing values and duplicate destinations refuse.
#guard (InspectOptions.read ["--form", "png"] {}).toOption.isNone &&
  (InspectOptions.read ["--form", "md"] { form := .json, explicitForm := true }).toOption.isNone &&
  (InspectOptions.read ["--form"] {}).toOption.isNone &&
  (InspectOptions.read ["--out"] {}).toOption.isNone &&
  (InspectOptions.read ["--session"] {}).toOption.isNone &&
  (InspectOptions.read ["--out", "one", "--out", "two"] {}).toOption.isNone &&
  (InspectOptions.read ["--session", "one", "--session", "two"] {}).toOption.isNone &&
  (InspectOptions.read ["--out", "--form", "json"] {}).toOption.isNone

-- reader: the session adapter uses the same checked constructor as direct library use.
#guard match check Examples.Todo.application with
  | .ok b => (inspectBuilt b (some "TodoApp")).toOption.isSome &&
      (inspectBuilt b (some "unknown-service")).toOption.isNone
  | .error _ => false

-- finite evaluation: TSV projects JSON cells, preserving a tab, newline and literal backslash.
#guard (InspectDocument.table (Tools.Document.Json.algebra.table ["column"]
    [[[.text "one\ttwo\nthree\\four"]]])).toOption ==
  some "column\none\\ttwo\\nthree\\\\four\n"

-- finite evaluation: the part key names its relation file; the JSON table remains the source.
#guard match InspectDocument.files .tsv "todo"
    { title := "rows", body := [.part "relation-nodes" "Nodes"
      [.table ["address"] [[[.code "0.0"]]]]] } with
  | .ok files => files == [("todo.relation-nodes.gen.tsv", "address\n0.0\n")]
  | .error _ => false

-- controls: ownership excludes other programs, forms, ordinary files and empty figure names.
#guard InspectDocument.owns .svg "todo" "todo.old.gen.svg" &&
  !InspectDocument.owns .svg "todo" "todo2.old.gen.svg" &&
  !InspectDocument.owns .svg "todo" "todo%2Eother.old.gen.svg" &&
  !InspectDocument.owns .svg "todo" "todo.old.gen.tsv" &&
  !InspectDocument.owns .svg "todo" "todo.notes.svg" &&
  !InspectDocument.owns .svg "todo" "todo.gen.svg" &&
  !InspectDocument.owns .md "todo" "todo.old.gen.md"

-- finite evaluation: a dot in a program name cannot alias the figure-key separator.
#guard match InspectDocument.files .tsv "todo.other"
    { title := "row", body := [.part "relation-nodes" "Nodes" [.table ["a"] []]] } with
  | .ok [(name, _)] => name == "todo%2Eother.relation-nodes.gen.tsv" &&
      InspectDocument.owns .tsv "todo.other" name && !InspectDocument.owns .tsv "todo" name
  | _ => false

-- controls: refuse path syntax and malformed graph edges before rendering any artifact.
#guard !(InspectDocument.files .md "../todo" { title := "none", body := [] }).toOption.isSome &&
  !(InspectDocument.files .svg "todo"
    { title := "bad", body := [.graph "bad" "bad" [] [("missing", "missing")]] }).toOption.isSome

-- finite evaluation: SVG uses the existing figure output, one artifact for the graph key.
#guard match InspectDocument.files .svg "todo"
    { title := "one", body := [.graph "boundary" "Boundary" [{ key := "main", label := "main" }] []] } with
  | .ok [(name, bytes)] => name == "todo.boundary.gen.svg" && (bytes.splitOn "<svg").length > 1
  | _ => false

/-! ## The defaults -/

-- `ts` is the target when none is named, `--pretty` is read, and `describe --pretty` records the
-- `emit` that it describes.
#guard (match Options.read [] {} with | .ok o => o.target.isNone && !o.pretty | .error _ => false) &&
  (match Options.read ["--pretty"] {} with | .ok o => o.pretty | .error _ => false) &&
  asEmit ["describe", "--pretty", "--out", "o"] == ["emit", "--out", "o"]

-- `describe --pretty` prints the manifest indented: two spaces a level, and the profile's reader
-- reads it back to the same tree.
#guard prettyText (.obj [("a", .arr [.nat 1, .obj []]), ("b", .str "x")]) ==
  "{\n  \"a\": [\n    1,\n    {}\n  ],\n  \"b\": \"x\"\n}"
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e =>
    match NatJson.parse (NatJson.codes (prettyText e.manifest)) with
    | .ok t => jsonText t == jsonText e.manifest
    | .error _ => false
  | .error _ => false

/-! ## The native target -/

-- The empty recipe gives the project's corrective action. The dogfood's declared roots admit.
#guard match ({} : Lowered).validate, Groups.todoLowered.validate with
  | .error why, .ok () => why.startsWith "no lowered roots:"
  | _, _ => false
#guard match Options.read ["--target", "ocaml", "--check"] {} with
  | .ok o => o.target == some "ocaml" && o.nativeCheck
  | .error _ => false
#guard Lowered.validName "todo_2" && Lowered.validName "Todo" &&
  !Lowered.validName "" && !Lowered.validName "2todo" && !Lowered.validName "_todo" &&
  !Lowered.validName "équipe" && !Lowered.validName "../todo"

-- The application supplies the ordinary v3 recipe, with names as data and one type owner.
#guard
  let recipe := Groups.todoLowered.recipe "todo"
  isStr "effect4-lcnf-roots-v3" (recipe.at? [.key "format"]) &&
    isStr "todo_gen.ml" (recipe.at? [.key "artifacts", .index 0, .key "out"])

-- A native manifest names its own artifacts and versions. An unchecked emission claims no
-- native compilation; --check adds that check, and neither mode claims a run.
#guard match checkProgram first.2 with
  | .error _ => false
  | .ok b =>
    let recipe := Groups.todoLowered.recipe "todo"
    let pins := Native.inputsJson inputs "library-commit" "ocaml-version" "zarith-version" (.arr [])
    let spec := { specOf "todo" with command := ["emit", "--target", "ocaml"] }
    let e := Native.emission spec b recipe "module bytes" "closure bytes" pins false
      (Native.command "lowering.json")
    isStr "ocaml" (e.manifest.at? [.key "target"]) &&
    isStr "ocaml-version" (e.manifest.at? [.key "inputs", .key "ocaml"]) &&
    isStr "zarith-version" (e.manifest.at? [.key "inputs", .key "zarith"]) &&
    (e.artifacts.map fun a => (a.path, a.kind)).take 3 ==
      [("todo_gen.ml", .module), ("closure-todo_gen.tsv", .closure), ("lowering.json", .recipe)] &&
    !(Native.checks false).any (·.name == "ocamlopt") &&
    (Native.checks true).any (·.name == "ocamlopt") &&
    (match e.manifest.at? [.key "checks", .key "notPerformed"] with
    | some (.arr checks) => checks.any (fun t => isStr "no program or host has run" (some t))
    | _ => false)

end Test.Codegen.CompilerEmit
