import Compiler.Check
import Compiler.Prelude
import Effect4.Api.Codegen
import Effect4.Store.Domain.JsonText
import Effect4.Store.Domain.ProgramWire
import Compiler.GeneratedStamp

/-!
# Compiler.Emit — a built program as one self-contained TypeScript folder

`emit --target ts` (`docs/research/2026-10-20-compiler-entry/README.md`, §5, E3 and E4) is the
print fold of §2 over a built program. Everything it writes is computed here, with no IO
(`emitTs`), and every check runs before a file is written. The folder holds:

- `<name>.gen.ts`, the checked emission (`Api.Typed.emit`, `ModuleEmission.file`) laid out as every
  producer lays a module out (`moduleFile`); it imports `./prelude/prelude.ts`, and the reading
  boundary admits it (`Api.admitModule`, its row services read first);
- `prelude/`, the prelude's import closure (`Compiler.Prelude.closure`), byte for byte;
- `<name>.surface.gen.ts`, the Schemas of each data service's methods
  (`ModuleEmission.surface`), when the program declares a data service;
- `<name>.eff`, the canonical bytes (`Api.bytesOf`), and `<name>.eff.json`, their tagged print
  with each list an array (`Compiler.programJson`);
- `certificate.json`, the certificate as `check --json` prints it (`Compiler.certificate`);
- `manifest.json` (`manifest`): the program and its address, the certificate, the profile, the
  target, each file written with its kind and SHA-256, the pins, the checks, and the command.

**One artifact mechanics** (decision E6). Every producer of a printed module calls it: the
compiler, the code generator's folder (`tools/Drivers/Emit.lean`), the printed corpus
(`tools/Drivers/Corpus.lean`) and the truth corpus (`tools/Drivers/Truth.lean`). Their
observations stay their own: the index and the trees, the diagnostics modules and the JSON
oracles, the run expectations and `corpus.json`.

- **The module text** (`moduleFile`): the module laid out at Effect's width, then one newline.
- **The header**: the compiler's names the program's address first (`header`), and a lane's
  names its producer and the command that regenerates it (`generatedHeader`).
- **The address**: the SHA-256 of the canonical bytes (`Tools.Code.addressOf`). The canonical bytes
  and their JSON print carry no header: it would change the bytes the address is taken of, and the
  print that `ts/eff`'s `toJson` writes. The manifest names them.
- **The manifest**: each file written with its kind and its SHA-256, the pins, the checks and the
  command (`manifestFields`), after the program (`manifest`) or a group's programs
  (`groupManifest`).

**A group** (`emitGroup`) is programs, each admitted at the empty application, as the wire corpus
is. Each is emitted under its own name, its certificate as `<name>.certificate.json`; the
prelude's closure is written once, and one manifest names every file. A second run with the same
command and pins writes the same bytes: nothing written depends on the time, and the output
folder appears only as the command spells it.

What it does not establish: tsgo's typing of the printed text, and any run (`notPerformed`).
-/

namespace Compiler

open Effect4 Effect4.Program Effect4.Store

/-- **An artifact's kind** (rustc's output types, as data): what `--emit` selects, and the
manifest's `kind`. The prelude is written with the module that imports it. -/
inductive Kind where
  | module
  | prelude
  | surface
  | canonical
  | certificate
  | manifest
  deriving DecidableEq, Repr

/-- A kind's name, in `--emit` and in the manifest. -/
def Kind.name : Kind → String
  | .module => "module"
  | .prelude => "prelude"
  | .surface => "surface"
  | .canonical => "canonical"
  | .certificate => "certificate"
  | .manifest => "manifest"

/-- The kind that selects a kind: the module selects the prelude. -/
def Kind.selector : Kind → Kind
  | .prelude => .module
  | k => k

/-- The kinds `--emit` names, in the order `emit` writes them. -/
def Kind.selectable : List Kind := [.module, .surface, .canonical, .certificate, .manifest]

/-- The kinds of `--emit=k₁,k₂,…`; `none` when one is no selectable kind's name. -/
def Kind.parse (text : String) : Option (List Kind) :=
  (text.splitOn ",").mapM fun s => Kind.selectable.find? (·.name == s)

/-- **One file an emission writes**: its path under the output folder, its kind and its bytes. -/
structure Artifact where
  path : String
  kind : Kind
  bytes : ByteArray

/-- The SHA-256 of a file's bytes, in hexadecimal. -/
def sha256Hex (bytes : ByteArray) : String := Digest.hex (Store.sha256 bytes.data.toList)

/-- A file as the manifest lists it: its path, its kind and the SHA-256 of its bytes. -/
def Artifact.json (a : Artifact) : NatJson :=
  .obj [("path", .str a.path), ("kind", .str a.kind.name), ("sha256", .str (sha256Hex a.bytes))]

/-- **The pins an emission records** (the manifest's `inputs`, decision E3). The import closure of
the application's Lean modules, with their digests, is a later addition: it is absent. -/
structure Inputs where
  /-- the Lean toolchain, as the library's `lean-toolchain` names it -/
  lean : String
  /-- the library's Git commit; `none` when its checkout has none. Uncommitted edits in the
  checkout are not recorded. -/
  library : Option String
  /-- Effect's version, as the library's TypeScript package pins it -/
  effect : String
  /-- tsgo's version, as the library's TypeScript package pins it -/
  tsgo : String

/-- The pins as the manifest writes them. -/
def Inputs.json (i : Inputs) : NatJson :=
  .obj [("lean", .str i.lean), ("library", (i.library.map NatJson.str).getD .null),
    ("effect", .str i.effect), ("tsgo", .str i.tsgo)]

/-- **What an emission is asked for**: the module's name, which names its files; the command's
arguments as given; the kinds to write; the prelude's import closure; and the pins. For an
application the name is the application's own: a library entry called by static import (E1) is
given a value, not the Lean module and declaration that hold it, so the manifest cannot name them.
A group's program writes its certificate under its own name (`emitGroup`). -/
structure Spec where
  name : String
  command : List String
  kinds : List Kind := Kind.selectable
  prelude : List (String × ByteArray)
  inputs : Inputs
  certificatePath : String := "certificate.json"

/-- **One check of an emission**: the kind of artifact it speaks of, its name, the declaration that
performs it, what it establishes, and its limit. -/
structure Check where
  kind : Kind
  name : String
  declaration : Lean.Name
  established : String
  limit : String

/-- A check as the manifest writes it. -/
def Check.json (c : Check) : NatJson :=
  .obj [("kind", .str c.kind.name), ("check", .str c.name), ("declaration", .str c.declaration.toString),
    ("established", .str c.established), ("limit", .str c.limit)]

/-- **The checks every emission performs**, before it writes a file. -/
def checks : List Check :=
  [⟨.module, "formation", ``Effect4.Program.Formation.checkInput,
    "The program and its rows are formed: distinct record fields, string map keys, admitted deferred errors, and no type variable outside a row template.",
    "It says nothing about typing."⟩,
   ⟨.module, "typing", ``Effect4.Program.checkTypedProgram,
    "The checker types the program at its rows' signature, and the module declares that type.",
    "Core typing: tsgo has not typed the printed text."⟩,
   ⟨.module, "profile", ``Effect4.Program.ProfileData.literalRefusal,
    "Every natural literal of the program is at most the profile's natBound: rc112.literalRefusal program = none.",
    "Literals only: arithmetic inside a run is not checked here."⟩,
   ⟨.module, "readBack", ``Effect4.Api.admitModule,
    "The reading boundary admits the structured module that the text lays out: every name it uses is bound in it or imported from effect or from ./prelude/prelude.ts; it reads back, its row services first as Api.readFile reads, to exactly this program, formed, inside the profile and typed at its rows; and its envelope is the printer's.",
    "The text is not parsed: it is the admitted module laid out. A bound name is a lexical fact that gives effect no meaning, and the boundary is no target type checking."⟩,
   ⟨.surface, "bindings", ``Effect4.Api.checkSourceBindings,
    "Every name the surface uses is bound in it, or imported from effect, from the module or from the prelude.",
    "Its Schemas are typed by tsgo in a project, and no gate runs them since 2026-10-18."⟩,
   ⟨.canonical, "decode", ``Effect4.Program.Wire.decodeProgram,
    "The canonical bytes decode to exactly this program, and the address is their SHA-256.",
    "The bytes name the program; they state nothing of its meaning."⟩,
   ⟨.canonical, "readJson", ``Effect4.Store.Canonical.readLocated,
    "The tagged print reads back to exactly this program under the profile's JSON reader.",
    "A reader in another language is checked by its own lane, not here."⟩,
   ⟨.certificate, "admission", ``Effect4.Api.Author.build,
    "The build admitted the program at its application: elaboration, the table, typing and the execution checks.",
    "A certificate states types; it states no run."⟩,
   ⟨.prelude, "copy", ``Compiler.Prelude.closure,
    "The prelude's import closure, copied byte for byte from the library at the commit in inputs.",
    "The library's target lane runs the prelude's self-test table (tools/target/prelude.test.ts); this copy is not run here."⟩]

/-- **What no emission performs.** -/
def notPerformed : List String :=
  ["a target compiler: tsgo 7 has not checked the module or the surface",
   "a run: no program has run on Effect"]

/-- **Why `emit` refuses**: `check`'s refusal, or a step of the TypeScript emission with its own
refusal. -/
inductive EmitRefusal where
  | check (why : CheckRefusal)
  /-- The emission's checker refuses the program at its rows' signature, at the located refusal
  that `Api.explain` names. -/
  | emissionTyping (why : Option TypeRefusal)
  /-- The checked emission (`Api.Typed.emit`): the target's support, formation, the profile or the
  printer. -/
  | emission (why : Codegen.EmissionRefusal)
  /-- The module as a file (`ModuleEmission.file`), refused by a row's spelling. -/
  | file (why : PrintRefusal)
  /-- The surface (`ModuleEmission.surface`), refused where a type has no TypeScript type. -/
  | surface (why : PrintRefusal)
  /-- The reading boundary refuses the structured module (`Api.admitModule`), or admits it to
  another program. -/
  | readBack (why : Option Codegen.SurfaceRefusal)
  /-- The lexical check refuses the surface's names (`Api.checkSourceBindings`). -/
  | bindings (why : Codegen.SurfaceRefusal)
  /-- The canonical bytes or their tagged print do not read back to the program. -/
  | canonical (part : String)
  /-- A program of a group refuses (`emitGroup`), by its name. -/
  | member (name : String) (why : EmitRefusal)
  /-- Two programs of a group share a name, so their files would share paths. -/
  | duplicate (name : String)

/-- A refusal as text: the step, then its refusal through its generated encoder where its carrier
has one (`tree`), or the words the tree already gives it (`Tools.Code.surfaceText`); a group's
program, by its name. -/
def EmitRefusal.text : EmitRefusal → String
  | .check why => why.text
  | .emissionTyping (some why) => "the emission's checker refuses: " ++ jsonText (tree why)
  | .emissionTyping none => "the emission's checker refuses the program"
  | .emission (.print why) => "the printer refuses: " ++ jsonText (tree why)
  | .emission (.formation why) => "formation refuses: " ++ jsonText (tree why)
  | .emission (.outsideProfile why) =>
    "the profile refuses: " ++ Tools.Code.surfaceText (.outsideProfile why)
  | .emission .illTyped => "the emission's checker refuses the program"
  | .file why => "the module's file refuses: " ++ jsonText (tree why)
  | .surface why => "the surface refuses: " ++ jsonText (tree why)
  | .readBack none => "the module reads back to another program"
  | .readBack (some why) => "the reading boundary refuses the module: " ++ Tools.Code.surfaceText why
  | .bindings why => "the surface's names are not bound: " ++ Tools.Code.surfaceText why
  | .canonical part => s!"the {part} does not read back to the program"
  | .member name why => s!"the program {name}: " ++ why.text
  | .duplicate name => s!"two programs are named {name}"

/-- The path the printed module and its surface import the prelude from: the folder beside them. -/
def preludeImport : String := "./prelude/prelude.ts"

/-- The name the printed module exports the program's main under. -/
def declaration : String := "main"

/-- The names a module exports: its exported constants and classes. -/
def exportedNames (m : TypeScript.Module) : List String :=
  m.decls.filterMap fun
    | .const d => if d.exported then some d.name else none
    | .classDecl c => if c.exported then some c.name else none
    | _ => none

/-- Whether a program's tagged print reads back to it: the profile's text reader (`NatJson.parse`),
then the shape's located reader (`Canonical.readLocated`). -/
def readsBack (json : ByteArray) (program : NativeEff) : Bool :=
  match NatJson.parse (json.data.toList.map UInt8.toNat) with
  | .ok t =>
    match Canonical.readLocated (α := Eff NativeOp) t with
    | .ok p => decide (p = program)
    | .error _ => false
  | .error _ => false

/-! ## One artifact mechanics -/

/-- **A printed module's file**: the module laid out at Effect's width under its header
(`Tools.Code.moduleText`), then exactly one newline (`GeneratedStamp.endWithOneNewline`). Every
printed module that a producer writes is this text: the compiler's emission, the code generator's
folder (`tools/Drivers/Emit.lean`), the printed corpus's modules (`tools/Drivers/Corpus.lean`) and
the truth corpus (`tools/Drivers/Truth.lean`). -/
def moduleFile (m : TypeScript.Module) : String :=
  Tools.GeneratedStamp.endWithOneNewline (Tools.Code.moduleText Tools.Code.Ts.width m)

/-- **A printed module's header**: its title, then the program's address (`Tools.Code.addressOf`),
then the producer's rows, laid out as a header block (`Tools.Code.headerBlock`). -/
def header (title address : String) (rows : List (String × List String)) : List String :=
  Tools.Code.headerBlock title (("program", [s!"sha256 {address}"]) :: rows)

/-- **A lane's module header**: the stamp of the producer and what it writes from
(`GeneratedStamp.note`), then the command that regenerates the module. The printed corpus's
modules and the truth corpus's are written under it. -/
def generatedHeader (producer command : String) : List String :=
  [Tools.GeneratedStamp.note producer ++ ".", s!"Regenerate: {command}"]

/-- The command as one line of a header: the arguments as given. -/
def commandLine (command : List String) : String := " ".intercalate command

/-- The header's manifest row, when a manifest is written. -/
def manifestRow (spec : Spec) : List (String × List String) :=
  if spec.kinds.contains .manifest then [("manifest", ["./manifest.json"])] else []

/-- **The printed module's header**: the program's address and type, the command, what was
checked of it, whether `run_eq_meaning` covers it, and its manifest. -/
def moduleHeader (spec : Spec) (b : Api.Built) (address : String) : List String :=
  header (s!"{spec.name}: " ++ Tools.GeneratedStamp.note "the Effect4 compiler, Compiler.main") address
    ([("type", [Tools.Code.effTyText b.ty]),
      ("command", [commandLine spec.command]),
      ("checked", ["formed, typed and inside the profile rc112; the reading boundary admits the structured",
        "module (Api.admitModule): its names are bound, it reads back to this program, and its envelope",
        "is the printer's; this text is that module laid out"]),
      ("covered", [if Denote.Straight b.program then "run_eq_meaning (the straight fragment)"
        else "outside the straight fragment"])] ++ manifestRow spec)

/-- **The surface's header**: the program's address, the command, the module it imports, what was
checked of it, and its manifest. -/
def surfaceHeader (spec : Spec) (address : String) : List String :=
  header (s!"{spec.name} surface: " ++ Tools.GeneratedStamp.note "the Effect4 compiler, Compiler.main")
    address
    ([("command", [commandLine spec.command]),
      ("module", [s!"./{spec.name}.gen.ts"]),
      ("checked", ["the Schemas of each data service's methods, from the program's checked types; its",
        "names are bound (Api.checkSourceBindings)"])] ++ manifestRow spec)

/-- **An emission**: the files it writes, the manifest excluded, and the manifest that names them. -/
structure Emission where
  artifacts : List Artifact
  manifest : NatJson

/-- The files `emit` writes: the artifacts, then the manifest when it is selected. The manifest
lists every other file written, and never itself. -/
def Emission.files (e : Emission) (kinds : List Kind) : List Artifact :=
  e.artifacts ++
    (if kinds.contains .manifest then [⟨"manifest.json", .manifest, jsonBytes e.manifest⟩] else [])

/-- **The manifest's fields after its programs**: the profile; the target; each file written; the
pins, with no module closure yet (`Inputs`); the checks performed and those not performed; and the
command's arguments as given. An emission's manifest and a group's share them. -/
def manifestFields (spec : Spec) (written : List Artifact) : List (String × NatJson) :=
  [("profile", .obj [("declaration", .str (``Effect4.Program.rc112).toString),
      ("name", .str rc112.name), ("natBound", match rc112.natBound with | some b => .nat b | none => .null)]),
    ("target", .str "ts"),
    ("artifacts", .arr (written.map Artifact.json)),
    ("inputs", spec.inputs.json),
    ("checks", .obj [("performed", .arr (checks.map Check.json)),
      ("notPerformed", .arr (notPerformed.map NatJson.str))]),
    ("command", .arr (spec.command.map NatJson.str))]

/-- A program as a manifest names it: its module's name, its declaration and its address. -/
def programEntry (name address : String) : List (String × NatJson) :=
  [("module", .str name), ("declaration", .str declaration), ("address", .str address)]

/-- **The manifest** (decision E3): the program, its declaration and its address; the certificate;
then the fields every manifest shares (`manifestFields`). -/
def manifest (spec : Spec) (b : Api.Built) (address : String) (written : List Artifact) : NatJson :=
  .obj ([("program", .obj (programEntry spec.name address)), ("certificate", certificate b)] ++
    manifestFields spec written)

/-- **A built program's TypeScript emission**, every check run before anything is written; or the
step that refuses, with its refusal. The module's file is admitted by the reading boundary, its
row services read first as `Api.readFile` reads them (`Api.admitModule`). -/
def emitTs (spec : Spec) (b : Api.Built) : Except EmitRefusal Emission := do
  let program := b.program
  let table := b.table
  let emission ← match b.typed.emit declaration with
    | .ok e => pure e
    | .error .illTyped => throw (.emissionTyping (Api.explain program { rows := table }))
    | .error why => throw (.emission why)
  let file ← (emission.file preludeImport).mapError .file
  let moduleOrigins := Tools.Code.originsAt preludeImport
  match Api.admitModule declaration file table moduleOrigins [] table with
  | .ok reading => unless decide (reading.program = program) do throw (.readBack none)
  | .error why => throw (.readBack (some why))
  let modulePath := s!"./{spec.name}.gen.ts"
  let surface ← (emission.surface preludeImport modulePath).mapError .surface
  let surfaceOrigins := moduleOrigins ++ [.imported "effect" (some "Schema")] ++
    (exportedNames file).map fun n => .imported modulePath (some n)
  if !surface.decls.isEmpty && (Api.checkSourceBindings surface surfaceOrigins).isNone then
    throw (.bindings (Codegen.lexicalRefusal surfaceOrigins surface))
  let bytes := Api.bytesOf program
  unless decide (Wire.decodeProgram bytes = some program) do throw (.canonical "canonical bytes")
  let json := programJson program
  unless readsBack json program do throw (.canonical "tagged print")
  let address := Tools.Code.addressOf program
  let surfaceFiles : List Artifact := if surface.decls.isEmpty then [] else
    [⟨s!"{spec.name}.surface.gen.ts", .surface,
      (moduleFile { surface with header := surfaceHeader spec address }).toUTF8⟩]
  let files : List Artifact :=
    [⟨s!"{spec.name}.gen.ts", .module, (moduleFile { file with header := moduleHeader spec b address }).toUTF8⟩] ++
      spec.prelude.map (fun (path, bytes) => ⟨"prelude/" ++ path, .prelude, bytes⟩) ++ surfaceFiles ++
      [⟨s!"{spec.name}.eff", .canonical, ⟨bytes.toArray⟩⟩, ⟨s!"{spec.name}.eff.json", .canonical, json⟩,
       ⟨spec.certificatePath, .certificate, jsonBytes (certificate b)⟩]
  let written := files.filter fun a => spec.kinds.contains a.kind.selector
  pure ⟨written, manifest spec b address written⟩

/-- **A program's emission with no application**: the program admitted at the empty application
(`checkProgram`), then emitted (`emitTs`). A program of the wire corpus is one. -/
def emitProgram (spec : Spec) (program : NativeEff) : Except EmitRefusal Emission :=
  (checkProgram program).mapError .check >>= emitTs spec

/-! ## A group -/

/-- The first name that two entries of a list share, if any. -/
def sharedName : List String → Option String
  | [] => none
  | n :: rest => if rest.contains n then some n else sharedName rest

/-- **A group's manifest**: the group's name; each program with its module's name, its declaration,
its address and its certificate; then the fields every manifest shares (`manifestFields`). -/
def groupManifest (spec : Spec) (programs : List (String × Api.Built)) (written : List Artifact) :
    NatJson :=
  .obj ([("group", .str spec.name),
    ("programs", .arr (programs.map fun (name, b) =>
      .obj (programEntry name (Tools.Code.addressOf b.program) ++ [("certificate", certificate b)])))] ++
    manifestFields spec written)

/-- **A group's emission** (`lake exe effect4 emit --group G`): each program admitted at the empty
application (`checkProgram`) and emitted under its own name (`emitTs`), its certificate as
`<name>.certificate.json`; then the prelude's import closure once, before the programs' files; and
one manifest that names every file written (`groupManifest`). Every program's checks run before a
file is written. A refusal names its program, and two programs with one name are refused. -/
def emitGroup (spec : Spec) (programs : List (String × NativeEff)) : Except EmitRefusal Emission := do
  if let some name := sharedName (programs.map (·.1)) then throw (.duplicate name)
  let emitted ← programs.mapM fun (name, program) => do
    let b ← (checkProgram program).mapError fun why => .member name (.check why)
    let e ← (emitTs { spec with name, certificatePath := s!"{name}.certificate.json" } b).mapError
      (.member name)
    pure (name, b, e)
  let prelude := (emitted.head?.map fun (_, _, e) => e.artifacts.filter (·.kind == .prelude)).getD []
  let written := prelude ++ emitted.flatMap fun (_, _, e) => e.artifacts.filter (·.kind != .prelude)
  pure ⟨written, groupManifest spec (emitted.map fun (name, b, _) => (name, b)) written⟩

end Compiler
