import Compiler.Check
import Compiler.Prelude
import Effect4.Api.Codegen
import Effect4.Store.Domain.JsonText
import Effect4.Store.Domain.ProgramWire
import Tools.GeneratedStamp

/-!
# Compiler.Emit — a built program as one self-contained TypeScript folder

`emit --target ts` (`docs/research/2026-10-20-compiler-entry/README.md`, §5, E3 and E4) is the
print fold of §2 over a built program. Everything it writes is computed here, with no IO
(`emitTs`), and every check runs before a file is written. The folder holds:

- `<name>.gen.ts`, the checked emission (`Api.Typed.emit`, `ModuleEmission.file`) laid out as every
  lane lays a module out (`Tools.Code.moduleText`); it imports `./prelude/prelude.ts`;
- `prelude/`, the prelude's import closure (`Compiler.Prelude.closure`), byte for byte;
- `<name>.surface.gen.ts`, the Schemas of each data service's methods
  (`ModuleEmission.surface`), when the program declares a data service;
- `<name>.eff`, the canonical bytes (`Api.bytesOf`), and `<name>.eff.json`, their tagged print
  with each list an array (`Compiler.programJson`);
- `certificate.json`, the certificate as `check --json` prints it (`Compiler.certificate`);
- `manifest.json` (`manifest`): the program and its address, the certificate, the profile, the
  target, each file written with its kind and SHA-256, the pins, the checks, and the command.

The address is the SHA-256 of the canonical bytes (`Tools.Code.addressOf`). The header of each
printed module names it and the command (`Tools.Code.headerBlock`). The canonical bytes and their
JSON print carry no header: it would change the bytes the address is taken of, and the print that
`ts/eff`'s `toJson` writes. The manifest names them. A second run with the same command and pins
writes the same bytes: nothing written depends on the time, and the output folder appears only as
the command spells it.

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
given a value, not the Lean module and declaration that hold it, so the manifest cannot name them. -/
structure Spec where
  name : String
  command : List String
  kinds : List Kind := Kind.selectable
  prelude : List (String × ByteArray)
  inputs : Inputs

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
   ⟨.module, "readBack", ``Effect4.Api.readFile,
    "The structured module that the text lays out reads back to exactly this program.",
    "The text is not parsed. The reading boundary's envelope check, Api.admitModule, reads no service declaration, so it is not run."⟩,
   ⟨.module, "bindings", ``Effect4.Api.checkSourceBindings,
    "Every name the module uses is bound in it, or imported from effect or from ./prelude/prelude.ts.",
    "A lexical fact: it gives effect no meaning and checks no annotation."⟩,
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
    "No lane runs its atoms' fixed cases since 2026-10-20."⟩]

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
  /-- The structured module does not read back (`Api.readFile`), or reads back to another program. -/
  | readBack (why : Option ReadRefusal)
  /-- The lexical check refuses the module's or the surface's names (`Api.checkSourceBindings`). -/
  | bindings (part : String) (why : Codegen.SurfaceRefusal)
  /-- The canonical bytes or their tagged print do not read back to the program. -/
  | canonical (part : String)

/-- A refusal as text: the step, then its refusal through its generated encoder where its carrier
has one (`tree`), or the words the tree already gives it (`Tools.Code.surfaceText`). -/
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
  | .readBack (some why) => "the module does not read back: " ++ jsonText (tree why)
  | .bindings part why => s!"the {part}'s names are not bound: " ++ Tools.Code.surfaceText why
  | .canonical part => s!"the {part} does not read back to the program"

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

/-- The command as one line of a header: the arguments as given. -/
def commandLine (command : List String) : String := " ".intercalate command

/-- The header's manifest row, when a manifest is written. -/
def manifestRow (spec : Spec) : List (String × List String) :=
  if spec.kinds.contains .manifest then [("manifest", ["./manifest.json"])] else []

/-- **The printed module's header**: the program's address and type, the command, what was
checked of it, whether `run_eq_meaning` covers it, and its manifest. -/
def moduleHeader (spec : Spec) (b : Api.Built) (address : String) : List String :=
  Tools.Code.headerBlock (s!"{spec.name}: " ++ Tools.GeneratedStamp.note "the Effect4 compiler, Compiler.main")
    ([("program", [s!"sha256 {address}"]), ("type", [Tools.Code.effTyText b.ty]),
      ("command", [commandLine spec.command]),
      ("checked", ["formed, typed and inside the profile rc112; the structured module reads back to this",
        "program (Api.readFile) and its names are bound (Api.checkSourceBindings); this text is that",
        "module laid out"]),
      ("covered", [if Denote.Straight b.program then "run_eq_meaning (the straight fragment)"
        else "outside the straight fragment"])] ++ manifestRow spec)

/-- **The surface's header**: the program's address, the command, the module it imports, what was
checked of it, and its manifest. -/
def surfaceHeader (spec : Spec) (address : String) : List String :=
  Tools.Code.headerBlock
    (s!"{spec.name} surface: " ++ Tools.GeneratedStamp.note "the Effect4 compiler, Compiler.main")
    ([("program", [s!"sha256 {address}"]), ("command", [commandLine spec.command]),
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

/-- **The manifest** (decision E3): the program, its declaration and its address; the certificate;
the profile; the target; each file written; the pins, with no module closure yet (`Inputs`); the
checks performed and those not performed; and the command's arguments as given. -/
def manifest (spec : Spec) (b : Api.Built) (address : String) (written : List Artifact) : NatJson :=
  .obj [("program", .obj [("module", .str spec.name), ("declaration", .str declaration),
      ("address", .str address)]),
    ("certificate", certificate b),
    ("profile", .obj [("declaration", .str (``Effect4.Program.rc112).toString),
      ("name", .str rc112.name), ("natBound", .nat rc112.natBound)]),
    ("target", .str "ts"),
    ("artifacts", .arr (written.map Artifact.json)),
    ("inputs", spec.inputs.json),
    ("checks", .obj [("performed", .arr (checks.map Check.json)),
      ("notPerformed", .arr (notPerformed.map NatJson.str))]),
    ("command", .arr (spec.command.map NatJson.str))]

/-- **A built program's TypeScript emission**, every check run before anything is written; or the
step that refuses, with its refusal. -/
def emitTs (spec : Spec) (b : Api.Built) : Except EmitRefusal Emission := do
  let program := b.program
  let table := b.table
  let emission ← match b.typed.emit declaration with
    | .ok e => pure e
    | .error .illTyped => throw (.emissionTyping (Api.explain program { rows := table }))
    | .error why => throw (.emission why)
  let file ← (emission.file preludeImport).mapError .file
  match Api.readFile file table with
  | .ok read => unless decide (read = program) do throw (.readBack none)
  | .error why => throw (.readBack (some why))
  let moduleOrigins := Tools.Code.originsAt preludeImport
  if (Api.checkSourceBindings file moduleOrigins).isNone then
    throw (.bindings "module" (Codegen.lexicalRefusal moduleOrigins file))
  let modulePath := s!"./{spec.name}.gen.ts"
  let surface ← (emission.surface preludeImport modulePath).mapError .surface
  let surfaceOrigins := moduleOrigins ++ [.imported "effect" (some "Schema")] ++
    (exportedNames file).map fun n => .imported modulePath (some n)
  if !surface.decls.isEmpty && (Api.checkSourceBindings surface surfaceOrigins).isNone then
    throw (.bindings "surface" (Codegen.lexicalRefusal surfaceOrigins surface))
  let bytes := Api.bytesOf program
  unless decide (Wire.decodeProgram bytes = some program) do throw (.canonical "canonical bytes")
  let json := programJson program
  unless readsBack json program do throw (.canonical "tagged print")
  let address := Tools.Code.addressOf program
  let layout (m : TypeScript.Module) : ByteArray :=
    (Tools.GeneratedStamp.endWithOneNewline (Tools.Code.moduleText Tools.Code.Ts.width m)).toUTF8
  let surfaceFiles : List Artifact := if surface.decls.isEmpty then [] else
    [⟨s!"{spec.name}.surface.gen.ts", .surface, layout { surface with header := surfaceHeader spec address }⟩]
  let files : List Artifact :=
    [⟨s!"{spec.name}.gen.ts", .module, layout { file with header := moduleHeader spec b address }⟩] ++
      spec.prelude.map (fun (path, bytes) => ⟨"prelude/" ++ path, .prelude, bytes⟩) ++ surfaceFiles ++
      [⟨s!"{spec.name}.eff", .canonical, ⟨bytes.toArray⟩⟩, ⟨s!"{spec.name}.eff.json", .canonical, json⟩,
       ⟨"certificate.json", .certificate, jsonBytes (certificate b)⟩]
  let written := files.filter fun a => spec.kinds.contains a.kind.selector
  pure ⟨written, manifest spec b address written⟩

/-- **A program's emission with no application**: the program admitted at the empty application
(`Api.Built.ofProgram`), then emitted (`emitTs`). A program of the wire corpus is one. -/
def emitProgram (spec : Spec) (program : NativeEff) : Except EmitRefusal Emission :=
  match Api.Built.ofProgram {} program with
  | .error why => .error (.check ⟨none, .admission why⟩)
  | .ok b => emitTs spec b

end Compiler
