import Compiler.Main
import Effect4.Author

/-!
# The compiler's emission, read: one corpus program's folder, and its controls

Readers and controls over `Compiler.emitProgram`, `Compiler.emitTs` and `Compiler.check`
(`tools/Compiler/`; the entry point's first slice, `docs/research/2026-10-20-compiler-entry/README.md`
§5 and E3). A battery reads no file, so the prelude's closure and the pins are data here; the IO
that reads them is `Compiler.Main`'s.

- **The folder of the wire corpus's first program**, `p42`, admitted at the empty application:
  its files and their kinds, the manifest read back from its own bytes, the address, the
  canonical bytes and their tagged print, the certificate, the prelude's files, and no import
  that leaves the folder.
- **The red control**: an application whose literal is one above rc112's `natBound`. `check`
  admits it, since profile support is no part of the build, and its emission refuses at the
  profile. Its twin at `natBound` emits, and its module imports the prelude beside it.
- **The command's controls**: an entry that the checker refuses is named, `--emit` selects, an
  unknown kind is refused, and an import that leaves the prelude's folder resolves to nothing.

Every check is a `#guard`, so the rendered bytes stay inside them.
-/

namespace Test.Codegen.CompilerEmit

open Effect4 Effect4.Program Effect4.Program.Authoring Compiler

/-- The pins of the battery's emissions, as data. -/
def inputs : Inputs :=
  { lean := "leanprover/lean4:v4.33.1", library := none, effect := "4.0.0-rc.112",
    tsgo := "7.0.0-dev.20260629.1" }

/-- A prelude of two files given as data: its root re-exports the other. -/
def prelude : List (String × ByteArray) :=
  [("prelude.ts", "export * from \"./a.ts\"\n".toUTF8), ("a.ts", "export const a = 1\n".toUTF8)]

/-- What `emit --target ts` asks for a module's name, with the kinds given. -/
def specOf (name : String) (kinds : List Kind := Kind.selectable) : Spec :=
  { name, command := ["emit", "--target", "ts"], kinds, prelude, inputs }

/-- The wire corpus's first program, with its name. -/
def first : String × NativeEff := Wire.Corpus.all.head?.getD ("", .succeed (.lit .unit))

/-- An application whose one entry adds a literal to its parameter. -/
def offset (literal : Nat) : Application NativeOp :=
  { name := "offset"
    entries := [{ name := "shift", params := [("n", .nat)], body := succeed (Atom.add (var "n") (nat literal)) }] }

/-- An application whose one entry adds a string to a natural. -/
def mixed : Application NativeOp :=
  { name := "mixed", entries := [{ name := "mix", body := succeed (Atom.add (nat 1) (str "x")) }] }

#guard first.1 == "p42"

/-! ## The folder of `p42` -/

-- The files in the order `emit` writes them: the module, the prelude's files, the canonical bytes
-- and their tagged print, the certificate, then the manifest. `p42` declares no data service, so
-- it has no surface.
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e => (e.files Kind.selectable).map (fun (a : Artifact) => (a.path, a.kind)) ==
      [("p42.gen.ts", .module), ("prelude/prelude.ts", .prelude), ("prelude/a.ts", .prelude),
       ("p42.eff", .canonical), ("p42.eff.json", .canonical), ("certificate.json", .certificate),
       ("manifest.json", .manifest)]
  | .error _ => false

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

-- The certificate file is `check --json`'s text and a newline, and the manifest holds the same
-- certificate. Its fields, for `Effect.succeed(42)`: a natural, no error, no key, row, service or
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
-- the structured read-back) with the lexical one, and that no target compiler and no run were
-- performed.
#guard match emitProgram (specOf first.1) first.2 with
  | .ok e =>
    match e.manifest.at? [.key "checks", .key "performed"], e.manifest.at? [.key "checks", .key "notPerformed"] with
    | some (.arr performed), some (.arr skipped) =>
      (performed.filter fun c => isStr "module" (c.at? [.key "kind"])).map
          (fun c => match c.at? [.key "check"] with | some (.str s) => s | _ => "") ==
        ["formation", "typing", "profile", "readBack", "bindings"] && skipped.length == 2
    | _, _ => false
  | .error _ => false

-- The prelude's files stand under `prelude/`, byte for byte, and every relative import of every
-- file resolves to a file of the folder: nothing leaves it.
#guard match emitProgram (specOf first.1) first.2 with
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

-- `--emit=module` writes the module and the prelude, and no manifest.
#guard match emitProgram (specOf first.1 [.module]) first.2 with
  | .ok e => (e.files [.module]).map (fun (a : Artifact) => a.kind) == [.module, .prelude, .prelude]
  | .error _ => false

/-! ## The red control: the profile is the emission's -/

-- One above rc112's bound: `check` admits the application, and its emission refuses at the profile,
-- with the literal.
#guard match check (offset (rc112.natBound + 1)) with
  | .ok b =>
    match emitTs (specOf "offset") b with
    | .error (.emission (.outsideProfile r)) => decide (r.reason = .aboveBound (rc112.natBound + 1))
    | _ => false
  | .error _ => false

-- At the bound itself it emits: the module imports the prelude beside it, and the surface imports
-- the module.
#guard match check (offset rc112.natBound) with
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

-- The scan reads re-exports, imports and both quotes, and keeps only relative specifiers; an import
-- that leaves the prelude's folder resolves to nothing, so `closure` refuses it.
#guard Prelude.relativeImports
    "export * from \"./a.ts\"\nimport { b } from './b.ts'\nimport \"./c.ts\"\nimport { Effect } from \"effect\"\n" ==
  ["./a.ts", "./c.ts", "./b.ts"]
#guard Prelude.resolve "prelude.ts" "../outside.ts" == none && Prelude.resolve "sub/x.ts" "../y.ts" == some "y.ts"

end Test.Codegen.CompilerEmit
