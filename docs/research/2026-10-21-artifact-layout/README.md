# 2026-10-21 The emitted artifacts: a file layout that is the algebra's image

Status: a design note. It rules nothing; it proposes decisions row 442.
The evidence words are those of `docs/core/controlled-english.md` §3.8.
Every count below is read off the to-do's emission at `62ccdab0b` (`lake exe effect4 --group todo emit --target ts|ocaml`, `check --out`).

## 1. The one thing to know

A file is the image of one named map of the algebra, and its folder is that map's domain.
A file that depends on the object alone is a program file.
A file that depends on the typing signature alone is a host file.
A file that depends on the object and a target is a target file.
A file that depends on a run is a run file.
The manifest is the digest map of the rest.
So the folder separates host from program by construction, and the compiler's IO is one map: write the list.

## 2. What the emission writes today

| Path | Map | Domain | Size |
| --- | --- | --- | --- |
| `todo.obj` (by `check --out`, outside `emit`) | `Object.bytes` | the object | 7,894 bytes |
| `ts/todo.gen.ts` | `Typed.emit`, the print fold | the object and the target | 5,034 bytes |
| `ts/todo.surface.gen.ts` | `ModuleEmission.surface` | the object and the target | 2,968 bytes |
| `ts/prelude/` (5 files) | `Prelude.closureOf` | the target | 51,333 bytes |
| `ts/todo.eff`, `ocaml/todo.eff` | `Api.bytesOf program` | the program | 5,713 bytes, twice |
| `ts/todo.eff.json`, `ocaml/todo.eff.json` | `programJson` | the program | 5,213 bytes, twice |
| `ts/certificate.json`, `ocaml/certificate.json` | `Built.certificate` | the object | 4,589 bytes, twice |
| `ocaml/todo_gen.ml` | the LCNF lowering | the object and the target | 1,697,753 bytes |
| `ocaml/lowering.json`, `ocaml/closure-todo_gen.tsv` | the lowering's recipe and closure | the object and the target | 326,919 bytes |
| `ts/manifest.json`, `ocaml/manifest.json` | `manifest` | the files written, the inputs | 73,870 and 72,784 bytes |

Three things are wrong with it, by the rule of §1.

1. The canonical artifact is outside the emission. `todo.obj` holds the program bytes and the typing signature; `todo.eff` holds the program bytes alone, and is written twice.
2. Host and program share a file. `todo.gen.ts` holds the program's definitions and `todoSession`, and also `TodoRepoKey`, the service shape the host's layer implements. The `Session` namespace the driver implements is written by hand in the gate (`scripts/check-service-identity.py`).
3. The folder is keyed by target first. A projection of the object (`certificate.json`) is written under each target, so a reader of the object must pick a target to find it.

## 3. The layout, by the domain of each map

```text
<name>/
  manifest.json                  the digest map: every file, its side, its kind, its SHA-256; the inputs; the checks
  program/                       functions of the object
    <name>.obj                     Object.bytes: the one canonical artifact
    <name>.<service>.session.obj   Object.bytes ∘ Object.session: the lifetime of one service
    certificate.json               Built.certificate: the type, the rows, the keys, the declarations
    <name>.eff.json                the program's tagged print, for reading
  host/                          functions of the typing signature alone
    interface.json                 the rows with their columns, and the keys the signature types
    ts/<name>.host.ts              the service shapes a layer implements, and the Session namespace a driver implements
    ocaml/<name>_host.mli          the lowered host record's type
  target/                        functions of the object and a target
    ts/<name>.gen.ts               the program, importing ../../host/ts/<name>.host.ts
    ts/<name>.surface.gen.ts       the data services' Schemas
    ts/prelude/                    the prelude's import closure
    ocaml/<name>_gen.ml            the lowered program
    ocaml/lowering.json            the recipe
    ocaml/closure.tsv              the closure
  run/                           functions of a run
    <id>.record                    LiveRecord.save: the object's reference, the session, the journal
```

Nothing the host author writes is in it. Their layer and their driver live beside `host/ts/`, and import the host file.
The host folder is the contract between the two authors: what the program needs, with no program in it.

### 3.1 Now, and when every slice has landed

| Side | Now (`62ccdab0b`) | When every slice has landed |
| --- | --- | --- |
| `program/` | `<name>.obj` by `check --out`; `certificate.json` and `<name>.eff.json` under each target | the four files once; the session object when a service is selected |
| `host/` | nothing: the shapes are inside `todo.gen.ts`, the `Session` namespace is hand-written in the gate, the OCaml host record is inside `todo_gen.ml` | `interface.json`, one host file a target, both read off `SigApp` |
| `target/` | `ts/` and `ocaml/` folders at the root | the same files, under `target/`, with the program file importing the host file |
| `run/` | `LiveRecord.save` exists; `run` prints lines and keeps no record | one record a run |
| `manifest.json` | one a target, 74 KB, the inputs' module closure in it | one for the folder; the inputs' closure as its own file, named by digest |

## 4. The file system as data, and the compiler's IO

The emission is already pure: `Emission.artifacts : List Artifact`, with `Artifact = {path, kind, bytes}` (`tools/Compiler/Emit.lean`).
This note adds the side, and states what the IO is.

```lean
inductive Side | program | host | target | run | manifest
structure Artifact where
  side : Side
  kind : Kind
  path : String        -- Kind.path side name: the layout of §3, as one function
  bytes : ByteArray

/-- The file system, as the compiler sees it: a finite map from path to bytes. -/
abbrev FS := List (String × ByteArray)

/-- The one IO: write each artifact at its path. -/
def write : List Artifact → FS → FS
```

The laws the layout must satisfy, each a finite check on the to-do until a theorem states it:

| Law | Statement | Owner |
| --- | --- | --- |
| determinism | `layout o` is a function: the same object gives the same bytes, so the manifest's digests are the object's | `Emission` is pure today |
| exact read-back | `Object.read (bytes at program/<name>.obj) = ok o` | `Object.read_exact` |
| separation | two objects with the same typing signature have the same `host/` files | the host files are `SigApp → Bytes` |
| the manifest | the manifest maps each path to the SHA-256 of the bytes written at it | `Artifact.json` today |
| closure | `write (layout o) fs` differs from `fs` only at the layout's paths | `write` as a map |

The compilation is then one composite, with the IO at the end: `write ∘ layout ∘ session ∘ open ∘ read`.
Each arrow is a map of the algebra, and the file system is the carrier the last one writes into.
A tool that reads a folder reads the manifest first, then the file its kind names.

## 5. What this changes, in slices

1. **The side and the layout function.** `Kind` gains `object`, `session`, `interface` and `record`; `canonical` goes, since the object holds the program bytes; `Kind.side` and `Kind.path` place each file. `check --out` folds into `emit` as the object kind. One manifest a folder.
2. **The host file.** The printer's `rowServiceDecls` and `hostBindings` already compute the service shapes and the host namespaces. They move from the program's file to `host/ts/<name>.host.ts`, and the program's file imports it. The gate's hand-written `Session` object then implements a printed type.
3. **The OCaml host type.** The lowered host record's type moves to `host/ocaml/<name>_host.mli`.
4. **The run record.** `run` writes `run/<id>.record` beside its lines, through `LiveRecord.save`.

Slice 1 is the cut this note is about. Slices 2 to 4 follow the driver and engine slices, which produce the files they place.

## 6. What this note does not establish

The layout is read off the to-do's emission alone. No file was moved, and no law above is proved: each is a finite check to write when the slice lands.
The manifest's inputs and checks keep their meaning (`Compiler.Emit`, decision E3). Host progress and the stage law stay outside Lean.
