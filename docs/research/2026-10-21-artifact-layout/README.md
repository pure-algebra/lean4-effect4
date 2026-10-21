# 2026-10-21 The project folder: every file the image of one map, nothing written by hand

Status: a design note after two modeling passes, for Codex to implement. It rules nothing; it proposes decisions row 442.
The evidence words are those of `docs/core/controlled-english.md` §3.8.
Every count below is read off the to-do at `62ccdab0b`; every "tested" is a finite evaluation in the probes beside this note's text (§7).

## 1. The one thing to know

Lean is the only text an author writes. Every other file of a project folder is the image of one named map of the algebra. The folder is laid out by who the file is for and what it is.
Two roles: the program's files and the host's files.
Three forms: a canonical object, a print for one target, a record of one run.
One index: the manifest, which is the folder's recognizer.
Hosts are objects too, so they are generated like programs, and no driver, layer or harness is written by hand.

## 2. What is written by hand today, and what replaces it

| Hand-written today | Where | Lines | Replaced by |
| --- | --- | --- | --- |
| the `Session` driver of the gate: a request array, `next`, `reply_check` | `scripts/check-service-identity.py` (`SESSION_HOST`) | 13 | a driver object: a service block over a request queue, printed as a layer (§4.2) |
| the gate's harness: run the program, compare replies with Lean's JSON | `scripts/check-service-identity.py` (`SESSION_RUNTIME`, `RUNTIME`, `INFERENCE`) | 60 | the run's record: the target writes the journal, Lean replays and checks it (`journal_bound_call`), no harness |
| the native hosts of the to-do | `ocaml/engine/test/todo/native_todo.ml`, `todo_core.ml` | 345 | the handler object lowered, with the engine slice |
| the prelude's four hand files | `ts/prelude/control.ts`, `records.ts`, `tuples.ts`, `prelude.ts` | 514 | a package pin, as `effect` is: outside the project folder |

The reference repository of the to-do (`Test.Dogfood.Scenario.Todo.repository`) is a Lean function, so it stands under the rule, and the lowering generates its OCaml.
As a handler object it would print to every target; today it prints to none.

## 3. The layout

```text
<name>/
  effect4.gen.json                   the manifest, and the recognizer of a project folder
  program/                           the application's files: functions of its object
    <name>.obj                         Object.bytes, canonical
    <name>.<service>.session.obj       Object.bytes ∘ Object.session, canonical: one service's lifetime
    certificate.gen.json               Built.certificate
    <name>.program.gen.json            the tagged print, for reading
    ts/<name>.gen.ts                   the print fold; imports ../../host/ts/<name>.host.gen.ts
    ts/<name>.surface.gen.ts           the data services' Schemas
    ocaml/<name>_gen.ml                the lowering (an OCaml module name holds no dot)
    ocaml/lowering.gen.json            the recipe
    ocaml/closure.gen.tsv              the closure
  host/                              the host's files: functions of the typing signature, and the handler objects
    interface.gen.json                 the rows with their columns, and the keys the signature types
    <ns>.handler.obj                   canonical: the service block that answers the rows of namespace <ns>
    Session.driver.obj                 canonical: the driver, a handler of the session rows over a request queue
    ts/<name>.host.gen.ts              types only: the shapes a layer and a driver implement (tested, §7)
    ts/<ns>.handler.gen.ts             the layer printed from the handler object
    ts/Session.driver.gen.ts           the driver printed from its object
    ocaml/<name>_host.mli              the lowered host record's type
    ocaml/<ns>_handler.ml              the lowered handler
  run/
    <id>.record                        LiveRecord.save, canonical: the object's reference, the session, the journal
```

### 3.1 The names

- A canonical file is a store node and ends in its kind: `.obj`, `.record`. It reads back exactly (`Object.read_exact`), and it is the authority on what it holds.
- Every other file is generated text and carries `.gen` before its extension. It is a print or a projection, read by a tool or a target, never the authority. An OCaml module keeps `_gen` and `_handler`, since its name holds no dot.
- `effect4.gen.json` is the manifest. A folder with it is a project folder; a tool reads it first, then the file whose role, form and kind it needs.
- `<name>` is the application's name; `<service>` a service of its block; `<ns>` a host namespace of its rows.

### 3.2 Interfaces, types and implementations

The host folder holds three sorts, kept apart by name.
`interface.gen.json` is the target-free contract: the rows' columns and the typed keys, a projection of `SigApp`.
`<name>.host.gen.ts` and `<name>_host.mli` are that contract as the target's types, with no value in them.
A handler object is an implementation, canonical and target-free; its prints under `ts/` and `ocaml/` are its images.
The program's print imports the types; the host's prints provide them. The two roles meet only at the types.

### 3.3 Now, and when every slice has landed

| | Now (`62ccdab0b`) | When every slice has landed |
| --- | --- | --- |
| `program/` | the object by `check --out`, apart from `emit`; the program bytes, the certificate and the readable print written under each target | the four target-free files once, then one folder a target |
| `host/` | nothing: the service shapes sit inside `todo.gen.ts`; the driver and the harness are hand-written in the gate; the native hosts are hand-written OCaml | the interface, the type files, the handler and driver objects with their prints |
| `run/` | `run` prints lines and keeps no record | one record a run, which the cross-language check replays |
| the manifest | one a target, 74 KB, with the module closure of the inputs in it | one a folder; the inputs' closure as its own file named by digest |

## 4. The model

### 4.1 The folder as an indexed family

```lean
inductive Role | program | host | run
inductive Form | object | print (target : Target) | record | index

structure Artifact where
  role : Role
  form : Form
  kind : Kind          -- object, session, certificate, program, module, surface, recipe, closure, interface, types, handler, driver, record, manifest
  path : String        -- Artifact.path role form kind name: §3 as one function
  bytes : ByteArray

/-- What each role's files are functions of. -/
def Domain : Role → Type
  | .program => Object
  | .host    => SigApp × List Object      -- the signature, and the handler objects that fit it
  | .run     => Live

/-- The layout: one pure function a role. -/
def layout : (r : Role) → Domain r → List Artifact

/-- The file system as the compiler sees it, and its one IO. -/
abbrev FS := List (String × ByteArray)
def write : List Artifact → FS → FS
```

The compilation is one composite with the write last: `write ∘ layout ∘ session ∘ open ∘ read`.
This is the shape of a content-addressed build, as in Nix's derivations and Bazel's actions. A pure function takes the inputs to an output set, and the index names each output by its digest.
The project folder is a view of that store, laid out for people; the manifest is the store's index.

### 4.2 Hosts are objects: the handler, dual to the session

`Object.session` reads a service and writes the program that calls rows: the service inside out.
A handler object is the other direction: a service block whose methods have the rows' columns, so it answers those rows.
Printed, it is the layer that provides the namespace (`TodoRepoLayer`). Lowered, it is the host record. On the machine, it is a reactor that runs the method's program for each request.
The driver is a handler of the session rows. Its `next` pops a queue held in a Ref, and each `reply_m` appends to a Ref list. The queue's initial value is the script.
So a driver is generated per script, as every other file is generated per object. The gate needs no harness: the run's record is the evidence, replayed by Lean.

The check that a handler fits an interface is the dual of the session's formation. Each method's request is the row's request, and its exit is the row's answer and error.
A handler object carries no row of the namespace it implements, so the printer's collision refusal (`serviceNamesFault`) does not fire on it.

What this does not yet have: the reactor made from a handler object on the Lean machine (a hosted stage), and the fit check. Both are the engine slice's and the driver slice's.

### 4.3 The laws

| Law | Statement | Today |
| --- | --- | --- |
| determinism | an artifact's bytes depend on the object, the target and the pins, never on the output path or the clock | **fails, tested**: `todo.gen.ts`, `todo.surface.gen.ts` and the manifest differ between two emissions, since the header and the manifest hold the `--out` path |
| exact read-back | `Object.read (bytes at program/<name>.obj) = ok o` | `Object.read_exact` |
| separation | two objects with one typing signature have equal host files | tested: the to-do and the cached to-do have one `SigApp` and different programs; the host files are functions of the signature |
| the index | the manifest maps each path to the SHA-256 of the bytes at it, with its role, form and kind | `Artifact.json` today, without role and form |
| closure | `write (layout o) fs` differs from `fs` only at the layout's paths | `write` as a map |

The determinism repair: no artifact carries the command; the manifest records the command without its `--out` argument.

## 5. What changes, in slices

1. **The layout.** `Role`, `Form`, the path function and the manifest with role and form. `check --out` folds into `emit` as the object kind. The canonical program bytes go, since the object holds them. `.gen` goes on every generated file, with the determinism repair. The host type file comes from `hostBindings` and `rowServiceDecls`, which exist.
2. **The driver object.** The session rows' handler over a Ref queue, generated from a script. Its print replaces the gate's hand-written driver. The gate compares the run's record by Lean replay, and its harness goes.
3. **The handler object.** The to-do's reference repository as a service block over a Ref list. Its print is the layer the TypeScript run provides. Its lowering replaces the hand-written native hosts with the engine slice.
4. **The run record.** `run` writes `run/<id>.record`.
5. **The prelude as a package.** Out of the project folder.

Slice 1 is the cut; it moves files. Slices 2 and 3 are where the hand-written host code goes. Slices 4 and 5 follow.

## 6. What this note does not establish

No file has moved, and no law of §4.3 is proved; each is a finite check to land with its slice.
The handler's reactor on the Lean machine is a design, not a probe.
The manifest's inputs and checks keep their meaning (`Compiler.Emit`, decision E3).

## 7. The probes

| Probe | States | Result |
| --- | --- | --- |
| two emissions of the to-do, compared byte for byte | the artifacts are a function of the object and the target | fails: three files differ by the `--out` path alone |
| `hostBindings` on the session object | the `Session` host type, `{ next: () => Effect<Option<…>>, reply_add: (Exit<…>) => Effect<void>, … }`, is a function of the signature | tested; `TypeScript.Render.type` prints it |
| `rowServiceDecls` on the session object | `TodoRepoKey` and `TodoRepo` are functions of the signature | tested |
| the to-do and the cached to-do | one `SigApp`, two programs | tested |
