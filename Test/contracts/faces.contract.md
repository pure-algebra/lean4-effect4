# The faces of one `Eff` program

Slice S1b, 2026-09-09 (DI-50). This packet is a **statement of what is claimed and by what
evidence**, not a red battery: every battery it names already exists and none is added here
(v1 DI-50: "cite the batteries that exist; add none"). `docs/DESIGN-MAP.md` §L4 is the prose;
this is the packet the map says the layer lacks.

Evidence words are `docs/DESIGN-MAP.md`'s four, and **several may apply to one claim**
(DI-32): *proved* (a Lean theorem, with its premises), *reproduced* (a gate that regenerates
and compares bytes), *tested* (a golden, differential, property or metamorphic corpus under a
named observer — `tsc` and `#guard` are finite checker runs and count here), *stamped* (a
verifying trace of the inputs a projection was cut from).

---

## 1. The nine faces

One program has nine representations that must agree. Each row says what the face *is*, what
holds it, and where the battery is.

| # | face | what it is | evidence | where |
| --- | --- | --- | --- | --- |
| 1 | the Lean printer | `Api.print` / `Api.printModule`: an `Eff` to one TypeScript expression, or a declaration block with one `const L_<path>` per hoisted layer | expression and declaration-block reconstruction proved on the stated readable domains (§2); module admission remains open | `src/Effect4/Codegen/Print.lean`; `src/Effect4/Laws/Codegen/Module.lean`; `Test/Codegen/PrintContract.lean` |
| 2 | the Lean reader | `readEff`: the partial expression inverse; `Api.readModule`: module reconstruction with a closed refusal alphabet | expression and declaration-block reconstruction proved on the stated readable domains (§2); module admission remains open | `src/Effect4/Codegen/Read.lean`; `src/Effect4/Laws/Codegen/Module.lean`; `Test/Codegen/ReadContract.lean` |
| 3 | the TypeScript printer-image reader | `ts/eff/read.ts`: a third implementation of face 2's relation, in the target language | tested (byte equality against Lean-cut oracles over the generated corpus), reproduced (its head union is generated, so `tsc` holds head coverage) | `ts/eff/read.ts`, `ts/eff/check.ts`; `ts/eff/test/read.test.ts`, `tables.test.ts`; `make check-ts-reader` |
| 4 | the foreign recognizer `ck` | `ts/eff/ingest/ck.ts` over the TypeScript compiler API: an island recognizer of a sub-language of rc.112 | tested (agreement with face 5; equality with Lean where an oracle exists) | `ts/eff/ingest/ck.ts`; `ts/eff/ingest/test/foreign.test.ts`, `gate.test.ts`, `refusals.test.ts` |
| 5 | the foreign recognizer `oxc` | `ts/eff/ingest/oxc.ts` over oxc 0.147.0, sharing **no** recognition code with face 4 | tested (the same) | `ts/eff/ingest/oxc.ts`; the same batteries |
| 6 | the canonical wire | the byte encoding of a program, in three implementations: `Effect4.Program.Wire`, `ts/eff/wire.gen.ts`, `ocaml/eff/eff_wire.ml` | proved (`decode_encode`, `decode_exact`, `encode_injective`), reproduced (goldens), tested | `src/Effect4/Program/Wire.lean`; `ocaml/goldens/eff`; `ts/eff/test/wire.test.ts`, `ocaml/eff/test/test_lean_wire.ml`, `prop_wire.ml` |
| 7 | the JSON projection | the same program as JSON, in three implementations: `OCaml5.Eff.effV.json`, `ts/eff/json.gen.ts`, `ocaml/eff/eff_json.ml` | reproduced (byte comparison against the Lean-cut oracle), tested | `src/OCaml5/Eff/Goldens.lean`; `ts/eff/json.gen.ts`; `ocaml/eff/test/test_eff.ml` |
| 8 | the executed image on rc.112 | the truth harness: the printed module *run* under the pinned host, its exit and observable schedule compared with the Lean machine's | tested (a bounded differential over a frozen corpus), reproduced (the gate regenerates the modules, the result and the tapes and compares bytes), stamped | `harness/truth/`; `scripts/check-truth.py`; the `#guard`s of `harness/truth/Truth.lean` |
| 9 | the OCaml conformance face | `ocaml/eff`: generated families, wire and JSON implementations; core typing verdicts retained as goldens, with no independent OCaml type checker | reproduced (goldens), tested (`dune-tests`) | `ocaml/eff/`; `bash scripts/check-ocaml.sh dune-tests`; `src/OCaml5/Tools/EffGen.lean` |

**Not a face of this layer.** The runtime coverage census is the traceability matrix for
rc.112's runtime, not a representation of an `Eff` program (`docs/DESIGN-MAP.md` §L4).

---

## 2. The two round-trip laws, with their side conditions

Both are theorems in `src/Effect4/Codegen/Read.lean`, and both carry premises that are part of
the claim.

**Law R1 — a readable program that prints comes back as itself.**

```
read_print (hl : LawfulSpelling sig spell) (e : Eff Op)
  (hr : readable sig spell n e = true) (hp : print sig n e = .ok x)
  : readEff sig spell n x = .ok e                                    -- Read.lean:1692
roundTrip_eq … : roundTrip sig spell n e = .ok e                     -- Read.lean:3032
read_print_native (table) (h : LawfulTable table = true) …           -- Read.lean:3024
```

Side conditions, each of which is a real restriction:

1. `LawfulSpelling sig spell` — the signature's spellings invert. For the native profile it is
   discharged by `nativeLawful table h` from `LawfulTable table = true`, decided.
2. `readable sig spell n e = true` — **the program must be in the reader's image.**
   `readable` is *print reconstruction*, not executable validity: a program can be well typed,
   admitted and runnable and still not readable (`pAwait` is the standing example — settlement
   v2 R2c; since DI-72, 2026-09-13, `yieldError e` is another: it prints as `Effect.fail(e)`,
   the failure it means, and reads back as `fail e`, so a bare value in effect position is a
   tree the printer never emits and the reader refuses). This is why the law is not "every
   program round-trips".
3. `print sig n e = .ok x` — the printer may refuse (§5.1's refused row of `Print.lean`).
4. `n` is the environment length; the law is stated at every `n`, not only at 0.

**Law R2 — what the reader accepts prints back to exactly the tree it read.**

```
read_exact (hl : LawfulSpelling sig spell) (h : readEff sig spell n x = .ok e)
  : print sig n e = .ok x                                            -- Read.lean:2829
read_exact_native (table) (ht : LawfulTable table = true) …          -- Read.lean:3038
```

Side condition: the same `LawfulSpelling`. R2 needs no `readable` premise — acceptance by the
reader is itself the hypothesis. Together R1 and R2 make printer and reader a **partial
isomorphism**, not a bijection: the domain of R1 is `readable`, the domain of R2 is the
reader's acceptance, and neither is all of `Eff`.

**What the round trip does not say (clarified 2026-09-16).** These laws concern
`TypeScript.Expr`, not complete declaration blocks or rendered text. They do not prove
the module hoist/restore relation, source parser adequacy, annotation validity or host
typing/execution. Lean `readModule` currently ignores declared types and export names;
`Api.readModule` also ignores module imports/header. The TypeScript reader drops imports
and the outer annotation. Thus accepting a module is not a typed-source certificate.
Faces 3–5 remain held by finite byte comparisons and mutual agreement, not these theorems.

`Api.printDecl`/`printModule` already consult `typeOfProgram`; it types the expanded
reference tree. That fact alone neither types the emitted target expression nor proves
that erasing shared layer references is an execution-preserving transformation. The
existing expression proofs retain their full statements and premises.

**Structural layer reconstruction (2026-09-16).**
`Eff.restoreAll_hoistAll` in `src/Effect4/Laws/Program/Hoisting.lean` proves, for
every operation alphabet and program, that
`root.hoistAll = .ok (main, declarations)` implies
`main.restoreAll declarations = some root`. The proof reverses the capture history
using addressed replacement laws and connects that history to the existing path sort.
The conclusion recovers the original sharing references; it does not expand them.
No typing or reference-validity assumption is required beyond successful hoisting.
`Eff.hoistAll_exists` in `Laws/Program/HoistingTotal.lean` additionally proves hoisting
succeeds for every program satisfying `layerRefsWF`; the more general
`Eff.hoistAll_exists_of_targets` needs only that referenced targets exist.
`Eff.hoistAll_restoreAll` composes success and restoration.

`readModule_printModule` in `Laws/Codegen/Module.lean` composes the actual declaration
printer/reader with the expression/layer laws and restoration. Its premises explicitly
require lawful row spellings, a successful hoist and print, readable main/captured
pieces, and readable emitted reference names. `Eff.restoreAll_perm` justifies the
printer's declaration reorder when target paths are unique. A duplicate-path control
demonstrates why that premise matters.

`readable_hoistAll` in `Laws/Codegen/HoistingReadable.lean` derives all main/piece/name
premises from readability of the original program. `printModule_readable` proves
successful printing for every readable program with well-formed layer references
and a structurally representable emitted declaration type;
`readModule_printModule_readable` reconstructs that original program under lawful
spellings. `Api.printModule_roundTrip` composes these through the actual API: a typed,
readable program under a lawful codegen table, with the same declaration-type
representability premise, has an emitted module that reads back exactly, with no
successful-output premise. These are module-AST adequacy and
reconstruction on that domain. None checks source declarations, imports, rendered
bytes, target typing or target execution.

**Shared typing and production evidence (2026-09-16).**
`Program.TypedProgram` retains the existing `typeOfProgram` equation for the exact
program and signature. `AdmittedProgram` extends it with the existing execution
checks; `Codegen.ModuleEmission` uses it without those runner restrictions. The
module producer records the successful `printEntry` equation and constructs its
syntax from the recorded declarations. `Api.emitModule` exposes that result;
`Api.printModule` projects its syntax. `Api.printDecl` uses the same computed typing
certificate. Neither producer accepts a separate claimed answer/error type.

`checkTypedProgram_type`, `checkTypedProgram_refusal_iff` and
`TypedProgram.hasTy` relate the evidence to the one checker and the declarative
judgment on `expandRefs`. `emitModule_erasure` and `Api.printDecl_erasure` retain
every previous output/refusal without restricting their inputs.
`emitModule_complete` establishes production on the same readable/lawful/representable
domain; `ModuleEmission.readModule` reconstructs the original program there, and
`ModuleEmission.unique` rules out two different certified outputs for one input.
The existing `Api.printModule_roundTrip` statement is unchanged and now composes
those results. Original source annotations/imports, nominal service requirements,
contextual target annotations and target typing/execution remain separate obligations.
This addition does not turn raw `Api.readModule` into typed source admission.

**Structural type amendment (2026-09-16, `E4-TARGET-TYPE-CE-001`).** The target
carrier now retains type syntax, parameter and local annotations, import aliases,
type-only markers and export presence. The canonical expression reader requires
unannotated binders and locals where the raw printer emits none; it must not erase
an annotation to satisfy `read_exact`. A future typed-source reader may validate
and normalize more source forms above that exact-image reader.

Legacy `Row.typeArgs` and `Ty.handle` strings retain their stored representation.
`Codegen.Types.parseLegacy` is a fallible bridge for the documented subset, not
another core type checker. Row calls and service keys refuse unsupported target
spellings with `PrintRefusal.typeSpelling`. Readability includes that conversion's
domain wherever the expression emits a type; bare value rows emit no type arguments.
`declarationTypeRepresentable` separately states that a declaration's emitted type is
representable. A raw answer type `handle "not a type !"` used to become unchecked
annotation text; it now refuses. `Test/Codegen/PrintContract.lean` retains this witness.
Accordingly `printModule_readable` and `Api.printModule_roundTrip` acquire the named
representability premise. Successful-print reconstruction and exact-image reading
retain their conclusions; no source typing or host agreement follows from parsing.

**Export-name hygiene (2026-09-16, `E4-TARGET-NAME-CE-001`).** `Program.exportNameSafe`
is the one predicate deciding which name a declaration block may export: a legal binding
name (`Codegen.Names.binderName`, shared with the lexical source check) that is no printed
binder `a…`, no reserved head and no layer reference name `L_…`. `printEntry` refuses an
unsafe name as `PrintRefusal.unsafeName` before it examines the row table, and the reading
boundary's envelope refuses the same names, so the two sides cannot drift. Because the
printer now refuses, `emitModule_complete` and `Api.printModule_roundTrip` carry
`exportNameSafe name = true` as an explicit premise beside the representability premise;
neither theorem claims anything about names it refuses. `Program.declarationType` is the
single owner of the emitted annotation (`printDecl` is that function plus the record), and
`printDecl_fields` states exactly what a successful declaration retains — its name, its
body, its export flag, and that annotation. `printModule_shape` states the block's shape:
plain exported layer constants, then the one main declaration.

The bridge accepts qualified names and generic arguments, literal strings, tuples,
parentheses and unions under its documented lexical restrictions. It does not resolve
names or check generic arity. Core unit still maps to `void`, and natural/integer
columns still share `number`; no injective core-type codec is claimed. Requirement
columns still omit the raw declaration annotation. Complete typed source admission,
nominal service requirements and the coupled unit repair remain separate obligations.

---

## 3. The two ingest contracts, and the inclusion property

The printed image and the foreign language are read by **different contracts**, and the
difference is a ruling, not an implementation detail (DI-37). The two differ on exactly three
axes:

| axis | the printed contract (`readPrintedSource`) | the foreign contract (`recognizeSource`) |
| --- | --- | --- |
| the admitted language | exactly what `Api.print` emits: one expression, the reserved heads, the row spellings, the pure atoms | a sub-language of rc.112 as people write it, including spellings the printer never emits and excluding shapes it does |
| the refusal discipline | a printed module that does not read is a **defect of the printer or the reader** and fails the gate | a refusal is an ordinary verdict with a code from a closed, exhaustive, injectively coded taxonomy (`src/Effect4/Ingest/Taxonomy.lean`), and the two engines must agree on it |
| the service-key numbering | the ordinals Lean minted, carried through the printed `Context.Service<T>("k<name>_<service>")` | renumbered from 4 in first-seen order (`ck.ts` and `oxc.ts`, `this.keys.length + 4`) |

**The inclusion property.** *The printed image is a sub-language of the foreign one*: every
printed module the foreign contract admits lifts to the program the printed oracle names, **up
to the service-key renumbering**. Checked by `bun ts/eff/ingest/check-corpus.ts inclusion
<printed corpus>`, wired into `bash scripts/check-ingest.sh`: each printed expression is
wrapped in the `effect` import header and one `export const main`, recognized by both engines,
and its lift compared with the printed oracle after canonically renumbering every
`{name,service}` key node on both sides. A module that lifts to a *different* program is a
contradiction and fails; a module the foreign contract refuses is counted and named by its
code, because the two contracts differ on the admitted language by design — that count is the
measurement the mode publishes. Evidence: tested.

---

## 4. The truth claim, and its quantifiers

The claim held by face 8 is bounded on five axes, and every one of them is part of it
(DI-23; the same text is in `harness/truth/Truth.lean`'s tape section).

1. **Single-fiber.** A tape is the list of package-row completions rc.112 gave one program on
   one run, consumed in file order. It is a faithful oracle only while every row of a program
   is made by one fiber. Every fixture with a tape is single-fiber; there is no fork-using
   host fixture. The first one inherits multi-fiber consumption order as a **named
   obligation**, not an extension: rows would have to be selected per fiber, and nothing in
   the harness detects a violation.
2. **`compareSchedules` is untouched by tapes.** The compared schedule is
   `started`/`forked`/`parked`/`resumed`/`ran`/`exited` over fiber indices in first-seen
   order, and is not a function of the tape. A tape decides what a row answered, never when a
   fiber ran.
3. **A pinned host.** `effect@4.0.0-rc.112` and `@effect/sql-sqlite-bun@4.0.0-rc.112` on bun;
   `scripts/check-truth.py` refuses to run without them. The claim is about those bytes.
4. **A hand corpus and a generated one.** The hand corpus is listed in
   `harness/truth/Truth.lean`, which cuts `harness/truth/corpus.json`; the program count is
   that file's `programs` length, and no gate compares this sentence to it, so read the file
   for the count of the day (34 on 2026-09-13). The programs that perform package rows have
   tapes; the gate re-records them on every run and refuses a byte that moved, so a committed
   tape is the answer rc.112 just gave. Since 2026-09-13 the 400 programs of
   `Test/Program/Gen.lean` are a second differential (`make check-corpus`): every printable
   program's module compiled, the admitted ones run, the sync exit, the schedule and the
   independently inferred type compared, one row per program in
   `harness/truth/corpus-results.tsv`, each disagreement registered by program, dimension and
   outcome in `harness/truth/corpus-known-differences.md` with the design issue that explains
   it. That register is the list of the language's known differences from rc.112.
5. **It is a differential, not a bisimulation.** Exits are compared exactly for a success
   value, a `fail` payload and a represented defect, and by kind otherwise; schedules are
   compared row by row with `scheduled` rows dropped on both faces, over the reduced alphabet
   `harness/truth/Truth.lean` (`reduce`) states: a fork appears when the runner can observe it
   (an immediate child at its first step, a scheduled non-daemon child at the parent's next
   primitive; a scheduled daemon fork on neither face), and the observation of a run ends when
   the queue is quiet after the root's exit, as `Api.run`'s flush rounds do (DI-75). Nothing
   here claims denotational equivalence for all programs.
6. **A fiber id is a position, not a value with cross-face meaning.** The machine numbers
   fibers from `0` in allocation order; rc.112's ids are its own counter. A handle or exit the
   recorder wires is renumbered in first-seen order, which is why exits agree; a bare id that a
   program observes (`getId` compared to a literal) is a named limitation (DI-73; the witness
   `pIdIsZero` in `Test/Api/ApiContract.lean` answers `true` here and `false` there), not a
   claim of the differential.

Since DI-59 a sixth quantifier is worth stating with them: **one error value.** A row whose
declared error column is the DB-15 pair projects at the adapter, before the printed program
sees it, so the value a printed handler observes, the value on the tape and the value the Lean
machine replays are one value (`harness/truth/prelude.ts` `toPair`; the recorder's
`taggedPair` is the same function).

---

## 5. The `ocaml/eff` conformance relation

`ocaml/eff` is not a second semantics; it is a **conformance suite** for the data faces.
Precisely, for each of the families the closed world names:

- **structure**: the OCaml types are generated from `OCaml5.Eff.World`, so a constructor or a
  field that moves in Lean moves there or the generator refuses;
- **bytes**: `eff_wire.ml` must produce the bytes `Effect4.Program.Wire` produces, on the
  goldens `src/OCaml5/Tools/EffWire.lean` cuts (`ocaml/goldens/eff`), and must decode them
  back exactly;
- **JSON**: `eff_json.ml` must produce the bytes `OCaml5.Eff.effV.json` produces;
- **typing** (amended 2026-09-13): there is no OCaml typing face. The hand-written
  `eff_typing.ml` that this bullet used to name was retired with the checking refactor; the
  typing has one implementation, `effTy`, and what the OCaml side holds is its *output* —
  `<name>.ty` and `corpus.txt` under `ocaml/eff/goldens`, cut by
  `src/OCaml5/Tools/EffGen.lean` — so a change in the typing shows as a diff of those
  goldens under `make check-gen`, never as a disagreement between two checkers;
- **reachability**: the generator refuses to write when the corpus fails to reach a
  constructor (`src/OCaml5/Tools/EffGen.lean`), which is the acceptance model DI-19 asks the
  OCaml engine's own test to follow.

Evidence: reproduced (the goldens, byte for byte) and tested (`make check-ocaml`); never
proved — no theorem relates an OCaml function to a Lean one.

---

## 6. Non-guarantees this packet does not remove

- No contract packet covers the printer, either reader, the ingest or the OCaml face; this one
  states the claims and cites their batteries, which is not the same as a red battery per law.
- A program with a non-empty Lean requirement row prints untyped (DI-24). Measured 2026-09-09:
  the four sqlite truth programs are in that class in Lean and yet have `R = never` on rc.112,
  because `effTy`'s `.scoped` arm passes the requirement row through while rc.112's
  `Effect.scoped` is `Exclude<R, Scope>`.
- The refusal taxonomy's classification is a function of rule order rather than of the input
  (DI-48).
- The hand truth corpus and every emitted generated-corpus module are type-checked
  (DI-49, `scripts/check-truth.py`, `scripts/check-corpus.py`). Deliberately ill-typed
  inputs retain compiler diagnostics. Independent inferred-type comparison is a finite
  target check, not a universal theorem about emitted code. It keeps A/R exact and
  accepts host E only within the declared core bound, with primitive-row comparisons
  retaining their exact contract.

## 7. Required typed-surface connection (2026-09-16)

Reader/printer integration must reuse the core checker and judgment. Executable
certificates stay below Laws; declarative consequences live in Laws. Codegen admission
requires spelling hygiene and the target profile, but not the runner's external/async
row restrictions. Its type fact concerns `typeOfProgram` and hence `HasTy` on the checked
expanded tree; its module reconstruction fact must recover the original sharing tree.

The remaining obligations are a canonical admitted annotation grammar with a round-trip
law, annotation/import validation before erasure, genuinely type-directed lowering,
and the checked source profile connecting to the proved printable domain. A normalization
needs its own typing and behavior relation. A read-and-check
wrapper or a target annotation does not discharge those obligations. Current source
parsing, core typing, target typing and host behavior remain distinct evidence boundaries.
The consolidated foundational implementation plan specifies the staged repair; this
section records the claim boundary and does not declare the repair implemented.

The lexical prerequisite is now executable as `Api.checkSourceBindings` on the
original `TypeScript.Module` and an explicit permitted-origin list. Its Laws theorem
`checkSourceBindings_iff` states exactly `SourceBindings.WellBound`: the original
imports have unique legal bindings with permitted origins, the retained syntax
meets the conservative shape restrictions, and every collected value/type reference
has a `Bindings.Resolves` derivation in its actual occurrence scope. That relation
selects the nearest name before testing its capability; it cannot skip a shadowing
local or type-only import. Local names mask the outer scope for their whole block,
including preceding statements, and become available after their declaration.
The profile refuses deferred forward references as well as immediate ones; it does
not implement TypeScript declaration merging. Child blocks do not export locals.

The traversal covers structural type children, parameter/local annotations,
class heritage and renderer-introduced references. Opaque declarations/class
members, empty named imports and unsafe verbatim names refuse. The finite controls
are in `Test/Codegen/ReadContract.lean`, including actual printed scalar, service and
layer modules supplied with imports. `Checked.use_binding` exposes the unique
resolution for every collected occurrence; `resolve_pending` proves that pending
locals cannot expose same-named enclosing bindings.

This certificate does not establish annotation agreement, expected origins for
specific core heads, package exports, generic arity, export selection, assignment
or control-flow typing, comment rendering safety, or target execution. For example,
a local value named `Effect` resolves lexically, but that is not evidence that it
implements the pinned Effect namespace. Raw `Api.readModule` remains unchanged;
combining it with the lexical check and core typing alone is not full source admission.

The first shared-lowering typing laws are in `src/Effect4/Laws/Codegen/Forms.lean`.
Arbitrary blocks of inserted binding slots preserve the complete checker result,
including refusal. The `andThen`, `tap`, `as`/`asVoid`, and `ensuring` laws read the
actual `Forms.all` expansions and state their argument environments explicitly.
They establish core typing of those expansions, not source-parser correctness or
host behavior. The compiler and OXC foreign readers now fold all nineteen generated
form rows, using their own source recognition and lexical environments. That includes
default fork options, yielded services, and one-parameter resource release with the
missing exit slot inserted after the resource. Explicit fork options and two-parameter
release retain their canonical primitive adapters. The canonical exact reader is unchanged.

The native service type tables in `Program/Native.lean` now feed the core lookup and
the generated reader profile. The canonical reader consumes the generated spelling;
both foreign readers use it for service annotation recognition and literal checking.
`nativeServiceTy_profile` in the existing reader battery proves agreement with the
former native lookup for every key. Unsupported foreign service annotations, including
`unknown`, refuse with `E-TYPE-PARAM`; they no longer acquire the unit service code.
Both foreign readers also share the service-key allocation/conflict check: a package
service and a declared service using one runtime name must have the same carrier,
regardless of encounter order. Opposite-order rejection and same-carrier alias controls
live in `ts/eff/ingest/test/services.test.ts`.
This consolidates the existing carrier mapping, without resolving the separate nominal
service identity or typed-module admission obligations.
