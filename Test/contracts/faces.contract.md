# The faces of one `Eff` program

Slice S1b, 2026-09-09 (DI-50). This packet is a **statement of what is claimed and by what
evidence**, not a red battery: every battery it names already exists and none is added here
(v1 DI-50: "cite the batteries that exist; add none"). `docs/research/history/DESIGN-MAP.md` §L4 is the prose;
this is the packet the map says the layer lacks.

Evidence words are `docs/research/history/DESIGN-MAP.md`'s four, and **several may apply to one claim**
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
| 6 | the canonical wire | the byte encoding of a program, in three implementations: `Effect4.Program.Wire`, `ts/eff/wire.gen.ts`, `ocaml/eff/eff_wire.ml` | proved (`decode_encode`, `decode_exact`, `encode_injective`), reproduced (goldens), tested | `src/Effect4/Store/Domain/ProgramWire.lean` (namespace `Effect4.Program.Wire`; moved at `05417cc6` from `git:f7d22703:src/Effect4/Program/Wire.lean`); `ocaml/goldens/eff`; `ts/eff/test/wire.test.ts`, `ocaml/eff/test/test_lean_wire.ml`, `prop_wire.ml` |
| 7 | the JSON projection | the same program as JSON, in three implementations: `OCaml5.Eff.effV.json`, `ts/eff/json.gen.ts`, `ocaml/eff/eff_json.ml` | reproduced (byte comparison against the Lean-cut oracle), tested | `src/OCaml5/Eff/Goldens.lean`; `ts/eff/json.gen.ts`; `ocaml/eff/test/test_eff.ml` |
| 8 | the executed image on rc.112 | the truth harness: the printed module *run* under the pinned host, its exit and observable schedule compared with the Lean machine's | tested (a bounded differential over a frozen corpus), reproduced (the gate regenerates the modules, the result and the tapes and compares bytes), stamped | `harness/truth/`; `scripts/check-truth.py`; the `#guard`s of `harness/truth/Truth.lean` |
| 9 | the OCaml conformance face | `ocaml/eff`: generated families, wire and JSON implementations; core typing verdicts retained as goldens, with no independent OCaml type checker | reproduced (goldens), tested (`dune-tests`) | `ocaml/eff/`; `make check-ocaml` (which took over `git:c67ff096:scripts/check-ocaml.sh`'s `dune-tests` at `b2f6aef1`); `src/OCaml5/Tools/EffGen.lean` |

**Not a face of this layer.** The runtime coverage census is the traceability matrix for
rc.112's runtime, not a representation of an `Eff` program (`docs/research/history/DESIGN-MAP.md` §L4).

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
judgment on `expandRefs`. **Formation amendment (2026-10-03, decisions rows 192 and 193).**
`emitModule_erasure` and `Api.printDecl_erasure` retain every previous output and refusal on
formed input (`Formation.InputFormed`). `Api.printDecl_erasure` also requires that no stored
annotation refuses (`annotationRefusal`). Malformed input now refuses before printing.
`emitModule_complete` and `admitModule_complete` take both premises beside the
readable, lawful and representable domain. There `ModuleEmission.readModule` reconstructs
the original program, and `ModuleEmission.unique` rules out two certified outputs for one input.
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

**The annotation refusal (2026-09-16, `E4-CHECK-CE-017`).** That refusal is now named
`ReadRefusal.annotation site` rather than reported as `arity` or `unsupportedStmt`, which
mean different things (an argument list the row table does not print; a statement form with
no reading). The alphabet is data consumers route on, so the distinction is part of the
claim. `annotationSite` decides the position, and `callRefusal`/`stmtRefusal` sit inside the
reader's existing wildcard arms: no arm is added, the accepted domain is unchanged, and
`read_print`, `read_exact` and `read_exact_all` keep their statements and proofs. The
TypeScript printer-image reader (`ts/eff/read.ts`) still reports the older constructors for
annotated input; the two faces agree that such input refuses, not yet on its name.

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

**Checked reading (2026-09-16).** `Api.admitModule` is the reading half of the module
boundary, beside the raw `Api.readModule` the way `emitModule` sits beside `printModule`.
`Codegen.ModuleReading table name allowed ambient` carries, for exactly the module it
indexes: a `SourceBindings.Checked` for that module with the host's ambient prelude
prepended, the raw reconstruction equation, the shared `Program.TypedProgram` certificate,
and `envelopeCheck name typing.ty module.decls = none`. `SurfaceRefusal` is the closed
alphabet, nesting `ReadRefusal` and `PrintRefusal` rather than re-listing them.

The theorems. `envelopeCheck_iff` is the envelope's reflection: the computed answer agrees
exactly with `EnvelopeValid` — a safe export name, a last declaration that is the exported
main constant under that name with `declarationType ty = .ok main.type`, and every earlier
declaration a plain exported constant (`layersPlain_iff`). `admitModule_typed` is the typing
projection (the core checker's own equation), `admitModule_read` the raw reader's,
`admitModule_bound` the lexical check's, `admitModule_envelope` the envelope's as a Prop.
`ModuleReading.recheck` says the boundary returns what a certificate holds, and
`ModuleReading.unique` that a module has one reading. `ModuleEmission.admit`, exposed as
`Api.admitModule_emitModule`, is the round trip in certificate form: the module the checked
producer emitted for a readable program under a lawful table is admitted, at the same
program and the same recorded type, once the host supplies the bindings its prelude
provides. Its premises are the emission itself, `LawfulTable`, `readable`, and that
`SourceBindings.Checked`; the export-name and representability facts are read off
`printEntry_ok` and `printDecl_fields` rather than assumed. `admitModule_complete` names the
recorded type rather than the certificate because two certificates for one program are equal
only by `TypedProgram.unique`, which `ModuleReading.typing_eq` states.

What checked reading does **not** claim. It does not widen a declared type: the comparison
is equality with the printer's own annotation, because the core has no subsumption at a
program's top type (DI-15), so a wider source declaration is refused by design. It admits no
binder, return or local annotation; the raw reader still refuses those, and the annotated
profile is a later packet. It gives the `effect` package no meaning: a resolved `Effect` is a
lexical fact about the supplied origins, not evidence that the host namespace is the pinned
rc.112 one, and the expected origin of a particular head is still unchecked. It is not target
type checking and not execution. Twelve controls in `Test/Api/ApiContract.lean` separate the
refusals one fact at a time; the axiom receipts are in `Test/Codegen/ReadContract.lean`.

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
law, binder/return/local annotation validation, the expected package origin of each core
head, genuinely type-directed lowering, and the checked source profile connecting to the
proved printable domain. The declaration's own annotation and the module's import
bindings are no longer owed: `Api.admitModule` checks both before erasure (§2, checked
reading), and its envelope compares the declaration against the printer's own annotation
rule rather than a second encoding of it. A normalization
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

---

## Amendment, 2026-09-17: the hand reader is retired; faces 1 and 2 are run from one table

The owner ruled a fast cutover. What this changes in the packet above, and nothing else:

- **Face 2 is the table reader.** `readEff` and `readLayer` are `readT`
  (`src/Effect4/Codegen/Read.lean`): the first row of `Codegen/Templates.lean` whose skeleton
  matches, its arguments read by sort, the constructor rebuilt by the generated `build`. It
  terminates for any table (`Template.match_below`). It reads what the hand reader read, and
  also the loop image and the two non-Boolean decisions; a loop whose cursor is annotated
  prints and is refused by name (no reader of types, B19).
- **Deleted with the hand reader:** `read_print`, `read_print_layer`, `read_exact`,
  `read_exact_all`, `read_print_native`, `read_exact_native`, `roundTrip_weaken`, the structural
  `readable` and `Laws/Codegen/HoistingReadable.lean` (`readable_hoistAll` and its lemmas),
  `printModule_readable`, `readModule_printModule_readable`, `emitModule_complete`,
  `ModuleEmission.readModule`, `Api.printModule_roundTrip`.
- **Evidence for faces 1 and 2, now.** *Proved*: `readable` is the round trip
  (`roundTrip_eq`, by definition); the leaf and row round trips (`readTerm`, `readCause`,
  `readKey`, `readForkOptions`, `read_printRow`, `readMethod_exact`); `readModule_printModule`
  over the premise that each hoisted piece reads back (`ReadsBack`); `ModuleEmission.admit` and
  `Api.admitModule_emitModule` over the premise that the emitted module reads back; the two
  engine lemmas of the calculus (`match_inst`, `inst_of_match`). *Tested*: on the 400 seeded
  programs the table reader agrees with the hand reader wherever that one read (356), reads 44
  images it refused, and what it reads prints back to the same tree on all 400
  (`Test/Codegen/ReadContract.lean`, `TemplatesContract.lean`).
- **Owed (R5.2):** `read_print` and `read_exact` over the table, the structural domain of
  `readable`, and with it the four module-level corollaries above.
- **Face 3** (`ts/eff/read.ts`) is still a port of the retired hand reader: it does not read the
  loop image or the two non-Boolean decisions until it becomes a matcher over the exported
  table (R6). `make check-ts-reader` is expected to differ on exactly those oracles until then.

## Amendment, 2026-10-04: payload classes (decisions row 120, part E2)

- **The reader's signature.** The table reader takes the module's payload classes as its first
  explicit argument: `readTerm`, `readTerms`, `readCause`, `readLeaf`, `readT`, `readEff`,
  `readLayer` and their kin (`src/Effect4/Codegen/Read.lean`). `Api.read` and `Api.readAt` pass
  `[]`. §2's `readEff sig spell n x` reads `readEff classes sig spell n x`, and `read_print` and
  `read_exact` are stated over the classes in place.
- **Face 1 and face 3 gain the class form.** Each tagged payload type prints once per module as
  `export class Tag extends Data.TaggedError("Tag")<{ readonly f: T; … }> {}`, and its value as
  `new Tag({ … })`. The Lean reader and `ts/eff/read.ts` read both back, restoring `_tag`. The
  envelope admits exactly the printed class declarations (`admitModule_classDecls`). Refusals carry
  the tag (`PrintRefusal.payloadClass`).
- **Evidence.** *Proved*: `read_print`, `read_exact`, `readModule_printModule`,
  `readClassDecl_exact`, `admitModule_classDecls`. *Tested*: tsgo 7.0.0-dev.20260629.1 on a green
  file and a red twin (TS2740, TS2375, TS2353, TS2322), the TypeScript reader lane, and two truth
  programs against rc.112. Seat E2's receipt: `docs/research/2026-10-04-seat-E2-receipt.md`.

## Amendment, 2026-10-05: an operation's binder term (the state plan's T5, decisions row 251)

- **Face 1 prints the term as a function.** A read-modify-write row carries a binder term
  (decisions row 43). The printer writes it after the row's call, as a function of the cell's
  current value: `Ref.update(a0, (a1) => succ(a1))` (`printPerform` and `withFunction`,
  `src/Effect4/Codegen/PrintLeaf.lean`). The parameter is the binder due at the node's level,
  and the body is the term one level up. A fold inside the term prints with no further rule.
- **The five names leave the faces.** No row spells `incr`, `double`, `zeroWhenPositive`,
  `noChange` or `takeAndBump`. One term has one printed form. A spelled row is its face, with the
  unit literal for its term (`Signature.face`, `src/Effect4/Program/Typing/Rules.lean`).
  `PrintRefusal.binderTerm` stays for one case: a value row that carries a term.
- **The readers install the term.** The Lean reader splits the function off the call
  (`splitFunction`). It reads the call to the row's face, and the body one level up. Then it
  installs the term (`readPerform` and `installTerm`, `src/Effect4/Codegen/Read.lean`).
  `ts/eff/read.ts` reads the same form. A term row without its function is refused by its
  spelling. So is a function on a row that carries no term.
- **The laws keep their statements.** `read_print` and `read_exact` are unchanged. Their domain
  admits a term row on two conditions. The term is scoped at `n + 1`, covered and unannotated.
  The row is no value row (`termReadable`; `rowDom`, `src/Effect4/Laws/Codegen/ReadPrint.lean`).
  `LawfulSpelling` states that a row does not depend on its operation's term. The row-call steps
  are `readPerform_printPerform` and `readPerform_exact`
  (`src/Effect4/Laws/Codegen/ReadLeaf.lean`).
- **The annotation refusal at a term row (`E4-CHECK-CE-017`).** An annotated function in the
  term's place is refused as `ReadRefusal.annotation "<spelling> <site>"`. The site is
  `parameter`, `return` or `thunk return` (`functionAnnotation`, beside `readPerform`). The
  reader asks it only after the row's face has refused, so the accepted domain does not move. A
  missing function, a wrong binder and a wrong number of parameters stay `ReadRefusal.arity`.
  The TypeScript reader refuses the same input. It claims no agreement on the refusal's name.
- **The foreign contract (§3).** The five names are no foreign spelling. Both recognizers read a
  row's function under any parameter name. Each of the four lambda shapes spells one term at each
  row (`LambdaShape.term`, `src/Effect4/Codegen/Forms.lean`). The foreign corpus restyles a
  printed function that is such a term (`Styles.lambdaOf`, `src/Effect4/Codegen/Styles.lean`).
  A term row declares no type argument. Both recognizers refuse a call that carries one, with
  the code `E-NODE` (`ts/eff/ingest/test/foreign.test.ts`).
- **The truth claim (§4).** The prelude exports no function name. A printed term calls the atoms
  alone, so one printed term means one function at every row's shape. This closes finding F3 of
  `harness/truth/prelude.ts`.
- **Not established.** A row's type arguments stay spelled at one instance: `Deferred.make` at
  any other instance is refused by name (`PrintRefusal.typeSpelling`). A fold with a stated
  type, and a loop with a stated cursor type, print and do not read back. No law states target
  typing or a host run.
- **A registered difference on the target.** `pair` and `tuple` keep a boolean or a number
  literal as a literal type, where Lean types `bool` and `nat`. Two arms that Lean types alike
  can then be two target types. The rate limiter's request and the Queue probe's first take
  attempt do not type-check under tsgo 7 for that reason. The compiler control pins three such
  lines as refused (`harness/truth/term-rows.typecheck.ts`).
- **Evidence.** *Proved*: `read_print`, `read_exact`, `readPerform_printPerform`,
  `readPerform_exact`. *Tested*: the batteries `Test/Codegen/TermRows.lean`,
  `Test/Codegen/ReadContract.lean` and `Test/Codegen/PrintContract.lean`. *Tested*: tsgo
  7.0.0-dev.20260629.1 on `harness/truth/term-rows.typecheck.ts`, with a red control at each of
  the eight rows. *Tested*: the TypeScript reader lane, and two truth programs against rc.112.

## Amendment, 2026-10-05: an operation's type arguments, a stated cursor type, and the literal rule (the state plan's T5, part B; decisions rows 212, 251 and 256)

What this changes in the packet above, and nothing else:

- **B19, amended: one checked reader of types.** B19 held that no reader of types exists. A
  declared type is compared as syntax, and never read. The payload class reader has read a
  field's type since the amendment of 2026-10-04. This amendment names the one reader and its
  domain. `Classes.readTyChecked` (`src/Effect4/Codegen/Classes.lean`) reads a type's syntax by
  `Classes.readTy`. It keeps the answer only when `Types.ofTy` prints that answer as the syntax
  read. The type printer is not injective, so the reader is no inverse of it, and none is
  claimed. A place that reads one type back reads it through this reader. The class reader
  checks a whole declaration by the same re-print. A module declaration's annotation is still
  compared as syntax, never read.
- **The readable types.** `Classes.ReadableTy ty` holds when the checked reader answers `ty`
  from the printed spelling of `ty`. Exactness holds at any syntax: what the reader accepts
  prints back to the syntax read (`readTyChecked_exact`). The retraction has the premise
  `ReadableTy ty` (`readTyChecked_of_readable`, `src/Effect4/Laws/Codegen/Classes.lean`). Four
  kinds of type are outside the domain, and `Test/Codegen/TypeReader.lean` pins one of each:
  - a type with no printed form: a row template's parameter, a nominal application at
    arguments. A map whose key is no string and a handle whose name does not parse are two
    more;
  - a collision: `int` and `number` print as `number`, which reads as `nat`;
  - a spelling with no reading: `unknown`, a handle type such as `Ref.Ref<A>` or
    `Deferred.Deferred<A, E>`, and a tagged payload record, which prints as its class's name;
  - a spelling that reads at the reader's own choice: `readonly [A, B]` reads as a product, and
    a union reads in its normal order of members.
- **An operation's type arguments.** `Deferred.make` carries its two types
  (`NativeOp.deferredMakeOf`), and the signature shows them (`Signature.typeArgsOf` and
  `withTypeArgs`, `src/Effect4/Program/Typing/Rules.lean`). The printer writes them on the
  call's head, each through `Types.ofTy`: `Deferred.make<void, never>()` (`printCall` and
  `withHeadTypes`, `src/Effect4/Codegen/PrintLeaf.lean`). The reader takes them off the head,
  reads the call to the row's face, and installs the types it read (`readCall` and
  `installTypeArgs`, `src/Effect4/Codegen/Read.lean`). A spelled row is its face: the unit
  literal for its term, and no type argument (`Signature.face`). A bare `Deferred.make()` is
  refused by its spelling. No instance is read at a default. A type with no printed form
  refuses the row by its spelling (`PrintRefusal.typeSpelling`).
- **A loop's stated cursor type.** `iterate` may state its cursor's type (DI-91), and the faces
  print it on the loop's `let`. The reader reads it through the checked reader (`readLeaf`). A
  spelling with no reading is refused by name, `ReadRefusal.annotation "local const"`. This is
  DI-91's fallback (a) in a checked form.
- **Not read: a list fold's stated accumulator type.** It is printed as the call's type
  argument and refused at reading, `ReadRefusal.annotation "fold accumulator"`.
- **The laws keep their statements.** `read_print` and `read_exact` are unchanged. Their domain
  admits a row whose type arguments are readable, on a row that declares none of its own and is
  no value row (`typeArgsReadable`). It admits a stated cursor type that is readable
  (`leafReadable`, `src/Effect4/Laws/Codegen/ReadPrint.lean`). `LawfulTypeArgs` states what the
  reader needs of a signature. The call's columns do not depend on the type arguments. Each
  update is read back by its own projection, and the two updates commute. The call's columns
  are the spelling, the shape, the trailing names, the request and the declared type arguments
  (`Row.callColumns`). The answer and error columns belong to the restored operation, not to
  the face. The row-call steps are `readCall_printCall` and `readCall_exact`
  (`src/Effect4/Laws/Codegen/ReadLeaf.lean`).
- **An operation's types are program annotations (decisions row 212).**
  `Formation.argumentAnnotations` reads them (`ScopedOp.typeArgs`,
  `src/Effect4/Program/Formation.lean`). So raw formation, the integer scan of admission and
  the module's class table reach a type argument. A module declares the class that a type
  argument names.
- **`ts/eff/read.ts` reads the same forms.** `readTypeChecked` is the checked reader's twin. It
  claims no agreement on a refusal's name.
- **The foreign contract (§3).** Both recognizers read `Deferred.make`'s type arguments and a
  loop's stated cursor type through that one reader (`readTypeText`). They lift the same
  program, and both refuse a type with no reading. One control runs both on the same sources
  (`ts/eff/ingest/test/foreign.test.ts`). Neither drops a type argument to agree.
- **The literal rule on the target (decisions row 256, inside DI-55's ruling).** The generated
  helpers `pair` and `tuple` widen a number or a Boolean type in an immediate slot. The slot's
  type is then `number` or `boolean`, as `litArgTy` types a number or a Boolean literal
  (`src/Effect4/Program/Typing/Rules.lean`). A string literal keeps its literal type. Every
  other argument keeps its type, and nothing is rewritten below the slot. `NativeAtom.row` owns
  the two bodies (`src/Effect4/Machine/Term.lean`). The shared type `Wide` has one owner, the
  preamble that `tools/Effect4Gen/PreludeAtoms.lean` writes. The consequence: a number or
  Boolean singleton type, or a brand, in a direct slot is lost on the target. A Boolean tuple
  tag no longer discriminates. The helpers keep no arbitrary TypeScript refinement.
- **The truth claim (§4).** The truth corpus gains `pRateRequest` and `pDeferredGate`
  (`harness/truth/Truth.lean`). The runner's import header names every atom of the generated
  profile (`harness/truth/run-truth.ts`). It also names the twelve printed helpers that are no
  atom. So a new atom needs no edit of the header. The lane's compiler controls gain two files.
  `harness/truth/literals.typecheck.ts` holds the literal rule's assertions and refusals.
  `harness/truth/queue-steps.typecheck.ts` holds the Queue module's six printed steps, each at
  the cell's printed type.
- **Superseded in the amendment above** ("an operation's binder term"). Its paragraph "Not
  established" said that a row's type arguments stay spelled at one instance. It also said
  that a loop with a stated cursor type does not read back. Its paragraph "A registered difference on the
  target" said that `pair` and `tuple` keep a Boolean or a number literal's type. Neither holds
  now. A fold with a stated type still prints and does not read back.
- **Not established.** No law states target typing or a host run. The compiler controls and
  the truth programs are finite checks under the pinned compiler and the pinned host.
  `Ref.make` carries no type argument, so `Ref.make<A>(v)` is not printed: it needs an appended
  constructor (decisions rows 210 and 212). A type argument outside the readable types is
  printed where it has a printed form. Its reading is refused, or it gives another type. No
  lane type-checks a whole printed Queue module.
- **Evidence.** *Proved*: `read_print`, `read_exact`, `readCall_printCall`, `readCall_exact`,
  `readTyChecked_exact`, `readTyChecked_of_readable`, `nativeLawful`. *Tested*: the batteries
  `Test/Codegen/TypeReader.lean`, `Test/Codegen/TermRows.lean`, `Test/Codegen/ReadContract.lean`,
  `Test/Program/FormationContract.lean` and `Test/Program/QueueFaces.lean`. *Tested*: tsgo
  7.0.0-dev.20260629.1 on the truth project's six control files, each with its refusals. *Tested*:
  the TypeScript reader lane, the two foreign readers on the constructed corpus, and four truth
  programs of this slice against rc.112.
