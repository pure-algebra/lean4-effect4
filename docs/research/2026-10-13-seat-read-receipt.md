# Seat READ receipt: the emitted module reads back whole, and its keys read by name (2026-10-13)

Status: receipt (history, not authority), written as the seat works. Seat READ, branch
`seat/read`, worktree `~/Dev/lean4-effect4-read`, base `d05312985`. The brief is
`docs/research/2026-10-13-seat-read-brief.md`.

## The one thing to know before merging

(Written last.)

## Base, head and evidence words

- Base: `d05312985`.
- Evidence words: **proved** means the kernel checked it and `#axiom_audit` passed its module.
  **Tested** means a `#guard` or a gate ran green at the head. **Reproduced** means a scratch
  evaluation printed the result. **Assumed** means read in the source and not run.

## The base and the merge

At the base `d05312985`, `lake build Test.Dogfood.Scenario.TodoService` failed three guards
(tested), because E3 made the to-do's rows require `todoRepoKey`. The coordinator's message during
the seat named `60f10bc4c` on `refactor/phase1-phase3`: seat SVC's E2 join (the file declares the
rows' services, `ModuleEmission.file`) and E4, with the battery restated. The seat merged it as
`9c5393ff5` before its first commit, as the message asked.

## 1. The class-aware header reader (item 1)

### What changed

| Declaration | File | Change |
| --- | --- | --- |
| `readNamed`, `readTy`, `readTys`, `readFieldTys`, `readFieldTy` | `src/Effect4/Codegen/Classes.lean` | one reader under a parameter `classes`; a class name reads as the record its declaration declares (`classes.lookup tag`) |
| `readTyChecked`, `ReadableTy`, `readTysChecked` | same | take the classes; the expression reader passes `[]` |
| `readClassDecl` | same | reads a class's fields under no class, as before |
| `readParam`, `readDefHead` | `src/Effect4/Codegen/Read.lean` | read the columns under the module's classes; `readDefHead` takes the signature and reads the requirement row `R` by `readKeys` (`readRequirement` and the re-print check) |
| `ParamDecl.readable`, `DefDecl.readable` | same | under the classes; the requirement row is canonical (`(Requirement.ofList d.requires).elems = d.requires`) instead of empty |
| `readLeaf` (`.optTy`), `installTypeArgs`, `typeArgsReadable` | same | read under no class, so the expression reader's domain is unchanged |

One reader serves both places: the header reads under the module's classes, and the expression
reader under none. The expression reader keeps its domain, so `read_print`, `read_exact` and
`PrintTyped`'s laws keep their statements.

### The laws

| Theorem | File | Change |
| --- | --- | --- |
| `readTyChecked_exact`, `readTyChecked_of_readable`, `ofTy_of_readable`, `readTysChecked_length`, `readTysChecked_exact`, `readTysChecked_of_readable`, `writeTys_of_readable` | `src/Effect4/Laws/Codegen/Classes.lean` | generalized over the classes; same proofs |
| `readParams_printParams`, `readDefHead_printDef`, `readDefs_printDefs`, `readModule_printModule_defs` | `src/Effect4/Laws/Codegen/Module.lean` | under the module's classes; the requirement row read back by `readKeys_requirementType` |
| `readDefHead_withDefs` (new) | same | the header reads alike at the block's signature, by `rfl` |
| `blockReadable`, `blockReadable_pieces` | `src/Effect4/Laws/Api/ModuleReadable.lean` | `DefDecl.readable classes` |
| `leafReadable` | `src/Effect4/Laws/Codegen/ReadPrint.lean` | `ReadableTy []` |

### The to-do

On the merged tree, `readBack? application`, `readBack? classFree` and `readBack? keyFree` are each
`some (true, true)` (reproduced, `<scratch>/lean/Probe2.lean`). So the to-do's service block is in
`blockReadable` under its module's classes (`NotFound`), and `Api.readModule e.module b.table` gives
the built program back. `lake build Test.Dogfood.Scenario.TodoService` fails exactly the two
guards that state today's reach (tested):

- line 88, `#guard readBack? application = some (false, false)`: flip to `some (true, true)`;
- line 91, `#guard readBack? classFree = some (false, false)`: flip to `some (true, true)`.

The guard at line 94, `readBack? keyFree = some (true, true)`, holds. The comments above the two
guards name the old reason (the header reader read no class and only `never`).

### Evidence for item 1

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Api.ModuleReadable` (before the merge) | green, 369 jobs |
| `lake build` of the direct dependents and the four edited batteries (before the merge) | green, 1150 and 860 jobs |
| the same set on the merged tree, with `Tools.Code.Module` and `Test.Dogfood.Scenario.Todo` | green, 1169 jobs |
| `lake env lean -DwarningAsError=true harness/channel-transforms/Produce.lean` | elaborates, exit 0 |
| `#axiom_audit` over `Codegen.Classes`, `Codegen.Read`, `Laws.Codegen.Classes`, `Laws.Codegen.ReadPrint`, `Laws.Codegen.Module`, `Laws.Api.ModuleReadable` and the four batteries (`<scratch>/lean/Audit1.lean`) | `2396 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals` |

The batteries (tested): `Test/Codegen/TypeReader.lean` reads a payload class under the classes
that declare it, alone, under `Option` and `ReadonlyArray` and in a union, with four red controls
(other fields, an undeclared name, a union out of normal form, a class whose field names another
class). `Test/Codegen/DefinitionsPrint.lean`'s control `withService` flips: a header's requirement
row now reads back, and three red controls refuse a row out of order, a literal that is no key's
text, and a row with a key twice.

## 2. The row services read back (item 2)

### The design

The rows' service declarations are a function of the table, so the reader takes the table and
checks them against the services' data, piece by piece (`readRowServices`,
`src/Effect4/Codegen/RowServices.lean`). Each piece is compared by a decision on strings, binders,
`TypeRef`s and parameters, never by a traversal of a `String`: `TypeScript.Expr` has a `BEq` but
no decidable equality, and the deriving handler does not apply to its mutual block (reproduced).

`rowServiceDecls` is now the image of the services' data (`RowServiceData`, `rowServiceData`,
`RowServiceData.decls`, `accessorExpr`, `accessorRequest`), with the same output and refusals.
`rowAccessor` is gone into `accessorExpr`.

The module reader takes one more argument, the rows whose services the module declares after its
classes (`Program.readModule … rows decls`):

- the file (`ModuleEmission.file`, seat SVC's E2 join): the table's rows, by `Api.readFile`;
- the envelope that a host wraps (`ModuleEmission.module`): none, by `Api.readModule`, as before.

So the envelope reads back as it did, `Api.printModule_roundTrip` and the reading boundary
(`admitModule`) keep their statements, and the file reads back whole. Each reader refuses the
other's form.

### The laws

| Theorem | File | Statement |
| --- | --- | --- |
| `isAccessor_accessorExpr`, `isAccessor_exact`, `isAccessors_map`, `isAccessors_exact` | `src/Effect4/Laws/Codegen/RowServices.lean` (new) | an accessor, and a service's accessors, are accepted exactly |
| `RowServiceData.isDecls_decls`, `RowServiceData.isDecls_exact` | same | a service's two declarations are accepted exactly |
| `readServiceDecls_decls`, `readServiceDecls_exact` | same | the services' declarations, in order |
| `readRowServices_rowServiceDecls` | same | retraction: the table's services' declarations read back, leaving what follows |
| `readRowServices_exact` | same | exactness: what the reader accepts is the table's services' declarations |
| `rowServiceDecls_nil` | same | no row prints no service, by `rfl` |
| `splitClasses_rowServices` | `src/Effect4/Laws/Codegen/Module.lean` | classes, then service constants, then constants, split after the classes |
| `readModule_printModule`, `readModule_printModule_defs` | same | restated with the rows' services after the classes |
| `readModule_printModule_readable`, `readModule_printModule_defs_readable` | `src/Effect4/Laws/Api/ModuleReadable.lean` | the same, on the readable domain |
| `ModuleEmission.readDecls` (new) | same | the emitted declarations read back after the classes and any rows' services |
| `ModuleEmission.readModule` | same | the envelope, at no row's services: the instance of `readDecls` |
| `ModuleEmission.readFile` (new) | same | **the file reads back**: `emission.file prelude except = .ok file` gives the program at the table's rows |

`Api.readFile` (new, `src/Effect4/Api.lean`) is the file reader at the application face;
`Api.readModule` reads the envelope at no row's services, as before.

### The to-do's file

`Test/Dogfood/Scenario/TodoFile.lean` (new; tested):

- reader: the to-do's file (`e.file "./prelude.ts"`) reads back to the built program by
  `Api.readFile`;
- reader: the envelope reads back by `Api.readModule`;
- control: each reader refuses the other's form (the envelope as a file: `shape "row services"`);
- control: a key at another identity (`"k30_7"`), an accessor that calls another method, and the
  two declarations in the other order: each `shape "row services"`.

### Evidence for item 2

| Command | Result |
| --- | --- |
| `lake build Effect4.Laws.Codegen.RowServices` | green, 113 jobs |
| `lake build Effect4.Laws.Api.ModuleReadable Effect4.Laws.Codegen.Admit Test.Codegen.DefinitionsPrint Test.Dogfood.Scenario.TodoFile` | green, 1136 jobs |
| `lake build` of the direct importers of `Effect4.Api`, `Codegen.Read`, `Codegen.RowServices`, `Codegen.Admit` and the law modules, the to-do's batteries and `Laws.Codegen.PrintTyped` (91 targets) | green, 1471 jobs |
| `#axiom_audit` over `Codegen.RowServices`, `Codegen.Read`, `Api`, `Codegen.Admit`, `Laws.Codegen.Admit`, `Laws.Codegen.Module`, `Laws.Api.ModuleReadable`, `Laws.Codegen.RowServices` and the two batteries (`<scratch>/lean/Audit2.lean`) | `1755 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals` |

With item 2, `Test.Dogfood.Scenario.TodoService` fails the same two guards as after item 1 and
nothing else: its `readBack?` reads the envelope, which still reads back.

(More in progress.)
