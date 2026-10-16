# 2026-10-16 Named types on the TypeScript face: the declaration block, its Schema, and the compiler's share

Status: research note (history, not authority). Base: `81f9a4354` on `refactor/phase1-phase3`.
Role: the type-research and compiler-usage seat of 2026-10-16, started by the coordinator after
decisions row 406. The seat edits no file under `src/`, `tools/`, `Test/` or `docs/core/`.

## The one thing to know first

A declared name prints as `export type N = …`, and tsgo 7 checks the block. One gap exists. The
compiler accepts a recursive alias only when its cycle passes a deferring position. Lean's
guardedness is weaker at four type formers: `option`, `except`, `exitOf` and `map`. The printer
closes the gap with a second spelling of those four on a cycle. The package lean4-typescript, at
`2ae4083` on branch `types/type-alias`, carries the declaration and the one missing type former.

## 1. Question

1. What does the printed module declare for a declared name, recursion included, and what does
   tsgo 7 accept?
2. What is the Schema face of a declared name at rc.112?
3. What does the Lean TypeScript package need?
4. Where should tsgo do work that the estate models by hand?

## 2. What was read or run

| Item | Evidence | Result |
| --- | --- | --- |
| `AGENTS.md`; the audit (`docs/research/2026-10-16-soundness-audit/README.md` §3, §4); the wiring plan's W5; decisions rows 158, 247, 380, 401, 402, 406 | reading | the representation this note builds on |
| `ofNormalized`, `legacyName?`, `payloadClass?` (`src/Effect4/Codegen/Types.lean`) | reading | `app n []` prints as the bare name `N`; nothing declares it |
| `schemaAlg`, `effDocument`, `rowDocument` (`src/Effect4/Schema/Bridge.lean`) | reading | `app` writes the marker `effect4/unlowered/app` |
| `headNames`, `rankHolds`, `guarded` (`src/Effect4/Program/TyDecls.lean`); `declChecks` (`src/Effect4/Program/SigApp.lean`) | reading | Lean's head is the union members; no spelling rule on a declared name |
| `ModuleEmission.file`, `preludeNames`, `moduleImports` (`src/Effect4/Codegen/Checked.lean`) | reading | the module's order and its free names |
| `declarationName`, `declarationBinding`, `declarationUses`, `typeUses` (`src/Effect4/Codegen/SourceBindings.lean`) | reading | the exhaustive matches a repin moves |
| `ts/eff/target-types.ts`; `readNamedType` (`ts/eff/read.ts`) | reading | the TypeScript twin prints a bare name; the reader reads a bare name as a class only |
| `vendor/effect-4.0.0-rc.112/src/internal/schema/fromRepresentation.ts`, `toRepresentation.ts`, `toCodeDocument.ts` | reading | revival by reference slots; reference allocation by identifier; code with `Schema.suspend` |
| `cd ts/eff && bun probe/named-types/run.ts` | tested | `PASS named-types compiler: 26 case files, 21 expected diagnostics, tsgo Version 7.0.0-dev.20260629.1`; `PASS named-types documents: 37 observations` |
| `LEAN_NUM_THREADS=2 lake build` in lean4-typescript at `2ae4083` | tested | `Build completed successfully (16 jobs)`; 40 guards and 6 axiom pins in `TypeScriptTest/TypeAlias.lean` |
| `tools/target/assignability.ts`, `checker.ts`, `oracle.ts`; `harness/tsdiag/run-tsdiag.mjs`; `generated/assignability.tsv`; `generated/tsdiag-agreement.tsv`; `src/Effect4/Laws/Codegen/TargetOrder.lean`; `codesOf` (`src/Effect4/Codegen/Diagnostics.lean`); the `Makefile`'s TypeScript lanes | reading | §5 |

The probe lives in `ts/eff/probe/named-types/`. Each case file states the error codes it expects
in its first line, and `run.ts` compares them with tsgo's codes as a multiset. `documents.run.ts`
revives documents at rc.112 and states one observation per line.

## 3. Findings

### F1. tsgo defers a recursive alias only at four kinds of position

The probe's cases `a04` to `a08`, `b01`, `c01` and `a17` establish the rule on the pinned build.

- **Deferring positions**: an object type's member, a tuple's element, and a type argument of an
  interface or a class. `ReadonlyArray`, `Cause.Cause`, `Ref.Ref`, `Fiber.Fiber` and
  `Deferred.Deferred` are interfaces.
- **Positions that do not defer**: a union member, and a type argument of an alias.
  `Option.Option` (`vendor/effect-4.0.0-rc.112/src/Option.ts:55`), `Result.Result`
  (`Result.ts:66`), `Exit.Exit` (`Exit.ts:59`), `Readonly` and `Record` are aliases.
- A cycle that passes no deferring position is refused with TS2456. `c01` refuses seven aliases on
  six such cycles and accepts eight cycles that pass one deferring position.
- Each of the four aliases has a deferring spelling of the same type, accepted on a cycle (`b01`):

| Lean type | The printed spelling | The deferring spelling |
| --- | --- | --- |
| `option a` | `Option.Option<A>` | `Option.None<A> \| Option.Some<A>` |
| `except e a` | `Result.Result<A, E>` | `Result.Success<A, E> \| Result.Failure<A, E>` |
| `exitOf a e` | `Exit.Exit<A, E>` | `Exit.Success<A, E> \| Exit.Failure<A, E>` |
| `map string v` | `Readonly<Record<string, V>>` | `{ readonly [key: string]: V }` |

`b01` assigns each deferring spelling to its printed spelling and back, and tsgo accepts all eight
assignments.

### F2. Lean's guardedness is weaker than tsgo's at those four formers

- `TyDecls.headNames` reads a body's union members. A table is guarded when the head references
  have no cycle (`TyDecls.guarded`).
- tsgo's head also passes the arguments of the four aliases of F1, and of a declared name with
  arguments.
- So `Peano = option Peano`, `Dict = map string Dict` and `Steps = except string Steps` are
  guarded in Lean, and their printed spellings are refused by tsgo (`a04`, `a05`, `a06`).
- The cycles that Lean refuses in `a09`, tsgo refuses too.
- At an unguarded table, rc.112 overflows the stack when it decodes (observations 7a and 7b). So
  Lean's refusal is load-bearing.

### F3. tsgo does not catch every clash of a declared name

- A declared name equal to a payload class gives TS2300 twice (`a16`).
- A declared name equal to a type the module imports from its prelude gives TS2440 (`b03`).
- A declared name equal to an `effect` namespace the module imports gives no diagnostic (`a15`,
  `b02`). A namespace has no type meaning, so the alias stands beside it and the name spells two
  things.
- So the printer must refuse a clash itself. The compiler finds only some clashes.

### F4. tsgo checks a variance annotation, on some bodies only

- `type Box<out A> = { readonly value: A }` is accepted (`a12`).
- An annotation that disagrees with the body gives TS2636 (`a13`).
- An annotation on an alias whose body is a union gives TS2637 (`a14`). A derived sum type has a
  union body.

### F5. The Schema document: rc.112 revives a bare reference, and rewrites it with a `Suspend`

The observations are those of `documents.run.ts`. Each comparison is modulo `N_S` (`normS`), whose
erased keys the probe copies.

- rc.112 revives a document whose declared names are bare `Reference` nodes, recursive or not. It
  decodes a tree, and it refuses a negative natural at depth (1a, 1b, 3e, 11c).
- rc.112 writes the revived Schema back with a `Suspend` around each back edge of its own
  traversal (1d). Which edges are back edges depends on the root (3a to 3c).
- So the bare document is no fixed point of revival and rewriting under `N_S`.
- It is a fixed point under `N_S` with one more rule (9a to 9c, 10a, 11a). The rule: a `Suspend`
  with no annotation and no check around a `Reference` is that `Reference`.
- A document that writes a `Suspend` itself can make rc.112 invent a reference named `Suspend_`.
  The revived wrapper is one object shared by every explicit `Suspend` of its key (10c, 10d, 11b).
- A declared name with no recursion stays a bare reference under rewriting (4a).

### F6. The Schema code: rc.112 needs the identifier and a `Schema.suspend` in recursive definitions

- Schema code allocates a reference only by an `identifier` annotation. Without it a recursive
  Schema is named `Objects_`, and a name used twice is written inline (13a, 13d).
- With `.annotate({ identifier: "Tree" })` the code writes the bare document modulo the extended
  `N_S` (13b, 13c).
- rc.112's code generator writes `Schema.suspend((): Schema.Codec<T> => T)` at each reference
  that a recursive definition makes to a recursive definition (8a, 8b, 12a, 12c;
  `vendor/effect-4.0.0-rc.112/src/internal/schema/toCodeDocument.ts:384`).
- That code, evaluated, writes the bare document modulo the extended `N_S` (12b, 12d).
- rc.112 writes no code for a document decoded from JSON: its checks carry no `toCode` (8c). Code
  is written from a revived Schema, as `harness/truth/schema-codec/check.ts` does.
- `Schema.Codec<T>` type-checks on a recursive body that holds an `Exit` with its defect slot
  (`b06`).

### F7. The readers read no declared name

- `readNamedType` (`ts/eff/read.ts`) reads a bare name as the record of a payload class, and as
  nothing otherwise. The Lean reader `readTy` (`src/Effect4/Codegen/Classes.lean`) reads the same.
- So a printed module that names a declared type does not read back today.

### F8. The repin moves six arms in this repository

- `Decl.typeAlias`: `declarationName`, `declarationBinding` and `declarationUses`
  (`src/Effect4/Codegen/SourceBindings.lean`).
- `TypeRef.index`: `TargetOrder.size` (`src/Effect4/Laws/Codegen/TargetOrder.lean`), `typeUses`
  (`src/Effect4/Codegen/SourceBindings.lean`) and `readTy` (`src/Effect4/Codegen/Classes.lean`).
- A law that splits on one of these functions' arms moves with it. The build finds them.

## 4. The design (proposals for the coordinator)

### 4.1 The names a module declares

- **The reached names**: each declared name in a type that the module prints, closed under the
  names that the reached bodies mention. The closure reads `SigApp.types`.
- **Their order**: the table's order, filtered. An alias is hoisted, so the order is for the
  reader and the diff, not for tsgo.
- A name that no printed type reaches is not printed.

### 4.2 The TypeScript declaration block

Each reached name `N` with body `b` prints `export type N = T`. `T` is `ofTy b`, with the deferring
spelling of F1 at each **head alias on a cycle**.

- The **target head** of a type is a set of positions. It holds the type itself and each member
  of a union at the head.
- It also holds each argument of an `option`, `except` or `exitOf` at the head. It holds the value
  of a `map` at the head, and each argument of a declared name at the head.
- The **target-head graph** has an edge from `N` to `M` when the target head of `N`'s body names
  `M`.
- A **head alias on a cycle** is an `option`, `except`, `exitOf` or `map` node at the head of
  `N`'s body. Its arguments' target head names some `M`, and the graph has a path from `M` to
  `N`.
- After the deferring spellings, a body's target head names only its union members' references.
  Those are `TyDecls.headNames`, and `TyDecls.guarded` makes them acyclic. So tsgo should accept
  the block on every guarded monomorphic table. The evidence is the finite probe `c01` with `b01`,
  not a proof.
- The deferring spelling is a second spelling of four formers. The block alone holds it, and the
  readers read it back (§4.7).
- The block stands after the payload classes and before the row services. A doc line names the
  declaration: `/** Declared type \`N\` (decisions row 406). */`.

The alternative of one spelling everywhere moves the shipped bytes of every module that prints
an `Option`. It moves the gate tables too, so this note does not propose it.

### 4.3 The names the printer refuses

The printer refuses a declared name by name, with a new `PrintRefusal`, when the name:

1. is not a target identifier (`targetIdentifier`), a dotted name included: an alias has one
   segment;
2. is a free name the module imports: an `effect` namespace (`effectNamespaces`), `pipe`, or a
   prelude name (`preludeNames`);
3. is a payload class's name, a row service's name, or a declaration name of the module;
4. is a reference key of the S-2 documents: `answer`, `error`, `request`, or a requirement key
   (`requirementKey`).

F3 shows that tsgo misses the second case at a namespace. The refusal belongs to the printer, not
to the typing signature's admission: the spelling is a target profile's, and Effect TypeScript is
one profile.

### 4.4 Parameters and variances (row 401 (4))

- A declared name with parameters prints `export type N<A> = …`, with the parameters of
  lean4-typescript's `TypeParam`.
- Where the body is an object type, the printer writes each parameter's declared variance as an
  annotation: `out`, `in`, or `in out`.
- The compiler then checks the variance table against the body (TS2636). This is the compiler
  checking the table for free (§5, P2).
- Where the body is a union, an annotation is refused (TS2637), so the parameter prints with none.
- A declared name with arguments on a cycle through its own arguments has no deferring spelling
  in F1's table. The printer refuses it by name until a deferring construct exists.

### 4.5 The Schema document

- `schemaAlg.ty_app` writes `.reference n` for `app n []`, in place of the unlowered marker.
- The document's references table gains `n ↦ schema body` for each reached name, beside the S-2
  entries. §4.3 keeps the keys disjoint.
- The document writes no `Suspend`. F5 shows that a written `Suspend` can make rc.112 allocate a
  `Suspend_` reference.
- `N_S` gains one rule: a `Suspend` with no annotation and no check around a `Reference` is that
  `Reference`. Revival makes every reference lazy, so the rule erases nothing that decodes.
- `ofSchema` gains a reference arm. It reads `.reference n`, and the `Suspend` around it, as
  `app n []`. Its exactness statement (`ofSchema_exact`) then holds modulo the extended `N_S`.
  This is a proposed statement, not a proved one.
- `reservedFree` stays false at `app` until the arm and its retraction are proved.

### 4.6 The Schema code

- Each reached name prints `export const N = C.annotate({ identifier: "N" })`, where `C` is the
  body's code (`Codegen.SchemaCode`). The `identifier` key is one that `N_S` erases.
- A reference to a declared name prints `N`. Inside a recursive name's body, a reference to a
  recursive name prints `Schema.suspend((): Schema.Codec<N> => N)`, as rc.112's generator does
  (F6).
- The constants stand in an order where each unsuspended reference points to an earlier constant.
  The graph of unsuspended references is acyclic, since every cycle passes a suspended reference.
- `SchemaCode`'s rule "no annotations" gains this one exception, and it stops refusing a
  reference.

### 4.7 The readers

- The TypeScript reader (`ts/eff/read.ts`) and the Lean reader (`Codegen/Read.lean`,
  `Codegen/Classes.lean`) read the module's `type` declarations into a declaration table.
- A bare name that the table declares reads as `app N []`, before the class lookup.
- Inside a declaration, each deferring spelling of F1 reads as its former.
- The read-back law (`read_print`) then speaks of a module and its table. Its statement is the
  coordinator's.

### 4.8 Where each change lands

| Change | File | Kind |
| --- | --- | --- |
| The pin of lean4-typescript at `2ae4083` | `lakefile.toml`, `lake-manifest.json` | the coordinator's, on the owner's word |
| The six arms of F8 | `Codegen/SourceBindings.lean`, `Laws/Codegen/TargetOrder.lean`, `Codegen/Classes.lean` | mechanical, with the repin |
| The reached names, the target head, the block | `Codegen/Types.lean` | new definitions beside `ofTy` |
| The block in the file; the refusals of §4.3 | `Codegen/Checked.lean`, `Codegen/Print.lean` | `ModuleEmission.file` and a `PrintRefusal` |
| The reference arm, the table entries, `N_S`'s rule, `ofSchema`'s arm | `Schema/Bridge.lean` | the writer, the reader and their laws |
| The identifier and the suspensions | `Codegen/SchemaCode.lean` | the code printer |
| The readers | `Codegen/Read.lean`, `Codegen/Classes.lean`, `ts/eff/read.ts`, `ts/eff/target-types.ts` | read the block |
| The differential at declared names | `tools/Tools/TyVectors.lean`, `tools/target/oracle.ts` | §5, P1 |

## 5. The audit: where the compiler should do more of the work

### 5.1 How the estate uses tsgo today

| Lane | Driver | What it asks tsgo | What it compares |
| --- | --- | --- | --- |
| `check-target`, the order | `tools/target/assignability.ts` over `checker.ts` | `isTypeAssignableTo` and one assignment statement, per pair and direction | `Ty.sub` against tsgo: 708 `agree`, 10 `cut`, 24 `incomplete` rows in `generated/assignability.tsv` |
| `check-target`, the corpus | `checker.ts` (`getTypeAtLocation`, `typeToString`) | the `A`, `E` and `R` columns of a printed program | Lean's declared type, by assignment |
| `check-tsdiag` | `harness/tsdiag/run-tsdiag.mjs` | every diagnostic of the unchecked corpus modules | the codes against `codesOf`'s predictions: 180 `refused-agree`, 65 `refused-unmapped`, 19 `refused-silent`, 5 `refused-gap`, 2 `refused-other`, 137 `typed-clean` |
| `check-truth` | `scripts/check-truth.py` | the printed modules and the `*.typecheck.ts` fixtures | no diagnostic; `@ts-expect-error` at each red line |
| `check-schema-codec` | the `tsgo` command | the generated Schemas | no diagnostic |
| `check-schema-ts` | `scripts/check-schema-typescript-generation.sh` | the Schema fixture, under `typescript` 7.0.2 and `@effect/tsgo` 0.38.0 | no diagnostic; the Effect language service's diagnostics |
| `ts/eff` | `bun run typecheck` | the reader's own sources | no diagnostic |

The Lean model `TargetOrder.assignable` transcribes tsgo's relater rule by rule. Its check is the
battery `Test/Codegen/TargetOrder.lean` against the committed verdicts.

### 5.2 Proposals

- **P1. Read tsgo's verdict at declared names, and keep the hand model free of names.**
  - `TargetOrder.rel` bounds its recursion by the sizes of the two types. Unfolding a recursive
    alias grows a type, so the model cannot follow one. tsgo relates recursive aliases with its own
    cycle handling.
  - Lean's order is nominal at a name with no argument: `Ty.sub` never unfolds one. So the
    printer's monotonicity there needs only the arms that unfold nothing. Those are reflexivity
    (`s == t`) and the arms at `never`, `unknown` and a union, and `rel` has each.
  - At a name and its body the model then answers `false` where tsgo answers `true`. So at names
    the model is a lower bound of tsgo's relation, and its battery compares it only where
    `Ty.sub` holds.
  - The differential has no pair at a declared name today: `generated/assignability.tsv` holds
    no `app` row. The pairs gain declared names, and the query source gains the declaration block.
  - The expected verdicts are `agree` at one name and `incomplete` across names, since tsgo is
    structural. A `defect` there would be a wrong body, a finding about the printer.
- **P2. Let tsgo check the variance table.** §4.4 prints a declared variance as an annotation
  on an object body, and the compiler checks it (TS2636). A union body takes no annotation
  (TS2637). There, a check module assigns `N<Sub>` to `N<Super>` for each covariant parameter.
  It assigns the reverse for each contravariant one. The compiler then measures the body: an
  outside oracle for the polarity reading of row 401 (4).
- **P3. Compare a refusal's place, not only its codes.** The tsdiag lane reads each refusal's
  program address (its `blamePath` column) and compares codes per program. `codesOf` holds a
  prediction per reason, and 65 rows have none. The printer's address-to-span map is still to
  come (row 380 (5)). With it, the lane can ask whether the compiler reports a diagnostic inside
  the refused address's span. The table of predicted codes then becomes data the lane observes,
  not a second hand copy.
- **P4. One build of the one compiler.** The Schema lane runs `typescript` 7.0.2 with
  `@effect/tsgo` 0.38.0 (`harness/schema-host/package.json`). Every other lane runs
  `@typescript/native-preview` 7.0.0-dev.20260629.1. Two builds can drift in what they accept,
  and the rule of `check-tsgo` is one compiler.
  - The release exports the same synchronous API at `typescript/unstable/sync`. Its declaration
    file has `isTypeAssignableTo`, `getTypeAtLocation`, `typeToString` and both diagnostic reads.
  - On this note's probe, the release (`Version 7.0.2+effect-tsgo.0.38.0`) reports the same 21
    diagnostics as the pinned build, at the same lines and columns.
  - So every lane can move to the release, and the Effect language service can then run on the
    printed modules too. Whether `checker.ts` runs unchanged on the release was not tested.
- **P5. Check the code of an expected error.** A `@ts-expect-error` line passes on any error, an
  unrelated one included. The probe's runner checks each case's codes as a multiset, and its
  form serves the `*.typecheck.ts` fixtures as well.
- **P6. One file of compiler options.** The options stand in `harness/truth/tsconfig.json`,
  `ts/eff/tsconfig.json`, `HostConfig` (`src/Effect4/Codegen/Diagnostics.lean`),
  `harness/schema-generation/tsconfig.json` and the probe's copy. A base file that each lane
  extends would make `HostConfig` its one writer.

### 5.3 What stays with Lean

- **The target head and the deferring spelling.** The printer chooses a spelling before tsgo
  runs, so the rule of §4.2 is Lean's. tsgo checks the result, case by case.
- **The clashes of §4.3.** tsgo is silent at a namespace (F3).
- **The nominal order.** tsgo compares aliases by structure, so it accepts more than `Ty.sub`
  does. The differential classifies that difference; it cannot replace the order.
- **The table's guardedness.** It is Lean's located refusal, and rc.112 overflows without it
  (F2).

## 6. Decisions rows to propose

1. A declared name prints as an alias in the module's declaration block. A head alias on a cycle
   takes its deferring spelling, and the readers read both spellings (§4.2, §4.7).
2. The printer refuses a declared name that is no target identifier, or that clashes with a
   module binding or an S-2 key (§4.3).
3. The Schema document writes a bare reference per declared name and no `Suspend`. `N_S` erases a
   bare `Suspend` around a reference (§4.5).
4. The Schema code annotates each declared name's identifier, and suspends each reference inside
   a recursive definition to a recursive definition (§4.6).
5. lean4-typescript v0.8.0 (`2ae4083`): `Decl.typeAlias` and `TypeRef.index`, pinned when the owner
   says.
6. P1 to P6 of §5.2, each its own slice.

## 7. What this does not establish

- The probe is a finite observation of one pinned tsgo build and of rc.112. The rule of F1 is
  read off 26 case files, not off tsgo's source.
- §4.2's claim that tsgo accepts every guarded monomorphic table under the deferring spelling is
  a proposal with finite evidence. No theorem states it.
- No Lean file of this repository changed, and no gate of this repository ran.
- The repin's cost in F8 comes from name searches. The build after the repin is the measure.
- P4 rests on the release's declaration file and on one probe run. No lane ran on the release.
