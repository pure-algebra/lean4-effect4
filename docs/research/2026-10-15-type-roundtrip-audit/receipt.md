# Receipt: the types landing (2026-10-15)

**The one thing to know before merging:** the types audit's six fixes land as one batch with one
gate run (decisions row 399).

The OCaml compile gaps of the lowered host are repaired as far as the probe measures. §5 gives
where the probe stops.

Status: the coordinator's receipt (history, not authority). Base: `bfefa348c` on
`refactor/phase1-phase3`. The audit and its plan are `README.md` beside this note (§6, §6A). §8 of
the audit recommends the next slices.

## 1. What landed

| Item | Change | Files |
| --- | --- | --- |
| §6.4 `eq` at `bool` | one scheme alternative and one evaluator arm (DI-35) | `src/Effect4/Program/NativeAtom.lean`, `src/Effect4/Machine/Term.lean`; the laws `Laws/Program/Typed.lean`, `Typed/Membership.lean`, `Typed/Denotation/Terms.lean`, `Typing/TermIntro.lean`, `Machine/TermHandles.lean`, `Program/Handles/Term.lean`; the prelude's self-test; the to-do's `sameFlag` replaced by `eq` |
| §6.1 the Schema arms | `number`, `null`, `undefined` and `bytes` written and read; `Uint8Array`'s id reserved | `src/Effect4/Schema/Bridge.lean` (the arms, `ofSchema_exact`'s cases, `ofSchema_schema`, `normS_null`, `normS_undefined`), `Schema/TyFaces.lean`, `Codegen/SchemaCode.lean` (`Schema.Uint8Array`); the codec gate's hand `Schema.Number` removed |
| §6.2 `Int` and `Num` | `int` and `number` print as the prelude's aliases and read back; no payload class takes either name | `Codegen/Types.lean`, `Codegen/Classes.lean`, `Codegen/Checked.lean` (`preludeNames`), `Program/Ty.lean` (`renderRaw`, the diagnostic spelling), `harness/truth/prelude.ts`; the twins `ts/eff/target-types.ts`, `ts/eff/read.ts` |
| §6.3 read back | `unknown`, `Exit`, `Cause`, `Fiber` and `Deferred` read wherever the checked reader reads | `Codegen/Classes.lean`, `ts/eff/read.ts` |
| §6.5 sum types | `Image.int`, `Image.lit`, `Image.union` (the values of a sum that exactly one side reads); `Modeled`'s carrier fold and `member` law over them; `deriving Modeled` on an inductive; `instance : Modeled Int` | `Store/Carrier/Image.lean`, `Image/Containers.lean`, `Schema/Modeled.lean`, `Schema/Modeled/Derive.lean`, `Laws/Schema/Modeled.lean` |
| §6.6 named row parameters | `r(a : A, b : B)` as one record request, a call by name, `fails E` per row | `Program/Authoring/Declare.lean` |
| §6.7 compile gaps | transparent structures (`Fin`, `BitVec`, the `UInt`s, `Char`) as their one field; `String.ofByteArray` through `lcnf_string_of_bytes`; an all-erased application eta-expanded | `OCaml5/Lcnf/TypeRows.lean`, `Lcnf/Builtins.lean`, `Lcnf/Translate.lean` |

The landing found two more facts on the way:

- `Ty.renderRaw`, the diagnostic spelling of a type, still spelled `int` and `number` as `number`.
  The agreement guard in `Test/Codegen/ExprContract.lean` found it. It now spells them as
  `Codegen.Types.ofTy` does.
- The target lane kept four hand copies of the names a printed type may use. `pairImports`
  (`tools/target/oracle.ts`) is now the one list, and it declares the prelude's aliases from
  `typeAliasNames`. `rows.ts`, `corpus.ts` and `profile.ts` read it.
- The assignability differential's spelling cut compares spellings with the aliases read as
  `number`, as tsgo reads them (`tools/target/assignability.ts`). No verdict of its 742 pairs
  moved. The verdict counts of `generated/assignability.tsv` and `generated/row-citations.tsv`
  are equal before and after; only spellings and the cut's wording changed.
- The printed corpus gains one program that both checkers type and both runs agree on: `g201`,
  whose `eq` at Booleans tsgo refused before. The tally of `harness/truth/corpus-results.tsv`
  goes from 122 agreeing runs to 123, with 6 signed differences before and after.
- The Queue and Semaphore library modules now print and read back to the programs they were
  built to. Their handles read at a definition header since `Deferred` reads. Before, both were
  refused as unreadable (`Test/Program/ModuleDefinitions.lean`, `Test/Codegen/ServicesPrint.lean`).

Batteries changed:
- the new readers and controls: `Test/Schema/Modeled.lean` (sum types, integers, literals, three
  refusal controls) and `Test/Program/AuthoringDeclare.lean` (named parameters, with a control);
- the controls that flipped from a refusal to a reading: `Test/Codegen/TypeReader.lean`,
  `Test/Codegen/SchemaCode.lean`, `Test/Codegen/SurfaceContract.lean`,
  `Test/Codegen/PayloadClasses.lean`, `Test/Codegen/ServicesPrint.lean`,
  `Test/Codegen/ExprContract.lean`, `Test/Codegen/DataTypes.lean`, `Test/Program/TyWave.lean`,
  `Test/Program/TypedContract.lean`, `Test/Program/ModuleDefinitions.lean`,
  `Test/Schema/DataBridge.lean`, `Test/Schema/DialectContract.lean`,
  `Test/Schema/DocumentJson.lean` and `Test/Dogfood/Scenario/Todo.lean`;
- the TypeScript tests whose red control was `unknown`: `ts/eff/test/payload-classes.test.ts`,
  `ts/eff/ingest/test/foreign.test.ts` and `ts/eff/test/term-rows.test.ts`. Their red control is
  now another type with no reading: `bigint` or `Ref` outside a header.

## 2. Placement

- §6.1 serves `exact-codecs` (R3). `ofSchema_exact` and `ofSchema_schema` keep their statements
  on the wider domain. No claim is added.
- §6.5 serves `store-typing` (R3). `Model.member` (claim `modeled-membership`) is proved for the
  three new carriers. The derived instances owe no proof of their own.
- §6.2, §6.3, §6.4 and §6.6 change printing, reading, an atom's scheme and authoring syntax. They
  keep every existing claim's statement.

## 3. Commands and results

Each Lean command ran through `scratch/lean-slot.sh`, one `lake` at a time.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4 Effect4Laws OCaml5 Conform Tools Effect4Gen Test` | `Build completed successfully (2752 jobs)`, after three repairs (§3.1) |
| `python3 scripts/generate.py`, then `--only lcnf` and `--only fixtures` | `PASS generate` each; changed: `harness/truth/prelude-atoms.gen.ts`, `ts/eff/test/type-projection.gen.json`, `ocaml/gen/api_gen.ml`, `ocaml/engine/api_engine.ml` and their closure manifests |
| `opam exec --switch=effect4 -- dune build` (in `ocaml/`) | exit 0 |
| `bash probes/host-compile.sh OUT` | `PASS host-compile: ocamlopt types 26804 lines`; 0 errors, 13 warnings 8 (partial match); closure 1330 of cap 4000, no declaration missing |
| `cd ts/eff && tsgo --noEmit -p tsconfig.json && bun test` | tsgo 7.0.0-dev.20260629.1 clean; 784 pass, 0 fail |
| `make check-full` | exit 0 at the seventh run (§3.2) |
| `make check-gen`, `make check-docs` | §3.3 |

### 3.1 The build's repairs

- `src/Effect4/Laws/Program/Typed/Denotation/Terms.lean`: `eq`'s progress proof gained its Boolean case.
- `src/OCaml5/Lcnf/Translate.lean`: `altPat`'s transparent-structure arm had its `else` on the wrong `if`.
- The battery guards that §1 lists pinned a refusal that now reads, or the old spelling. Each is
  now a reader of the new answer, and each control moved to a type that still refuses.

### 3.2 The runs of `make check-full`

Each failed run stopped at one committed table that the change moves. Each table was diffed, and
its verdict columns compared, before its promotion.

| Run | Stop | Action |
| --- | --- | --- |
| 1 | `row-types` | regenerated: `lt`, `plus` and `minus` spell `Int` |
| 2, 3 | `assignability`, then `rows` | the target lane's one import list (§1); both promoted with equal verdict counts |
| 4 | `ts-reader`'s typecheck | a test literal widened to `string`; `as const` |
| 5 | `corpus` | promoted (`make gen-corpus-results`): `g201` types and agrees; three messages name `boolean` |
| 6 | `tsdiag` | promoted (`make gen-tsdiag`): `g201` typed and clean on both sides |
| 7 | none | every step passes: `tsgo`, `schema-codec`, `schema-ts`, `truth`, `target`, `ts-reader`, `corpus`, `tsdiag`, `host-protocol`, `ingest-smoke`, `service-identity`, `native`, `compiler`, `ocaml` |

### 3.3 Drift and documents

`make check-gen` compares the generators' output with the index, so it ran after the commits.
Before them it listed the eight regenerated files above and nothing else. `make check-docs`
asked only that this receipt be force-added.

## 4. Axiom output

`#axiom_audit` over the 39 touched `Effect4` and `Test` modules
(`tools/ProofGraph/AxiomAudit.lean`):

- 38 modules: `5961 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- `Effect4.Schema.Modeled.Derive`: 8 declarations reach `Classical.choice`, through
  `Lean.Name.toString` and `Lean.getConstInfoCtor`. The module is a command elaborator, and the
  axiom gate admits it whole (`Test/Audit/AxiomGate.lean`). Five of the eight are declarations of the base
  (`defaultSpelling`, `deriveModeled`, `elabDeriveModeled`, `modeledHandler` and the
  registration's `initFn`). The new ones are `deriveModeledSum`,
  `ctorTag` and `ctorFields`.

The `OCaml5` modules sit outside the gate's audit, as the lowering cleanup's receipt records.

## 5. Open, and bounded evidence

- `app` and `contextOf` stay unlowered in the Schema. The JSON images of `null`, `undefined` and
  `bytes` are a later slice.
- `Shape` as a fold of `Ty` is a later slice (the audit's §8.2).
- Optional keys in `Modeled`, and one Lean declaration for both faces, wait for P1.
- An `unbound-type` diagnostic in `Ml.checkModule` is not written. The compile probe stands in.
- The lowered to-do host types under ocamlopt, but nothing runs it yet, and no gate holds it.
  P1's first step builds and runs it under dune.
- The 13 partial-match warnings are the lowered decidable equalities of `NativeOp`. They are
  warnings, not errors, under the estate's flags.
