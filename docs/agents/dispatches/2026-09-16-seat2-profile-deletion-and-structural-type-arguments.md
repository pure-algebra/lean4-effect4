# Seat 2 brief: delete the profile module; structural type arguments on the TypeScript side

Status: amended 2026-09-16 after an audit of the first draft against the tree at `0c3f605b` (seat 1 landed). Dispatched to one seat in the main checkout `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, base commit `0c3f605b`. The seat holds the Lake lane for the whole run; the coordinator runs no Lean while it works.

## Ground rules

- Edit with the Write/Edit tools; never rewrite tracked files with heredocs or sed scripts.
- One Lean compiler process at a time: `lake build <targets>` in the foreground, wait, never overlap. The editor's `lake serve` and its `lean --worker` processes are not builds; leave them alone.
- Never redirect stderr to `/dev/null` on Lean or lake commands (a hook blocks it).
- New Lean definitions stay at `[propext, Quot.sound]`; the traps are in `/Users/pooks/.claude/projects/-Users-pooks-Dev-lean4-effect4/memory/lean-proof-traps-2026-09-06.md` and `docs/research/2026-09-05-tactics-cheatsheet.md`.
- No gate ceremony: build what you touch; run the named lane checks once per step; `make check` once at the end. Report unrelated failures rather than fixing them.
- Commit messages: title states what became true; body says why; end with `Co-Authored-By: Claude Fable 5.1 <noreply@anthropic.com>`. No push.
- Do not change persisted `Row.typeArgs` strings or `Ty.handle` text (wire change scheduled for S1, review log B18). Do not add a handwritten type parser on the TypeScript side: structure comes from host parser type nodes or from Lean.
- Plain words in every commit body and in the receipt. No em-dashes.

## Read first

1. `docs/research/2026-09-16-implementation-review-log.md`: register items B12, B18, B19, B20, B21 and entries 18 and 21.
2. `git:0c3f605b:src/Effect4/Codegen/Profile.lean` (whole file, 210 lines, deleted by `670f76ab`) and `Test/Audit/AxiomGate.lean` lines 137 to 160 (the seven exact-name exemptions for this module).
3. `src/Effect4/Codegen/Types.lean` (`ofTy`, `parseLegacy`, and the private `unionOf`/`finishUnion` at lines 160 to 180, which is where the canonical union form lives), `src/Effect4/Codegen/Read.lean` lines 264 to 300 and 344 to 370 (`readRowCall` compares `rowTypeArgs (sig.rowOf op) = some typeArgs`, `readKey` compares `ofTy ty = some arg`: exact structural equality, no canonicalization of the source side).
4. `tools/Tools/TsGen.lean` lines 500 to 630 (`tyJs`, the service tables with `ty` and `rendered`, the `Profile` schema, `serviceTypeFor`) and line 807 to 810 (`hostPin.libraries` in the header), plus the header of `ts/eff/profile.gen.ts`.
5. `ts/eff/read.ts` lines 140 to 150 (`Expr.generic`), 205 to 240 (`typeName`, an ESTree walker), 740 to 760 (`readRowCall`), 815 to 835 (`readKey`); `ts/eff/ingest/ck.ts` lines 314 to 315, 544 to 545, 647 (compiler API, `getText`); `ts/eff/ingest/oxc.ts` lines 188 to 205, 299 to 313 (ESTree, source slices); `ts/eff/ingest/package-rows.ts`.
6. `tools/target/profile.ts` lines 60 to 110 (`renderTy`, a second renderer of `Ty`) and its test.
7. Codex's probe: `/private/tmp/effect4-typeargs-host-boundary.ts` and `.log` (eight assertions: spaced and parenthesized legacy arguments refuse as `arity`; unions, tuples and literal types refuse as `node … typeArgument`; a wrong argument refuses).

## Scope (files you own)

`git:0c3f605b:src/Effect4/Codegen/Profile.lean` (deleted), `src/Effect4.lean` (one import line), `Test/Audit/AxiomGate.lean`, `Test/Codegen/ExprContract.lean`, `tools/Tools/TsGen.lean`, `ts/eff/read.ts`, `ts/eff/ingest/ck.ts`, `ts/eff/ingest/oxc.ts`, `ts/eff/ingest/package-rows.ts`, `ts/eff/ingest/test/**` (new tests), `ts/eff/*.gen.ts` (regenerated only), `tools/target/profile.ts` and its test, `Test/Counterexamples/REGISTER.md` (if a domain changes).

Do not touch `src/Effect4/Codegen/{Types,Print,Read,Checked,Admit,Names,SourceBindings}.lean`, `src/Effect4/Api.lean`, `src/Effect4/Laws/**`, `src/Effect4/Program/**`, `tools/Effect4Gen/**`, `Test/Api/**`, `Test/Codegen/{Read,Print,SourceBindings}Contract.lean`.

## Deliverables, in order

### Step 1: delete the profile module (B20, B21 residue)

The audit found that the only definition in `Codegen/Profile.lean` with a consumer is `hostPin`, read once at `tools/Tools/TsGen.lean:809`. Everything else (`reservedExtra`, `bindingName`, `mentions`, `namespacesOf`, `importedNames`, `neededNamespaces`, `OpRow`, `errorAbort`, `ServiceRow` and its namespace) is the archived EffectV4 DSL's remnant with no producer in `src` or `tools`; `Test/Codegen/ExprContract.lean` is its only builder, and the archive register's `E4-SURFACE-CE-109` already ruled that its string spellings are not a typing source. `Codegen/Names.lean` (`ecd44103`) owns the legal binding-name rule now.

So the cut is the whole module, not a trimmed one:

- Move `hostPin` to `tools/Tools/TsGen.lean` as a private definition beside its use (the `HostPin` structure is `TypeScript.HostPin` from the carrier package, which `TsGen` already reaches through `Effect4.Codegen.Read`). Keep its docstring sentence: the exact host every generated module is checked against.
- Delete `git:0c3f605b:src/Effect4/Codegen/Profile.lean`. Remove `import Effect4.Codegen.Profile` from `src/Effect4.lean:67`, `tools/Tools/TsGen.lean:8` and `Test/Codegen/ExprContract.lean:2`.
- Remove the seven exemptions in `Test/Audit/AxiomGate.lean:148-157` (`ServiceRow.namespaces`, `ServiceRow.receiver`, `ServiceRow.sheet`, `ServiceRow.usesResult`, `mentions`, `namespacesOf`, `neededNamespaces`) and the comment above them. The gate refuses an exemption that names no declaration, so this goes in the same commit.
- Delete the route block in `Test/Codegen/ExprContract.lean` lines 98 to 131 (`getRow`, `cellRows`, the `methodType`/`shapeType`/`classDecl` guards and the `importedNames` guard). Keep the `ofTy` and `parseLegacy` guards above it.
- Delete `docs/research/foundational-language-implementation/structural-profile-host.lean` (local, untracked; it renders `classDecl`). The literal-declaration escaping it also exercised is pinned by `ExprContract.lean`'s renderer guard.
- `docs/ARCHITECTURE.md` and `docs/DESIGN-MAP.md` do not mention the module (checked); nothing to edit there.

Build: `lake build Effect4 Tools.TsGen Test.Codegen.ExprContract Test.Audit.AxiomGate`, then `lake env lean Test/All.lean` (the root gate must still see every library source reachable). Commit: "refactor: delete the profile module; the host pin moves to its one reader".

### Step 2: structural type arguments in every TypeScript reader

Today the Lean reader compares `TypeRef` structure while the three TypeScript readers compare rendered text, so spaced or parenthesized legacy arguments refuse and unions, tuples and literal types are unrecognized (the probe's eight rows). Make structure the wire between Lean's profile and the readers.

**The rule, fixed by the audit: exact structural equality, no canonicalization of the source side.** Lean's reader compares the carrier's `TypeRef` exactly against the row's canonical form (`Read.lean:271`, `:364`); the canonical form (unions flattened, duplicates erased, a single member standing alone) is produced once in Lean when a legacy string or a `Ty` is projected (`Types.lean:160-180`). If the TypeScript side deduplicated or flattened source nodes, it would accept `number | number` or `A | (B | C)` where Lean refuses, and the 416-program agreement between `read.ts` and `Read.lean` would no longer be agreement by construction. So the conversion from a host type node to `TypeRef` is faithful and nothing more: unwrap a parenthesized type, keywords become `name [kw] []`, references keep their qualified segments and arguments, unions keep their members in source order, tuples keep `readonly`, string literal types become `literal`. Whitespace and parentheses disappear because the parser never saw them as structure; that is what makes the probe's spaced and parenthesized rows pass.

a. Generator (`tools/Tools/TsGen.lean`). Each row in `profile.gen.ts` gains `typeArgsRef` (the structural form of `typeArgs`, computed with `Effect4.Program.rowTypeArgs`; refuse generation with a clear error if any row's legacy text does not parse, since the Lean printer would refuse that row too). Each entry of `serviceTypes.reserved` and `serviceTypes.ordinary` gains `ref` (from `Effect4.Codegen.Types.ofTy`), beside the existing `ty` and `rendered`. The `TypeRef` JSON encoding: neither `tools/Effect4Gen/manifest.json` nor the carrier package has one (checked), so write one `typeRefJs : TypeRef → String` in `TsGen.lean` next to `tyJs`, using the same positional-list convention as the other schemas, and emit the matching `TypeRef` Effect Schema into `profile.gen.ts` from the same generator. The TypeScript type and schema are generated output, not a second hand encoding. Say in a comment that Effect4Gen cannot describe a carrier from another package.

b. Two node builders, not three. `read.ts` and `oxc.ts` both walk ESTree type nodes (`TSNumberKeyword`, `TSTypeReference`, `typeArguments.params`), so one exported `typeRefOfEstree(node): TypeRef | undefined` in `read.ts` serves both; `ck.ts` walks the TypeScript compiler API, so it gets its own `typeRefOfTs(node, file)`. DI-37 keeps the two host parsers independent; it does not ask `read.ts` and `oxc.ts` to duplicate a walker. One exported `typeRefEquals(a, b): boolean` in `read.ts` is the only comparison, structural and order-sensitive, used by all three readers.

c. `read.ts`: replace `typeName` with `typeRefOfEstree`; `Expr.generic.typeArgs` becomes `ReadonlyArray<TypeRef>`; `readRowCall` compares `row.typeArgsRef` with the call's arguments through `typeRefEquals`; `readKey` compares `serviceTypeFor(key).ref`. `ck.ts` (lines 314 to 315, 544 to 545, 647) and `oxc.ts` (196 to 197, 299 to 313): stop comparing `getText` and source slices; build with the engine's builder and compare with `typeRefEquals` against `typeArgsRef`. `package-rows.ts`: rows interned from foreign source produce `typeArgsRef` through the engine's builder and keep the `typeArgs` text for the wire. Remove the `rendered`-string comparisons once nothing reads them; leave `rendered` in the profile until then and say in the receipt who still reads it.

d. Tests, under `ts/eff/ingest/test/`: turn the probe's eight assertions into permanent tests (spaced and parenthesized legacy arguments now accepted for the same structure; union, readonly tuple and literal arguments recognized; a wrong argument still refused), the same cases for `ck` and `oxc`, and two negative controls that pin agreement with Lean's reader: a source `number | number` against a row `number` refuses, and `A | (B | C)` against `A | B | C` refuses. If the foreign corpus (`make check-ingest`) shows real programs writing a type argument in a non-canonical spelling, report the program and the spelling; do not widen the rule.

e. Verification, in this order: `make gen` (regenerates the derived schemas and `profile.gen.ts`; `make check-gen` must then pass), `make check-ts-reader` (390 tests plus yours; this includes the `check.ts` oracle run over the corpus and the truth modules, which is the 416-program agreement), `make check-ingest-smoke` then `make check-ingest` if it finishes in reasonable time (the foreign corpus agreement, 22,986 units), `make check-target` (47 comparisons). Report every number.

Commit: "feat: compare type arguments structurally in every TypeScript reader".

`tools/target/profile.ts` `renderTy` is a second renderer of `Ty`, and `rendered` in the profile is a third string producer beside the carrier's renderer (design D2 retires both eventually). If the oracle can take its expected `A` and `E` spellings from the profile instead, delete `renderTy`; if not, leave it and say in the receipt exactly what still needs it.

### Step 3: receipt

Run `make check` once, then report:
1. Commits (hash, title).
2. Deleted declarations and exemptions, by name; net line count for each commit.
3. The new profile fields and the `TypeRef` JSON convention chosen.
4. Lane results: `check-gen`, `check-ts-reader`, `check-ingest-smoke`, `check-ingest` (or why not run), `check-target`, `make check` (exit code, the audit line with module and declaration counts).
5. Anything left: the wire change for `Row.typeArgs` and `Ty.handle` (S1), `renderTy` and `rendered` if kept, any engine case you could not map to `TypeRef`, any foreign program refused by the exact rule.

Write the receipt to `docs/research/2026-09-16-seat2-receipt.md` (the directory is git-ignored; that is expected) and end your report with its path and the two commit hashes.
