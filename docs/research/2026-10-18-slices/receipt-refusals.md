# 2026-10-18 seat 1 receipt: located refusals, hole hygiene, one method table

**The one thing to know before merging:** every method tool of `eff mcp` now carries the closed
schema of `Wire.Envelope Reply` as its `outputSchema`. R5.1 and the brief ask for it, and that
schema is 88,948 bytes. So `tools/list` grows from about 41 KB to about 1.7 MB, and O1 gives the
measure and the options.

The rest merges as planned. No recipe root moves, and no path of `ocaml/gen/public-names.tsv`
moves (reading). `Test/Run/LiveContract.lean` now carries the integration branch's own text
(`f8eb23ea5`), so it merges clean.

Seat 1 of wave 1 (`docs/research/2026-10-18-slices/wave1-briefs.md`, "Seat 1"). Each slice is its
own commit after its narrow build.

## Base and head

- Branch `seat/w1-refusals`, worktree `/Users/pooks/Dev/wt-w1-refusals`.
- Base: `4a81cc034`. The branch was not rebased or merged.
- Slice 1a, located refusals: `17dcd5eae`.
- Slice 1b, hole hygiene: `2e1748b4f`.
- `0651bb236`: `Test/Run/LiveContract.lean` takes the integration branch's text.
- Slice 1c, one method table: `2897bb0db`.
- Head: the commit that adds this receipt.

## Changed files

### Slice 1a (`17dcd5eae`, 66 files)

Sources:
- `src/Effect4/Data/Located.lean` (new): `Located Site Reason`, `mapSite`, `mapSite_comp`, and
  the one prefix rule `Located.under`.
- `src/Effect4/Program/Typing/Blame.lean`: `TypeRefusal` is `Located (List Nat) TypeReason`;
  `TypeRefusal.path` reads `site`; three reasons appended (`unboundVariable`, `unknownAtom`,
  `refusedArguments`).
- `src/Effect4/Program/Typing/TermRefusal.lean`: the term diagnostic names the three causes, each
  at its address within the term.
- `src/Effect4/Program/Checker.lean`: the checker maps each cause to its reason.
- `src/Effect4/Program/Typing/Rules.lean`, `src/Effect4/Program/Native.lean`:
  `Signature.knownAtom`, the catalogue's names (`nativeKnownAtom`).
- `src/Effect4/Program/Typing/SignatureSupport.lean`: `SigExtends` keeps `knownAtom`.
- `src/Effect4/Program/CheckedTyping.lean`: `programRefusal`, `programRefusal_none_iff`,
  `programRefusal_isSome`, `programTyping`.
- `src/Effect4/Program/Admission.lean`: `AdmitRefusal.illTyped (why : TypeRefusal)`.
- `src/Effect4/Program/Typing/SourceSession.lean`: the feed places a part's refusal once
  (`Located.under`); `FeedRefusal.rootRefused`; `typeChanged` has an old type.
- `src/Effect4/Program/Typing/FillSet.lean`: `AddRefusal.notCertified (why : FeedRefusal)`.
- `src/Effect4/Program/Typing/Suggest.lean`: the second relocation is gone.
- `src/Effect4/Program/Check.lean`: placement and layer relocation through `Located`.
- `src/Effect4/Api.lean`: `explain` and `explain_none_iff` read `programRefusal`.
- `src/Effect4/Api/Author.lean`: an ill-typed admission reports its located refusal.
- `src/Effect4/Codegen/Diagnostics.lean`: the codes of the three reasons.
- `src/Effect4/Api/HostSession.lean`, `src/Effect4/Run/LiveRecord.lean`,
  `src/Effect4/Run/Preview.lean`: `Repr` dropped from refusals that now hold a located refusal.

Laws:
- `src/Effect4/Laws/Program/CheckAgreement.lean`: `mapError_layer_rebase` by `mapSite_comp`.
- `src/Effect4/Laws/Program/CheckedTyping.lean`: `programTyping_eq_ok`.
- `src/Effect4/Laws/Program/SourceTable.lean`: `finish_ok` and `finish_keepExact_ok` at the new
  `finish`.
- `src/Effect4/Laws/Program/Typing/Rebase.lean`: `TypeRefusal.rebase` is `Located.under`.
- `src/Effect4/Laws/Run.lean`: `admitProgram_certificate` by `admitProgram_eq_ok`.
- `src/Effect4/Laws/Program/Definitions.lean`, `Signature.lean`, `Sketch.lean`: the `SigExtends`
  constructions gain the `knownAtom` field.
- `src/Effect4/Laws/Api/AuthorBuild.lean`, `src/Effect4/Laws/Api/Codegen.lean`: the admission's
  refusal pattern.

Batteries:
- `Test/Program/FillSetControls.lean`: the red control `LocatedRoutes` (Codex R1.1), and the
  pending fill's refusal payloads.
- `Test/Program/BlameContract.lean`: "A term's refusal names its cause", each cause and two
  controls.
- `Test/Program/SourceFeedControls.lean`: `rootRefused` at a refused root.
- `Test/Program/FocusControls.lean`, `RecordRefusals.lean`, `TupleRefusals.lean`,
  `InvocationContract.lean`, `SourceDocumentControls.lean`, `AuthorContract.lean`,
  `Test/Api/ApiContract.lean`, `Test/Dogfood/P2HandlerLayers.lean`,
  `Test/Counterexamples/Program/AdmissionUnserved.lean`,
  `Test/Counterexamples/Machine/Semantics/LayerValue.lean`: each reads the named cause.
- `Test/Run/LiveContract.lean`: it read `WaitView.registration`, renamed to `site` before the
  base (`43e7cb7d5`).

OCaml, hand:
- `ocaml/engine/kit/kit.ml`: `format_version = 2`.
- `ocaml/engine/kit/kit.mli`, `kit_author.mli`: the refusal type is
  `(int list, type_reason) located`.
- `ocaml/engine/test/kit/test_kit.ml`, `ocaml/gen/test_checker_native.ml`: they read `site`.
- `ocaml/engine/test/kit/test_shapes.ml`: the pins at version 2.
- `ocaml/engine/test/kit/serve.transcript`: two answers name `site`.

Generated, each by its producer:
- `python3 scripts/generate.py --only derived`: `src/Effect4/Api/RefusalsDerived.lean`,
  `RunnerDerived.lean`, `src/Effect4/Tool/CheckDerived.lean`, `ToolDerived.lean`, from
  `tools/Effect4Gen/manifest.json` (the `Located` instance before `AdmitRefusal`) and the guards
  `tools/Effect4Gen/guards/refusals.lean`, `runner.lean`.
- `python3 scripts/generate.py --only lcnf`: `ocaml/gen/api_gen.ml`, `.mli`,
  `closure-api_gen.tsv`, `ocaml/engine/test/todo/todo_gen.ml`, `.mli`,
  `ocaml/gen/closure-todo_gen.tsv`.
- the fixtures: `ocaml/engine/test/kit/verdicts.txt`, `generated/corpus-index.tsv`.
- `tools/Drivers/Session.lean`: `ocaml/engine/test/kit/tool-replies.jsonl`.

### Slice 1b (`2e1748b4f`, 11 files)

- `src/Effect4/Tool/Protocol.lean`: `HoleDecl` (index, name, the exact `perform` term, performed);
  `DocView.declared`.
- `src/Effect4/Tool/Actions.lean`: `docView` lists every declared hole.
- `src/Effect4/Program/Typing/Suggest.lean`: `localCandidates` drops the place's own program and
  every table entry that encloses the place.
- `Test/Program/FillSetControls.lean`: the red control `HoleHygiene`.
- `tools/Effect4Gen/manifest.json`: `HoleDecl` in the Tool group.
- Generated: `src/Effect4/Tool/ToolDerived.lean` (derived), `ocaml/gen/api_gen.ml`, `.mli`,
  `closure-api_gen.tsv` (lcnf), `ocaml/engine/test/kit/tool-replies.jsonl` and
  `tool-numbers-replies.jsonl` (`tools/Drivers/Session.lean`).

### The battery's text (`0651bb236`, 1 file)

- `Test/Run/LiveContract.lean`: the integration branch's text (`f8eb23ea5`), which reads the
  wait's site as `some (.deferred _)`.

### Slice 1c (`2897bb0db`, 12 files)

- `src/Effect4/Tool/RequestSyntax.lean` (new, a meta module): `tool_requests`. It declares
  `Action`, `Query`, `Request`, `MethodKey` and each key's wire name, case name and kind, with
  `MethodKey.name_nodup` and `Request.methodKey`. It refuses a wire name written twice.
- `src/Effect4/Tool/Protocol.lean`: the requests by `tool_requests`, `open_` with `wire "open"`;
  `MethodKind`; `MethodKey.versions`; `Request.method` and `supportedMethods` read the keys.
- `src/Effect4/Tool/Methods.lean`: the descriptor and the table. `MethodKey.description` and
  `MethodKey.hints` are exhaustive; `caseOf`, `caseOf_isSome` and `caseFor` find each case.
  `MethodDescriptor` and `methodDescriptor` own the table; `Listing`, `listingOf`, `entriesAt` and
  `entries` render it, with `replySchema` rendered once. `fieldsSchema` and `docSchema` replace
  `argumentSchema`, and `describe` has its own listing.
- `src/Effect4/Laws/Tool/Serve.lean`: `query_hint` and `hinted_readOnly`.
- `src/Effect4/Laws/Tool/Wire.lean`: `method_name_agrees`, `supportedMethods_descriptors` and
  `listing_outputSchema`.
- `Test/Program/ToolMethodsControls.lean`: the hints, the closed reply schema, `describe`'s
  schemas, the two red controls and one green declaration.
- `ocaml/engine/kit/kit_mcp.ml`: one renderer, `tool_of`, over every listing, with `outputSchema`
  and `annotations`.
- `ocaml/engine/test/kit/test_mcp.ml`: C2 reads the output schemas and the hints.
- `scripts/check-mcp-protocol.py`: each structured result against its tool's output schema, the
  bare-`Reply` red control, and the bytes of the listing.
- Generated by `python3 scripts/generate.py --only lcnf`: `ocaml/gen/api_gen.ml`, `.mli`,
  `closure-api_gen.tsv`.

## Commands and results

Every Lean command ran from the worktree. `PATH` began with a `lake` wrapper that runs
`python3 /private/tmp/seams-lean-one.py lake "$@"`, so the generators' own builds took the lock.
`make` targets ran under the same `PATH`.

### Slice 1a

| Command | Result |
| --- | --- |
| `python3 scripts/generate.py --only derived` | `PASS generate: requested producers ran in dependency order` |
| `python3 /private/tmp/seams-lean-one.py lake build Effect4 Effect4.Laws` | `Build completed successfully (1423 jobs).` |
| `make batteries-touched BASE=4a81cc034` | `batteries-touched: 162 batteries`; `Build completed successfully (1524 jobs).` |
| `python3 scripts/generate.py --only lcnf` | `PASS generate: requested producers ran in dependency order` |
| `make check-ocaml` | `PASS native: shared result e75b0205ad44`; `PASS compiler: shared result 8633cea4e468`; `PASS ocaml: recorded 25d41ddec92a (17.351s)` |
| `python3 /private/tmp/seams-lean-one.py lake env lean --run tools/Drivers/Session.lean < ocaml/engine/test/kit/tool-requests.jsonl` | the replies; they differ from the fixture only where a refusal's `path` is now `site` |
| the same with `tool-numbers.jsonl` | equal to `tool-numbers-replies.jsonl` |
| `python3 /private/tmp/seams-lean-one.py lake env lean <scratch>/Audit1a.lean` | see the axiom output |

### Slice 1b

| Command | Result |
| --- | --- |
| `python3 scripts/generate.py --only derived` | `PASS generate: requested producers ran in dependency order` |
| `python3 /private/tmp/seams-lean-one.py lake build Effect4 Effect4.Laws` | `Build completed successfully (1423 jobs).` |
| `make batteries-touched BASE=4a81cc034` | `batteries-touched: 162 batteries`; `Build completed successfully (1524 jobs).` |
| `python3 scripts/generate.py --only lcnf` | `PASS generate: requested producers ran in dependency order` |
| `python3 /private/tmp/seams-lean-one.py lake build Tools.WireText Effect4.Tool.Wire` | `Build completed successfully (228 jobs).` |
| the session driver on `tool-requests.jsonl` and `tool-numbers.jsonl` | 10 and 6 replies; each equals the fixture once `declared` is dropped (a JSON comparison); installed |
| `make check-ocaml` | `PASS native: shared result e75b0205ad44`; `PASS compiler: shared result 8633cea4e468`; `PASS ocaml: recorded 5c10c0e1210c (18.684s)`; 217 `PASS` lines and no `FAIL` |
| `python3 /private/tmp/seams-lean-one.py lake env lean <scratch>/Audit1b.lean` | see the axiom output |

### Slice 1c

The last run of each, after the last source edit of the slice:

| Command | Result |
| --- | --- |
| `python3 scripts/generate.py --only derived` | `PASS generate: requested producers ran in dependency order`; the derived codecs unchanged |
| `python3 /private/tmp/seams-lean-one.py lake build Effect4 Effect4.Laws` | `Build completed successfully (1424 jobs).` |
| `make batteries-touched BASE=4a81cc034` | `batteries-touched: 165 batteries`; `Build completed successfully (1532 jobs).` |
| `python3 /private/tmp/seams-lean-one.py lake build Test.Program.ToolMethodsControls`, after the guard that pins `supportedMethods` | `Build completed successfully (737 jobs).` |
| `python3 scripts/generate.py --only lcnf` | `PASS generate: requested producers ran in dependency order`; no change to the committed files |
| `python3 /private/tmp/seams-lean-one.py lake build Tools.WireText Effect4.Tool.Wire` | `Build completed successfully (229 jobs).` |
| the session driver on `tool-requests.jsonl` and `tool-numbers.jsonl` | byte for byte the fixtures (`cmp`) |
| `make check-ocaml`, at the generated files of this commit | `PASS native: shared result e75b0205ad44`; `PASS compiler: shared result 8633cea4e468`; `PASS ocaml: recorded 323e7bd986ad (28.058s)`; 219 `PASS` lines and no `FAIL`. A rerun after the last Lean edit answered `PASS ocaml: shared result 323e7bd986ad` |
| `opam exec --switch=effect4 -- dune build engine/kit/bin/eff.exe`, from `ocaml/` | built |
| `uv run --with jsonschema==4.25.1 python scripts/check-mcp-protocol.py --binary ocaml/_build/default/engine/kit/bin/eff.exe --schema /Users/pooks/Dev/refs/ocaml-tooling/mcp-spec/schema/2025-06-18/schema.json` | `"status": "PASS"`, `"schema_checks": 101`, `"tools": 20`, `"annotated_tools": 20`, `"output_schema_tools": 20`, `"tools_list_bytes": 1734544`, `"input_schema_bytes": 40069`, `"output_schema_bytes": 1847143` |
| `eff.exe mcp` on empty input, timed eight times with `/usr/bin/time -p` | 0.04 s each; the integration branch's build at `/Users/pooks/Dev/lean4-effect4` 0.01 s |
| `python3 /private/tmp/seams-lean-one.py lake env lean <scratch>/Audit1c.lean` | see the axiom output |

## Axiom output

Each audit file imports the slice's touched `src` and `Test` modules and runs `#axiom_audit` over
them (`tools/ProofGraph/AxiomAudit.lean`).

- Slice 1a, 47 modules: `#axiom_audit: 9418 declarations within [propext, Quot.sound], 0 of them
  modulo planned goals; 1 planned goals`. The one planned goal is `explain_replays`
  (`src/Effect4/Laws/Program/CheckAgreement.lean`), declared at the base.
- Slice 1b, 5 modules (`Effect4.Program.Typing.Suggest`, `Effect4.Tool.Actions`,
  `Effect4.Tool.Protocol`, `Effect4.Tool.ToolDerived`, `Test.Program.FillSetControls`):
  `#axiom_audit: 3007 declarations within [propext, Quot.sound], 0 of them modulo planned goals;
  0 planned goals`.
- Slice 1c, 6 modules (listed below): `#axiom_audit: 1341 declarations within [propext,
  Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- `Effect4.Tool.RequestSyntax` alone, the macro: `#axiom_audit: 45 declarations within [propext,
  Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- `0651bb236`, `Test.Run.LiveContract`: `#axiom_audit: 22 declarations within [propext,
  Quot.sound], 0 of them modulo planned goals; 0 planned goals`.

The slice 1c audit's modules:

```text
Effect4.Tool.RequestSyntax Effect4.Tool.Protocol Effect4.Tool.Methods Effect4.Laws.Tool.Serve
Effect4.Laws.Tool.Wire Test.Program.ToolMethodsControls
```

The slice 1a audit's modules:

```text
Effect4.Api Effect4.Api.Author Effect4.Api.HostSession Effect4.Api.RefusalsDerived
Effect4.Api.RunnerDerived Effect4.Codegen.Diagnostics Effect4.Data.Located
Effect4.Laws.Api.AuthorBuild Effect4.Laws.Api.Codegen Effect4.Laws.Program.CheckAgreement
Effect4.Laws.Program.CheckedTyping Effect4.Laws.Program.Definitions
Effect4.Laws.Program.Signature Effect4.Laws.Program.Sketch Effect4.Laws.Program.SourceTable
Effect4.Laws.Program.Typing.Rebase Effect4.Laws.Run Effect4.Program.Admission
Effect4.Program.Check Effect4.Program.CheckedTyping Effect4.Program.Checker
Effect4.Program.Native Effect4.Program.Typing.Blame Effect4.Program.Typing.FillSet
Effect4.Program.Typing.Rules Effect4.Program.Typing.SignatureSupport
Effect4.Program.Typing.SourceSession Effect4.Program.Typing.Suggest
Effect4.Program.Typing.TermRefusal Effect4.Run.LiveRecord Effect4.Run.Preview
Effect4.Tool.CheckDerived Effect4.Tool.ToolDerived Test.Api.ApiContract
Test.Counterexamples.Machine.Semantics.LayerValue Test.Counterexamples.Program.AdmissionUnserved
Test.Dogfood.P2HandlerLayers Test.Program.AuthorContract Test.Program.BlameContract
Test.Program.FillSetControls Test.Program.FocusControls Test.Program.InvocationContract
Test.Program.RecordRefusals Test.Program.SourceDocumentControls Test.Program.SourceFeedControls
Test.Program.TupleRefusals Test.Run.LiveContract
```

## What moved on the wire

The owner ruled the wire greenfield until release (slices README §9). Each move below is
regenerated in this branch.

Slice 1a, the program's refusal:
- A refusal's JSON names its address `site`, not `path` (`Located`, every `TypeRefusal`).
- `TypeReason` appends `unboundVariable` (the address in the term, the index, the environment's
  depth), `unknownAtom` (address, atom) and `refusedArguments` (address, atom, argument types).
  The checker answers these where it answered `term`.
- `AdmitRefusal.illTyped` carries the located refusal, and `AddRefusal.notCertified` the feed's
  refusal. Both were bare tags.
- `FeedRefusal.typeChanged` carries the old type, not an option, and `FeedRefusal.rootRefused`
  is appended.
- A suggestion's `refused` evidence names the program's own address: the second prefix is gone.
- The kit's format version is 2. `test_shapes.ml` pins admit's shape at
  `fece61a8e4b0cec24350afeea5a9b63d4e28b14a2ed3e7487738141b81f8ee7f` and the refusal's at
  `27dc1facbfc1308441beb99940201e98d7ac0f26558d53d8fb91739b2efadfac`.

Slice 1b, the document's view:
- Every document view carries `declared`: one `HoleDecl` for each hole of the sketch.
- `suggest` offers neither the place's own program nor a program that encloses the place.

Slice 1c, the MCP face only:
- Every tool of `tools/list` carries `outputSchema` and `annotations`, with the four hints.
- The descriptions of `open`, `edit`, `fill`, `start`, `doc` and `suggest` name the moves above.
- The session protocol does not move: the method names, their versions, the request and reply
  codecs and the `discover` answer are the base's. Both session fixtures replay byte for byte,
  and a battery guard pins `supportedMethods` to the hand list it replaces.

## Public names, recipe roots and the open method

- No recipe root moves: no slice edits `ocaml/gen/roots.json`, and no root names a declaration
  the branch renames or removes (reading).
- No path of the integration branch's `ocaml/gen/public-names.tsv` moves (reading). The public
  values `Effect4.Tool.Native.methods`, `Effect4.Tool.Native.describe`, `Effect4.Run.Kit.*` and
  `Effect4.Program.admit` keep their names. Their types change, and the manifest pins no type of
  them.
- `ocaml/engine/test/stm/stm_tool.ml` keeps `open_`: its A0 line writes method `open` and case
  tag `open_`, and both stay. The case is still `Action.open_`, and `wire "open"` at the case is
  the one place that spells the method `open`.

The Lean declarations the branch renames or removes:

| Declaration | Now |
| --- | --- |
| `Effect4.Program.TypeRefusal`, a structure | an `abbrev` for `Located (List Nat) TypeReason`; `⟨site, reason⟩` and `.reason` still elaborate |
| `TypeRefusal.path`, a field | a function that reads `site` |
| `TypeRefusal.mk` | `Located.mk` |
| `AdmitRefusal.illTyped`, `AddRefusal.notCertified` | each takes its reason |
| `FeedRefusal.typeChanged` | its first argument is an `EffTy` |
| `Effect4.Store.RefusalsGen.TypeRefusalC.*` (generated) | `LocatedC.*` |
| `Effect4.Tool.Methods.descriptions` | `MethodKey.description`, exhaustive over the keys |
| `Effect4.Tool.Methods.argumentSchema` | `fieldsSchema defs tools true` |
| `Methods.Entry.name`, `.description`, `.schema` | `Entry.listing` (`Listing.inputSchema` for `schema`) |
| `Methods.Describe.name`, `.description`, `.schema` | `Describe.listing` |
| `Request.method`, `supportedMethods` | the same names, read off the keys |
| `Action`, `Query`, `Request` | the same names and cases, declared by `tool_requests` |

In OCaml, `Api_gen.type_refusal` is now `(int list, type_reason) located`, and the records
`effect4_tool_methods_entry` and `describe` hold a `listing`. `kit_mcp.ml` is their one reader.

## Evidence

- **proved**: `Located.mapSite_comp`, `programRefusal_none_iff`, `programRefusal_isSome`,
  `programTyping_eq_ok`, `Methods.caseOf_isSome`, `MethodKey.name_nodup`, `query_hint`,
  `hinted_readOnly`, `method_name_agrees`, `supportedMethods_descriptors` and
  `listing_outputSchema`. The kernel accepted each, and the audits hold each within
  `[propext, Quot.sound]`.
- **proved**, re-proved at the new definitions: `mapError_layer_rebase`, `finish_ok`,
  `finish_keepExact_ok`, `admitProgram_eq_ok`, `admitProgram_certificate`, `Api.explain_none_iff`
  and the `SigExtends` constructions.
- **tested**: the red controls. `LocatedRoutes` (`Test/Program/FillSetControls.lean`) reads one
  unbound-variable refusal at `[1]` on the edit, pending-fill and suggestion routes. It shows the
  second prefix reads `[1, 1]`, and signature admission refuses first.
- **tested**: `HoleHygiene` (same file). With one application row, `bind (external 0)
  (external 0)` leaves hole 0 declared as `perform (external 1) unit` and not performed.
- **tested**: `Test/Program/ToolMethodsControls.lean`. A description that misses `slots` fails
  with `Missing cases`, and a wire name written twice refuses the whole `tool_requests`.
- **tested**, host-only: `make check-ocaml`, the kit's tool and MCP suites against Lean's driver.
  `scripts/check-mcp-protocol.py` checks every tool's output schema against the upstream
  2025-06-18 schemas. The enveloped results validate against it. The bare `Reply` schema refuses
  each envelope and accepts its payload, the red control.
- **reproduced**: a fresh `generate.py --only derived` run leaves the committed derived codecs
  unchanged at each slice's head.
- **reading**: no recipe root and no public path moves. A literal always types in a term
  (`argTy`'s literal arm), so the term diagnostic has no literal cause (O4).
- The schema checks are finite and host-only. No theorem relates an emitted schema to the
  codec's acceptance.

## Landed theorems and their placement

`Located.mapSite_comp` (`src/Effect4/Data/Located.lean`):
- Concept: `initial-algebras-folds`; property: a path is an inherited attribute that only locates
  a refusal.
- Question: registry claim `checker-base-natural` (role compatibility); consumer:
  `mapError_layer_rebase` (`src/Effect4/Laws/Program/CheckAgreement.lean`).
- Reach: every pair of site maps and every located refusal; the proof is `rfl`.
- Does not establish: that a reason is right, or any judgment.
- Unlocks: R14, one relocation rule on the edit, pending-fill and suggestion routes.

`programRefusal_none_iff` (`src/Effect4/Program/CheckedTyping.lean`):
- Concept: `residual-program-typing`; property: the located refusal is absent exactly when the
  whole-program typing answers.
- Question: DI-86's law, which no registry claim holds (P2 proposes one); consumers:
  `Api.explain_none_iff` (`src/Effect4/Api.lean`), now one line, and `programRefusal_isSome`.
- Reach: every signature and program; the observation is `typeOfProgram`'s answer.
- Does not establish: that the refusal names the most useful cause. It says nothing of the
  signature and formation gates that program admission runs first.
- Unlocks: R14 (a sketch explains its types) and DI-86's located admission.

`programRefusal_isSome` (same file):
- Concept: `residual-program-typing`; property: as above.
- Question: a step of `programRefusal_none_iff`'s claim; consumer: `programTyping`, whose
  refusal admission reports.
- Reach: every program the checker refuses.
- Does not establish: which refusal.
- Unlocks: `AdmitRefusal.illTyped why`, with no fallback reason.

`programTyping_eq_ok` (`src/Effect4/Laws/Program/CheckedTyping.lean`):
- Concept: `residual-program-typing`; property: admission's equation at a certificate.
- Question: a step of `admitProgram_eq_ok`; consumers: `admitProgram_eq_ok` and
  `admitProgram_certificate` (`src/Effect4/Laws/Run.lean`).
- Reach: every program with a typing certificate.
- Does not establish: anything where the checker refuses.
- Unlocks: R1's program admission equation, kept at the located route.

`MethodKey.name_nodup` (declared by `tool_requests`, `src/Effect4/Tool/RequestSyntax.lean`):
- Concept: `exact-codecs`; property: one wire name names one method.
- Question: a step of the proposed claim `tool-method-descriptor` (P1). Its consumers are the
  wire's lookups (`Wire.check`, `Connection.valid`) and the MCP call's lookup by name
  (`kit_mcp.ml`).
- Reach: the declared keys; the kernel decides it.
- Does not establish: anything of decoding.
- Unlocks: R8, the protocol's faces name one method each.

`Methods.caseOf_isSome` (`src/Effect4/Tool/Methods.lean`):
- Concept: `exact-codecs`; property: each method's arguments are its case's fields in the
  derived shape document.
- Question: a step of the proposed claim `tool-method-descriptor`; consumer: `Methods.caseFor`,
  so `methodDescriptor` has no fallback shape.
- Reach: every key, at the real derived document; the kernel decides each.
- Does not establish: that the schema rendered from the shape is exact; the schema checks are
  finite.
- Unlocks: R8.

`query_hint` and `hinted_readOnly` (`src/Effect4/Laws/Tool/Serve.lean`):
- Concept: `host-session-protocol`; property: a query leaves the tool's state unchanged.
- Question: registry claim `tool-serve-query` (role preservation), from `serve_query`;
  `query_hint` is its classification step; consumer: the MCP `readOnlyHint` of every tool.
- Reach: every oracle, state and request; the observation is `serve`'s next state.
- Does not establish: anything of a host's external effects or the transport, and nothing of
  the three hints set by hand.
- Unlocks: R6, the hint a client reads is a law of the tool.

`method_name_agrees`, `supportedMethods_descriptors` and `listing_outputSchema`
(`src/Effect4/Laws/Tool/Wire.lean`):
- Concept: `exact-codecs`; property: the request codec's faces name the methods the descriptors
  name.
- Question: the proposed claim `tool-method-descriptor` (P1, role compatibility); consumers:
  `Wire.check`, `Connection.valid`, `discover` and `Methods.entries`.
- Reach: every request, every key and every listing; each proof is `rfl`.
- Does not establish: decoding, the transport, or that an emitted schema accepts what the exact
  reader accepts.
- Unlocks: R8; the one renderer of the MCP table.

The re-proved theorems keep their placements: `mapError_layer_rebase` (`checker-combine-deps`),
`finish_ok` and `finish_keepExact_ok` (`src/Effect4/Laws/Program/SourceTable.lean`),
`admitProgram_eq_ok`, `admitProgram_certificate`, `Api.explain_none_iff` and `method_supported`.

## Open obligations

- **O1, the size of `tools/list`.** `scripts/check-mcp-protocol.py` measures 1,734,544 bytes for
  the `tools/list` reply. The output schemas are 1,847,143 bytes and the input schemas 40,069
  (`json.dumps`). The closed reply schema is 88,948 bytes, and its 63 definitions hold the
  grammar, the views, the runs and the refusals. The MCP specification says an output schema
  helps clients and models read a result, so a client may show it to a model. The generated
  module renders the schema once when it starts. `eff mcp` on empty input then takes 0.04 s, and
  the integration branch's build takes 0.01 s (eight runs each, `/usr/bin/time -p`). Rendered for
  each method, it took 0.16 s. The options:
  - (a) keep the closed envelope schema on every method, as landed, exact and standalone;
  - (b) narrow each method's result to the answers that pair with it (`Wire.responds`). It stays
    closed. It needs a per-method table with a law against `Wire.responds`, and `Refusal` alone
    reaches most of the grammar;
  - (c) leave the result's object definitions to `describe`, as the input schemas do; small, and
    not closed, which R5.1 refuses;
  - (d) drop `outputSchema`, which MCP makes optional; the client then checks nothing.

  Recommendation: keep (a), and measure what one client sends to its model. If a client sends the
  output schemas, take (d) for the methods and keep `describe`'s.
- **O2, the claims.** `tool-method-descriptor` and the located-refusal claim are proposals (P1,
  P2). `tools/ProofGraph/Registry.lean` and `docs/core/semantics.md` are not this seat's files.
- **O3, the hints by hand.** No law states `destructive`, `idempotent` or `openWorld`. `edit` is
  marked non-destructive because the history keeps it and a revert undoes it; the owner may rule
  otherwise.
- **O4, the fourth cause.** The brief names a literal outside the alphabet. A literal always types
  in a term (`argTy`'s literal arm), and a layer value's literal already refuses with
  `TypeReason.literalOutsideAlphabet` (reading). `TypeReason.term` stays for a field read or
  update at a member that is no record.
- **O5, a code for `unknownAtom`.** `codesOf` answers no TypeScript code for it: no corpus program
  names an atom outside the catalogue.
- **O6, the repeated wire name.** The macro compares literal text, so two spellings of one string
  pass it. `MethodKey.name_nodup` then fails the build.
- **O7, the bounded evidence.** The schema checks are a finite stdio trace against the upstream
  schemas. No theorem relates an emitted schema to the exact reader.

## Proposed decisions rows (proposals only)

- **P1.** Register the claim `tool-method-descriptor` (concept `exact-codecs`, role compatibility,
  R8). Its pointers are `method_name_agrees`, `supportedMethods_descriptors` and
  `listing_outputSchema`; its steps are `MethodKey.name_nodup` and `Methods.caseOf_isSome`.
- **P2.** Register the claim that the program's located refusal is complete against its typing
  (concept `residual-program-typing`, role decidability, R14), pointer `programRefusal_none_iff`.
- **P3.** Rule O1: the closed output schema on every method, or one of (b) to (d).
