# G additional-layer census — read-only review

At HEAD `fa5add2092f05fa476dccdee4722fcd1f1d12d91`, with F's source changes present, the bounded static review found no further named **whole program changing from accepted to refused** beyond the known exceptions and `TemplatesContract.layerSamples[1]?`. There is one separate native-projection boundary worth recording below. This is source inspection and retained-byte inspection, not a Lean check or a whole-repository equivalence claim. No source was edited and no Lean/build/generator was run.

## Actual source boundary: projected failure-only docs layer

`src/Effect4/Program/Provision.lean:636` runs `(docsLayer (.effect dbKey (.fail (.lit (.nat 7))))).map (provideThenService · dbKey)`, with the `orDie` variant at :638. `docsLayer` keeps keys unchanged (:575–586), and `dbKey` is name10/code10 (:441). The **actual use supplies no typing signature**: `provideThenService` (:424–425) passes `.provideLayer l true (.service key)` to `runNative`, which directly compiles and runs it (:395–398). There is no native typed-admission assertion at either source occurrence.

For a separate checker comparison, the original DocsOp leaf under `docsSig` has `dbKey : handle "Db"` (:464–472) and a `never` answer, so the proposed subtype check still accepts it. Its native projection, considered on its own, was accepted by the old `checkLayer` despite `nativeServiceTy dbKey = none` (Native.lean:277–293); the revised effect leaf would return `serviceUnknown dbKey` at `[]`, or at `[0]` inside `orDie`. The complete native program already fails because its body reads this unknown service. Thus do not invent a previous native admission or call this a newly refused whole runtime fixture. If the stop is interpreted to count every independently rechecked projected layer subvalue as a fixture, name this boundary explicitly in the amendment; no runtime fixture rewrite is required by the observed code path.

Uncompiled, source-tied probe: `/private/tmp/GProjectedLayerBoundaryProbe.lean`. It includes exact projection and actual runtime-call equalities; exact original standalone layer results under docs/native signatures; revised-leaf results; and prior refusal of both complete native programs. The plain/orDie native comparisons are explicitly additional checks, not assertions already made by the source. Thirteen authored theorem axiom prints are included.

## Corpus diagnostic change, already within G's measurement allowance

The retained `.lake/corpus/index.tsv` exactly matches the data rows of committed `generated/corpus-index.tsv`. The seven retained random programs containing effect-backed layers are `g9`, `g98`, `g141`, `g155`, `g204`, `g227`, `g310`; all seven already have `wellTyped=false`. The index has 135 accepted rows including its eight wire fixtures. No accepted retained random program has an effect-backed layer. Literal layers are generated only with code4 keys and numeric literals (Gen.lean:179–203,329–332).

`g141` concretely contains `provideLayer (orDie (effect key(7,4) (yieldNow 0))) false (...)`. Its index currently reports a later term refusal at `[1,0]` (index:144). G should instead refuse the earlier layer leaf at `[0,0]` with `valueNotSubtype key(7,4) unit nat`. This changes diagnostic columns, not the acceptance bit. `g9` also contains a string-returning effect at a numeric key, but an earlier `notFiber` refusal already blocks its enclosing program; do not assert a moved diagnostic without rerunning the actual checker.

Uncompiled source-equality probe: `/private/tmp/GAdditionalLayerCensusProbe.lean`, tied to `Test.Program.Gen.program 141 4` rather than only retained JSON. It includes five axiom prints. The actual rerun of `make corpus` remains the authority for the final changed-row list, as addendum2 G.5 already specifies.

## Checked source call sites

- `Test/Codegen/TemplatesContract.lean:25–60`: the known unit→nat effect leaf; all other layer samples are matching nat literals, discards, wrappers of discards, or the already-refused bare reference.
- `Test/Codegen/ReadContract.lean:741–766,785–805`: numeric and Boolean literal keys agree; effect bodies answer nat; reference targets match.
- `Test/Codegen/SourceBindingsContract.lean:160`, `Test/Api/ApiContract.lean:157–162`: numeric literal leaves agree.
- `Test/Program/TypedCorpus.lean:35–36,66–76`: both keys are nat; all effect results are nat or never; literal values agree.
- `Test/Program/CompileContract.lean:752–781`, `LoadedAdmission.lean:153–156`: nat effect/literal leaves agree.
- `Test/Program/LayerSharingContract.lean:16–32`, `AuthoringContract.lean:194–199`: counted layer returns nat5 for a nat service.
- `Test/Program/AuthorContract.lean:58,161–175,262–292`: Counter string is the third known exception; other Counter/Db/Rate/configuration values are nat. Greeting's string is checked under the explicitly supplied string carrier table, so remains valid.
- `Test/Api/PackagesContract.lean:168–176`: SQL build's final success is nat1 at code4.
- `Test/Counterexamples/Machine/Runtime/LayerEnvironment.lean:32–76`: F's effect leaves answer never or nat; discards unaffected; retained service context carries nat.
- `Test/Program/WeakenContract.lean:25–31`: closed layer is effectDiscard, unaffected.
- `Test/Program/BlameContract.lean:122–123`, `ProvisionContract.lean:112`, `Program/Provision.lean:642`: string succeed leaves are already rejected by the literal-domain check, which G keeps first.
- `Program/Provision.lean:441–509,575–608,636–638`: DocsOp service operations match handle carriers; configuration literals match nat; leftWins/rightWins are the two authorized exceptions; native projection boundary is separated above.
- `src/OCaml5/Eff/Goldens.lean:414–440`: nat/bool literals and nat effect leaves agree, including diamond/ref and mergeAll.
- `harness/truth/Truth.lean:130–192,270–309`: pProvide/layerBump/layerCount/SQL/text-failure leaves all return nat at numeric keys; checked every actual layerBump/layerCount call.
- `src/Effect4/Store/Domain/ProgramWire.lean:74–114`: eight fixed wire corpus programs contain no layers.
- `Test/Program/Gen.lean:179–203,329–374`: generator and reference pass inspected; retained 400 outputs inspected for effect leaves, with the limits above.
- `tools/Effect4Gen/guards/fold.lean` / corresponding generated `Program/Fold.lean` examples are structural, with unbound variable bodies and no checker admission; guards/authoring and guards/scopedlaws use only discards. No additional concrete carrier fixture is exposed there.

## Minimal amendment recommendation

Keep the fourth-fixture amendment confined to the actual public TemplatesContract list element, retaining printer bytes and adding its expected located refusal plus the neighboring nat positive control. The source scan does not justify another newly refused whole-program exception. Record the raw-runtime projection boundary and the expected g141 diagnostic change as receipt limits; if the owner's definition of "in-tree program" includes independently rechecked native projected layer subvalues, explicitly acknowledge that boundary before implementation rather than silently changing signatures or runtime fixtures.

## Exact root-run commands for the uncompiled drafts

Run serially in `/Users/pooks/Dev/lean4-effect4-slice6` before G changes the checker:

```
lake env lean -DwarningAsError=true /private/tmp/GProjectedLayerBoundaryProbe.lean
lake env lean -DwarningAsError=true /private/tmp/GAdditionalLayerCensusProbe.lean
```

These are proposed commands only; neither was run by this reviewer. The existing fourth-fixture probe remains `/private/tmp/GFourthFixtureProbe.lean`.
