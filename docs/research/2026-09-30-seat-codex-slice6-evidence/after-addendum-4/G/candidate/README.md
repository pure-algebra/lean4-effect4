# G candidate: authorized changes and separate fourth-fixture proposal

This is an uncompiled candidate prepared under `/private/tmp` only. It is concrete enough to review and apply after the outstanding G scope ruling, but it is not a passing implementation receipt. The exact old/new hunks and Python syntax were checked; this seat ran no Lean, builds, generators, OCaml commands, or repository edits.

No retained `G/implementation.patch` exists in either the current slice6 evidence tree or the main checkout's copy: G retained its AuthorContract probe and log, while A and F retained implementation patches. This candidate was therefore assembled from current source and addenda 2–4. It does not claim to recover an absent patch.

## Files and separation

`prepare.py` reads the selected live worktree and renders candidates only beneath `/private/tmp`. It has no apply mode. Re-run it after F's final commit so `Test/All.lean`, hashes and base HEAD record that actual landing. Every old block must match exactly once. Failure means inspect live source, not replace it with an older file.

```sh
python3 /private/tmp/g-candidate/prepare.py
python3 -m py_compile /private/tmp/g-candidate/prepare.py
git apply --check /private/tmp/g-candidate/rendered/authorized-source.patch
git apply --check /private/tmp/g-candidate/rendered/register-after-success.patch
```

`rendered/authorized-source.patch` changes these nine paths, with no generated snapshots:

1. `src/Effect4/Program/Checker.lean`: two leaf checks, retaining existing literal/body refusal precedence.
2. `src/Effect4/Laws/Program/Typing/HasTy.lean`: the two authorized service-lookup/subtyping premises and truthful docstrings.
3. `src/Effect4/Laws/Program/Typing/CheckInversion.lean`: return those premises from successful leaf checks, with the existing checker aesop bank.
4. `src/Effect4/Laws/Program/Typing/CheckSound.lean`: supply the returned premises to the strengthened constructors. The existing complete proof should close from its added constructor hypotheses through the same bank; this remains uncompiled.
5. `src/Effect4/Program/Provision.lean`: move leftWins/rightWins to dbBinding, positively check each before comparing their types, update expected name-20 contexts, and remove the false build_total claim from the header.
6. `Test/Program/ProvisionContract.lean`: the same positive admission and updated contexts, so equality cannot pass merely as none = none.
7. `Test/Program/AuthorContract.lean`: the third approved fixture expects the located string-at-nat refusal. Its shared Counter and positive Greeting string-carrier test remain unchanged.
8. `Test/Counterexamples/Machine/Semantics/LayerValue.lean`: new original gap refusals, exact paths, the two authorized unknown-key controls, matching-value acceptance, retained former leaf rules and their failed carrier claims, and refusal-order controls. All named facts print their axiom dependencies.
9. `Test/All.lean`: import LayerValue immediately after M6Capstone. The current F LayerEnvironment import and every other import are preserved.

`rendered/register-after-success.patch` changes only E4-PROV-CE-002 and E4-PROV-CE-006. It is deferred until actual successful validation; refresh it from live REGISTER then so F's concurrent CE005 row survives. The CE006 repaired text is a proposed final status, not a claim that tests have passed. Replace its date if the landing date changes.

`rendered/PROPOSED-fourth-fixture.patch` is separate and depends on the authorized candidate. It adds the TemplatesContract import to LayerValue and the four exact-source/negative/positive theorems from `/private/tmp/GFourthFixtureControls.proposed.lean`. It changes no shared template fixture or printer guard and no generated output. It is NOT included in the authorized source patch or treated as permission to continue. Its application was checked against the rendered authorized files, not against the current unmodified tree where LayerValue does not exist.

The proposed fourth amendment is exactly:

> Permit the existing `Test.Codegen.TemplatesContract.layerSamples[1]?` entry as the fourth expected refusal: the effect body returns unit at name-7/code-4 (nat), so checkLayer refuses `valueNotSubtype key unit nat` at `[]`. Retain the sample and its shared definitions for printer coverage. Add an exact-source negative checker control and its neighboring nat-valued succeed positive control. Correct addendum 3's unchanged-leaf census; retain the stop on any further newly refused in-tree program or layer beyond the gap cases and four named exceptions.

Do not add the DocsLayer projection's raw runtime controls: their whole programs were already refused, and they are outside this additional-refusal amendment.

## Statement and proof scope

`statement-diff.md` records the exact old and new two leaf constructors and inversion statements. The soundness, completeness and uniqueness theorem statements stay unchanged; the judgments they name acquire exactly the authorized premises. `Typing/Sound.lean` is not edited speculatively: its layerTy projections and uniqueness proof call the same checkLayer laws, so rebuilding it is the appropriate check. Any actual additional proof repair must be recorded by declaration.

The local `Reviewed.LayerHasTy` copies only the two former leaf constructors verbatim in premise and conclusion shape. It is explicitly a leaf fragment, not a claim to preserve every mutually recursive old typing judgment. Those are the only rules G changes. Its concrete bodies use the unchanged pure succeed rule; the two theorems refute the old leaf rules' proposed carrier conclusion using Boolean-at-nat and string-at-nat witnesses.

Likely elaboration points to inspect if a narrow build fails: the two strengthened inversion statements' existential order, constructor implicit `ty`, and aesop normalization of the added Bool guard in completeness. The new test uses Api.explain for the located refusal and Api.typeOf for rejection, because Api.checkTyping returns an optional certificate rather than a located Except. The AuthorContract test maps the successful certificate to Unit before comparing the Except, so it does not require equality of proof-bearing TypedLayer values.

## Exact validation sequence for root's single Lean lane

First compile the separate retained fourth-fixture probe against the current checker. If it confirms the fourth refused fixture, original addendum 4's stop remains in force until the owner accepts an amendment. No candidate application is authorized by this preparation.

After that ruling and source application, rebuild changed modules and direct consumers together. The inclusion of Assembly also reaches Admission; the two Folds modules check their derived algebras against the changed definitions. The Laws umbrella and remaining transitives will also be reached by make corpus's required default build; no separate broad sweep is proposed.

```sh
lake build Effect4.Program.Checker Effect4.Program.Typing Effect4.Program.Provision Effect4.Laws.Program.Typing.HasTy Effect4.Laws.Program.Typing.CheckInversion Effect4.Laws.Program.Typing.CheckSound Effect4.Laws.Program.Typing.Sound Effect4.Laws.Program.Folds.Checker Effect4.Laws.Program.Folds.Provision Effect4.Laws.Program.Typed.Assembly
lake build Test.Program.ProvisionContract Test.Program.AuthorContract Test.Program.CheckerRulesRed Test.Counterexamples.Machine.Semantics.LayerValue
lake env lean -DwarningAsError=true Test/Counterexamples/Machine/Semantics/LayerValue.lean
lake env lean -DwarningAsError=true /private/tmp/g-candidate/Axioms.lean
```

After the fourth amendment, also run its retained printer module directly. The four proposed theorems are then part of LayerValue and print their axioms there.

```sh
lake env lean -DwarningAsError=true Test/Codegen/TemplatesContract.lean
```

Preserve all theorem prints, requiring `[propext, Quot.sound]` or less. No axiom allowance or root import change is proposed. Axiom-print success alone does not establish the new guards executed; retain each command's exit/output.

G changes the checker, not the runtime. Addendum 2 explicitly says checkLayer is outside the engine closure and requires no LCNF regeneration. Do not restore or regenerate the old A/F/C generated snapshots. No new syntax constructor, generator input or match on a policy family is added here, so no independent gen-derived/gen-eff/gen-wire/gen-cas cycle or new case-census amendment is proposed for G.

Retain the pre-G corpus index, then run G's named producer once:

```sh
cp generated/corpus-index.tsv /private/tmp/g-candidate/corpus-index.before.tsv
env LEAN_NUM_THREADS=1 make corpus
git diff -- generated/corpus-index.tsv
```

Makefile:230–241 rebuilds Drivers.Corpus, generates the 400 depth-4 programs plus wire corpus, and writes the committed index. The default build prerequisite also checks source/test consumers. Compare the before/after verdict columns and name every changed program. An unchanged index is the expected result. A newly refused in-tree program beyond the authorized gap cases/exceptions still stops G; do not silently promote an unexpected verdict. `make corpus` is the requested producer, not a request to run or promote the TypeScript truth corpus.

Then apply the refreshed two-row register patch, record actual base/head, path list, commands, axiom output, statement changes and finite corpus result in the slice6 receipt, and make the one explicit-path G commit with any selected research files force-added. No decisions.md edit and no push.

## Preservation checks already done

Python rendering and syntax passed. `git apply --check` passes on the live current tree for the authorized source and deferred register patches; the separate fourth patch passes against the rendered authorized candidate. `manifest.json` names each before/after SHA-256 and the actual base HEAD. Its preservation hashes include current Compile/Fibers, roots, externs and prelude. None of those C/F implementation or producer paths is emitted by this candidate. No generated files are included.
