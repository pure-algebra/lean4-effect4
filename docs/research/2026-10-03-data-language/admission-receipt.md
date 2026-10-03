# Program admission slice receipt

The coordinator must regenerate the refusal codecs before building the combined root.
This branch deliberately leaves root imports, the generator manifest, its guard inputs, generated outputs and measured traversal policy to integration.
The Lean slot is released. No Lean process remains in this worktree.

## Result and scope

Base: `82d34358`. Implementation: `128fec34`. Branch: `codex/data-admission`.
Worktree: `/Users/pooks/.codex/worktrees/data-admission/lean4-effect4`.
The receipt is committed separately so it can name the exact implementation commit.
No push, full battery or whole-root axiom gate was run.

The shared check rejects duplicate record names and invalid closed map keys before normalization.
Every raw table column and existing program type annotation participates, even when unused.
The declaration retains the raw type, enclosing path and deterministic preorder occurrence index on refusal.
Open map keys may pass only at row-template positions. Actual substitution checks request, answer and error strictly.
Program annotations never defer an open key.

The check reaches runtime admission, checked module reading and both module producers, TypeScript declaration printing and checked replay.
Their successful certificates retain the declarative formation judgment.
Replay distinguishes a static formation refusal from an actual decision refusal, including on an empty tape.
Raw expression printing, raw readers and typing-only APIs keep their existing scope.

Template inference now visits named fields, map arguments, tuple positions and same-name nominal arguments.
The existing subtype guard still decides matching after inference.
Request mismatch keeps precedence. A matched request with malformed substituted columns gets the new precise formation reason.

## Contract amendment and retained counterexample

The coordinator approved a formation premise on the old unconditional `rowTy_closed` statement.
A closed malformed map cannot keep the old acceptance behavior under row 193.
The successful-result theorem `rowTy_closed_some` keeps its original statement: success discharges the new check.

The fixture retains a stronger control against a closed-row bypass.
The key `union unknown (var 0)` is open, so the raw template pass defers it.
Row normalization erases the parameter and produces a closed `unknown` key.
The actual row check still refuses that key. No closed-row bypass remains.
The fixture also retains the ordinary malformed closed-map case.

## Proof placement

The coordinator placed `raw-formation` and `instantiated-formation` in the existing semantics registry before these proofs.
No second ledger or parallel graph was introduced.
All rows below inherit decisions 192 and 193 and the existing template-matching limits.

| Declaration or changed family | Concept, question and role | Consumer and exact reach | Limit and requirement |
| --- | --- | --- | --- |
| `Formation.check_eq_none_iff`, `checkInput_eq_none_iff` | Type algebra, `raw-formation`, decidability | Admission certificates; every raw occurrence collected by the existing generated folds | Formation only; no inhabitance or codec law; R3 and R8 |
| `rowTy_eq_some_iff`, `rowTy_instantiated_formed` | Residual typing, `instantiated-formation`, compatibility | Checker inversion and admission; successful actual match plus all three strict instantiated columns | No host reply guarantee; R1 and R3 |
| `checkRow_formation_iff`, `checkRow_request_iff` | Residual typing, `instantiated-formation`, located refusal | The shared diagnostic worker and `Checker.perform`; actual template match or mismatch | No claim that inference accepts every possible match; R3 |
| `Ty.infer_closed`, `infer_widensSub`, `infer_widens` | Type algebra, existing template substitution laws | `matchTemplate`, row typing and native atom schemes; all structural cases and either join setting | Existing union restrictions and subtype guard remain; R3 |
| `templateAdmissibleFields_eq_all`, `templateAdmissibleItems_eq_all`, `templateAdmissible_of_closed` | Type algebra, existing template-profile admission | `admitSig` and native signature profile proofs | The profile still refuses parameters beneath union heads; R3 |
| `rowTy_closed`, `rowTy_closed_some` | Residual typing, existing closed-row compatibility | Existing row consumers; explicit formed premise on equality, successful match on projection | No malformed closed-row acceptance; R3 |
| Module emission and reading recheck, erasure, completeness and admission laws | Representation and residual typing, helpers of `raw-formation` and existing module certificates | The exact program, raw table, name and existing printer/reader image | Formed-input premises are explicit; no target execution theorem; R3 and R8 |
| `Api.replayChecked_formation`, `replayChecked_formed` | Residual typing, helpers of `raw-formation` | Every replay tape and fuel; static refusal or successful inspection | No progress, liveness or host behavior; R1 and R3 |
| Checked typing, Run certificate and handle replay migrations | Existing program admission and handle-invariant questions, direct consumer repair | Extra retained formation evidence and the new replay refusal sum | Existing hypotheses stay present; no M6 or M7 extension |

The field and item equations serve the existing template-profile theorem, not a new general-purpose interface.
The new inference widening proof reuses `WidensSub`; the duplicate value-level induction was removed.
The existing checker proof bank uses the proved projection equation and passes its omitted-bank negative fixture.

## Verification

All Lean commands ran serially in this worktree with `LEAN_NUM_THREADS=3`.
The final commands and results were:

```text
lake build Effect4.Laws.Program.Template Effect4.Laws.Program.Typing.CheckSound Effect4.Laws.Codegen.Admit Test.Program.FormationContract
PASS: 308 jobs

lake build Effect4.Laws.Run Effect4.Laws.Program.Handles.Evaluation Effect4.Laws.Api.Codegen Effect4.Laws.Api.ModuleReadable Effect4.Laws.Program.Signature Test.Api.ExternalContract Test.Api.AcquireHandleContract Test.Api.PackagesContract Test.Program.HostSpecContract Test.Program.CheckerRulesRed
PASS: 422 jobs

lake env lean Test/Program/FormationContract.lean
PASS: exit 0

git diff --check
PASS

python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/admission-brief.md docs/research/2026-10-03-data-language/admission-receipt.md
PASS: no finding in either note
```

The dedicated fixture has 41 finite guards, three certificate examples and 13 axiom queries.
The guards cover all checked entry points, unused raw input, normalization loss, nested inference, substitution failures and positive controls.
They also check retained integer refusal and request-mismatch precedence.
The existing replay fixtures passed after migrating only their refusal patterns.
Finite guards supplement the general laws; they do not establish host or target execution.

The direct fixture printed `[propext, Quot.sound]` for each of:

```text
Effect4.Api.replayChecked_formation
Effect4.Api.replayChecked_formed
Effect4.Program.Formation.checkInput
Effect4.Program.Formation.checkInput_eq_none_iff
Effect4.Program.rowTy_instantiated_formed
Effect4.Program.rowTy_eq_some_iff
Effect4.Program.checkRow_formation_iff
Effect4.Program.checkRow_request_iff
Effect4.Program.Ty.infer_closed
Effect4.Program.Ty.infer_widensSub
Effect4.Program.Ty.infer_widens
Effect4.Codegen.ModuleEmission.recheck
Effect4.Codegen.ModuleReading.recheck
```

The prior diagnostic build failed in two closed-row proofs because tactic splitting selected an outer match.
The repair split the subtype result explicitly. The statements did not change after the approved formation premise.
The final build and direct fixture above passed after that repair.

Local logs: `/tmp/data-admission-diagnostic-final.log`, `/tmp/data-admission-consumers-final.log`, `/tmp/data-admission-fixture-final.log`.
The strict wording check reports existing findings in other documents; none belongs to the new brief.

## Integration requirements

1. Import `Effect4.Laws.Api.Formation` after `Effect4.Laws.Api.Codegen` in `src/Effect4/Laws.lean`.
2. Import `Test.Program.FormationContract` after `Test.Program.AdmissionColumns` in `Test/All.lean`.
3. Point registry claims at `Formation.checkInput_eq_none_iff` and `rowTy_instantiated_formed`.
4. Add `Effect4.Program.FormationReason` and `Effect4.Program.FormationRefusal` to the Refusals manifest before their consumers.
5. Extend `tools/Effect4Gen/guards/refusals.lean` with the new formation examples and the appended `TypeReason.instantiatedFormation` case.
6. Regenerate `src/Effect4/Api/RefusalsDerived.lean` and `src/Effect4/Api/RunnerDerived.lean` through the repaired stage-zero route.
7. Measure and update reached case and traversal policy, then run the relevant gates. This branch does not guess their counts.

The manifest lives at `tools/Effect4Gen/manifest.json`.
The guard input compares the exhaustive `reasons` list against `Canonical.heads TypeReason`, so adding its new witness is required.
The actual new carrier names avoid the existing authoring `Reason` and `Refusal` namespaces in the generator.
All new cases append to existing alphabets. Existing source ordinals stay fixed; regenerated wire compatibility remains integration evidence.
`ReplayCheckRefusal` is the public static-or-dynamic result, not a new machine decision or stored program constructor.

The next record slice must extend `Formation.programSites` to inspect the declared type metadata in its new `Term` constructor.
It should reuse `sites false`, with the term's located path. The present collector covers the existing iteration annotation.

The coordinator owns the combined-root and generator checks above.
No open theorem remains in this slice. Whole-root trust, generated-output freshness and the new record metadata remain explicit integration obligations.

## Changed files

- `Test/Api/AcquireHandleContract.lean`
- `Test/Api/ExternalContract.lean`
- `Test/Api/PackagesContract.lean`
- `Test/Program/FormationContract.lean`
- `Test/Program/HostSpecContract.lean`
- `docs/research/2026-10-03-data-language/admission-brief.md`
- `src/Effect4/Api.lean`
- `src/Effect4/Codegen/Admit.lean`
- `src/Effect4/Codegen/Checked.lean`
- `src/Effect4/Laws/Api/Codegen.lean`
- `src/Effect4/Laws/Api/Formation.lean`
- `src/Effect4/Laws/Api/ModuleReadable.lean`
- `src/Effect4/Laws/Codegen/Admit.lean`
- `src/Effect4/Laws/Codegen/Checked.lean`
- `src/Effect4/Laws/Program/CheckedTyping.lean`
- `src/Effect4/Laws/Program/Handles/Evaluation.lean`
- `src/Effect4/Laws/Program/Template.lean`
- `src/Effect4/Laws/Program/TypeAlgebra.lean`
- `src/Effect4/Laws/Program/Typing/CheckInversion.lean`
- `src/Effect4/Laws/Run.lean`
- `src/Effect4/Program/Admission.lean`
- `src/Effect4/Program/Checker.lean`
- `src/Effect4/Program/Formation.lean`
- `src/Effect4/Program/Ty.lean`
- `src/Effect4/Program/Typing/Blame.lean`
- `src/Effect4/Program/Typing/Rules.lean`
