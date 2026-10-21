# Service extraction receipt

The coordinator must connect the battery to `Test/All.lean` and run the reached behavior gates after integration.
The service extraction and its narrow checks pass.

## Commits and files

Base: `40770f079d8d7594021691e0f0b1d39025b211e0`.
Definition extraction: `30e263cbbfff7fbd07595e267937846b29091683`.
Laws and controls: `3b509f4e15e1f834d7a8a2736bbd3cf5c32eb394`.
The branch is `codex/program-services`.

| File | Added | Deleted |
| --- | --- | --- |
| `src/Effect4/Program/Services.lean` | 143 | 0 |
| `src/Effect4/Codegen/Print.lean` | 12 | 94 |
| `src/Effect4/Laws/Codegen/Services.lean` | 161 | 2 |
| `Test/Codegen/ProgramServices.lean` | 68 | 0 |

The counts come from `git diff --numstat 40770f079 3b509f4e1`.
The role reading keeps its declaration names.
`NameProfile` contains executable functions and is never stored in program data.
The printer selects its existing name checks through `tsProfile`.
The existing service theorem statements stay unchanged.

## Commands and results

Commands run in `/Users/pooks/.codex/worktrees/program-services/lean4-effect4`.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Program.Services Effect4.Codegen.Print` | Pass; 118 jobs |
| `LEAN_NUM_THREADS=3 lake build Test.Codegen.ProgramServices Test.Codegen.DefinitionsPrint Effect4.Laws.Codegen.Module ProofGraph.AxiomAudit` | Pass; 990 jobs |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/program-services-audit.lean` | Pass; declaration audit and compiled import checks |
| `git diff --check` | Pass |

The first proof build exposed one projection that needed reduction before rewriting.
The first battery proof attempted kernel reduction of a TypeScript identifier check.
The corrected battery checks that finite result and applies the theorem under its explicit acceptance premise.
The final commands above pass after those repairs.

The final build output is `/private/tmp/program-services-final-build.log`.
The final audit output is `/private/tmp/program-services-final-audit.log`.

```text
#axiom_audit: 330 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
Program.Services reaches neither Codegen.Print nor TypeScript.Identifier
```

## Placement and scope

Placement precedes proof work in `4d0b06374:docs/research/2026-10-21-program-domain-landing/README.md`.

| Declaration | Placement | Consumer |
| --- | --- | --- |
| `serviceFaultIn_anyName` | `exact-codecs`; compatibility claim `service-view-printed`; R8 | The printer's compatibility with domain role formation |
| `entriesOf_isSome` | `exact-codecs`; adequacy claim `service-view`; R8 | Service entry readers and the object service view |
| `serviceFault_eq` and the service helpers | Steps of those claims | The two declarations above |

These declarations live in `src/Effect4/Laws/Codegen/Services.lean`.
The controls distinguish domain names, target names, malformed requests and refusal precedence.
The existing module round-trip proof and definition-printing battery pass.
These results establish no service execution, host behavior or target runtime agreement.
The integration owns `check-ts` and any other reached behavior gates.
No root, registry, semantics, decisions or generated file changes in this branch.
