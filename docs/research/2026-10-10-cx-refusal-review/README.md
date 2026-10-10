# Review of located layer refusals

The next shared-layer proof needs the module declaration's typing evidence at the reference hop.
The tool summary also drops the new refusal's target and specific fault.

Reviewed source: `41ec1e0c1d55f05393f3b4e7f938a5d87f7a6214`.
Prior source checkpoint: `3ef7aeb0f41bbb3796f44edc873e4185e760c6ca`.
This packet changes no production source.

## Result

The finite probe passes all 26 guards.
The narrow builds pass.
The cycle-aware audit accepts 1,620 declarations in the three reviewed modules.
It finds no planned goal or declaration resting on one.
The [verification record](verification.json) holds commands, results and source hashes.
The [probe log](probe.log) and [audit log](audit.log) hold their exact output.

The review finds no concrete acceptance regression in the located-refusal change.
`Eff.refFault_isNone` in `src/Effect4/Program/Refs.lean` states the former formation conditions exactly.
`Eff.firstRefFault_eq_none` ties absence of a fault to reference formation.
`Api.explain_none_iff` in `src/Effect4/Api.lean` retains the absence-of-refusal judgment.
These are source-inspected generic laws.
The audit below covers the reference and refusal modules, not the entire API or M7 dependency graph.

The finite controls cover each fault, two faults together, an earlier valid reference, and the same-scope positive case.
They also retain ordinary child-2 handler paths for the next program syntax change.
They establish no general theorem about the earliest fault.

## New authoring gap: the summary drops the detail

`Tools.Query.refusalJson` in `tools/Tools/Query.lean` retains only the source path and the reason's constructor name.
Two refusals with different specific faults produce the same summary.
The generated carrier keeps that distinction.

For the probe's actual missing target, the summary is:

```json
{"path":[0,1],"reason":"referenceIllFormed"}
```

The existing generated format gives:

```json
{"path":[0,1],"reason":{"_tag":"referenceIllFormed","target":[0,0,5],"why":"noLayer"}}
```

The distinction matters to an author deciding whether to move a declaration, repair an address, or change its scope.
The current summary deliberately promises only a reason name.
This is an authoring limitation exposed by the richer refusal, not a regression in its documented format.

Smallest next action: retain the summary fields and add the existing canonical refusal as structured detail.
Use the generated `Canonical TypeRefusal` instance from `src/Effect4/Api/RefusalsDerived.lean`.
Reuse `Tools.Session.printJson` in `tools/Tools/Session.lean`, or move its generic conversion to the existing JSON bridge.
Keep one structured refusal projection for tool, preview and rendering consumers.
Do not introduce another reason enumeration.

This change alone does not connect source annotation with reference-aware admission.
The existing source-view gap remains: `EditSession.open` reports `layerReference`, and the layer's visible line carries no refusal marker.
The probe rechecks that boundary at this commit.
The previous packet records it at `git:86d72c10:docs/research/2026-10-10-live-graph-support/run-view/COMPATIBILITY-3ef7aeb0.md`.
It is unchanged evidence, not a new notification.

## Proof support for the next slices

[NEXT-PROOFS.md](NEXT-PROOFS.md) gives the proof dependency graph and all five placement fields.
Its two main recommendations are these:

1. Carry module-layer typing through `SourceWF` to the layer-reference proof.
2. Give call identity its own invariant, including calls with no program parameters.

The controls show why checking a target only after copying it into a caller is insufficient.
A parameter-reading layer checks under the caller's typing signature with a parameter and refuses at the source signature.
A closed layer checks alike under both signatures.
These controls do not demonstrate a runtime defect in a currently admitted program.
The new module field is absent from the reviewed commit.

The implementation draft already limits module child `2` to root definition blocks.
That avoids confusing it with an ordinary handler child.
This statement comes from the bounded session tail, not a compiled draft.

## Commands and evidence limits

Run the narrow dependencies, then the packet:

```sh
LEAN_NUM_THREADS=3 lake build Tools.Session Tools.View.Program ProofGraph.AxiomAudit Effect4.Api.RefusalsDerived
python3 docs/research/2026-10-10-cx-refusal-review/verify.py
```

The actual build runs occur in two commands.
The first builds the tool, view and audit dependencies.
The second builds the generated refusal codec, which the first probe import lacked.

[build.log](build.log) and [build-codec.log](build-codec.log) record both successful runs.

[probe-preflight.log](probe-preflight.log) and [preflight.json](preflight.json) retain that setup failure.
It is no counterexample or intended refusal.

The audit imports these modules:

- `Effect4.Program.Refs`
- `Effect4.Program.Typing.Blame`
- `Effect4.Api.RefusalsDerived`

The probe applies the generated codec law at a concrete refusal.
It contains no new general proof, planned goal or production repair.
The audit does not cover later code, host behavior, the whole machine, or the entire M7 proof graph.
No TypeScript compiler, outside-runtime gate, full sweep, merge or push runs in this review.

## Ownership and checkpoint

The [checkpoint](checkpoint.json) records the primary commit, owned paths and bounded session evidence.
Claude's primary branch advances to `34a39a38` during this review.
That commit adds a polarity research packet; its findings are outside this review.
The active session begins polarity implementation and reviews the retained graph branch.
Its broad behavior gates remain under investigation in the last inspected tail.
Reported gate results are not reproduced results here.

The review leaves the primary checkout, owner decisions and implementation session unchanged.
Two Sol 6.1 agents independently inspect refusal changes and the next layer proof dependencies.
The parent runs the finite controls and audit in the attached review worktree.
