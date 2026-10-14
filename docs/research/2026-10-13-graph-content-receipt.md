# Graph source content receipt

This projection records syntax and typing observations, not runtime state.
Production typography and graph labels remain the coordinator's consumer work.
The source API adds no role taxonomy or geometry policy.

Base: `f25c74f3e2c6acd2bf4ad85c7cbd205dcc8952e0`.
Source and plan: `ac97df6e96e80ea387493d89311eb80b66eb9b07`.
Probe: `732ba85ee522b0e449145d36cdc85d07535bf2f2`.
Branch: `codex/graph-node-content`.
Worktree: `C:/Users/kokok/Dev/effect4-peg-board`.

## Interface and observation

`Tools.View.GraphContent.Node` in `tools/Tools/View/GraphContent.lean` records address, depth, family, constructor, arguments, and optional operation.
`GraphContent.ofProgram` in that file folds the generated `EffAlgebra.ofLayer`.
It suppresses the same list spines as `Program.lines` in `tools/Tools/View/Program.lean`.
Child indices count child arguments alone.
No declaration enumerates the constructors of `Eff` by hand.

`GraphContent.Argument` in `tools/Tools/View/GraphContent.lean` uses the existing `ArgF` alphabet.
The `argument` adapter replaces each child carrier with `Unit`.
It retains the child family and original argument position.
Other arguments retain their original values, including `NativeOp` binder terms and definition declarations.
The output holds no subtree or host closure.

`GraphContent.Entry` in that file joins the node with optional `Table.Entry`, operation metadata, and optional type text.
`ofSession` reads the supplied session table by exact address.
First-occurrence indexing determines duplicate-address behavior.
The function does not assert the supplied session's coherence.

`GraphContent.Operation` in that file retains the actual operation value.
Its optional row comes from `Sketch.sigAt` in `src/Effect4/Program/Sketch.lean`.
The row exists only when that address-local signature declares the operation.
The typing signature normalizes row types.
It retains row spelling, kind, registration, request, answer, error, and requirements.
This includes hole declarations and definition-body parameter signatures.
The optional row does not certify row admission or runnable registration.

An `invoke` node retains its constructor, numeric index, and child arguments.
It has no invented `NativeOp` value.
Operation metadata corresponds only to an actual `ArgF.op` argument.

`ofSessionPage` additionally reads the supplied page's first `Line.type` by explicit key.
The optional text remains separate from raw typing.
A missing line differs from a present line with empty type text.
The function does not assert consistency between the supplied page and session.
`Node.key` uses the existing address formatter without parsing its spelling.
The consumer can format arguments through existing `Program.argText` or `Program.ownText`.
No new text-rendering declaration crosses the inherited rendering boundary.

## Typing distinctions

Raw `EffTy` retains distinct answer, error, and requirement columns.
Raw `NodeEnv` retains variable environments and the node-family context separately.
A missing table entry differs from an existing entry with no result.
An existing entry with no result differs from an admitted type whose error is `never`.
A refusal retains its located path.
An enclosing node can retain a refusal located at a descendant.
These observations describe the checker and source data, not execution outcomes or future completion.

## Commands and measured results

Each Lake command exports `LEAN_NUM_THREADS=3` in PowerShell.
The commands run serially in this worktree.

| Command | Result |
| --- | --- |
| `lake build Tools.View.GraphContent` | Pass, 182 jobs |
| `lake build Tools.View.FlowSpecimen ProofGraph.AxiomAudit` | Pass, 198 jobs |
| `lake env lean -DwarningAsError=true -o .lake/build/lib/lean/GraphContentProbe.olean tools/view/GraphContentProbe.lean` | Pass, 16 specimen programs reported |
| `lake env lean .lake/GraphContentAudit.lean` | Pass, checked strict module and compiled-probe audit |
| `(Select-String -Pattern '^#guard\b' -Path tools/view/GraphContentProbe.lean).Count` | 37 finite controls |
| `git diff --check` | Pass |

The ignored audit file contains these imports and command:

```lean
import Tools.View.GraphContent
import GraphContentProbe
import ProofGraph.AxiomAudit
#axiom_audit checked Tools.View.GraphContent GraphContentProbe
```

The source-only audit reports 72 declarations and 3546 captured constants.
The final combined audit reports 115 declarations and 4330 captured constants.
Both report zero planned goals and zero declarations modulo goals.
Their labels contain only `propext` and `Quot.sound`.
The inherited manifest warning reports a changed local `whatwg` dependency revision.
This slice changes no dependency declaration or manifest.

The finite controls compare text, addresses, depth, and operations with the existing line fold across all real flow specimens.
They also inspect original argument ordering and operation binder data.
Other controls cover typed nodes, requirements, located refusal, unreached entries, external rows, holes, local calls, and local parameters.
They cover all operations in `NativeOp.spelled` and distinct deferred value/error type parameters.
Duplicate table addresses and page keys receive explicit first-occurrence controls.
Rendered bytes occur only inside guards.

## Placement and limits

The plan is `docs/research/2026-10-13-graph-content-plan.md`.
This passive metadata slice introduces no theorem, admission judgment, or registry claim.
It serves R14's authoring view under decisions row 334, point 3.
The controls establish finite observations only.
They do not prove fold agreement for every program.
The source does not assign visual style, alter node dimensions, or change connector geometry.
No machine, program syntax, codegen, or external behavior gate changes.
The coordinator owns visual gallery integration and its browser observations.
