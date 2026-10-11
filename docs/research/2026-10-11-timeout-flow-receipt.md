# Timeout source-flow receipt

The original timeout goals remain open.
The source proof now covers every effect location and compilation fuel.
The machine-step assertion must consume this proof before clause four closes.

Base: `af0ece79a1501ce5acb2e98b4e4e4200ecd844e7`.
The observation reader from coordinator commit `3b586b452` is also integrated.
Changed files: `HostTimeoutSlots.lean`, `HostTimeoutFlow.lean`, and `HostTimeoutNative.lean` under `Test/Dogfood/Proofs`.
The audit reader and this receipt also change.

Placement: host-session-protocol, R6, serving `Timeout.stale_never_applies` clause four.
Consumer: the command assertion over `Run.HistoryOf`.
Reach: the exact elaborated timeout program, arbitrary source environments satisfying `EnvAt`, compilation fuel, and visible completed exits.
Evidence kind: checked universal source and callback equations.
The complete generated source census supplies thirty-eight cases.
The predicates inspect existing code and names, rather than introducing stored program syntax.

`EnvAt` correlates each source location with its lexical slots.
`ValueAt` retains applied-body membership in successful answers and retry results.
`SavedAt` and `StackAt` order the value classes between saved continuations.
`source_head` consumes the source census, callback equations, and actual reference, timer, external-call, and race routes.
The race's two entrants resolve the exact attempt and timer source positions.
Reference reads and cell allocations discard arbitrary results in lexical slots.
Reference updates return unit, while cleanup retains the saved exit's successful body.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutNative` | passed, 1063 jobs |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/TimeoutFlowAudit.lean` | passed: 438 declarations within `[propext, Quot.sound]`; zero planned goals or dependencies |

The machine assertion still needs fused pop, finalizer, pending resume, race settlement, forced-yield, and command closure.
The run assertion quantifies over every body set containing the current applied-body prefix.
Each transport proof fixes that set, so callback premises remain valid for later replies.
The source equations establish neither reachability nor progress.
They establish no host-runtime agreement or heap count/log invariant.
The retry and cleanup observations still need those heap facts.
The coordinator owns reached behavior gates, root imports, and registry placement.
This commit excludes the coordinator's `RaceFirst.lean` repair and the older untracked `KernelRfl.lean` helper.
No push occurs.
