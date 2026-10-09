# Ref caller packet receipt

The packet needs `Step.callback` before it builds.
Root integration must register the two batteries and expose the callback and generated Forms through the author entry.
The coordinator owns those root changes.

Base: `b8b4099eb6516f59d4380f8a8bdcb488332adeee`.
Dependency: `e4fedc27`, picked here as `4541c2ef`.
Branch: `codex/ref-callers`.
The packet commit follows that dependency and changes only the assigned caller, harness, and research files.

## Result

The finite packet checks 21 callers against their expected machine observations and Effect `4.0.1`.
The compiler is tsgo `7.0.0-dev.20260629.1`; the runtime is Bun `1.4.2`.
The packet checks each reply together with the cell read afterward.
Its identities cover thirteen effectful operations, four non-writing branches, two captured names, a string replacement, and an allocated-handle replacement.

The stored-state control changes one update while keeping reply `41`.
The compiler accepts it, and the host detects cell `5` instead of `7`.
Four isolated compiler faults produce diagnostics at their intended lines.
The restored project compiles with no diagnostics.

The evidence is [receipt.json](2026-10-08-ref-callers-evidence/receipt.json).
The directory retains the manifest, emitted declarations, compiled inputs, source hashes, and the axiom probe.

## Changed files

| Path | Role |
| --- | --- |
| `Test/Program/RefPrograms.lean` | Actual public operations, typed callbacks, machine observations, and rejection controls |
| `Test/Program/RefFaces.lean` | Checked emission, reading, inferred types, and rendered text inside guards |
| `harness/ref-catalogue/Produce.lean` | The producer of exact checked declarations and observations |
| `harness/ref-catalogue/controls.ts` | Positive and negative compiler controls |
| `harness/ref-catalogue/observe.ts` | The latest-host observer and raw-set control |
| `harness/ref-catalogue/run.py` | The focused compiler and host comparison, with identity and hash checks |
| `harness/ref-catalogue/README.md` | The reproduction procedure and boundaries |
| `docs/research/2026-10-08-ref-callers-evidence/` | Retained finite evidence |

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Test.Program.RefFaces` | Pass, 559 jobs |
| `python3 harness/ref-catalogue/run.py --skip-build --install /Users/pooks/Dev/lean4-effect4/ts/release/node_modules --out docs/research/2026-10-08-ref-callers-evidence` | Pass, 21 checked callers, four intended compiler refusals, stored-state control detected |
| `LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-08-ref-callers-evidence/Axioms.lean` | Pass, 49 battery declarations at `[propext, Quot.sound]` |

The packet runs no sweep and changes no engine fixture.
The coordinator owns engine-fixture integration after the packet lands.

## Placement and limits

| Field | Placement |
| --- | --- |
| Concept and property | `translation-simulation`, the proposed `ref-steps-agree`; checked printing also serves R8's `read_print` and `read_exact` |
| Question and role | Finite controls of actual callers; no new theorem or registry claim |
| Reach | Thirteen effectful rows; pure typed callbacks; allocated cells; natural-number, string, and Deferred-handle consumers |
| Limits | No arbitrary JavaScript closure, callback exception, reentrant mutation, aliasing, schedule, progress, or whole-program host theorem |
| Consumer | Ref catalogue callers, then later composed modules; R10 and the checked emission boundary |

`Ref.set` discards its raw reply explicitly through `Forms.asVoid` in `src/Effect4/Codegen/Authoring/Forms.lean`.
The machine's raw reply is its cell identity.
Effect `4.0.1`'s raw reply is its backing MutableRef, and differs from its outer Ref object.
The finite controls retain this difference without amending DI-98.
The direct host operations `makeUnsafe` and `getUnsafe` stay outside the effectful surface.

## Authoring findings

The callback body prepends its current-value input to one declared capture context.
The step and capture source reader share the same names and types.
The callers write no input positions and repeat no capture declarations.

At the base, `Effect4.Author` does not re-export the generated Forms module.
The packet therefore imports that existing module explicitly for `Forms.asVoid`.
The coordinator resolves this entry gap during root integration.
The callback agent owns the captured-fold depth control; this packet does not repeat that battery.
