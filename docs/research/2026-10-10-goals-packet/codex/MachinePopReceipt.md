# Native value continuation custody

The command obligation remains open; its value-resume subcase now compiles without a goal.

Base: b7104ddc, including the coordinator's completed scheduler closure.
Files: ReleaseCustody/Producers.lean and ReleaseCustody/Pop.lean.

Placement:

1. Concept: scope-lifetime-finalization; required property: at most one release start per counted registration.
2. Question: Execution.command_custody consumes the native continuation debit; Workers.Assertions.releases_step consumes that obligation.
3. Reach: every native root, table, callback, generator fuel, generator cursor, environment, value and saved frame stack.
4. Limit: cause popping and the remaining evaluator and command branches stay open. No progress or host agreement follows.
5. Unlock: R11 through the existing Machine.Lift command interface.

The value pop follows the actual fused hook traversal and its pushed masks.
Saved constants retain their code and the sharper response projection beneath them.
The scope-add answer retains only its response-dependent reservation.
Native value arms consume the actual saved callback and iterator producers.
Source generators carry zero credits before their registration frame executes.
Stored close iterators split the head finalizer from the residual order.
The actual resumeValue result consumes the combined pop and arm bounds.

Commands:

- LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ReleaseCustody.Pop: passes, 347 jobs.
- LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Programs: passes, 1030 jobs.
- LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/MachinePopCustody.lean: passes.
- Axiom audit: 873 declarations within propext and Quot.sound; zero goals and zero modulo declarations.

The audit covers Evaluation, Producers and Pop.
The reader applies the actual native resume rule at the worker acquisition identity and a saved yield continuation.
The original command goal is not marked proved.
The coordinator owns root imports and the final behavior gates.
