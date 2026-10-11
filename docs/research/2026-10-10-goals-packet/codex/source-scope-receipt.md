# Source scope and native writer receipt

The source transports and the actual Queue writer command compile without planned goals.
Universal history provenance and Queue custody preservation remain open.

The slice moves `HeapSites.levelAt` unchanged into `SourceScope.levelAt`.
The old name is an abbreviation, so `HeapSites.SitesKeep` retains its statement and binder calculation.
`SourceScope` imports no Atomic-specific module.
`WriterScope` imports the heap-site premise and consumes the generic source transports.
The copied HeapSites base comes from coordinator commit `299c8b45`.

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
Concept: translation-simulation R10, serving QueueWorkers `Assertions.jobs_step`.
The helpers retain source nodes, lexical lengths, compiler fuel and actual callback arguments.
They use the generated `Node.child` and `Node.childLevel` tables.
They introduce no new program representation or planned goal.

`At` names a point's source level and captured environment length.
`GenAt` names the generator's effective address, including its statement counter and pending answer binder.
`bind_contA` transports the actual second child with one answer.
`releaseBody_contA` transports the actual captured release with its acquired value and exit.
`gen_modify` identifies the actual iterator's emitted writer and advanced callback scope.
Its reach is a yielding Ref.modify statement, with its source node and incoming generator scope supplied.
It does not cover pure statement walks, branches, block exits or every compiler name.

`WriterScope.modify_loop_keeps` proves the exact native command and its heap predicate after that command.
It retains the source-site, point-scope, current-code, successful store-answer and command-budget premises.
It retains every pending command after the generated drain and delivery commands.
`QueueWorkers.Source.take_loop` instantiates the command at the actual first worker's take writer.
`take_source` and `take_level` range over every natural job count.
`take_loop_keeps` consumes the shared source scope and heap writer law at that site.
These statements establish no cell alias, global source ownership, custody, rest correspondence or progress.

- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.SourceScope Effect4.Laws.Program.WriterScope Test.Dogfood.Scenario.QueueWorkers.Source`: passes, 1040 jobs.
- Lake reports SourceScope 6.7 seconds, HeapSites 1.8 seconds, WriterScope 1.5 seconds and QueueWorkers.Source 3.1 seconds in the final build.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceScopeProbe.lean`: passes.
- The probe reads the actual generator writer equation and the universal Queue source level.
- Its control proves the advanced generator's raw root address has the wrong lexical length.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SourceScopeAudit.lean`: passes.
- The audit walks 100 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.
- `git diff --check`: passes.

The coordinator owns the broader history induction and the behaviour gates.
The queue's original conservation, rest and cleanup obligations retain their existing statements and open dynamic premises.
