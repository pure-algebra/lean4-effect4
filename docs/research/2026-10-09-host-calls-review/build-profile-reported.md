# Build profile (.lake/gen/build.log)

482 modules rebuilt, 2749 s summed; the slowest is Effect4.Laws.Codegen.PrintTyped at 184 s.

Critical path: 269 s over 5 modules (rebuilt modules only; a module the build reused counts zero).

| s | module |
| ---: | --- |
| 33.0 | Effect4.Laws.Program.Typing.Annotate |
| 184.0 | Effect4.Laws.Codegen.PrintTyped |
| 3.8 | Effect4.Laws |
| 18.0 | Test.Audit.ProofStyle |
| 30.0 | Test.All |

Slowest modules:

| s | module |
| ---: | --- |
| 184.0 | Effect4.Laws.Codegen.PrintTyped |
| 116.0 | Effect4.Laws.Library.Queue.Typing |
| 94.0 | Effect4.Laws.Library.Pool.Typing |
| 70.0 | Effect4.Laws.Library.Queue.Data |
| 64.0 | Test.Program.PoolPublic |
| 61.0 | Test.Dogfood.Scenario.QueueWorkers |
| 52.0 | Test.Program.PoolScenarios |
| 50.0 | Effect4.Laws.Program.Typing.Splice |
| 33.0 | Effect4.Laws.Program.Typing.Annotate |
| 30.0 | Effect4.Laws.Program.Typing.Parts |
| 30.0 | Test.All |
| 29.0 | Effect4.Laws.Machine.Scheduling |
| 28.0 | Test.Program.SemaphoreScenarios |
| 22.0 | Effect4.Laws.Step |
| 22.0 | Test.Program.PoolTraces |
