# Transparent input metadata receipt

Input declarations and their type projection are transparent aliases.
This keeps generated literal contexts aligned with named compatibility witnesses during proof rewriting.
Their names, types, and generated Step data stay unchanged.

The source changes are `src/Effect4/Modules/Step/Inputs.lean` and `src/Effect4/Modules/Step/Elab/Inputs.lean`.
The consumer is the named Semaphore migration and its unchanged public proof statements.
No new theorem or judgment lands here.

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Semaphore.Ops Test.Program.SemaphoreData Test.Program.SemaphoreAgreement Test.Program.SemaphoreOps Test.Program.SemaphoreScenarios Test.Program.StepInputs` passes with 906 jobs.
The build includes the shared option and interpretation-requirement checkpoints.
The named input controls continue to pass.
