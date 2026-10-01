import Effect4.Api.Author

/-! Seat J, step 3: why the build refusal is not in the Refusals group. `Effect4.Api.Author`
imports `Effect4.Program.Authoring.Services`, whose `syntax "daemon " term …`
(`Program/Authoring/Services.lean:151`) makes `daemon` a keyword in every module that imports
it, so the structure-instance field `daemon := …` of `Supervision.ForkOptions` no longer parses
there. A Refusals group importing `Effect4.Api.Author`, imported by the Runner group, carried
the keyword into every importer of `Api/RunnerDerived.lean`; `Test/Run/RunContract.lean:88`
(`{ daemon := false, startImmediately := true, maskMode := .inherit }`) failed with
"unexpected token ':='; expected term". This file reproduces the failure at the import alone.
Run: `lake env lean docs/research/2026-10-01-landing/seat-J/probes/DaemonKeywordLeak.lean`
(expected: exit 1, the same parse error). -/

def opts : Effect4.Supervision.ForkOptions :=
  { daemon := false, startImmediately := true, maskMode := .inherit }
