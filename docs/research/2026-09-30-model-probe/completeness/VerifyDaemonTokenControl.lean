import Effect4.Api

/-! CONTROL (imports Effect4.Api, not Effect4.Api.Author; expected exit 0). Incidental (verifier of the completeness seat). Importing `Effect4.Api.Author` brings
`syntax (name := daemonFork_) "daemon " term …` (`src/Effect4/Program/Authoring/Services.lean:151`),
which makes `daemon` a keyword: the structure-instance field `daemon := …` of `ForkOptions` no
longer parses. Expected: exit 1, one parse error at the `daemon` field. The control is
`VerifyDaemonTokenControl.lean` (the same file importing `Effect4.Api` instead; exit 0). -/

def opts : Effect4.Supervision.ForkOptions :=
  { startImmediately := false, daemon := false, maskMode := .inherit }
