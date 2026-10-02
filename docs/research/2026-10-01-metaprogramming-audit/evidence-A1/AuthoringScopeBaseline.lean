import Effect4.Api.Author

/-!
# Authoring scope — the surface's two words are keywords only where the surface is open

The authoring surface writes two words of its own: `eff` (a program block,
`Program/Authoring/Sugar.lean`) and `daemon` (a detaching fork, `Program/Authoring/Services.lean`).
Both are `scoped syntax` of `Effect4.Program.Authoring` (decisions row 17, seat J2; the repair of
`E4-AUTHOR-CE-002`): a module that imports the surface and does not open the namespace keeps both
as plain identifiers. Seat J measured the leak this repairs: with the syntax global, importing
`Effect4.Api.Author` alone made `daemon` a keyword, so the field `daemon := …` of
`Supervision.ForkOptions` stopped parsing in every importer
(`docs/research/2026-10-01-landing/seat-J/probes/DaemonKeywordLeak.lean`, "unexpected token ':=';
expected term"). That probe's program is the first control below and elaborates; then `eff` is
pinned as no keyword without the `open`; then, with `open scoped Effect4.Program.Authoring`, both
words are the surface again.
-/

namespace Test.Program.AuthoringScope

/-- The leak's own program (seat J's probe): elaborates, so `daemon` is a field name here. -/
def opts : Effect4.Supervision.ForkOptions :=
  { daemon := false, startImmediately := true, maskMode := .inherit }

#guard opts.daemon == false && opts.startImmediately

-- Without the `open`, `eff` is an identifier like any other, and there is none of that name.
/-- error: Unknown identifier `eff` -/
#guard_msgs (error) in
example := eff do return 1

section Surface

open scoped Effect4.Program.Authoring
open Effect4.Program Effect4.Program.Authoring

/-- With the surface open, the block and the detaching word are the surface's again. -/
def detached : Src NativeOp := eff do
  let f ← daemon (succeed (nat 1))
  join f

#guard elaborate detached
  = .ok (.bind (.withFiber (.fork (.succeed (.lit (.nat 1))) daemonOptions))
      (.awaitFiber (.var 0) .joinEffect))

-- The parser API reads both surface block forms, including a pure local binding.
#guard_msgs in
#guard elaborate (eff { let n := 7; return nat n } : Src NativeOp)
  = .ok (.succeed (.lit (.nat 7)))

#guard_msgs in
#guard elaborate (eff do return nat 7 : Src NativeOp)
  = .ok (.succeed (.lit (.nat 7)))

#guard_msgs in
#guard elaborate (eff { return } : Src NativeOp) = .ok (.succeed (.lit .unit))

/-- error: unsupported final statement in eff block -/
#guard_msgs (error) in
example : Src NativeOp := eff do
  let x ← succeed (nat 1)

/-- error: destructuring pattern bindings are not supported in eff blocks; bind to a variable and project instead -/
#guard_msgs (error) in
example : Src NativeOp := eff do
  let (x, y) ← succeed (nat 1)
  return x

end Surface

end Test.Program.AuthoringScope
