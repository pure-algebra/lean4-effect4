import Effect4.Author
import Effect4.Run
import Effect4.Emit
import Effect4.Library
import Effect4.Laws.Author
import Lean

/-! A finite import-surface control at fdbae937, under decisions row 332.
The author entries expose program construction but omit the landed edit session.
This is a reachability observation, not an execution or typing theorem. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  unless env.contains `Effect4.Api.Author.program do
    throwError "positive control missing: public program authoring"
  for n in #[`Effect4.Program.EditSession.open, `Effect4.Program.EditSession.feed,
      `Effect4.Program.EditSession.view, `Effect4.Program.EditSession.reached_view] do
    if env.contains n then throwError "review checkpoint changed: {n} is now public"
  logInfo "PASS: public authoring is present; all three edit operations and their view law are absent through the five entry modules"
