import Effect4.Laws.Program.ReleaseCustody.RuntimeShape
import Effect4.Laws.Program.NativeReplies

/-!
Concept: scope-lifetime-finalization, R11.
Question: native resume sequencing serves Execution.history and Workers.Assertions.releases_step.
Reach: the existing source predicate, exact native reply forms, and stable actual saved stacks.
Limit: these local transfers establish neither whole-history custody nor source uniqueness or progress.
Unlock: the worker source excludes race cleanup and retains forced-yield callback custody through every other reply.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.ReplySequencing
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Sequencing
open Effect4.Program.SourceScope

/-- A source without race actions has no owned runtime race.
Consumer: native command sequencing excludes race launch and settlement cases. -/
theorem no_races (root : NativeEff) (source : RaceFreeSource root) (m : NativeMachine)
    (owned : ConfigurationAt root m) : m.races = [] := by
  cases found : m.races with
  | nil => rfl
  | cons race rest =>
    exact False.elim (source.not_race (owned.races race (by rw [found]; exact .head _)).2)

/-- Every native reply available to this source retains its saved callback sequence.
Consumer: the actual token-matched resume command. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem terminal (root : NativeEff) (source : RaceFreeSource root) (answer : NCode)
    (owned : CodeAt root answer) (reply : TerminalReply answer) (frames : List NCode)
    (stable : StableFrames frames) : Kept answer frames := by
  cases reply with
  | success value => exact stable_value stable value
  | failure cause => exact stable_cause stable cause
  | refGet cell => exact stable_refGet stable cell
  | raceCleanup race exit => exact False.elim (source.not_race owned.1)

end Effect4.Program.ReleaseCustody.ReplySequencing
