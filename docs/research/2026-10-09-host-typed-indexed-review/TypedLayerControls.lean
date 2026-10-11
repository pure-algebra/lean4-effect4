import Effect4.Laws.Api.HostDrive
import H9Controls

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace TypedLayerReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Run
open HostGeneralizationH9Review (budget)
open Test.Run.RunContract (twice)

-- Control for rows-denotation-driver: first failure changes the lower host's state.
def flaky : Effects.Comodel (RowSig twice.table) Nat where
  answer _ st := if st = 0 then some (.failure Cause.empty, st + 1)
    else some (.success (.nat 7), st + 1)

-- Reader premise at a concrete host, without another reply guard.
theorem flaky_meets : flaky.Meets (externalProtocol twice.table) := by
  intro op st answer next h
  obtain ⟨⟨i, hi⟩, request⟩ := op
  have hi0 : i = 0 := by
    have hi' : i < 1 := hi
    omega
  subst i
  change (if st = 0 then some (.failure Cause.empty, st + 1)
    else some (.success (.nat 7), st + 1)) = some (answer, next) at h
  split at h
  · cases h
    rfl
  · cases h
    rfl

def layered := flaky.through (retry twice.table)
def driven : Run × Nat := Run.runWith twice (Reactor.ofHost twice.table layered).guardRows
  0 "session-A" budget 4

#guard driven.1.exit = some (.success (.nat 7))
#guard driven.2 = 3
#guard driven.1.session.applied = 2
#guard funded driven.1 && atRest driven.1 && hostDriven driven.1
#guard (Run.runWith twice (Reactor.ofHost twice.table flaky).guardRows
  0 "session-A" budget 4).1.exit = some (.failure Cause.empty)

-- Reader: the law consumes the typing and lower-host protocol premises.
example : hostRun layered twice.program [] Stores.empty 0 =
    some (.success (.nat 7), (driven.1.machine.state, driven.2)) :=
  runWith_layer_denotes twice (retry twice.table)
    (retry_typed twice.table (externalProtocol twice.table)) flaky flaky_meets
    0 "session-A" budget 4 (by decide) (by decide) (by decide) (by decide)
    (.success (.nat 7)) (by decide)

-- Reader: the guarded interpretation equals the layered host, under those same premises.
example : hostGuard twice.table layered = layered :=
  hostGuard_through twice.table (retry_typed twice.table (externalProtocol twice.table)) flaky_meets

-- A real table row works without the runtime guard in this finite case.
#guard (Run.runWith twice (Reactor.ofHost twice.table layered)
  0 "session-A" budget 4).1.exit = driven.1.exit
#guard (Run.runWith twice (Reactor.ofHost twice.table layered)
  0 "session-A" budget 4).2 = driven.2

-- Control: global equality of the raw and guarded reactors would be too strong.
-- The reactor accepts any row with this key; its protocol describes the table's actual row.
def otherColumns : Row := { Profile.Scalar.waitRow with answer := .string }
#guard rowKey otherColumns = rowKey Profile.Scalar.waitRow
#guard Reactor.ofHost twice.table layered otherColumns (.nat 2) 0 =
  some (.ofExit (.success (.nat 7)), 2)
#guard (Reactor.ofHost twice.table layered).guardRows otherColumns (.nat 2) 0 = none

example : Reactor.ofHost twice.table layered ≠ (Reactor.ofHost twice.table layered).guardRows := by
  intro h
  have bad := congrArg (fun r => r otherColumns (.nat 2) 0) h
  have hl : Reactor.ofHost twice.table layered otherColumns (.nat 2) 0 =
      some (.ofExit (.success (.nat 7)), 2) := rfl
  have hr : (Reactor.ofHost twice.table layered).guardRows otherColumns (.nat 2) 0 = none := rfl
  rw [hl, hr] at bad
  cases bad

#eval (driven.2, driven.1.session.applied)
end TypedLayerReview
