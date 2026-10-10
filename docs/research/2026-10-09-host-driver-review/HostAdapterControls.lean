import Effect4.Laws.Api.HostDrive
import H9Controls

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace HostAdapterReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote
open Effect4.Run
open HostGeneralizationH9Review
open Test.Run.RunContract (twice)

def adapted : Run × Nat :=
  Run.runWith twice (Reactor.ofHost twice.table host).guardRows 0 "session-A" budget 4
#guard adapted.2 = 2
#guard adapted.1.exit = some (.success (.nat 4))
#guard funded adapted.1 && atRest adapted.1 && hostDriven adapted.1

-- Reader of rows-denotation-driver through the new comodel adapter.
example : hostRun (hostGuard twice.table host) twice.program [] Stores.empty 0 =
    some (.success (.nat 4), (adapted.1.machine.state, adapted.2)) :=
  runWith_host_denotes twice host 0 "session-A" budget 4
    (by decide) (by decide) (by decide) (by decide) (.success (.nat 4)) (by decide)

-- The round trip needs distinct keys: a key lookup otherwise answers the first occurrence.
def duplicateTable : RowTable := twice.table ++ twice.table
#guard !decide ((duplicateTable.map rowKey).Nodup)
def positionHost : Effects.Comodel (RowSig duplicateTable) Nat :=
  ⟨fun op st => some (.success (.nat op.1.val), st + 1)⟩
def second : (RowSig duplicateTable).Op := ⟨⟨1, by decide⟩, .nat 2⟩
#guard (show Option (ExitV × Nat) from
    (reactorHost duplicateTable (Reactor.ofHost duplicateTable positionHost).guardRows).answer second 0) =
  some (.success (.nat 0), 1)
#guard (show Option (ExitV × Nat) from (hostGuard duplicateTable positionHost).answer second 0) =
  some (.success (.nat 1), 1)

#eval (adapted.2, adapted.1.session.applied, decide ((duplicateTable.map rowKey).Nodup))
end HostAdapterReview
