import H9Controls

set_option autoImplicit false
set_option maxRecDepth 8192

namespace HostGeneralizationCheckerReview
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Run
open HostGeneralizationH9Review
open Test.Run.RunContract (twice)

-- Read the checker at a real finished run, with its actual starting and final host states.
def check (host : Effects.Comodel (RowSig twice.table) Nat) (s : Run) (st : Nat) : Option Nat :=
  hostAnsweredCheck twice.table host s.built.program s.budget.fuel (tapeOf s)
    (Api.load s.built.program s.budget.compileFuel) st

#guard check host completed 0 = some 2
#guard check host completed 1 = none

def declining : Effects.Comodel (RowSig twice.table) Nat := ⟨fun _ _ => none⟩
#guard check declining completed 0 = none

-- No applied reply means no reconstructed host transition, even though drive changed state.
#guard check (reactorHost twice.table bad) rejected.1 0 = some 0
#guard (check (reactorHost twice.table bad) rejected.1 0).isSome
#guard check (reactorHost twice.table bad) rejected.1 0 ≠ some rejected.2

-- The separately scoped zero-fuel driver suffix also has no applied answer.
def suffixCheck : Option Nat :=
  hostAnsweredCheck twice.table (reactorHost twice.table echo) twice.program 0
    ((tapeFrom unfunded (Rows.answer unfunded ⟨Api.root, 0⟩
      (.ofExit (.success (.nat 2))))).1.map (·.decision)) unfunded.machine 0
#guard suffixCheck = some 0
#guard suffixCheck ≠ some pending.2

#eval (check host completed 0, check host completed 1,
  check (reactorHost twice.table bad) rejected.1 0, rejected.2, suffixCheck, pending.2)
end HostGeneralizationCheckerReview
