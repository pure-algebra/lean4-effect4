import Effect4.Machine.Timer
import Effect4.Store.Domain.Clock
import Effect4.Laws.Auto.Obligations

/-!
The exact-clock obligations: source statements and pending markers were checked before
proof attempts in docs/research/2026-09-20-m1-evidence/clock/{ClockWanted,TimerWanted}.lean.
The core keeps its small structural proofs; this law-side instrument checks their complete
statement list without importing proof search into the runtime root.
-/

namespace Effect4

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  ClockMillis.ofNat_toNat ClockMillis.toNat_ofNat ClockMillis.toNat_add

namespace Machine.TimerStore
universe u

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  cancel_pending dueMin_first fireNext_none clockStep_finish
attribute [aesop safe forward (rule_sets := [Effect4.Stores])]
  dueMin_none_of_late dueMin_mem dueMin_le dueMin_min fireNext_now fireNext_owed clockStep_owed
attribute [aesop safe apply (rule_sets := [Effect4.Stores])]
  empty_wf empty_quiet sleep_wf cancel_wf fireNext_wf clockStep_wf

end Machine.TimerStore
end Effect4

/-! Decimal transport and the canonical store image. The pending source statements were
checked before the proofs in the clock evidence's decimal and canonical snapshots. -/
namespace Effect4

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  ClockMillis.Decimal.readBytes_digits ClockMillis.Decimal.readChars_core
  ClockMillis.Decimal.readBytes_repr ClockMillis.ofDecimal_toDecimal
  Store.ClockCanonical.ofVal_toVal Store.ClockCanonical.fits
attribute [aesop safe forward (rule_sets := [Effect4.Stores])]
  ClockMillis.ofDecimal_exact Store.ClockCanonical.ofVal_exact

end Effect4
