/-
Checked region stack-safety receipts. Allowed union: propext, Quot.sound.
No sorryAx, Classical.choice, native_decide, or new axioms are admitted.
Independent implementation review also checks private ownership invariants.
-/

import Effect4.Semantics.RegionSafety

#print axioms Effect4.Flow.runRegionsCause_checked_not_stuck
#print axioms Effect4.Flow.runRegions_checked_not_stuck
#print axioms Effect4.Flow.interpretRegionsWF_checked_not_stuck
