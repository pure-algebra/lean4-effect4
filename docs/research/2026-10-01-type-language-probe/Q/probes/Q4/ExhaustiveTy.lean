import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive
import OCaml5
import Tools.TyVectors
import Tools.ProfileJson
import Conform.Lcnf.Cases
import Conform.Effect4.LcnfMl
import Conform.Effect4.LcnfSemantics
import Test.Audit.ExhaustiveFixture

/-! Seat Q, Q4 (2026-10-01): the exhaustiveness inventory of `Ty` at the base `bff50631`, the
tree's own instrument (`src/Effect4/Laws/Auto/Exhaustive.lean`, decisions row 61), over the core
and over the three estates outside it. Printed, not asserted (the instrument's own rule); the
counts are read off this file's log by `Q/bin/exhaustive-count.py`. -/

#exhaustive_gate Effect4.Program.Ty
#exhaustive_gate Effect4.Program.Ty under OCaml5
#exhaustive_gate Effect4.Program.Ty under Tools
#exhaustive_gate Effect4.Program.Ty under Conform
#exhaustive_gate Effect4.Program.Ty under Test
#exhaustive_gate Effect4.Store.Val
