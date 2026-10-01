import ProbeU.Enum
import Tools.TyVectors

/-! Probe U, question 1: the assignability lane's per-head core (tested): every constructor
but `int` and `var`, by design (`TyVectors.lean:56-60`). -/

open ProbeU

#guard missing Tools.TyVectors.core == [.int, .var]
