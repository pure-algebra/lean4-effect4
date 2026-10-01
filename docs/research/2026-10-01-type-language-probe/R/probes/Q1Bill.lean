import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-!
# Seat R, question 1: the bill of each route, read from the compiled environment

The tree's own instrument (`#exhaustive_gate`, `Laws/Auto/Exhaustive.lean`; decisions row 61),
as the data probe's `ProbeBill.lean` used it at `bc77e97f`, here at `bff50631`. A definition
whose match on the family has no catch-all is one the compiler refuses the day a constructor is
appended. Route (b) appends to `Term`; route (a) appends to `NativeAtom` (and to
`NativeAtom.CustomScheme` for the record rules); stage 2's record discriminant appends to
`Decision`. Proofs are not seen by this instrument; their count is taken separately. Prints only.
-/

#exhaustive_gate Effect4.Program.Term
#exhaustive_gate Effect4.Program.Terms
#exhaustive_gate Effect4.Program.NativeAtom
#exhaustive_gate Effect4.Program.NativeAtom.CustomScheme
#exhaustive_gate Effect4.Program.Decision
