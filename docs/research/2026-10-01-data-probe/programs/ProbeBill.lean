import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-! Seat PROGRAMS of the data probe (2026-10-01), probe 3: the bill of an append, read from the
compiled environment at `bc77e97f` with the tree's own instrument (`#exhaustive_gate`,
`Laws/Auto/Exhaustive.lean`; decisions row 61: "read it before appending a constructor").
A definition whose match on the family has no catch-all is one the compiler refuses the day a
constructor is appended. Proofs are not seen by this instrument (its module note says so);
their count is taken by grep in the note. Scratch, not in the tree; prints only. -/

#exhaustive_gate Effect4.Program.Ty
#exhaustive_gate Effect4.Machine.Err
#exhaustive_gate Effect4.Store.Val
#exhaustive_gate Effect4.Program.Lit
#exhaustive_gate Effect4.Program.NativeAtom
