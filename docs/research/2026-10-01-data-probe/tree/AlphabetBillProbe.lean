import Effect4
import Effect4.Laws
import Effect4.Laws.Auto.Exhaustive

/-! Seat TREE, data probe (2026-10-01): the bills of the other alphabets a data push touches,
by the tree's own instrument (definitions only, `Effect4.*`, private definitions not seen):
`Err` (a structured error payload), `Lit` (a signed literal), `NativeAtom` (integer atoms),
`Store.Val` (a new value frame). Printed, not asserted. Scratch, not in the tree. -/

#exhaustive_gate Effect4.Machine.Err
#exhaustive_gate Effect4.Program.Lit
#exhaustive_gate Effect4.Program.NativeAtom
#exhaustive_gate Effect4.Store.Val
