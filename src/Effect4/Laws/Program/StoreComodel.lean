import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Machine.RefKernel

/-!
# Program.StoreComodel: the store handler is a comodel of state on its allocated cells

Formal pass, algebra note A9 (`docs/research/2026-10-01-formal-pass/algebra/note.md` §2.4; probe
`algebra/probes/P4ComodelIteration.lean`, confirmed by its verifier as ALG-09). `storeHandler`
(`Denote.lean`) gives each store operation a co-operation `Stores → Val × Stores`: a comodel of
the store signature (Plotkin and Power 2008, by name), against which `runP` (`DenoteB.lean`) runs
a program. Read against the theory of state (lookup and update; Plotkin and Power 2002, by name),
the handler satisfies, on a cell the heap holds:

* put-get (`put_get`): reading after writing answers the value written;
* get-get (`get_get`, on any cell): two reads answer the same value and leave the stores;
* put-put (`put_put`): the second write wins, as one write would.

On a cell the store never allocated, `refSet` and `refGet` do not step
(`syncOpStep_ref_unallocated`, `Laws/Machine/RefKernel.lean`) and the handler's fallback answers
`Val.unit` (`E4-DEN-CE-002`), so put-get fails there (the red control `put_get_dead_fails`,
`Test/Program/StoreComodel.lean`). The store is a lawful comodel of state on its allocated cells,
which under world validity are exactly the declared cells (`WorldValid.heap`,
`Laws/Program/Typed/Validity.lean`), the only cells a fitting handle names (`RefDeclared`,
`Laws/Program/Typed/Membership.lean`).

Get-put and the commutation of distinct cells are not stated at the handler; their machine forms
are the step-level read-over-write (`refStep_get_after_set`, `Machine/Stores.lean`) and the
arena's non-interference (`peek_poke_other`, `Laws/Machine/Arena.lean`). The handler laws are
owed in full only when a form or an optimization declares a state equation (R10).
-/

set_option autoImplicit false

namespace Effect4.Program.Denote

open Effect4 Effect4.Machine Effect4.Program

/-- One store operation as a program of the store signature. -/
abbrev storeOp (o : SyncOp) : Effects.Program StoreSig Val := Effects.Program.perform (S := StoreSig) o

/-- The co-operation: one store step, with the handler's fallback. -/
theorem runP_storeOp (o : SyncOp) (s : Stores) :
    runP (storeOp o) s = (match syncOpStep o s with
      | some (s', v) => (v, s')
      | none => (Val.unit, s)) := by
  unfold runP
  rw [Effects.interpret_perform]
  rfl

/-- **put-get** on an allocated cell: reading after writing answers the value written. -/
theorem put_get {s : Stores} {c : RefKey} (h : c.index < s.refs.length) (v : Val) :
    runP (storeOp (.refSet c v) >>= fun _ => storeOp (.refGet c)) s =
      (v, { s with refs := s.refs.set c.index v }) := by
  have h' : c.index < ({ s with refs := s.refs.set c.index v } : Stores).refs.length := by
    simp only [List.length_set]
    exact h
  have h1 : runP (storeOp (.refSet c v)) s =
      (Val.cell c, { s with refs := s.refs.set c.index v }) := by
    rw [runP_storeOp, syncOpStep_refSet_allocated h v]
  rw [runP_bind, h1]
  dsimp only
  rw [runP_storeOp, syncOpStep_refGet_allocated h']
  simp only [List.getElem_set_self]

/-- **get-get**: two reads answer the same value and leave the stores, on any cell (an
unallocated one answers the fallback twice). -/
theorem get_get (s : Stores) (c : RefKey) :
    runP (storeOp (.refGet c) >>= fun a => storeOp (.refGet c) >>= fun b => pure (a, b)) s =
      ((match syncOpStep (.refGet c) s with | some (_, v) => v | none => Val.unit,
        match syncOpStep (.refGet c) s with | some (_, v) => v | none => Val.unit), s) := by
  by_cases h : c.index < s.refs.length
  · have h1 : runP (storeOp (.refGet c)) s = (s.refs[c.index]'h, s) := by
      rw [runP_storeOp, syncOpStep_refGet_allocated h]
    rw [runP_bind, h1]
    dsimp only
    rw [runP_bind, h1]
    rw [syncOpStep_refGet_allocated h]
    rfl
  · have h1 : runP (storeOp (.refGet c)) s = (Val.unit, s) := by
      rw [runP_storeOp, (syncOpStep_ref_unallocated h Val.unit).2]
    rw [runP_bind, h1]
    dsimp only
    rw [runP_bind, h1]
    rw [(syncOpStep_ref_unallocated h Val.unit).2]
    rfl

/-- **put-put** on an allocated cell: the second write wins, as one write would. -/
theorem put_put {s : Stores} {c : RefKey} (h : c.index < s.refs.length) (v v' : Val) :
    runP (storeOp (.refSet c v) >>= fun _ => storeOp (.refSet c v')) s =
      runP (storeOp (.refSet c v')) s := by
  have h' : c.index < ({ s with refs := s.refs.set c.index v } : Stores).refs.length := by
    simp only [List.length_set]
    exact h
  have h1 : runP (storeOp (.refSet c v)) s =
      (Val.cell c, { s with refs := s.refs.set c.index v }) := by
    rw [runP_storeOp, syncOpStep_refSet_allocated h v]
  rw [runP_bind, h1]
  dsimp only
  rw [runP_storeOp, syncOpStep_refSet_allocated h', runP_storeOp,
    syncOpStep_refSet_allocated h v']
  simp only [List.set_set]

end Effect4.Program.Denote
