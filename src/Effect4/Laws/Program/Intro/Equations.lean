import Effect4.Laws.Program.Intro.Prepare

/-!
# Intro.Equations: the `perform` route by the row's kind

The non-synchronous kinds compile and denote through the shared async dispatcher (DI-61);
the compile arms themselves and the continuation equations are `Agreement.lean`'s.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## The `perform` route -/

section performRoute

variable {p : Point} {k : Nat}

/-- Every non-sync native operation is an async built-in or an external index. -/
theorem compileEff_perform_nonsync (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind ≠ .sync) :
    compileEff (.perform op r) p = asyncRoute op r p := by
  rw [compileEff_perform op r hf]
  cases op with
  | scopeMake strategy => cases strategy <;> exact absurd rfl hkind
  | external i => rfl
  | deferredAwait => rfl
  | sleep => rfl
  | _ => exact absurd rfl hkind

theorem compileEff_perform_async (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind = .async) :
    compileEff (.perform op r) p = asyncRoute op r p :=
  compileEff_perform_nonsync op r hf (by rw [hkind]; exact nofun)

/-- The only native placeholder of program kind is external; it now registers. -/
theorem compileEff_perform_program (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind = .program) :
    compileEff (.perform op r) p = asyncRoute op r p :=
  compileEff_perform_nonsync op r hf (by rw [hkind]; exact nofun)

theorem denoteR_perform_nonsync (root : NativeEff) (op : NativeOp) (r : Term)
    (hpos : p.fuel ≠ 0) (hkind : (NativeOp.row op).kind ≠ .sync) :
    denoteR root (.perform op r) p = denoteAsyncRoute op r p := by
  rw [denoteR_perform root op r hpos]
  cases op with
  | scopeMake strategy => cases strategy <;> exact absurd rfl hkind
  | external i => rfl
  | deferredAwait => rfl
  | sleep => rfl
  | _ => exact absurd rfl hkind

end performRoute

end Effect4.Program.Sched
