import Effect4.Laws.Program.Typed.Assembly
import Effect4.Program.Admission
import Effect4.Laws.Program.Typing.Sound

/-!
# Seat TYPES, formal pass (2026-10-01): M5 is false on a checked, closed, host-free program

Research probe, outside every root; nothing imports it. It reads the tree's own `TypedState`,
`TypedProg`, `Fits`, `loadR`, `denoteR`, the checker and `Api.typeOf`.

The program forks a closed child that joins inside itself (so the child's certificate is forced
and is the raw product `prod (nat | string) unit`), then returns the fiber handle through a
`select` (so the root's checked answer is the canonical form of the fiber type). M5's obligation
`typedState_load` (`Laws/Program/Typed/Assembly.lean:154-156`) claims a typed state exists at
load. It does not: the root's code must be derivable at the root's type, the derivation must
cover the fork's answer at a world declaring the fiber at its certificate, and there the final
exit does not fit (`Fits`'s fiber arm compares in the raw order, which does not distribute).

* `m5_false` (proved): no world types the loaded state, at fuel and compile fuel 100.
* The premises of `typedState_load` hold (proved by kernel evaluation): the program checks at
  `rootTy3`, which is closed.
* RED CONTROL kept as the theorem itself; the positive control is TY-01's amendment (the leaf
  holds when the fiber arm compares in the checker's order: `prog3_leaf_amended` in
  `TypesOrderProbe.lean`).
-/

set_option autoImplicit false

namespace Research.TypesSeat.M5

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Machine.Env (Requirement)

abbrev u : Ty := Ty.normalize (.union .nat .string)
abbrev T : Ty := .prod u .unit

def forkOpts : Supervision.ForkOptions := ⟨false, false, .inherit⟩

/-- `x := if true then 1 else "x"; succeed(pair(x, undefined))`, closed. -/
def child : NativeEff :=
  .bind (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.str "x"))))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))

/-- Fork `child`, then `if true then f else f`. -/
def prog3 : NativeEff :=
  .bind (.withFiber (.fork child forkOpts))
    (.select (.lit (.bool true)) .bool (.succeed (.var 0)) (.succeed (.var 0)))

def src : ProgramSource := { program := prog3, table := [] }

def certT : EffTy := ⟨T, .never, Requirement.empty⟩

def rootTy3 : EffTy := ⟨.fiberOf T.normalize .never, .never, Requirement.empty⟩

/-! ## The premises of M5, by kernel evaluation -/

theorem prog3_typed : Api.typeOf prog3 [] = some rootTy3 := by decide +kernel

theorem rootTy3_closed : ClosedEff rootTy3 := ⟨by decide +kernel, by decide +kernel⟩

theorem child_cert : effTy (nativeSignature []) [] child = some certT := by decide +kernel

theorem T_not_sub : Ty.sub T T.normalize = false := by decide +kernel

theorem child_at : Node.at_ (.eff prog3) [0, 0, 0] = some (.eff child) := rfl

/-! ## The leaf -/

theorem leaf_false (w : Typed.World) (id : FiberId) (hΓ : w.Γ id = some certT) :
    ¬ FitsExit w rootTy3 (.success (Val.fiber id)) := by
  intro h
  rw [fitsExit_success_iff] at h
  change FiberDeclared w id T.normalize .never at h
  obtain ⟨fty, hΓ', ha, _⟩ := h
  rw [hΓ] at hΓ'
  cases hΓ'
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub] at ha'
  exact Bool.noConfusion ha'

/-! ## The fiber inversion the tree does not state -/

theorem fiber_inv {w : Typed.World} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
    (h : TypedProg src w ty (.vis (.inr op) k))
    (hg : ∀ kind, op ≠ .guard_ kind) (hu : ∀ ex, op ≠ .unguard ex)
    (hf : ∀ ex, op ≠ .finishFinalizer ex) (hs : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) :
    ∃ cert : (Ψ_F src).Cert op, (Ψ_F src).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_F src).post w' op cert ans → TypedProg src w' ty (k ans) := by
  cases h with
  | fiber _ _ _ _ cert pre next => exact ⟨cert, pre, next⟩
  | guard _ _ _ _ => exact absurd rfl (hg _)
  | unguard _ => exact absurd rfl (hu _)
  | finishFinalizer _ => exact absurd rfl (hf _)
  | scopeExit _ _ => exact absurd rfl (hs _ _ _)

/-! ## M5 at this program -/

/-- **M5's `typedState_load` is false here (proved).** No world types the loaded state. -/
theorem m5_false : ¬ ∃ w, TypedState src rootTy3 w (loadR prog3 100 100) := by
  rintro ⟨w, hvalid, hok, -⟩
  -- the root fiber's saved frame, at the root's declared type
  have hfib := hok.c0 _ (List.mem_singleton_self _)
  have hsaved := hfib.c0.c0 rootTy3 hvalid.root
  obtain ⟨tin, hcode, hstack, -⟩ := hsaved
  change Contracts.StackAccepts (TypedProg src) FitsExit (frameProtocols src) w tin rootTy3 [] at hstack
  cases hstack
  -- the guard the bind opens
  obtain ⟨mid, hbody, hrun, -⟩ := TypedProg.guard_inv hcode
  -- its body is the fork
  obtain ⟨cert, hpre, hnext⟩ := fiber_inv hbody (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have hpre' : BodyTyped src w (.at_ ((((rootPoint 100).child 0).child 0).child 0)) cert := hpre
  cases hpre' with
  | at_ p ty hpt =>
    obtain ⟨e, env, hat, hcheck, henv⟩ := hpt
    have hlen : env.length = 0 := henv.1
    have henv0 : env = [] := List.eq_nil_of_length_eq_zero hlen
    subst henv0
    have hat' : Node.at_ (.eff prog3) [0, 0, 0] = some (.eff e) := hat
    rw [child_at] at hat'
    cases hat'
    -- the certificate is forced: the child's checked type at the empty environment
    have hty : Conform.Effect4.Typing.HasTy (nativeSignature []) [] child cert :=
      Conform.Effect4.Typing.check_sound _ _ _ _ _ hcheck
    have hcert : cert = certT := by
      have h2 := Conform.Effect4.Typing.effTy_complete _ _ _ _ hty
      rw [child_cert] at h2
      exact (Option.some.inj h2).symm
    subst hcert
    -- a world where the fork answered: fiber 1, declared at the certificate
    have hfresh : w.Γ ⟨1⟩ = none := by
      cases h1 : w.Γ ⟨1⟩ with
      | none => rfl
      | some ty1 =>
        exfalso
        have hin := (hvalid.fibers ⟨1⟩).mp (by rw [h1]; rfl)
        exact absurd hin (by decide)
    have hext := fork_extension w ⟨1⟩ certT hfresh
    have hle : w.leHost (w.addFiber ⟨1⟩ certT) := ⟨hext.1, (leHost_refl w).2⟩
    have hΓ1 : (w.addFiber ⟨1⟩ certT).Γ ⟨1⟩ = some certT := hext.2.1
    -- the fork's continuation reaches `unguard`: the guard's body exit fits `mid`
    have hb := hnext _ hle (Val.fiber ⟨1⟩) ⟨⟨1⟩, rfl, hΓ1⟩
    have hpay := unguard_payload_inv src _ mid _ _ hb
    -- the guard's saved arm continues with that exit at the root's type
    have hr := hrun _ hle (.success (Val.fiber ⟨1⟩)) ⟨rfl, hpay⟩
    -- the construction the bind's continuation opens
    obtain ⟨_, _, hnext2⟩ := fiber_inv hr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hc := hnext2 _ (leHost_refl _) [] (fun _ hp => nomatch hp)
    -- the select's checkpoint
    obtain ⟨_, _, hnext3⟩ := fiber_inv hc (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hs := hnext3 _ (leHost_refl _) Val.unit trivial
    -- the construction inside the checkpoint
    obtain ⟨_, _, hnext4⟩ := fiber_inv hs (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hleaf := hnext4 _ (leHost_refl _) [] (fun _ hp => nomatch hp)
    -- the arm finishes with the handle itself, at the root's type
    have hexit := TypedProg.pure_inv hleaf
    exact leaf_false _ ⟨1⟩ hΓ1 hexit

/-- **The obligation's own statement, refuted (proved).** `typedState_load`
(`Laws/Program/Typed/Assembly.lean:154-156`) quantifies over every source, type and budget. -/
theorem typedState_load_false :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat),
        Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel)) :=
  fun h => m5_false (h src rootTy3 100 100 prog3_typed rootTy3_closed)

-- tested: admission accepts the program (no host row, no `int`)
#guard (match admitProgram prog3 [] with | .ok _ => true | .error _ => false)

end Research.TypesSeat.M5

#print axioms Research.TypesSeat.M5.prog3_typed
#print axioms Research.TypesSeat.M5.rootTy3_closed
#print axioms Research.TypesSeat.M5.child_cert
#print axioms Research.TypesSeat.M5.leaf_false
#print axioms Research.TypesSeat.M5.fiber_inv
#print axioms Research.TypesSeat.M5.m5_false
#print axioms Research.TypesSeat.M5.typedState_load_false
