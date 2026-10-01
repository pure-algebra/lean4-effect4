import Effect4.Laws.Program.Typed.Assembly
import Effect4.Program.Admission
import Effect4.Laws.Program.Typing.Sound

/-!
# E4-TYPED-CE-009: `Fits` compares declared types in the raw order, the checker in the normalized one

The checker compares and joins types in the normalized order (`sub (normalize a) (normalize b)`,
`Ty.join a b = normalize (union a b)`), while the handle arms of `Fits` (`FiberDeclared`,
`RefDeclared`/`Equiv`, `PromiseDeclared`) compare a declaration with raw `Ty.sub`, which does not
distribute a product over a union (formal pass 2026-10-01, types seat TY-01).

The program below is checked, closed, admitted and host-free:

```text
fork(x := if true then 1 else "x"; succeed(pair(x, undefined)));  if true then f else f
```

The child's certificate is forced to the raw product `prod (nat | string) unit`; the root's checked
answer is the canonical form of the fiber's type. At load the root's code must answer the forked
handle at that canonical form, and the raw fiber arm refuses it, so:

* `m5_false`, `typedState_load_false`: M5's `typedState_load` is false (proved);
* `capstone_false`: M6's capstone `typedState_reachable` is false, through the empty tape (proved);
* `not_fits_fiber_normal`, `not_fits_cell_raw`, `not_fits_join`: the three red controls on `Fits`
  itself (proved): a fiber declared at the raw product does not fit the canonical form of its own
  type; a cell declared at the canonical form does not fit the raw spelling; a value that fits
  each arm of a `select` does not fit the joined answer.

Sources: `docs/research/2026-10-01-formal-pass/types/M5CounterProbe.lean` and
`TypesOrderProbe.lean` (types seat), `verify-CapstoneProbe.lean` (its verifier), as ported to the
merged typed state (H1's `CodeInert`, H2's `ExitOk`) by the synthesis seat
(`docs/research/2026-10-01-landing/ports-at-dceae006/HeadM5Fits.lean`).
-/

set_option autoImplicit false

namespace Test.Counterexamples.Machine.Semantics.FitsOrder

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Machine.Env (Requirement)

/-! ## The program and its checked premises -/

/-- `nat | string` as the checker builds it (`Ty.join .nat .string` unfolds to this). -/
abbrev u : Ty := Ty.normalize (.union .nat .string)

/-- A product over a union: what `pair(x, undefined)` types at when `x : nat | string`. -/
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

/-- The child's certificate: the raw product. -/
def certT : EffTy := ⟨T, .never, Requirement.empty⟩

/-- The root's checked type: the canonical form of the fiber's type. -/
def rootTy3 : EffTy := ⟨.fiberOf T.normalize .never, .never, Requirement.empty⟩

theorem prog3_typed : Api.typeOf prog3 [] = some rootTy3 := by decide +kernel

theorem rootTy3_closed : ClosedEff rootTy3 := ⟨by decide +kernel, by decide +kernel⟩

theorem child_cert : effTy (nativeSignature []) [] child = some certT := by decide +kernel

/-- The raw order does not see product distribution: `T` is not below its own normal form. -/
theorem T_not_sub : Ty.sub T T.normalize = false := by decide +kernel

theorem child_at : Node.at_ (.eff prog3) [0, 0, 0] = some (.eff child) := rfl

-- tested: admission accepts the program (no host row, no `int`)
#guard (match admitProgram prog3 [] with | .ok _ => true | .error _ => false)

/-! ## The three red controls on `Fits` -/

/-- The root declared at the raw product, as a fork of `succeed (pair x undefined)` declares it. -/
def rt : EffTy := ⟨T, .never, Requirement.empty⟩

def w0 : Typed.World := initialWorld rt

theorem w0_root : w0.Γ Api.root = some rt :=
  insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root rt

/-- The handle fits its declared (raw) type. -/
theorem fits_fiber_raw : Typed.Fits w0 (Val.fiber Api.root) (.fiberOf T .never) :=
  ⟨rt, w0_root, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Red control.** It does not fit the canonical form of the same type. -/
theorem not_fits_fiber_normal :
    ¬ Typed.Fits w0 (Val.fiber Api.root) (.fiberOf T.normalize .never) := by
  intro h
  change FiberDeclared w0 Api.root T.normalize .never at h
  obtain ⟨fty, hΓ, ha, _⟩ := h
  rw [w0_root] at hΓ
  cases hΓ
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub] at ha'
  exact Bool.noConfusion ha'

/-- A world that declares a cell at the canonical form. -/
def w1 : Typed.World := { initialWorld rt with Ρ := fun _ => some T.normalize }

theorem fits_cell_normal : Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf T.normalize) :=
  ⟨T.normalize, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Red control.** The same cell does not fit the raw spelling of its own declared type. -/
theorem not_fits_cell_raw : ¬ Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf T) := by
  intro h
  change RefDeclared w1 ⟨0⟩ T at h
  obtain ⟨t', hΡ, _, hback⟩ := h
  have ht : t' = T.normalize := (Option.some.inj hΡ).symm
  subst ht
  rw [T_not_sub] at hback
  exact Bool.noConfusion hback

/-- **Red control.** The fiber fits each arm's answer and does not fit their join, which is
what a `select` returning the handle twice types at (`Ty.join a a = normalize a`). -/
theorem not_fits_join :
    ¬ Typed.Fits w0 (Val.fiber Api.root) (Ty.join (.fiberOf T .never) (.fiberOf T .never)) := by
  rw [Ty.join_self]
  exact not_fits_fiber_normal

/-! ## M5 at this program -/

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

/-- An ordinary fiber operation's typing inverts to its certificate, precondition and
continuation (TY-16; landed here locally, `Residual.lean` is seat B's). -/
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

/-- The loaded root is not inert (no halt, no queued finish, no published exit), so H1's
conditional current-code clause applies to it. -/
theorem load_not_inert (p : NativeEff) (fuel compileFuel : Nat) :
    ¬ CodeInert (loadR p fuel compileFuel) [] .root := by
  intro h
  rcases h with hs | hterm
  · exact Bool.noConfusion hs
  · rcases hterm with ⟨_, hmem⟩ | ⟨fb, hfb, _, hex⟩
    · cases hmem
    · change fb ∈ [_] at hfb
      rw [List.mem_singleton] at hfb
      subst hfb
      exact Bool.noConfusion hex

/-- **M5 is false here (proved).** No world types the loaded state: the root's code must answer
the forked handle at the root's canonical type, at a world declaring the fork at its raw
certificate, and the fiber arm refuses that leaf. -/
theorem m5_false : ¬ ∃ w, TypedState src rootTy3 w (loadR prog3 100 100) := by
  rintro ⟨w, hvalid, hok, -⟩
  have hfib := hok.c0 _ (List.mem_singleton_self _)
  have hsaved := hfib.c0.c0 rootTy3 hvalid.root
  obtain ⟨tin, hcode0, hstack, -⟩ := hsaved
  have hcode := hcode0 (load_not_inert prog3 100 100)
  change Contracts.StackAccepts (TypedProg src) ExitOk (frameProtocols src) w tin rootTy3 [] at hstack
  cases hstack
  obtain ⟨mid, hbody, hrun, -⟩ := TypedProg.guard_inv hcode
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
    have hty : Conform.Effect4.Typing.HasTy (nativeSignature []) [] child cert :=
      Conform.Effect4.Typing.check_sound _ _ _ _ _ hcheck
    have hcert : cert = certT := by
      have h2 := Conform.Effect4.Typing.effTy_complete _ _ _ _ hty
      rw [child_cert] at h2
      exact (Option.some.inj h2).symm
    subst hcert
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
    have hb := hnext _ hle (Val.fiber ⟨1⟩) ⟨⟨1⟩, rfl, hΓ1⟩
    have hpay := unguard_payload_inv src _ mid _ _ hb
    have hr := hrun _ hle (.success (Val.fiber ⟨1⟩)) ⟨rfl, hpay⟩
    obtain ⟨_, _, hnext2⟩ := fiber_inv hr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hc := hnext2 _ (leHost_refl _) [] (fun _ hp => nomatch hp)
    obtain ⟨_, _, hnext3⟩ := fiber_inv hc (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hs := hnext3 _ (leHost_refl _) Val.unit trivial
    obtain ⟨_, _, hnext4⟩ := fiber_inv hs (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hleaf := hnext4 _ (leHost_refl _) [] (fun _ hp => nomatch hp)
    have hexit := TypedProg.pure_inv hleaf
    exact leaf_false _ ⟨1⟩ hΓ1 hexit.1

/-- **M5's obligation, refuted (proved).** `M3bAssembly.typedState_load` quantifies over every
source, type and budget. -/
theorem typedState_load_false :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat),
        Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel)) :=
  fun h => m5_false (h src rootTy3 100 100 prog3_typed rootTy3_closed)

/-! ## M6's capstone, through the empty tape -/

/-- Replaying the empty tape leaves the loaded machine as it is. -/
theorem replayR_nil_machine (p : NativeEff) (fuel : Nat) :
    (replayR p fuel []).machine = loadR p fuel fuel := by
  unfold replayR replayEval
  split
  · rfl
  · split
    · rfl
    · rfl

/-- The loaded machine is reachable by the empty tape, which has no host answer. -/
theorem rreachable_load (root : ProgramSource) (fuel : Nat) :
    RReachable root fuel (loadR root.program fuel fuel) :=
  ⟨[], (fun _ h => nomatch h), (replayR_nil_machine root.program fuel).symm⟩

/-- **M6's capstone, refuted (proved).** `M6Ledger.typedState_reachable` at this program and the
empty tape is M5 at equal budgets, which `m5_false` refutes. -/
theorem capstone_false :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState),
        Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        RReachable root fuel m → ∃ w, TypedState root rootTy w m) :=
  fun cap => m5_false (cap src rootTy3 100 _ prog3_typed rootTy3_closed (rreachable_load src 100))

#print axioms prog3_typed
#print axioms rootTy3_closed
#print axioms child_cert
#print axioms T_not_sub
#print axioms child_at
#print axioms w0_root
#print axioms fits_fiber_raw
#print axioms not_fits_fiber_normal
#print axioms fits_cell_normal
#print axioms not_fits_cell_raw
#print axioms not_fits_join
#print axioms leaf_false
#print axioms fiber_inv
#print axioms load_not_inert
#print axioms m5_false
#print axioms typedState_load_false
#print axioms replayR_nil_machine
#print axioms rreachable_load
#print axioms capstone_false

end Test.Counterexamples.Machine.Semantics.FitsOrder
