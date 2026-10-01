import Effect4.Laws.Program.Typed.Assembly
import Effect4.Program.Admission
import Effect4.Laws.Program.Typing.Sound

/-!
# Synthesis seat, formal pass (2026-10-01): TY-01 at the merged head

Port of the types seat's `M5CounterProbe.lean` (sha 627b12f2…) and the types verifier's
`verify-CapstoneProbe.lean` §2 to the tree after the merge of `codex/slice6-fixes`
(`0c534f06`, H1's `CodeInert` and H2's `ExitOk`). Changes from the seat's text: the saved
current-code clause is now conditional on `¬ CodeInert`, so the load machine's root is shown
not inert (`load_not_inert`); the stack and leaf read `ExitOk` (whose first conjunct is the old
`FitsExit`). The argument is otherwise the seat's.
-/

set_option autoImplicit false

namespace Research.Synthesis.HeadM5Fits

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Machine.Env (Requirement)

abbrev u : Ty := Ty.normalize (.union .nat .string)
abbrev T : Ty := .prod u .unit

def forkOpts : Supervision.ForkOptions := ⟨false, false, .inherit⟩

def child : NativeEff :=
  .bind (.select (.lit (.bool true)) .bool (.succeed (.lit (.nat 1))) (.succeed (.lit (.str "x"))))
    (.succeed (.app "pair" (.cons (.var 0) (.cons (.lit .unit) .nil))))

def prog3 : NativeEff :=
  .bind (.withFiber (.fork child forkOpts))
    (.select (.lit (.bool true)) .bool (.succeed (.var 0)) (.succeed (.var 0)))

def src : ProgramSource := { program := prog3, table := [] }
def certT : EffTy := ⟨T, .never, Requirement.empty⟩
def rootTy3 : EffTy := ⟨.fiberOf T.normalize .never, .never, Requirement.empty⟩

theorem prog3_typed : Api.typeOf prog3 [] = some rootTy3 := by decide +kernel
theorem rootTy3_closed : ClosedEff rootTy3 := ⟨by decide +kernel, by decide +kernel⟩
theorem child_cert : effTy (nativeSignature []) [] child = some certT := by decide +kernel
theorem T_not_sub : Ty.sub T T.normalize = false := by decide +kernel
theorem child_at : Node.at_ (.eff prog3) [0, 0, 0] = some (.eff child) := rfl

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

/-- New at the merged head: the loaded root is not inert (no halt, no queued finish, no
published exit), so H1's conditional code clause applies to it. -/
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

/-- M5's obligation at the merged head (`M3bAssembly.typedState_load`), refuted. -/
theorem typedState_load_false :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat),
        Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel)) :=
  fun h => m5_false (h src rootTy3 100 100 prog3_typed rootTy3_closed)

theorem replayR_nil_machine (p : NativeEff) (fuel : Nat) :
    (replayR p fuel []).machine = loadR p fuel fuel := by
  unfold replayR replayEval
  split
  · rfl
  · split
    · rfl
    · rfl

theorem rreachable_load (root : ProgramSource) (fuel : Nat) :
    RReachable root fuel (loadR root.program fuel fuel) :=
  ⟨[], (fun _ h => nomatch h), (replayR_nil_machine root.program fuel).symm⟩

/-- M6's capstone at the merged head (`M6Ledger.typedState_reachable`), refuted at the empty tape. -/
theorem capstone_false :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState),
        Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        RReachable root fuel m → ∃ w, TypedState root rootTy w m) :=
  fun cap => m5_false (cap src rootTy3 100 _ prog3_typed rootTy3_closed (rreachable_load src 100))

#guard (match admitProgram prog3 [] with | .ok _ => true | .error _ => false)

end Research.Synthesis.HeadM5Fits

#print axioms Research.Synthesis.HeadM5Fits.load_not_inert
#print axioms Research.Synthesis.HeadM5Fits.m5_false
#print axioms Research.Synthesis.HeadM5Fits.typedState_load_false
#print axioms Research.Synthesis.HeadM5Fits.capstone_false
