import Effect4.Laws.Program.Typed.Assembly

/-!
# Verifier of seat PROOFS — G6a at the program level: M5 is false for the corpus's
# `awaitFiber.value` entry

Base `ea5b28b5`. The program is `Test/Program/TypedCorpus.lean:62`'s `awaitFiber.value`:
`bind (withFiber (fork (succeed 1))) (awaitFiber (var 0) awaitValue)`, checked at
`pure (exitOf nat never)`. Seat PROOFS proved the local refusal on a hand-built await code and
left the program-level step as reading. This probe proves it on the denotation itself:
`M3bAssembly.typedState_load`'s proposition is false here at fuel 5.

Route (the denoted root, scouted in `VerifyScout5.lean`): the root is a guard whose body forks
`succeed 1` (certified at its checked type `pure nat`) and closes with `unguard (success
fiber)`; the guard's exit arm runs a `construction`, whose continuation at the empty
completed list is the await. The await row's post admits `nat 5` (the target's *answer*
column), and the await's continuation passes it on as the program's success value, which
cannot fit `exitOf nat never`.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace FormalPass.Proofs.Verify.AwaitLoad
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def n (i : Nat) : Term := .lit (.nat i)
def v (i : Nat) : Term := .var i
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def forked : NativeEff := .withFiber (.fork (.succeed (n 1)) opts)
/-- `Test/Program/TypedCorpus.lean:62`, `awaitFiber.value`. -/
def awaitProg : NativeEff := .bind forked (.awaitFiber (v 0) .awaitValue)
def rootTy : EffTy := EffTy.pure (.exitOf .nat .never)

theorem typed_source : Api.typeOf awaitProg = some rootTy := by rfl'
theorem closed_root : ClosedEff rootTy := ⟨rfl, rfl⟩

def code : RProgram := denoteR awaitProg awaitProg (rootPoint 5)

/-- The root code is a guard; `guardK` reads its continuation. -/
def guardK : RProgram → Option ExitV → RProgram
  | .vis (.inr (.guard_ _)) k => k
  | _ => fun _ => .pure (.success .unit)

theorem code_eq : code = .vis (.inr (.guard_ .onSuccess)) (guardK code) := rfl

theorem node_body : Node.at_ (.eff awaitProg) [0, 0, 0] = some (.eff (Eff.succeed (n 1))) := rfl

theorem check_body :
    Checker.check (nativeSignature []) [] [0, 0, 0] (Eff.succeed (n 1)) = .ok (EffTy.pure .nat) := rfl

/-- The certificate of the fork is the body's checked type. -/
theorem cert_of_bodyTyped (w : W) (cert : EffTy) (p : Point) (hpath : p.path = [0, 0, 0])
    (henv : p.env = []) (h : BodyTyped (awaitProg : ProgramSource) w (.at_ p) cert) :
    cert = EffTy.pure .nat := by
  cases h with
  | at_ _ _ pt =>
    obtain ⟨e, env, hnode, hcheck, hen⟩ := pt
    rw [hpath] at hnode hcheck
    rw [node_body] at hnode
    cases hnode
    have hlen : env.length = 0 := by rw [hen.1, henv]; rfl
    have henv0 : env = [] := List.eq_nil_of_length_eq_zero hlen
    subst henv0
    change Checker.check (nativeSignature []) [] [0, 0, 0] (Eff.succeed (n 1)) = .ok cert at hcheck
    rw [check_body] at hcheck
    cases hcheck
    rfl

/-- **The denoted root is not typed at its checked type, at any valid load world.** -/
theorem root_code_refused (w : W) (fresh : w.Γ ⟨1⟩ = none) :
    ¬ TypedProg (awaitProg : ProgramSource) w rootTy code := by
  intro h
  rw [code_eq] at h
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv h
  -- the guard's body: the fork
  cases body with
  | fiber _ notUnguard _ _ certF preF nextF =>
    have hcert : certF = EffTy.pure .nat := cert_of_bodyTyped w certF _ rfl rfl preF
    subst hcert
    obtain ⟨le, here, _⟩ := fork_extension w ⟨1⟩ (EffTy.pure .nat) fresh
    have ord : w.leHost (w.addFiber ⟨1⟩ (EffTy.pure .nat)) := ⟨le, fun _ _ x => x⟩
    have hf := nextF _ ord (Val.fiber ⟨1⟩) ⟨⟨1⟩, rfl, here⟩
    -- the fork's continuation closes the guard with `unguard (success (fiber 1))`
    have payload : FitsExit (w.addFiber ⟨1⟩ (EffTy.pure .nat)) mid (.success (Val.fiber ⟨1⟩)) := by
      cases hf with
      | fiber _ nu _ _ _ _ _ => exact absurd rfl (nu _)
      | unguard payload => exact payload
    -- the guard's exit arm: the construction, then the await
    have hc := run _ ord (.success (Val.fiber ⟨1⟩)) ⟨rfl, payload⟩
    cases hc with
    | fiber _ _ _ _ certC _ nextC =>
      have ha := nextC _ (leHost_refl _) [] (fun p hp => nomatch hp)
      cases ha with
      | fiber _ _ _ _ certA _ nextA =>
        have hp := nextA _ (leHost_refl _) (Val.nat 5) ⟨EffTy.pure .nat, here, trivial⟩
        have fits := TypedProg.pure_inv hp
        exact fits

theorem one_not_loaded : (⟨1⟩ : FiberId) ∉ (loadR awaitProg 5 5).fibers.map (·.id) := by
  decide

/-- **M5 is false here:** `M3bAssembly.typedState_load`'s proposition at this program, fuel 5. -/
theorem typedState_load_false :
    ¬ (Api.typeOf awaitProg [] = some rootTy → ClosedEff rootTy →
        ∃ w, TypedState (awaitProg : ProgramSource) rootTy w (loadR awaitProg 5 5)) := by
  intro h
  obtain ⟨w, typed⟩ := h typed_source closed_root
  have valid := typed.1
  have fresh : w.Γ ⟨1⟩ = none := by
    cases hg : w.Γ ⟨1⟩ with
    | none => rfl
    | some t =>
      exact absurd ((valid.fibers ⟨1⟩).mp (by rw [hg]; rfl)) one_not_loaded
  -- the loaded root fiber
  have hroot : (loadR awaitProg 5 5).fibers =
      [RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx] := rfl
  have hmemb : RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx ∈
      (loadR awaitProg 5 5).fibers := by rw [hroot]; exact List.mem_singleton_self _
  have saved := ((typed.2.1.c0 _ hmemb).c0).c0 rootTy valid.root
  obtain ⟨tin, hcode, hstack, _⟩ := saved
  cases hstack
  exact root_code_refused w fresh hcode

end FormalPass.Proofs.Verify.AwaitLoad

open FormalPass.Proofs.Verify.AwaitLoad in
#print axioms typed_source
open FormalPass.Proofs.Verify.AwaitLoad in
#print axioms code_eq
open FormalPass.Proofs.Verify.AwaitLoad in
#print axioms cert_of_bodyTyped
open FormalPass.Proofs.Verify.AwaitLoad in
#print axioms root_code_refused
open FormalPass.Proofs.Verify.AwaitLoad in
#print axioms one_not_loaded
open FormalPass.Proofs.Verify.AwaitLoad in
#print axioms typedState_load_false
