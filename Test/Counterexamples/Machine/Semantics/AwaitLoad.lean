import Effect4.Laws.Program.Typed.Assembly

/-!
# `E4-TYPED-CE-010` against M5 restated over `J`

The typed corpus's `awaitFiber.value` (`Test/Program/TypedCorpus.lean:62`):
`bind (withFiber (fork (succeed 1))) (awaitFiber (var 0) awaitValue)`, checked at
`pure (exitOf nat never)`. The definitions and `root_code_refused` are copied from the synthesis
seat's tracked port (`docs/research/2026-10-01-landing/ports-at-dceae006/HeadAwaitLoad.lean`,
compiled there at `dceae006`; brief amendment 1: copy, do not re-port). The await row's post
admits the target's *answer* column (`nat`), and the await's continuation returns it as the
program's success value, which cannot fit `exitOf nat never` (seat B's post, decisions row 136).

New here: the refutation of `LoadsTyped`, M5's proposition after row 134's split. `J`'s
`LiveCode` types the loaded root (not exited, not running, not a race marker), so the refused
code refutes `J` at every world of the load. The port's H1-shaped `typedState_load_false` and
`load_not_inert` are not restated: `TypedState` no longer types current code.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Counterexamples.Machine.Semantics.AwaitLoad
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
    have payload : ExitOk (w.addFiber ⟨1⟩ (EffTy.pure .nat)) mid (.success (Val.fiber ⟨1⟩)) := by
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
        exact fits.1

theorem one_not_loaded : (⟨1⟩ : FiberId) ∉ (loadR awaitProg 5 5).fibers.map (·.id) := by
  decide

/-- **M5 restated over `J` is false here** (`E4-TYPED-CE-010`): `LoadsTyped` at this program,
fuel 5, the empty row table. -/
theorem loadsTyped_false : ¬ LoadsTyped (awaitProg : ProgramSource) rootTy 5 5 := by
  intro h
  obtain ⟨w, typed⟩ := h rfl typed_source closed_root
  have valid := typed.typed.1
  have fresh : w.Γ ⟨1⟩ = none := by
    cases hg : w.Γ ⟨1⟩ with
    | none => rfl
    | some t =>
      exact absurd ((valid.fibers ⟨1⟩).mp (by rw [hg]; rfl)) one_not_loaded
  have hroot : (loadR awaitProg 5 5).fibers =
      [RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx] := rfl
  have hmemb : RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx ∈
      (loadR awaitProg 5 5).fibers := by
    rw [hroot]
    exact List.mem_singleton_self _
  obtain ⟨tin, hcode, hstack, _⟩ := typed.code _ hmemb rfl rfl rfl rootTy valid.root
  cases hstack
  exact root_code_refused w fresh hcode

end Test.Counterexamples.Machine.Semantics.AwaitLoad

open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms typed_source
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms code_eq
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms cert_of_bodyTyped
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms root_code_refused
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms one_not_loaded
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms loadsTyped_false
