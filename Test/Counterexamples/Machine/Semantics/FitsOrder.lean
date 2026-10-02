import Effect4.Laws.Program.Typed.Assembly
import Effect4.Program.Admission
import Effect4.Laws.Program.Typing.Sound
import Test.Counterexamples.Machine.Semantics.H1Shapes

/-!
# E4-TYPED-CE-009: `Fits` compared declared types in the raw order, the checker in the normalized one

The checker compares and joins types in the normalized order (`Ty.subN a b = sub (normalize a)
(normalize b)`, `Ty.join a b = normalize (union a b)`). Before decisions row 137 the handle arms of
`Fits` (`FiberDeclared`, `RefDeclared`/`Equiv`, `PromiseDeclared`) compared a declaration with raw
`Ty.sub`, which does not distribute a product over a union (formal pass 2026-10-01, types seat
TY-01). The program below is checked, closed, admitted and host-free:

```text
fork(x := if true then 1 else "x"; succeed(pair(x, undefined)));  if true then f else f
```

The child's certificate is forced to the raw product `prod (nat | string) unit`; the root's checked
answer is the canonical form of the fiber's type. At load the root's code must answer the forked
handle at that canonical form (`m5_forces_leaf`, proved over the production judgment).

* **Historical controls** (`Reviewed`, local copies of the pre-137 arms, as `ValueMembership.lean`
  keeps its retired judgments): with the raw fiber arm that leaf is false, so M5's
  `typedState_load` and M6's capstone `typedState_reachable` were false (`Reviewed.m5_false`,
  `Reviewed.typedState_load_false`, `Reviewed.capstone_false`), and the old judgment failed its
  three closure laws (`Reviewed.not_fits_fiber_normal`, `Reviewed.not_fits_cell_raw`,
  `Reviewed.not_fits_join`). These were proved against the production judgment at `bb269fde`
  (this battery's first commit) and are restated here over the copies; since seat I2 they read
  M5's and the capstone's propositions over row 134's split (`J = MachineTyped`, `LoadsTyped`,
  `ReachableTyped`), the statements seat C's `RawOrderLoad.lean` refuted before row 137 merged.
* **The repair** (row 137, `Laws/Program/Typed/Membership.lean`): the arms compare in `Ty.subN`.
  The three laws now hold of the production judgment (`fits_fiber_normal`, `fits_cell_raw`,
  `fits_join`), the leaf holds (`leaf_holds`), and the old reading of the leaf is refuted
  (`rawLeaf_false`).
* **Red controls** (`#guard_msgs (error)`): the old refutation proofs no longer close against the
  production judgment.
* **M5's first positive control**: the same program loads into `J`
  (`prog3_loads_typed`, through the loaded code's derivation `prog3_typedF` and
  `machineTyped_load`, which reduces M5 to the loaded code); M5's and the capstone's
  propositions hold there (`loadsTyped`, `capstone_at_load`).

Sources: `docs/research/2026-10-01-formal-pass/types/M5CounterProbe.lean` and
`TypesOrderProbe.lean` (types seat), `verify-CapstoneProbe.lean` and `verify-AmendedFitsProbe.lean`
(its verifier), as ported to the merged typed state by the synthesis seat
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

/-! ## Worlds for the controls -/

/-- The root declared at the raw product, as a fork of `succeed (pair x undefined)` declares it. -/
def rt : EffTy := ⟨T, .never, Requirement.empty⟩

def w0 : Typed.World := initialWorld rt

theorem w0_root : w0.Γ Api.root = some rt :=
  insert_here (fun _ : FiberId => (none : Option EffTy)) Api.root rt

/-- A world that declares a cell at the canonical form. -/
def w1 : Typed.World := { initialWorld rt with Ρ := fun _ => some T.normalize }

/-- `T` and its normal form are one type in the checker's order. -/
theorem T_subN_normal : Ty.subN T T.normalize = true := by
  rw [Ty.subN_normalize_right]
  exact Ty.subN_refl T

theorem normal_subN_T : Ty.subN T.normalize T = true := by
  rw [Ty.subN_normalize_left]
  exact Ty.subN_refl T

/-! ## The judgment before row 137 (historical copy)

The tree's `Fits` at `bb269fde`, with its four declaration arms in the raw order. The context arm
reads the production `ServicesFit`, `Live` and `CauseFits`; no control here reaches them. -/
namespace Reviewed

/-- Invariance as raw `Ty.sub` read it: subtyping both ways. -/
def Equiv (declared t : Ty) : Prop := declared.sub t = true ∧ t.sub declared = true

def RefDeclared (w : Typed.World) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ Equiv t' t

def PromiseDeclared (w : Typed.World) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ Equiv a' a ∧ Equiv e' e

def FiberDeclared (w : Typed.World) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ fty.answer.sub a = true ∧ fty.error.sub e = true

def HandleFits (w : Typed.World) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = NativeOp.refTarget ∧ RefDeclared w ⟨index⟩ .nat
  | some .promise => target = NativeOp.deferredTarget ∧ PromiseDeclared w ⟨index⟩ .nat .nat
  | some .scope => target = Ty.scopeTarget
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

def Fits (w : Typed.World) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w kind index target
    | _ => target = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w ctx.services ∧ Live w v
  | .option a =>
    match v with
    | .none => True
    | .some x => Fits w x a
    | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, Fits w (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, Fits w x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => Fits w x a ∧ Fits w y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => Fits w err e
    | .ctor 1 [val] => Fits w val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => Fits w x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => Fits w x e) c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => Fits w x e) c
    | none => False
  | .fiberOf a e =>
    match v with
    | Value.fiber index => FiberDeclared w ⟨index⟩ a e
    | _ => False
  | .union l r => Fits w v l ∨ Fits w v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t =>
    match v with
    | Value.cell index => RefDeclared w ⟨index⟩ t
    | _ => False
  | .deferredOf a e =>
    match v with
    | Value.promise index => PromiseDeclared w ⟨index⟩ a e
    | _ => False
  | .var _ => False
  | .unknown => Live w v

/-- The handle fits its declared (raw) type. -/
theorem fits_fiber_raw : Fits w0 (Val.fiber Api.root) (.fiberOf T .never) :=
  ⟨rt, w0_root, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Historical red control.** It did not fit the canonical form of the same type. -/
theorem not_fits_fiber_normal : ¬ Fits w0 (Val.fiber Api.root) (.fiberOf T.normalize .never) := by
  intro h
  change FiberDeclared w0 Api.root T.normalize .never at h
  obtain ⟨fty, hΓ, ha, _⟩ := h
  rw [w0_root] at hΓ
  cases hΓ
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub] at ha'
  exact Bool.noConfusion ha'

theorem fits_cell_normal : Fits w1 (Val.cell ⟨0⟩) (.refOf T.normalize) :=
  ⟨T.normalize, rfl, Ty.sub_refl _, Ty.sub_refl _⟩

/-- **Historical red control.** The cell did not fit the raw spelling of its declared type. -/
theorem not_fits_cell_raw : ¬ Fits w1 (Val.cell ⟨0⟩) (.refOf T) := by
  intro h
  change RefDeclared w1 ⟨0⟩ T at h
  obtain ⟨t', hΡ, _, hback⟩ := h
  have ht : t' = T.normalize := (Option.some.inj hΡ).symm
  subst ht
  rw [T_not_sub] at hback
  exact Bool.noConfusion hback

/-- **Historical red control.** The fiber fit each arm's answer and not their join. -/
theorem not_fits_join :
    ¬ Fits w0 (Val.fiber Api.root) (Ty.join (.fiberOf T .never) (.fiberOf T .never)) := by
  rw [Ty.join_self]
  exact not_fits_fiber_normal

end Reviewed

/-! ## The repair: the three laws hold of the production judgment -/

/-- The fiber fits the canonical form of its declared type (was `Reviewed.not_fits_fiber_normal`). -/
theorem fits_fiber_normal : Typed.Fits w0 (Val.fiber Api.root) (.fiberOf T.normalize .never) :=
  ⟨rt, w0_root, T_subN_normal, Ty.subN_refl _⟩

/-- The cell fits the raw spelling of its declared type (was `Reviewed.not_fits_cell_raw`). -/
theorem fits_cell_raw : Typed.Fits w1 (Val.cell ⟨0⟩) (.refOf T) :=
  ⟨T.normalize, rfl, normal_subN_T, T_subN_normal⟩

/-- The fiber fits the join of the two arms' answers (was `Reviewed.not_fits_join`), through the
general join closure. -/
theorem fits_join :
    Typed.Fits w0 (Val.fiber Api.root) (Ty.join (.fiberOf T .never) (.fiberOf T .never)) :=
  fits_join_left w0 _ _ _ ⟨rt, w0_root, Ty.subN_refl _, Ty.subN_refl _⟩

-- Red control: the old refutation no longer closes against the production judgment.
/--
error: Type mismatch
  ha
has type
  rt.answer.subN T.normalize = true
but is expected to have type
  T.sub T.normalize = true
-/
#guard_msgs (error) in
example : ¬ Typed.Fits w0 (Val.fiber Api.root) (.fiberOf T.normalize .never) := by
  intro h
  change FiberDeclared w0 Api.root T.normalize .never at h
  obtain ⟨fty, hΓ, ha, _⟩ := h
  rw [w0_root] at hΓ
  cases hΓ
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub] at ha'
  exact Bool.noConfusion ha'

/-! ## M5 at this program -/

/-- **Historical (H1's clause, before row 134).** The loaded root was not inert (no halt, no
queued finish, no published exit), so H1's conditional current-code clause applied to it. Under
the split, `J`'s `LiveCode` reads the loaded root's code at the three premises `rfl` gives
(not exited, not running, no race marker). -/
theorem load_not_inert (p : NativeEff) (fuel compileFuel : Nat) :
    ¬ H1Shapes.CodeInert (loadR p fuel compileFuel) [] .root := by
  intro h
  rcases h with hs | hterm
  · exact Bool.noConfusion hs
  · rcases hterm with ⟨_, hmem⟩ | ⟨fb, hfb, _, hex⟩
    · cases hmem
    · change fb ∈ [_] at hfb
      rw [List.mem_singleton] at hfb
      subst hfb
      exact Bool.noConfusion hex

/-- **What a typed load forces (proved, production judgment).** Every typed state of the loaded
machine yields a world declaring fiber 1 at the child's raw certificate whose successful exit
with that handle fits the root's canonical type: the root's code opens a guard over the fork, the
fork's certificate is the checker's type of the child, and the select's arm returns the handle. -/
theorem m5_forces_leaf (typed : ∃ w, MachineTyped src rootTy3 w (loadR prog3 100 100)) :
    ∃ w : Typed.World, w.Γ ⟨1⟩ = some certT ∧ FitsExit w rootTy3 (.success (Val.fiber ⟨1⟩)) := by
  obtain ⟨w, typed⟩ := typed
  have hvalid := typed.typed.1
  obtain ⟨tin, hcode, hstack, -⟩ :=
    typed.code _ (List.mem_singleton_self _) rfl rfl rfl rootTy3 hvalid.root
  change HostStack src w _ _ tin rootTy3 [] at hstack
  cases hstack
  obtain ⟨mid, hbody, hrun, -⟩ := TypedProg.guard_inv_of_ne hcode (fun h => nomatch h)
  obtain ⟨cert, hpre, hnext⟩ := TypedProg.fiber_inv hbody (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have hpre' : BodyTyped src w (.at_ ((((rootPoint 100).child 0).child 0).child 0)) cert := hpre
  cases hpre' with
  | at_ p ty hpt =>
    obtain ⟨e, env, hat, hcheck, henv, -⟩ := hpt
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
    obtain ⟨_, _, hnext2⟩ := TypedProg.fiber_inv hr (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hc := hnext2 _ (leHost_refl _) [] (fun _ hp => nomatch hp)
    obtain ⟨_, _, hnext3⟩ := TypedProg.fiber_inv hc (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hs := hnext3 _ (leHost_refl _) Val.unit trivial
    obtain ⟨_, _, hnext4⟩ := TypedProg.fiber_inv hs (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
    have hleaf := hnext4 _ (leHost_refl _) [] (fun _ hp => nomatch hp)
    exact ⟨_, hΓ1, (TypedProg.pure_inv hleaf).1⟩

/-- **The leaf holds under row 137 (proved).** At every world declaring a fiber at the child's
raw certificate, the handle's successful exit fits the root's canonical type. -/
theorem leaf_holds (w : Typed.World) (id : FiberId) (hΓ : w.Γ id = some certT) :
    FitsExit w rootTy3 (.success (Val.fiber id)) :=
  ⟨certT, hΓ, T_subN_normal, Ty.subN_refl _⟩

/-- The leaf as the raw fiber arm read it: the production exit judgment at the leaf implied the
old one, as it did by definition before row 137. -/
def RawLeaf : Prop :=
  ∀ (w : Typed.World) (id : FiberId), FitsExit w rootTy3 (.success (Val.fiber id)) →
    Reviewed.Fits w (Val.fiber id) rootTy3.answer

/-- **The repair took (proved).** The production leaf no longer implies the raw one. -/
theorem rawLeaf_false : ¬ RawLeaf :=
  fun raw => Reviewed.not_fits_fiber_normal (raw w0 Api.root (leaf_holds w0 Api.root w0_root))

namespace Reviewed

theorem leaf_false (w : Typed.World) (id : FiberId) (hΓ : w.Γ id = some certT) :
    ¬ Fits w (Val.fiber id) rootTy3.answer := by
  intro h
  change FiberDeclared w id T.normalize .never at h
  obtain ⟨fty, hΓ', ha, _⟩ := h
  rw [hΓ] at hΓ'
  cases hΓ'
  have ha' : Ty.sub T T.normalize = true := ha
  rw [T_not_sub] at ha'
  exact Bool.noConfusion ha'

/-- **Historical: M5 was false here (proved).** Under the raw fiber arm no world typed the loaded
machine (proved against the production judgment at `bb269fde`, battery commit 1, and by seat C's
`RawOrderLoad.m5_false` over `J` before row 137 merged). -/
theorem m5_false (raw : RawLeaf) : ¬ ∃ w, MachineTyped src rootTy3 w (loadR prog3 100 100) := by
  intro typed
  obtain ⟨w, hΓ1, hexit⟩ := m5_forces_leaf typed
  exact leaf_false w ⟨1⟩ hΓ1 (raw w ⟨1⟩ hexit)

/-- **Historical: M5's proposition was false at this program (proved).** -/
theorem loadsTyped_false (raw : RawLeaf) : ¬ LoadsTyped src rootTy3 100 100 :=
  fun h => m5_false raw (h src.lawful prog3_typed rootTy3_closed rfl)

/-- **Historical: M5's obligation was false (proved).** -/
theorem typedState_load_false (raw : RawLeaf) :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat),
        LoadsTyped root rootTy fuel compileFuel) :=
  fun h => loadsTyped_false raw (h src rootTy3 100 100)

end Reviewed

/-! ## M6's capstone, through the empty tape (`rreachable_load`, `Typed/Assembly.lean`) -/

/-- The capstone's statement contains M5's at equal budgets. -/
theorem capstone_implies_load
    (cap : ∀ (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState),
        ReachableTyped root rootTy fuel m)
    (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) :
    LoadsTyped root rootTy fuel fuel :=
  fun lawful h1 h2 h3 => cap root rootTy fuel _ lawful h1 h2 h3 (rreachable_load root fuel)

/-- **Historical: M6's capstone was false (proved)**, at this program and the empty tape. -/
theorem Reviewed.capstone_false (raw : RawLeaf) :
    ¬ (∀ (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState),
        ReachableTyped root rootTy fuel m) :=
  fun cap => Reviewed.loadsTyped_false raw (capstone_implies_load cap src rootTy3 100)

-- Red control: the old leaf refutation no longer closes against the production judgment.
/--
error: Type mismatch
  ha
has type
  certT.answer.subN T.normalize = true
but is expected to have type
  T.sub T.normalize = true
-/
#guard_msgs (error) in
example (w : Typed.World) (id : FiberId) (hΓ : w.Γ id = some certT) :
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

/-! ## M5's first positive control: the program loads into `J` (row 137)

`machineTyped_load` (`Typed/Assembly.lean`, M5's builder over row 134's split) reduces M5 at a
source to "the loaded code is typed at every world" (every other clause is over an empty list or
the empty context at load). The derivation `prog3_typedF` follows the loaded code: the guard the bind opens, the
fork (its certificate the checker's type of the child, by `check_complete`), the `unguard` of
the handle at the guard's type, then the select's construction, checkpoint and construction, and
the arm's exit, which fits the root's canonical type through `fits_subN`. -/

/-- The guard's intermediate type: the fork's raw answer. -/
def midTy : EffTy := ⟨.fiberOf T .never, .never, Requirement.empty⟩

theorem child_check : Checker.check (nativeSignature []) [] [0, 0, 0] child = .ok certT :=
  Conform.Effect4.Typing.check_complete _ _ _ _
    (Conform.Effect4.Typing.effTy_sound _ _ _ _ child_cert) _

/-- The fork's answer type is below the root's canonical answer in the checker's order. -/
theorem fiber_subN_root : Ty.subN (.fiberOf T .never) rootTy3.answer = true := by
  refine ((Ty.subN_equiv_iff _ _).mpr ?_).1
  show Ty.fiberOf T.normalize Ty.never = Ty.fiberOf T.normalize.normalize Ty.never
  rw [Ty.normalize_idem]

/-- **The loaded code is typed at every world (proved).** -/
theorem prog3_typedF (w : Typed.World) :
    TypedProg src w rootTy3 (denoteR prog3 prog3 (rootPoint 100)) := by
  refine TypedProg.guard midTy ?_ ?_ ?_
  · refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) certT
      (BodyTyped.at_ _ _ ⟨child, [], child_at, child_check, ⟨rfl, fun _ _ _ h => nomatch h⟩,
        fun _ h => nomatch h⟩) ?_
    intro w' _ ans hpost
    obtain ⟨id, rfl, hid⟩ := hpost
    exact TypedProg.unguard ⟨⟨certT, hid, Ty.subN_refl _, Ty.subN_refl _⟩, trivial⟩
  · intro w' _ ex hpost
    cases ex with
    | failure c => exact Bool.noConfusion hpost.1
    | success v =>
      have hv : Typed.Fits w' v (.fiberOf T .never) := hpost.2.1
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial ?_
      intro w2 hle2 _ _
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial ?_
      intro w3 hle3 _ _
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial ?_
      intro w4 hle4 _ _
      have hv4 : Typed.Fits w4 v (.fiberOf T .never) :=
        fits_mono (leHost_trans _ _ _ (leHost_trans _ _ _ hle2 hle3) hle4) hv
      exact TypedProg.pure ⟨fits_subN w4 fiber_subN_root v hv4, trivial⟩
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact strongExit_of_clean w' _ c (cleanExit_of_never w' midTy c rfl hex) hex.2

/-- **M5's first positive control (proved).** The TY-01 program, which refuted M5 and the
capstone under the raw arms, loads into `J` under row 137. -/
theorem prog3_loads_typed : ∃ w, MachineTyped src rootTy3 w (loadR prog3 100 100) :=
  ⟨_, machineTyped_load src rootTy3 100 100 rootTy3_closed rfl (prog3_typedF _)⟩

/-- **The flip of `Reviewed.loadsTyped_false`: M5's proposition holds at this program.** -/
theorem loadsTyped : LoadsTyped src rootTy3 100 100 :=
  fun _ _ closed _ => ⟨_, machineTyped_load src rootTy3 100 100 closed rfl (prog3_typedF _)⟩

/-- **The flip of `Reviewed.capstone_false` at this program: the capstone's proposition holds at
the loaded machine**, which the empty tape reaches. -/
theorem capstone_at_load : ReachableTyped src rootTy3 100 (loadR prog3 100 100) :=
  fun lawful checked closed row _ => loadsTyped lawful checked closed row

/-- And its leaf, read off the typed load. -/
theorem prog3_leaf : ∃ w : Typed.World, w.Γ ⟨1⟩ = some certT ∧
    FitsExit w rootTy3 (.success (Val.fiber ⟨1⟩)) :=
  m5_forces_leaf prog3_loads_typed

#print axioms prog3_typed
#print axioms rootTy3_closed
#print axioms child_cert
#print axioms T_not_sub
#print axioms child_at
#print axioms w0_root
#print axioms T_subN_normal
#print axioms normal_subN_T
#print axioms Reviewed.fits_fiber_raw
#print axioms Reviewed.not_fits_fiber_normal
#print axioms Reviewed.fits_cell_normal
#print axioms Reviewed.not_fits_cell_raw
#print axioms Reviewed.not_fits_join
#print axioms fits_fiber_normal
#print axioms fits_cell_raw
#print axioms fits_join
#print axioms load_not_inert
#print axioms m5_forces_leaf
#print axioms leaf_holds
#print axioms rawLeaf_false
#print axioms Reviewed.leaf_false
#print axioms Reviewed.m5_false
#print axioms Reviewed.loadsTyped_false
#print axioms Reviewed.typedState_load_false
#print axioms capstone_implies_load
#print axioms Reviewed.capstone_false
#print axioms child_check
#print axioms fiber_subN_root
#print axioms prog3_typedF
#print axioms prog3_loads_typed
#print axioms loadsTyped
#print axioms capstone_at_load
#print axioms prog3_leaf
#print axioms Effect4.Program.Typed.machineTyped_load
#print axioms Effect4.Program.Typed.typedState_load_of_code
#print axioms Effect4.Program.Typed.rreachable_load

/-! The repair's own theorems (`Laws/Program/TypeAlgebra.lean`, `Laws/Program/Typed/Membership.lean`). -/
#print axioms Effect4.Program.Ty.subN_refl
#print axioms Effect4.Program.Ty.subN_trans
#print axioms Effect4.Program.Ty.sub_le_subN
#print axioms Effect4.Program.Ty.subN_normalize_left
#print axioms Effect4.Program.Ty.subN_normalize_right
#print axioms Effect4.Program.Ty.subN_equiv_iff
#print axioms Effect4.Program.Ty.ofRaw_eq_iff
#print axioms Effect4.Program.Ty.subN_join_left
#print axioms Effect4.Program.Ty.subN_join_right
#print axioms Effect4.Program.Typed.fits_sub
#print axioms Effect4.Program.Typed.fits_ofMembers
#print axioms Effect4.Program.Typed.fits_members
#print axioms Effect4.Program.Typed.fits_factors
#print axioms Effect4.Program.Typed.fits_normalizeRow
#print axioms Effect4.Program.Typed.fits_prod_iff
#print axioms Effect4.Program.Typed.fits_productMembers
#print axioms Effect4.Program.Typed.causeFits_iff
#print axioms Effect4.Program.Typed.fiberDeclared_normalize
#print axioms Effect4.Program.Typed.equiv_normalize
#print axioms Effect4.Program.Typed.fits_normalize
#print axioms Effect4.Program.Typed.fits_subN
#print axioms Effect4.Program.Typed.fits_join_left
#print axioms Effect4.Program.Typed.fits_join_right
#print axioms Effect4.Program.Typed.fitsExit_subN
#print axioms Effect4.Program.Typed.await_fits
#print axioms Effect4.Program.Typed.fits_mono
#print axioms Effect4.Program.Typed.fits_map
#print axioms Effect4.Program.Typed.fits_live
#print axioms Effect4.Program.Typed.fits_hasTy

end Test.Counterexamples.Machine.Semantics.FitsOrder
