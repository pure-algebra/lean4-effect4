import Effect4.Laws.Program.Typed.Assembly

/-!
# Verifier probe: `typedState_load` against the obligation's own proposition, and how far the
obstruction reaches

Adversarial verifier of seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. Independent of the
seat's files (research files cannot import each other); nothing here copies the seat's proofs.

1. The loaded code of `Ref.make(5)` is literally the `refMake` step followed by returning the
   answer (`rfl`).
2. A general lemma: at every world that is valid for *some* machine, no `TypedProg` types
   "allocate a cell, then return it", at any type, whatever the heap holds. So the obstruction
   is not an artifact of the empty initial heap. The same for a fresh deferred (the seat's open
   question, settled here).
3. No typed state holds a fiber whose current code is that shape, whatever its stack.
4. `typedState_load`'s proposition, read from the declaration exactly as the obligation ledger
   reads it (`Laws/Auto/Obligations.lean` `readGoal`), is refuted; a meta check confirms the
   refuted statement is that proposition, with a red control.
5. Binding a fresh cell is enough: `Ref.make(5).flatMap(r => Ref.get(r))` refutes it too.
6. Green control: the obligation holds for `succeed(1)`.
7. The M6 capstone `typedState_reachable`, and every tape-restricted capstone, are false at
   `Ref.make(5)`: the empty tape reaches the loaded state.
-/

set_option autoImplicit false

namespace Research.Pass.Membership.Verify
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched

abbrev W := Effect4.Program.Typed.World

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
def defProg : NativeEff := .perform .deferredMake (.lit .unit)

/-! ## 1. The loaded code, literally -/

theorem refProg_loaded_code :
    denoteR refProg refProg (rootPoint 20) =
      .vis (.inl (.refMake (.nat 5))) (fun ans => .pure (.success ans)) := rfl

theorem defProg_loaded_code :
    denoteR defProg defProg (rootPoint 20) =
      .vis (.inl .deferredMake) (fun ans => .pure (.success ans)) := rfl

theorem refProg_checks :
    Api.typeOf refProg [] = some (EffTy.pure (.handle NativeOp.refTarget)) := by decide +kernel

theorem defProg_checks :
    Api.typeOf defProg [] = some (EffTy.pure (.handle NativeOp.deferredTarget)) := by decide +kernel

#print axioms refProg_loaded_code
#print axioms defProg_loaded_code
#print axioms refProg_checks
#print axioms defProg_checks

/-! ## 2. Allocate-then-return has no typing at any valid world

The later world declares the fresh key and keeps the stores: it is `leHost`-after `w`, it meets
the allocation's post, and the returned handle's `HandlesLive` asks for a store length the
world does not have. Validity of `w` supplies only the freshness of the key. -/

/-- Declaring a fresh cell without touching the stores is a later world. -/
theorem addRef_later (w : W) (key : RefKey) (cert : Ty) (fresh : w.Ρ key = none) :
    w.leHost (w.addRef w.state key cert) :=
  ⟨⟨⟨fun _ h => h, Stores.le_refl _⟩, table_refl _, table_refl _, insert_extends _ _ _ fresh,
    ⟨fun k ty h => ⟨insert_extends _ _ _ fresh k ty h.1, fun value hv => h.2 value hv⟩,
     fun _ types h => ⟨h.1, fun cell hc comp hcomp =>
       completionOk_extends w (w.addRef w.state key cert) types (insert_extends _ _ _ fresh) rfl
         comp (h.2 cell hc comp hcomp)⟩⟩,
    fun _ => table_refl _⟩, fun _ _ h => h⟩

/-- Declaring a fresh deferred without touching the stores is a later world. -/
theorem addPromise_later (w : W) (key : DeferredKey) (cert : Ty × Ty) (fresh : w.«Π» key = none) :
    w.leHost (w.addPromise w.state key cert) :=
  ⟨⟨⟨fun _ h => h, Stores.le_refl _⟩, table_refl _, insert_extends _ _ _ fresh, table_refl _,
    ⟨fun _ _ h => h,
     fun k types h => ⟨insert_extends _ _ _ fresh k types h.1, fun cell hc comp hcomp =>
       completionOk_extends w (w.addPromise w.state key cert) types (table_refl _) rfl
         comp (h.2 cell hc comp hcomp)⟩⟩,
    fun _ => table_refl _⟩, fun _ _ h => h⟩

/-- At a world valid for any machine, "allocate a cell, return it" has no typing at any type,
whatever the initial value and whatever the heap already holds. -/
theorem refReturn_untypable_valid (root : ProgramSource) {rootTy : EffTy} {w : W} {m : RState}
    (valid : WorldValid rootTy w m) (tin : EffTy) (v : Val) :
    ¬ TypedProg root w tin (.vis (.inl (.refMake v)) (fun ans => .pure (.success ans))) := by
  intro h
  obtain ⟨cert, _, next⟩ := TypedProg.store_inv h
  have fresh := valid_refMake_fresh rootTy w m valid
  have post : (Ψ_S root).post (w.addRef w.state ⟨m.state.refs.length⟩ cert) (.refMake v) cert
      (Val.cell ⟨m.state.refs.length⟩) := ⟨_, rfl, insert_here _ _ _⟩
  have hex := TypedProg.pure_inv (next _ (addRef_later w _ cert fresh) _ post)
  have hlive := (hex.2.1 _ rfl).2.2 (Handle.cell ⟨m.state.refs.length⟩)
    (by rw [Val.keys_cell]; exact List.mem_singleton_self _)
  change m.state.refs.length < w.state.refs.length at hlive
  rw [valid.state] at hlive
  exact Nat.lt_irrefl _ hlive

/-- The same for a fresh deferred. -/
theorem deferredReturn_untypable_valid (root : ProgramSource) {rootTy : EffTy} {w : W}
    {m : RState} (valid : WorldValid rootTy w m) (tin : EffTy) :
    ¬ TypedProg root w tin (.vis (.inl .deferredMake) (fun ans => .pure (.success ans))) := by
  intro h
  obtain ⟨cert, _, next⟩ := TypedProg.store_inv h
  have fresh := valid_deferredMake_fresh rootTy w m valid
  have post : (Ψ_S root).post (w.addPromise w.state ⟨m.state.deferreds.cells.length⟩ cert)
      .deferredMake cert (Val.promise ⟨m.state.deferreds.cells.length⟩) := ⟨_, rfl, insert_here _ _ _⟩
  have hex := TypedProg.pure_inv (next _ (addPromise_later w _ cert fresh) _ post)
  have hlive := (hex.2.1 _ rfl).2.2 (Handle.promise ⟨m.state.deferreds.cells.length⟩)
    (by rw [Val.keys_promise]; exact List.mem_singleton_self _)
  change m.state.deferreds.cells.length < w.state.deferreds.cells.length at hlive
  rw [valid.state] at hlive
  exact Nat.lt_irrefl _ hlive

#print axioms addRef_later
#print axioms addPromise_later
#print axioms refReturn_untypable_valid
#print axioms deferredReturn_untypable_valid

/-! ## 3. No typed state holds a fiber about to allocate and return, whatever its stack -/

theorem declared_of_mem {rootTy : EffTy} {w : W} {m : RState} (valid : WorldValid rootTy w m)
    {f : RFiber} (hmem : f ∈ m.fibers) : ∃ ty, w.Γ f.id = some ty :=
  Option.isSome_iff_exists.mp ((valid.fibers f.id).mpr (List.mem_map_of_mem hmem))

theorem no_typedState_refReturn (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (h : TypedState root rootTy w m) (f : RFiber) (hmem : f ∈ m.fibers) (v : Val)
    (hcur : f.frame.current = .vis (.inl (.refMake v)) (fun ans => .pure (.success ans))) :
    False := by
  obtain ⟨valid, ok, _⟩ := h
  obtain ⟨ty, hty⟩ := declared_of_mem valid hmem
  obtain ⟨tin, hprog, _, _⟩ := (ok.c0 f hmem).c0.c0 ty hty
  rw [hcur] at hprog
  exact refReturn_untypable_valid root valid tin v hprog

theorem no_typedState_deferredReturn (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState)
    (h : TypedState root rootTy w m) (f : RFiber) (hmem : f ∈ m.fibers)
    (hcur : f.frame.current = .vis (.inl .deferredMake) (fun ans => .pure (.success ans))) :
    False := by
  obtain ⟨valid, ok, _⟩ := h
  obtain ⟨ty, hty⟩ := declared_of_mem valid hmem
  obtain ⟨tin, hprog, _, _⟩ := (ok.c0 f hmem).c0.c0 ty hty
  rw [hcur] at hprog
  exact deferredReturn_untypable_valid root valid tin hprog

#print axioms declared_of_mem
#print axioms no_typedState_refReturn
#print axioms no_typedState_deferredReturn

/-! ## 4. The obligation's proposition is refuted, for a Ref and for a Deferred -/

theorem ref_loaded_root : ∃ f, (loadR refProg 20 20).fiber? Api.root = some f ∧
    f.frame.current = denoteR refProg refProg (rootPoint 20) := ⟨_, rfl, rfl⟩

theorem def_loaded_root : ∃ f, (loadR defProg 20 20).fiber? Api.root = some f ∧
    f.frame.current = denoteR defProg defProg (rootPoint 20) := ⟨_, rfl, rfl⟩

/-- `M3bAssembly.typedState_load`'s proposition (`Typed/Assembly.lean:148-150`), quantifiers
included, is false. -/
theorem typedState_load_refuted :
    ¬ ∀ (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat),
      Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel) := by
  intro obligation
  obtain ⟨w, h⟩ := obligation refProg _ 20 20 refProg_checks ⟨rfl, rfl⟩
  obtain ⟨f, hf, hcur⟩ := ref_loaded_root
  exact no_typedState_refReturn _ _ w _ h f (List.mem_of_find?_eq_some hf) (.nat 5)
    (hcur.trans refProg_loaded_code)

/-- The instance at `Deferred.make()` is false too (the seat's open question). -/
theorem typedState_load_refuted_deferred :
    ¬ (Api.typeOf defProg [] = some (EffTy.pure (.handle NativeOp.deferredTarget)) →
      ClosedEff (EffTy.pure (.handle NativeOp.deferredTarget)) →
        ∃ w, TypedState (defProg : ProgramSource) (EffTy.pure (.handle NativeOp.deferredTarget)) w
          (loadR defProg 20 20)) := by
  intro obligation
  obtain ⟨w, h⟩ := obligation defProg_checks ⟨rfl, rfl⟩
  obtain ⟨f, hf, hcur⟩ := def_loaded_root
  exact no_typedState_deferredReturn _ _ w _ h f (List.mem_of_find?_eq_some hf)
    (hcur.trans defProg_loaded_code)

#print axioms ref_loaded_root
#print axioms def_loaded_root
#print axioms typedState_load_refuted
#print axioms typedState_load_refuted_deferred

/-! ## 5. Binding a fresh Ref is enough: nothing needs to return it

`Ref.make(5).flatMap(r => Ref.get(r))` answers a number. Its loaded code is `bind`'s guard
(`DenoteR.lean:604`): the body allocates and then `unguard`s the successful exit of the cell,
and `TypedProg`'s `unguard` arm (`Typed/Residual.lean:208-209`) asks `StrongExit` of that
payload, hence `HandlesLive` of the fresh cell at the later world that declares it without
growing the heap. So the old judgment refutes `typedState_load` for every checked program that
binds the result of `Ref.make`, not only for one that returns the cell. -/

def getProg : NativeEff := .bind (.perform .refMake (.lit (.nat 5))) (.perform .refGet (.var 0))

theorem getProg_checks : Api.typeOf getProg [] = some (EffTy.pure .nat) := by decide +kernel

theorem getProg_loaded_code :
    ∃ k, denoteR getProg getProg (rootPoint 20) = .vis (.inr (.guard_ .onSuccess)) k ∧
      ∃ j, k none = .vis (.inl (.refMake (.nat 5))) j ∧
        ∀ ans, ∃ k2, j ans = .vis (.inr (.unguard (.success ans))) k2 :=
  ⟨_, rfl, _, rfl, fun _ => ⟨_, rfl⟩⟩

/-- At a valid world, allocate-then-unguard the cell has no typing at any type. -/
theorem refUnguard_untypable_valid (root : ProgramSource) {rootTy : EffTy} {w : W} {m : RState}
    (valid : WorldValid rootTy w m) (mid : EffTy) (v : Val) (j : Val → RProgram)
    (hj : ∀ ans, ∃ k2, j ans = .vis (.inr (.unguard (.success ans))) k2) :
    ¬ TypedProg root w mid (.vis (.inl (.refMake v)) j) := by
  intro h
  obtain ⟨cert, _, next⟩ := TypedProg.store_inv h
  have fresh := valid_refMake_fresh rootTy w m valid
  have post : (Ψ_S root).post (w.addRef w.state ⟨m.state.refs.length⟩ cert) (.refMake v) cert
      (Val.cell ⟨m.state.refs.length⟩) := ⟨_, rfl, insert_here _ _ _⟩
  have typed := next _ (addRef_later w _ cert fresh) _ post
  obtain ⟨k2, hk2⟩ := hj (Val.cell ⟨m.state.refs.length⟩)
  rw [hk2] at typed
  have hex := unguard_payload_inv _ _ _ _ _ typed
  have hlive := (hex.2.1 _ rfl).2.2 (Handle.cell ⟨m.state.refs.length⟩)
    (by rw [Val.keys_cell]; exact List.mem_singleton_self _)
  change m.state.refs.length < w.state.refs.length at hlive
  rw [valid.state] at hlive
  exact Nat.lt_irrefl _ hlive

theorem getProg_untypable_valid (root : ProgramSource) {rootTy : EffTy} {w : W} {m : RState}
    (valid : WorldValid rootTy w m) (tin : EffTy) :
    ¬ TypedProg root w tin (denoteR getProg getProg (rootPoint 20)) := by
  intro h
  obtain ⟨k, hk, j, hj, hshape⟩ := getProg_loaded_code
  rw [hk] at h
  obtain ⟨mid, body, _, _⟩ := TypedProg.guard_inv h
  rw [hj] at body
  exact refUnguard_untypable_valid root valid mid (.nat 5) j hshape body

theorem get_loaded_root : ∃ f, (loadR getProg 20 20).fiber? Api.root = some f ∧
    f.frame.current = denoteR getProg getProg (rootPoint 20) := ⟨_, rfl, rfl⟩

/-- `typedState_load` at `Ref.make(5).flatMap(r => Ref.get(r))` is false. -/
theorem typedState_load_refuted_get :
    ¬ (Api.typeOf getProg [] = some (EffTy.pure .nat) → ClosedEff (EffTy.pure .nat) →
        ∃ w, TypedState (getProg : ProgramSource) (EffTy.pure .nat) w (loadR getProg 20 20)) := by
  intro obligation
  obtain ⟨w, valid, ok, _⟩ := obligation getProg_checks ⟨rfl, rfl⟩
  obtain ⟨f, hf, hcur⟩ := get_loaded_root
  have hmem : f ∈ (loadR getProg 20 20).fibers := List.mem_of_find?_eq_some hf
  obtain ⟨ty, hty⟩ := declared_of_mem valid hmem
  obtain ⟨tin, hprog, _, _⟩ := (ok.c0 f hmem).c0.c0 ty hty
  rw [hcur] at hprog
  exact getProg_untypable_valid _ valid tin hprog

#print axioms getProg_checks
#print axioms getProg_loaded_code
#print axioms refUnguard_untypable_valid
#print axioms getProg_untypable_valid
#print axioms get_loaded_root
#print axioms typedState_load_refuted_get

/-! ## 6. Green control: the same obligation holds for a program with no allocation

`succeed(1)` has a typed initial state at the initial world. So `typedState_load` is not false
for every program: the allocation is what separates the refuted instances. This is the first
construction of the generated `RStateOk` for any state (no file in `src/` or `Test/` builds one). -/

def one : NativeEff := .succeed (.lit (.nat 1))

theorem typedState_load_one :
    ∃ w, TypedState (one : ProgramSource) (EffTy.pure .nat) w (loadR one 20 20) := by
  refine ⟨initialWorld (EffTy.pure .nat), initial_world_valid _ one 20 20 ⟨rfl, rfl⟩,
    ⟨?_, ?_, ?_⟩, ?_⟩
  · intro f hf
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    refine ⟨⟨?_⟩, ?_, ?_, ?_, ⟨?_⟩, ?_⟩
    · intro ty hty
      have h0 : tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root (EffTy.pure .nat)
          Api.root = some (EffTy.pure .nat) := insert_here _ _ _
      change tableInsert (fun _ : FiberId => (none : Option EffTy)) Api.root (EffTy.pure .nat)
        Api.root = some ty at hty
      rw [h0] at hty
      cases hty
      refine ⟨EffTy.pure .nat,
        TypedProg.pure (strongExit_success _ _ _ ⟨rfl, trivial, (fun _ mem => nomatch mem)⟩),
        .nil _, ⟨(fun _ h => nomatch h), (fun h => nomatch h)⟩⟩
    · intro p hp
      cases hp
    · intro v0 h
      cases h
    · intro v0 h
      cases h
    · intro v0 hv
      cases hv
    · intro key sv sty hget
      change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
      rw [Env.Context.getV_empty] at hget
      cases hget
  · intro r hr
    cases hr
  · refine ⟨(fun o ho => nomatch ho), (fun i v h => nomatch h), ⟨(fun i v h => nomatch h)⟩,
      ⟨(fun v0 hv => nomatch hv)⟩, (fun v0 hv => nomatch hv), trivial⟩
  · intro f hf token hp
    change f ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst hf
    cases hp

#print axioms typedState_load_one

/-! ## 7. The capstone's own conclusion is false at `Ref.make(5)`

The empty tape reaches the loaded state (`replayEval`'s `[]` arm returns the machine it is
given). So `M6Ledger.typedState_reachable` (`Typed/Assembly.lean:225-227`) is false, and so is
every capstone that restricts the tape's decisions (the lift seat's `RReachableNoAnswer` is the
case `P d := isAnswer d = false`): the empty tape meets every restriction. No derivation of the
capstone can succeed while the value judgment stays `StrongValue`; the lift seat's
`m6_capstone` is a sound implication whose premise `typedState_load` fails here. -/

theorem replay_empty_ref : (replayR refProg 20 []).machine = loadR refProg 20 20 := rfl

theorem typedState_reachable_refuted :
    ¬ ∀ (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState),
      Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        RReachable root fuel m → ∃ w, TypedState root rootTy w m := by
  intro capstone
  obtain ⟨w, h⟩ := capstone refProg _ 20 (loadR refProg 20 20) refProg_checks ⟨rfl, rfl⟩
    ⟨[], replay_empty_ref.symm⟩
  obtain ⟨f, hf, hcur⟩ := ref_loaded_root
  exact no_typedState_refReturn _ _ w _ h f (List.mem_of_find?_eq_some hf) (.nat 5)
    (hcur.trans refProg_loaded_code)

/-- Every tape-restricted capstone, whatever the restriction `P`. -/
theorem restricted_capstone_refuted (P : Api.Decision → Prop) :
    ¬ ∀ (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState),
      Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
        (∃ tape, (∀ d ∈ tape, P d) ∧ m = (replayR root.program fuel tape).machine) →
          ∃ w, TypedState root rootTy w m := by
  intro capstone
  obtain ⟨w, h⟩ := capstone refProg _ 20 (loadR refProg 20 20) refProg_checks ⟨rfl, rfl⟩
    ⟨[], (fun _ hd => nomatch hd), replay_empty_ref.symm⟩
  obtain ⟨f, hf, hcur⟩ := ref_loaded_root
  exact no_typedState_refReturn _ _ w _ h f (List.mem_of_find?_eq_some hf) (.nat 5)
    (hcur.trans refProg_loaded_code)

#print axioms replay_empty_ref
#print axioms typedState_reachable_refuted
#print axioms restricted_capstone_refuted

end Research.Pass.Membership.Verify

/- The refuted statement is exactly the proposition the obligation ledger reads from the
declaration (`readGoal`: strip the binders, take the argument of `ProofGraph.Obligation`). -/
open Lean Meta Elab Command in
#eval show CommandElabM Unit from liftTermElabM do
  let info ← getConstInfo ``Effect4.Program.Typed.M3bAssembly.typedState_load
  let prop ← forallTelescope info.type fun xs body => do
    unless body.isAppOfArity ``ProofGraph.Obligation 1 do throwError "not an obligation"
    mkForallFVars xs body.appArg!
  let refuted ← getConstInfo ``Research.Pass.Membership.Verify.typedState_load_refuted
  unless ← withReducible (isDefEq refuted.type (mkNot prop)) do
    throwError "the refuted statement is not the ledger's proposition"
  logInfo m!"statement check: typedState_load_refuted : ¬ (ledger proposition of M3bAssembly.typedState_load), reducible defeq"
  -- red control: the same check refuses a statement that is only an instance of the proposition
  let inst ← getConstInfo ``Research.Pass.Membership.Verify.typedState_load_refuted_deferred
  if ← withReducible (isDefEq inst.type (mkNot prop)) then
    throwError "control failed: the check accepted an instance statement"
  logInfo m!"red control: the same check refuses typedState_load_refuted_deferred (an instance)"
  -- the declared M6 capstone
  let cinfo ← getConstInfo ``Effect4.Program.Typed.M6Ledger.typedState_reachable
  let cprop ← forallTelescope cinfo.type fun xs body => do
    unless body.isAppOfArity ``ProofGraph.Obligation 1 do throwError "not an obligation"
    mkForallFVars xs body.appArg!
  let crefuted ← getConstInfo ``Research.Pass.Membership.Verify.typedState_reachable_refuted
  unless ← withReducible (isDefEq crefuted.type (mkNot cprop)) do
    throwError "the capstone refutation is not the ledger's proposition"
  logInfo m!"statement check: typedState_reachable_refuted : ¬ (ledger proposition of M6Ledger.typedState_reachable), reducible defeq"
