import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Typed.Seq
import Test.Program.ProtocolPosts

/-!
# `E4-TYPED-CE-010` against M5 restated over `J`: refuted under the old post, repaired

The typed corpus's `awaitFiber.value` (`Test/Program/TypedCorpus.lean:62`):
`bind (withFiber (fork (succeed 1))) (awaitFiber (var 0) awaitValue)`, checked at
`pure (exitOf nat never)`. Before decisions row 136 the await row's post admitted the target's
*answer* column (`nat`), and the await's continuation returned it as the program's success value,
which cannot fit `exitOf nat never`, so M5 restated over `J` was false here (seat C, `56a63f07`,
from the synthesis seat's port `docs/research/2026-10-01-landing/ports-at-dceae006/HeadAwaitLoad.lean`).
Seat B's post (`exitOf ty.answer ty.error`) repairs it.

**History** (the refutation over the pre-row-136 judgment). `root_code_refused` is seat B's
refutation over its local copy of the old judgment (`OldTypedProg`,
`Test/Program/ProtocolPosts.lean`, section `AwaitLoad`), restated here under seat C's name.
`OldMachineTyped` is `J` with its code clause (`LiveCode`) read over `OldTypedProg`; every other
clause is the current one, so this retains the old post's omission, not a complete
pre-amendment model. `loadsTyped_false` and `capstone_false` refute M5's and the capstone's
propositions as they read under the old post.

**The flip** (the current judgment). `code_typed` types the loaded root at its checked type at
every world: seat E's `seq_typed` sequences the fork with the await (`denoteR`'s bind), the
fork's post declares the child, and the await is typed by the row-136 post when the target is
still running and by `await_fits` when it completed before the continuation was constructed.
`machineTyped_load` then gives `J` at the load (`loadsTyped`: M5's proposition holds at this
program), and the capstone's proposition holds at the loaded machine (`capstone_at_load`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace Test.Counterexamples.Machine.Semantics.AwaitLoad
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
open Test.Program.ProtocolPosts (OldTypedProg)
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

theorem one_not_loaded : (⟨1⟩ : FiberId) ∉ (loadR awaitProg 5 5).fibers.map (·.id) := by
  decide

/-! ## History: the refutation under the old post -/

/-- **Historical: under the old post the denoted root is not typed at its checked type, at any
world where the forked fiber is fresh** (`E4-TYPED-CE-010`'s program-level refutation; seat B's
proof over `OldTypedProg`, `Test.Program.ProtocolPosts.AwaitLoad.root_code_refused`). -/
theorem root_code_refused (w : W) (fresh : w.Γ ⟨1⟩ = none) :
    ¬ OldTypedProg (awaitProg : ProgramSource) w rootTy code :=
  Test.Program.ProtocolPosts.AwaitLoad.root_code_refused w fresh

/-- `J`'s code clause (`LiveCode`) read with the pre-row-136 judgment. -/
def OldLiveCode (root : ProgramSource) (w : W) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, f.exit = none → f.running = false → raceRegistrationR f.frame.current = none →
    ∀ ty, w.Γ f.id = some ty →
      Contracts.SavedOk (OldTypedProg root) ExitOk (frameProtocols root) w ty f.frame

/-- `J` with its code clause over the old judgment; the other clauses are the current ones. -/
structure OldMachineTyped (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) :
    Prop where
  typed : TypedState root rootTy w m
  services : w.serviceTy = root.sig.serviceTy
  code : OldLiveCode root w m
  live : MachineLive m

/-- M5's proposition (`LoadsTyped`) over the old judgment. -/
def OldLoadsTyped (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) : Prop :=
  LawfulSource root → Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    ∃ w, OldMachineTyped root rootTy w (loadR root.program fuel compileFuel)

/-- The capstone's proposition (`ReachableTyped`) over the old judgment. -/
def OldReachableTyped (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) : Prop :=
  LawfulSource root → Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
    RReachable root fuel m → ∃ w, OldMachineTyped root rootTy w m

/-- **Historical: M5 restated over `J` was false here under the old post** (`E4-TYPED-CE-010`):
M5's proposition at this program, fuel 5, the empty row table, with `J`'s code clause over the
old judgment. -/
theorem loadsTyped_false : ¬ OldLoadsTyped (awaitProg : ProgramSource) rootTy 5 5 := by
  intro h
  obtain ⟨w, typed⟩ := h (awaitProg : ProgramSource).lawful typed_source closed_root
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

/-- **Historical: the capstone restated over `J` was false here under the old post**, at the
loaded machine, which the empty tape reaches. -/
theorem capstone_false :
    ¬ OldReachableTyped (awaitProg : ProgramSource) rootTy 5 (loadR awaitProg 5 5) :=
  fun cap => by
    obtain ⟨w, typed⟩ := cap (awaitProg : ProgramSource).lawful typed_source closed_root
      (rreachable_load (awaitProg : ProgramSource) 5)
    exact loadsTyped_false (fun _ _ _ => ⟨w, typed⟩)

-- Red fixture: seat C's refutation script (`56a63f07`, from the port), verbatim, against the
-- current judgment. The await's post now admits the encoded exit (row 136), so the `nat` the old
-- script fed the await's continuation no longer fits the post: the repair is in force where the
-- refutation stood.
/--
error: Application type mismatch: The argument
  trivial
has type
  True
but is expected to have type
  Typed.Fits (World.addFiber w { value := 1 } (EffTy.pure Ty.nat)) (Val.nat 5)
    ((EffTy.pure Ty.nat).answer.exitOf (EffTy.pure Ty.nat).error)
in the application
  ⟨here, trivial⟩
-/
#guard_msgs (error) in
example (w : W) (fresh : w.Γ ⟨1⟩ = none) :
    ¬ TypedProg (awaitProg : ProgramSource) w rootTy code := by
  intro h
  rw [code_eq] at h
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv h
  cases body with
  | fiber _ notUnguard _ _ certF preF nextF =>
    have hcert : certF = EffTy.pure .nat := cert_of_bodyTyped w certF _ rfl rfl preF
    subst hcert
    obtain ⟨le, here, _⟩ := fork_extension w ⟨1⟩ (EffTy.pure .nat) fresh
    have ord : w.leHost (w.addFiber ⟨1⟩ (EffTy.pure .nat)) := ⟨le, fun _ _ x => x⟩
    have hf := nextF _ ord (Val.fiber ⟨1⟩) ⟨⟨1⟩, rfl, here⟩
    have payload : ExitOk (w.addFiber ⟨1⟩ (EffTy.pure .nat)) mid (.success (Val.fiber ⟨1⟩)) := by
      cases hf with
      | fiber _ nu _ _ _ _ _ => exact absurd rfl (nu _)
      | unguard payload => exact payload
    have hc := run _ ord (.success (Val.fiber ⟨1⟩)) ⟨rfl, payload⟩
    cases hc with
    | fiber _ _ _ _ certC _ nextC =>
      have ha := nextC _ (leHost_refl _) [] (fun p hp => nomatch hp)
      cases ha with
      | fiber _ _ _ _ certA _ nextA =>
        have hp := nextA _ (leHost_refl _) (Val.nat 5) ⟨EffTy.pure .nat, here, trivial⟩
        have fits := TypedProg.pure_inv hp
        exact fits.1

/-! ## The flip: the loaded root is typed, so `J` holds at the load -/

/-- `Ty.sub` at `exitOf` from its columns, read off the generated arm lemma as
`sub_prod_mono` reads `prod`'s (`Laws/Program/TypeAlgebra.lean`). -/
theorem sub_exitOf_mono (a b c d : Ty) (hac : Ty.sub a c = true) (hbd : Ty.sub b d = true) :
    Ty.sub (.exitOf a b) (.exitOf c d) = true := by
  rw [Ty.sub_args_exitOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, hac, hbd]

/-- A value at a fiber handle type is a fiber handle declared below the columns. -/
theorem fiber_of_fits {w : W} {x : Val} {a e : Ty} (h : Typed.Fits w x (.fiberOf a e)) :
    ∃ index, x = Value.fiber index ∧ FiberDeclared w ⟨index⟩ a e := by
  simp only [Typed.Fits] at h
  split at h
  · rename_i index
    exact ⟨index, rfl, h⟩
  · exact h.elim

/-- The fork's body: the point `[0, 0, 0]` the fork action names. -/
def forkPoint : Point := (((rootPoint 5).child 0).child 0).child 0

/-- The fork is typed at the handle of its body's checked type, at every world. -/
theorem fork_typed (w : W) :
    TypedProg (awaitProg : ProgramSource) w (EffTy.pure (.fiberOf .nat .never))
      (denoteR awaitProg forked ((rootPoint 5).child 0)) := by
  have unfolded : denoteR awaitProg forked ((rootPoint 5).child 0) =
      denoteAction awaitProg ((rootPoint 5).child 0) :=
    denoteR_withFiber awaitProg _ _ (by decide)
  rw [unfolded]
  show TypedProg _ w _ (.vis (.inr (.fork (.at_ forkPoint) opts _)) fun x => .pure (.success x))
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat)
    (.at_ _ _ ⟨Eff.succeed (n 1), [], node_body, check_body, envTyped_nil w⟩) ?_
  intro w' _ ans post
  obtain ⟨id, rfl, declared⟩ := post
  exact TypedProg.pure ⟨⟨EffTy.pure .nat, declared, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩

/-- The bind's continuation is typed at the root's type on every fiber handle the fork's answer
column admits: the construction reads the completed exits, then the await answers either the
completed target's reified exit (`await_fits`) or, through the row-136 post, the encoded exit the
observer delivers. -/
theorem await_typed (w : W) (x : Val) (hx : Typed.Fits w x (.fiberOf .nat .never)) :
    TypedProg (awaitProg : ProgramSource) w rootTy
      (constructR fun completed =>
        denoteR awaitProg (.awaitFiber (v 0) .awaitValue)
          ({ rootPoint 5 with completed }.childWith 1 x)) := by
  obtain ⟨index, rfl, fty, hfty, ha, he⟩ := fiber_of_fits hx
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () trivial ?_
  intro w' ord completed post
  show TypedProg _ w' rootTy
    (match ({ rootPoint 5 with completed }.childWith 1 (Value.fiber index)).awaitExit
        ⟨index⟩ .awaitValue with
      | some exit => .pure exit
      | none => .vis (.inr (.await ⟨index⟩ .awaitValue)) fun y => .pure (.success y))
  cases found : ({ rootPoint 5 with completed }.childWith 1 (Value.fiber index)).awaitExit
      ⟨index⟩ .awaitValue with
  | some exit =>
    obtain ⟨entry, hfind, hexit⟩ := Option.map_eq_some_iff.mp found
    subst hexit
    have hmem := List.mem_of_find?_eq_some hfind
    have holds := List.find?_some hfind
    have hid : entry.1 = ⟨index⟩ := of_decide_eq_true holds
    obtain ⟨ty, declared, typed⟩ := post entry hmem
    rw [hid] at declared
    exact TypedProg.pure (strongExit_success w' rootTy _
      (await_fits hx ord declared typed.1 Env.Requirement.empty))
  | none =>
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () ?_ ?_
    · show (w'.Γ ⟨index⟩).isSome = true
      rw [ord.1.2.1 _ _ hfty]
      rfl
    · intro w'' ord' ans post'
      obtain ⟨ty, declared, fits⟩ := post'
      rw [(leHost_trans _ _ _ ord ord').1.2.1 _ _ hfty] at declared
      cases declared
      -- row 137: the declaration compares in the checker's order, so the columns are read
      -- normalized (`normalize` keeps `exitOf`) and the answer moves by `fits_subN`
      have below : Ty.subN (.exitOf fty.answer fty.error) rootTy.answer = true :=
        sub_exitOf_mono _ _ _ _ ha he
      exact TypedProg.pure (strongExit_success w'' rootTy ans (fits_subN w'' below ans fits))

/-- **The loaded root is typed at its checked type at every world** (the current judgment). -/
theorem code_typed (w : W) : TypedProg (awaitProg : ProgramSource) w rootTy code := by
  have unfolded : code = (guardR .onSuccess (denoteR awaitProg forked ((rootPoint 5).child 0))).bind
      (seqR fun x => constructR fun completed =>
        denoteR awaitProg (.awaitFiber (v 0) .awaitValue)
          ({ rootPoint 5 with completed }.childWith 1 x)) :=
    denoteR_bind awaitProg forked _ (rootPoint 5) (by decide)
  rw [unfolded]
  exact seq_typed _ (fork_typed w) (fun w' _ x hx => await_typed w' x hx) rfl

/-- **The flip of `loadsTyped_false`: M5's proposition over `J` holds at this program** (fuel 5,
the empty row table), through `machineTyped_load`. -/
theorem loadsTyped : LoadsTyped (awaitProg : ProgramSource) rootTy 5 5 :=
  fun _ _ closed => ⟨_, machineTyped_load _ rootTy 5 5 closed rfl code_typed⟩

/-- **The flip of `capstone_false`: the capstone's proposition holds at the loaded machine.** -/
theorem capstone_at_load :
    ReachableTyped (awaitProg : ProgramSource) rootTy 5 (loadR awaitProg 5 5) :=
  fun lawful checked closed _ => loadsTyped lawful checked closed

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
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms capstone_false
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms sub_exitOf_mono
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms fiber_of_fits
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms fork_typed
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms await_typed
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms code_typed
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms loadsTyped
open Test.Counterexamples.Machine.Semantics.AwaitLoad in
#print axioms capstone_at_load
