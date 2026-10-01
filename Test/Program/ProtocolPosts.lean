import Effect4.Laws.Program.Typed.Assembly

/-!
# Test.Program.ProtocolPosts — protocol posts against the machine's answers

`E4-TYPED-CE-010` and `E4-TYPED-CE-013`. A protocol row's postcondition is what `TypedProg`'s
store and fiber arms type a continuation on. Where the post excludes the answer the machine
actually gives, a typed program's next step is untyped (the impossible-post shape the
post-Phase C plan forbids, §5.3, the converse of `E4-SCHED-CE-013`'s `True` posts); where it reads
the wrong column, checked code is refused. Formal pass 2026-10-01: seat PROOFS' probes
`StorePostAdequacy.lean`, `AwaitValuePost.lean`, `CloseScopePost.lean` and its verifier's
`VerifyPosts.lean` and `VerifyAwaitLoad.lean`, ported to the merged tree
(`docs/research/2026-10-01-landing/ports-at-dceae006/`).

* `StoreUnit`: `scopeRemove`, `scopeAdd` (open scope) and `deferredAwaitCleanup` answer `unit`;
  the posts say `bool` (`*_post_excludes`); a typed program's next step is untyped
  (`store_step_leaves_typing`).
* `Memo`: the last observer's `memoRelease` answers the layer scope's handle; the post says
  `unit`.
* `Modify`: `refModify`'s pre admits a cell at any type, its handler answers the old value, the
  post says `nat`; at a `bool` cell no world admits the answer (`adequacy_false_refModify`).
* `Frontier`: the scope rows' pre is `True`; a store frontier answers `unit`
  (`EvaluateR.lean:304`), which `scopeIsClosed`'s post excludes.
* `CloseScope`, `CloseIter`: `Scope.close` and the close walk answer their own exit, `success
  unit` with no finalizer failure; the posts say the closing argument.
* `AwaitValue` (`E4-TYPED-CE-010`): the await-by-value post reads the target's answer column
  where the checker and the machine use the encoded exit; the denoted await code is refused at
  the checked type, and so is the denoted root of the typed corpus's `awaitFiber.value`, so M5's
  load proposition is false there.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Program.ProtocolPosts
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

theorem unit_not_bool : ¬ ∃ b, (Val.unit : Val) = Val.bool b := by
  rintro ⟨b, h⟩
  cases h

/-! ## Three store rows answer `unit` where the post says `bool` -/

namespace StoreUnit

theorem scopeRemove_answer (st : Stores) (scope key : Nat) :
    ∃ st', syncOpStep (.scopeRemove scope key) st = some (st', Val.unit) := ⟨_, rfl⟩

theorem awaitCleanup_answer (st : Stores) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ∃ st', syncOpStep (.deferredAwaitCleanup cell waiter token) st = some (st', Val.unit) :=
  ⟨_, rfl⟩

/-- A store holding one open sequential scope at key 0. -/
def oneScope : Stores :=
  ((syncOpStep (.scopeMake .sequential) Stores.empty).map (·.1)).getD Stores.empty

theorem scopeAdd_open_answer :
    ((syncOpStep (.scopeAdd 0 (.closeChildScope 9)) oneScope).map (·.2)) = some Val.unit := by
  decide +kernel

theorem scopeRemove_post_excludes (w : W) (scope key : Nat)
    (cert : StoreCert (.scopeRemove scope key)) :
    ¬ storePost w (.scopeRemove scope key) cert Val.unit := unit_not_bool

theorem scopeAdd_post_excludes (w : W) (scope : Nat) (fin : FinName)
    (cert : StoreCert (.scopeAdd scope fin)) :
    ¬ storePost w (.scopeAdd scope fin) cert Val.unit := unit_not_bool

theorem awaitCleanup_post_excludes (w : W) (cell : DeferredKey) (waiter : FiberId) (token : Nat)
    (cert : StoreCert (.deferredAwaitCleanup cell waiter token)) :
    ¬ storePost w (.deferredAwaitCleanup cell waiter token) cert Val.unit := unit_not_bool

def natTy : EffTy := EffTy.pure .nat

/-- Answers a string at `unit`, which the machine gives, and a number at every `bool`, which it
never gives. -/
def k : Val → RProgram := fun v =>
  if v = Val.unit then .pure (.success (.str "x")) else .pure (.success (.nat 0))

def code : RProgram := .vis (.inl (.scopeRemove 0 1)) k

theorem admitted (root : ProgramSource) (w : W) : TypedProg root w natTy code := by
  refine TypedProg.store (cert := PUnit.unit) trivial ?_
  intro w' _ ans post
  obtain ⟨b, rfl⟩ := post
  have hk : k (Val.bool b) = .pure (.success (.nat 0)) := by
    unfold k
    rw [if_neg (by intro h; cases h)]
  rw [hk]
  exact TypedProg.pure ⟨trivial, trivial⟩

theorem next_untyped (root : ProgramSource) (w' : W) : ¬ TypedProg root w' natTy (k Val.unit) := by
  intro h
  have hk : k Val.unit = .pure (.success (.str "x")) := by
    unfold k
    rw [if_pos rfl]
  rw [hk] at h
  exact (TypedProg.pure_inv h).1

/-- Together: a typed program whose store step (on any store) leads to an untyped program. -/
theorem store_step_leaves_typing (root : ProgramSource) (w : W) (st : Stores) :
    TypedProg root w natTy code ∧
      ∃ st', syncOpStep (.scopeRemove 0 1) st = some (st', Val.unit) ∧
        ∀ w', ¬ TypedProg root w' natTy (k Val.unit) :=
  ⟨admitted root w, (scopeRemove_answer st 0 1).elim fun st' h => ⟨st', h, next_untyped root⟩⟩

end StoreUnit

/-! ## `memoRelease`: the last release answers the layer scope -/

namespace Memo

/-- A store with one memo map holding one built entry for the layer at `[]` (one observer). -/
def memoStore : Stores :=
  let s1 := (syncOpStep (.memoFork none) Stores.empty).map (·.1) |>.getD Stores.empty
  (syncOpStep (.memoBuild [] ⟨0⟩) s1).map (·.1) |>.getD s1

theorem memoRelease_answers_scope :
    ((syncOpStep (.memoRelease [] ⟨0⟩) memoStore).map (·.2)) = some (Val.scopeHandle 1) := by
  decide +kernel

theorem memoRelease_post_excludes (w : W) (cert : StoreCert (.memoRelease [] ⟨0⟩)) :
    ¬ storePost w (.memoRelease [] ⟨0⟩) cert (Val.scopeHandle 1) := by
  intro h
  cases h

def natTy : EffTy := EffTy.pure .nat

/-- Typed at the post's `unit`; at the handle the machine gives, a string at `nat`. -/
def k : Val → RProgram := fun v =>
  if v = Val.unit then .pure (.success (.nat 0)) else .pure (.success (.str "x"))

def memoCode : RProgram := .vis (.inl (.memoRelease [] ⟨0⟩)) k

theorem memo_admitted (root : ProgramSource) (w : W) : TypedProg root w natTy memoCode := by
  refine TypedProg.store (cert := PUnit.unit) trivial ?_
  intro w' _ ans post
  have hans : ans = Val.unit := post
  subst hans
  have hk : k Val.unit = .pure (.success (.nat 0)) := by
    unfold k
    rw [if_pos rfl]
  rw [hk]
  exact TypedProg.pure ⟨trivial, trivial⟩

theorem memo_next_untyped (root : ProgramSource) (w' : W) :
    ¬ TypedProg root w' natTy (k (Val.scopeHandle 1)) := by
  intro h
  have hk : k (Val.scopeHandle 1) = .pure (.success (.str "x")) := by
    unfold k
    rw [if_neg (by intro e; cases e)]
  rw [hk] at h
  exact (TypedProg.pure_inv h).1

end Memo

/-! ## `refModify`: the pre admits a cell at any type -/

namespace Modify

def boolCellStore : Stores :=
  (syncOpStep (.refMake (.bool true)) Stores.empty).map (·.1) |>.getD Stores.empty

theorem refModify_bool_answer :
    ((syncOpStep (.refModify ⟨0⟩ .incr) boolCellStore).map (·.2)) = some (Val.bool true) := by
  decide +kernel

theorem refModifySome_bool_answer :
    ((syncOpStep (.refModifySome ⟨0⟩ .noChange) boolCellStore).map (·.2)) =
      some (Val.bool true) := by
  decide +kernel

/-- A world declaring cell 0 at `bool`. -/
def wb : W := { initialWorld (EffTy.pure .nat) with Ρ := tableInsert (fun _ => none) ⟨0⟩ .bool }

theorem refModify_pre (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    storePre root wb (.refModify ⟨0⟩ .incr) cert := ⟨.bool, rfl⟩

theorem refModify_post_excludes (w' : W) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    ¬ storePost w' (.refModify ⟨0⟩ .incr) cert (Val.bool true) := by
  rintro ⟨n, h⟩
  cases h

/-- Adequacy at this row, as the pass first proposed it, is false: the pre holds, the handler
answers, and no world admits the answer. -/
theorem adequacy_false_refModify (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    storePre root wb (.refModify ⟨0⟩ .incr) cert ∧
      ((syncOpStep (.refModify ⟨0⟩ .incr) boolCellStore).map (·.2)) = some (Val.bool true) ∧
      ¬ ∃ w', storePost w' (.refModify ⟨0⟩ .incr) cert (Val.bool true) :=
  ⟨refModify_pre root cert, refModify_bool_answer,
    fun ⟨w', h⟩ => refModify_post_excludes w' cert h⟩

theorem refModifySome_post_excludes (w' : W) (cert : StoreCert (.refModifySome ⟨0⟩ .noChange)) :
    ¬ storePost w' (.refModifySome ⟨0⟩ .noChange) cert (Val.bool true) := by
  rintro ⟨n, h⟩
  cases h

end Modify

/-! ## The frontier arm: an unknown scope steps to `none`, answered `unit` -/

namespace Frontier

theorem scopeIsClosed_unknown : syncOpStep (.scopeIsClosed 7) Stores.empty = none := rfl

theorem scopeIsClosed_pre (root : ProgramSource) (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    storePre root w (.scopeIsClosed 7) cert := trivial

theorem scopeIsClosed_post_excludes_unit (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    ¬ storePost w (.scopeIsClosed 7) cert Val.unit := by
  rintro ⟨b, h⟩
  cases h

end Frontier

/-! ## `Scope.close` answers `void`, not the closing exit -/

namespace CloseScope

def failed : ExitV := .failure (Cause.fail (.tag 1))
def closeCode : RProgram := .vis (.inr (.closeScope 0 failed)) Effects.Program.pure

def isPureUnit : Option (Stores × RProgram) → Bool
  | some (_, .pure (.success .unit)) => true
  | _ => false

/-- With no finalizer in the scope, the close program is `pure (success unit)`. -/
theorem close_no_finalizer : isPureUnit (closeScopeR 0 failed true StoreUnit.oneScope) = true := by
  decide +kernel

theorem post_excludes_answer (w' : W) (cert : FiberCert (.closeScope 0 failed)) :
    ¬ fiberPost w' (.closeScope 0 failed) cert (.success .unit) := by
  intro h
  cases h

/-- The denotation's close code with a typed-failure argument is refused at the checker's
`pure unit`, at every world. -/
theorem close_code_refused (root : ProgramSource) (w : W) :
    ¬ TypedProg root w (EffTy.pure .unit) closeCode := by
  intro h
  cases h with
  | fiber _ _ _ _ cert _ next =>
    have hnext := next w (leHost_refl w) failed rfl
    have fits := TypedProg.pure_inv hnext
    have clean := cleanExit_of_never_fits w (EffTy.pure .unit) (Cause.fail (.tag 1)) rfl fits.1
    exact Bool.noConfusion clean

end CloseScope

/-! ## The close walk answers its own merged exit -/

namespace CloseIter

def failed : ExitV := .failure (Cause.fail (.tag 1))

def isDoneUnit : IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Bool
  | .done .unit => true
  | _ => false

/-- With no finalizer failure the walk answers `success unit`, whatever exit closed the scope. -/
theorem closeSeq_done (root : NativeEff) :
    isDoneUnit ((interpR root).iterNext (.store (.closeSeq [] failed [])) .unit).2 = true := rfl

theorem closeIter_post_excludes (w : W) (cert : FiberCert (.closeIter .sequential [] failed)) :
    ¬ fiberPost w (.closeIter .sequential [] failed) cert (.success .unit) := by
  intro h
  cases h

end CloseIter

/-! ## The await-by-value post reads the answer column (`E4-TYPED-CE-010`) -/

namespace AwaitValue

def target : FiberId := ⟨1⟩
def checkedTy : EffTy := EffTy.pure (.exitOf .nat .never)

/-- A world whose fiber table declares the target at `pure nat`. -/
def w : W := (initialWorld checkedTy).addFiber target (EffTy.pure .nat)

theorem target_declared : w.Γ target = some (EffTy.pure .nat) := by
  change tableInsert (initialWorld checkedTy).Γ target (EffTy.pure .nat) target = some _
  unfold tableInsert
  rw [if_pos rfl]

/-- The await code exactly as `denoteR` builds it for a target that has not exited. -/
def awaitCode : RProgram := .vis (.inr (.await target .awaitValue)) fun v => .pure (.success v)

def delivered : Val := reifyExitVal (.success (.nat 5))

theorem exitValue_delivers (root : NativeEff) :
    (interpR root).exitValue (.success (.nat 5)) .awaitValue = .pure (.success delivered) := rfl

theorem delivered_fits_checked (w' : W) : Fits w' delivered (.exitOf .nat .never) := trivial

/-- At the world where the target is declared at `pure nat`, the post refuses the delivered
value. (A target declared at an exit, `unknown`, or a union holding one admits it; the defect is
that the post reads the wrong column.) -/
theorem post_excludes_delivered (cert : FiberCert (.await target .awaitValue)) :
    ¬ fiberPost w (.await target .awaitValue) cert delivered := by
  rintro ⟨ty, hty, h⟩
  rw [target_declared] at hty
  cases hty
  exact h

theorem await_code_refused (root : ProgramSource) : ¬ TypedProg root w checkedTy awaitCode := by
  intro h
  cases h with
  | fiber _ _ _ _ cert _ next =>
    have hnext := next w (leHost_refl w) (Val.nat 5) ⟨EffTy.pure .nat, target_declared, trivial⟩
    exact (TypedProg.pure_inv hnext).1

end AwaitValue

/-! ## The program level: M5's load proposition is false for the corpus's `awaitFiber.value`

The program is `Test/Program/TypedCorpus.lean:62`'s `awaitFiber.value`, checked at
`pure (exitOf nat never)`. The denoted root is a guard whose body forks `succeed 1` (certified at
its checked type `pure nat`) and closes with `unguard (success fiber)`; the guard's exit arm
runs a `construction`, whose continuation at the empty completed list is the await. -/

namespace AwaitLoad

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

/-- **The denoted root is not typed at its checked type, at any world where the forked fiber is
fresh.** -/
theorem root_code_refused (w : W) (fresh : w.Γ ⟨1⟩ = none) :
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
        exact (TypedProg.pure_inv hp).1

/-- The loaded root is not inert, so the conditional code clause applies. -/
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
  have hroot : (loadR awaitProg 5 5).fibers =
      [RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx] := rfl
  have hmemb : RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx ∈
      (loadR awaitProg 5 5).fibers := by rw [hroot]; exact List.mem_singleton_self _
  have saved := ((typed.2.1.c0 _ hmemb).c0).c0 rootTy valid.root
  obtain ⟨tin, hcode0, hstack, _⟩ := saved
  have hcode := hcode0 (load_not_inert awaitProg 5 5)
  cases hstack
  exact root_code_refused w fresh hcode

end AwaitLoad

end Test.Program.ProtocolPosts

open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeRemove_post_excludes
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeAdd_post_excludes
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.awaitCleanup_post_excludes
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeAdd_open_answer
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.store_step_leaves_typing
open Test.Program.ProtocolPosts in
#print axioms Memo.memoRelease_answers_scope
open Test.Program.ProtocolPosts in
#print axioms Memo.memoRelease_post_excludes
open Test.Program.ProtocolPosts in
#print axioms Memo.memo_admitted
open Test.Program.ProtocolPosts in
#print axioms Memo.memo_next_untyped
open Test.Program.ProtocolPosts in
#print axioms Modify.adequacy_false_refModify
open Test.Program.ProtocolPosts in
#print axioms Modify.refModifySome_post_excludes
open Test.Program.ProtocolPosts in
#print axioms Frontier.scopeIsClosed_unknown
open Test.Program.ProtocolPosts in
#print axioms Frontier.scopeIsClosed_post_excludes_unit
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_no_finalizer
open Test.Program.ProtocolPosts in
#print axioms CloseScope.post_excludes_answer
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_code_refused
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeSeq_done
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeIter_post_excludes
open Test.Program.ProtocolPosts in
#print axioms AwaitValue.post_excludes_delivered
open Test.Program.ProtocolPosts in
#print axioms AwaitValue.await_code_refused
open Test.Program.ProtocolPosts in
#print axioms AwaitLoad.root_code_refused
open Test.Program.ProtocolPosts in
#print axioms AwaitLoad.typedState_load_false
