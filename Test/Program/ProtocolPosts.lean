import Effect4.Laws.Program.Typed.Assembly
import Effect4.Laws.Program.Typed.Seq
import Test.Program.H2PartOne

/-!
# Test.Program.ProtocolPosts — protocol posts against the machine's answers

`E4-TYPED-CE-010` and `E4-TYPED-CE-013`, repaired by decisions row 136. A protocol row's post is
what `TypedProg`'s store and fiber arms type a continuation on. Where the post excluded the
answer the machine gives, a typed program's next step was untyped (the impossible-post shape the
post-Phase C plan forbids, §5.3, the converse of `E4-SCHED-CE-013`'s `True` posts); where it read
the wrong column, checked code was refused. Formal pass 2026-10-01: seat PROOFS' probes
`StorePostAdequacy.lean`, `AwaitValuePost.lean`, `CloseScopePost.lean` and its verifier's
`VerifyPosts.lean` and `VerifyAwaitLoad.lean`, ported to the merged tree
(`docs/research/2026-10-01-landing/ports-at-dceae006/`).

The refutations are historical controls over local copies of the pre-amendment rows
(`oldStorePre`, `oldStorePost`, `oldFiberPost`) and of the program judgment built on them
(`OldTypedProg`); the original statements over the then-current judgment are checked at
`eb3ab9a9`. The flips run against the current judgment: each excluded answer is now admitted
(`*_post_admits`), the program whose next step was untyped is now refused, the refused checked
code is now typed, and the handlers' adequacy instances (`Typed/Adequacy.lean`) are the generic
positive controls. `#guard_msgs (error)` fixtures pin the old exclusion proofs failing against
the current posts.

Three red controls found while landing the repair (decisions row 136, for the coordinator):
`completeWith_old_adequacy_false` (the old `deferredCompleteWith` pre admitted a completion no
later world types; the pre now types it), `lone_release_outside_post` (a scope's lone finalizer
answers outside the close-scope post) and `closeSeq_protocol_refused` (the close walk's iterator
protocol cannot carry shape-defect exclusion through reified exits). Decisions row 152 (seat D1,
2026-10-01) repairs the last: membership at an exit type reads `ShapeFree`, so a reified
`badName` failure no longer fits (`badName_refused`), the refutation is history over the old
`exitOf` arm (`old_closeSeq_protocol_refused`), and the walk types at the exact post for clean
finalizers (`closeSeq_protocol`, `closeSeq_protocol_typed`). Decisions row 151 (a″) (seat D4,
2026-10-01) repairs the second: `Scope.close` voids a lone finalizer's value on both machines (the
signed divergence `U-02`; `closeLone` answers `unit`), every finalizer a scope holds is typed at
`⟨unknown, never⟩` by the scope store's typing, the registration pre refuses the failing release
(`release_registration_refused`, the base's admission history over `OldScopeAddPre`), and the
close of a lone typed finalizer is typed at the post (`close_one_typed`, `foreign_close_typed`).
One finding of that landing is open: the close-scope row's pre admits a closing exit the
closed-scope row refuses (`closeScope_pre_admits_unfit_exit`).
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Program.ProtocolPosts
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-! ## The pre-amendment rows and judgment, kept local -/

def oldStorePre (root : ProgramSource) (w : W) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ Fits w initial cert
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refUpdate cell _ | .refGetAndUpdate cell _ | .refUpdateAndGet cell _
  | .refUpdateSome cell _ | .refGetAndUpdateSome cell _ | .refUpdateSomeAndGet cell _
  | .refModify cell _ | .refModifySome cell _ => ∃ ty, w.Ρ cell = some ty
  | .deferredMake => cert.1.closed = true ∧ cert.2.closed = true
  | .deferredIsDone key | .deferredPoll key | .deferredAwaitCleanup key _ _ => (w.«Π» key).isSome = true
  | .deferredCompleteWith key _ => (w.«Π» key).isSome = true
  | .deferredInterruptWith key _ => (w.«Π» key).isSome = true
  | .clockNow | .sleepCancel _ _ => True
  | .scopeMake _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ | .scopeFork _ _ => True
  | .memoFork _ | .memoComplete _ _ _ | .memoRelease _ _ => True
  -- the looked-up layer's own checked error type (decision row 90)
  | .memoGet layer _ => ∃ l lt, Node.at_ (.eff root.program) layer = some (.layer l) ∧
      Checker.checkLayer (nativeSignature root.table) layer l = .ok lt ∧ lt.error = cert
  | .memoBuild _ _ => cert.1.closed = true ∧ cert.2.closed = true

def oldStorePost (w' : W) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refUpdate _ _ | .refUpdateSome _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ | .refGetAndUpdateSome cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refUpdateAndGet cell _ | .refUpdateSomeAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refModify _ _ | .refModifySome _ _ => ∃ n, ans = Val.nat n
  | .deferredMake => ∃ key : DeferredKey, ans = Val.promise key ∧ w'.«Π» key = some cert
  | .deferredIsDone _ => ∃ b, ans = Val.bool b
  | .deferredPoll _ => ∃ b, ans = Val.bool b
  | .deferredCompleteWith _ _ | .deferredInterruptWith _ _ | .deferredAwaitCleanup _ _ _ => ∃ b, ans = Val.bool b
  | .clockNow => ∃ n, ans = Val.nat n
  | .sleepCancel _ _ => ans = Val.unit
  | .scopeMake _ => ∃ sc, ans = Val.scopeHandle sc
  | .scopeAdd _ _ | .scopeRemove _ _ => ∃ b, ans = Val.bool b
  | .scopeIsClosed _ => ∃ b, ans = Val.bool b
  | .scopeFork _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoFork _ => ∃ id, ans = Val.memoMap id
  | .memoGet _ _ => ans = Val.unit ∨ ∃ cell owner, Val.memoHit? ans = some (cell, owner) ∧
      w'.«Π» cell = some (.handle Ty.contextTarget, cert)
  | .memoBuild _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoComplete _ _ _ | .memoRelease _ _ => ans = Val.unit

def oldFiberPost (w' : W) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op with
  | .getId => ∃ (id : FiberId), ans = Val.nat id.value
  | .getContext | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren => Fits w' ans cert
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ | .awaitNewChildren _ => ans = Val.unit
  | .ambientScope => ∃ sc, ans = Val.scopeHandle sc
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ ExitOk w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ Fits w' ans ty.answer
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    ExitOk w' cert ans
  | .unguard ex | .finishFinalizer ex | .closeScope _ ex | .scopeExit _ _ ex | .closeIter _ _ ex => ans = ex
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ ExitOk w' cert ex
  -- a live frontier is never answered (fuel exhaustion is not an exit)
  | .frontier _ _ => False
  -- the completed exits a callback reads, each at its fiber's declared type
  | .construction => ∀ p ∈ ans, ∃ ty, w'.Γ p.1 = some ty ∧ ExitOk w' ty p.2
  | .suspend _ | .refuse _ => True

inductive OldTypedProg (root : ProgramSource) : W → EffTy → RProgram → Prop
  | pure {w : W} {ty : EffTy} {ex : ExitV} (exit : ExitOk w ty ex) :
      OldTypedProg root w ty (.pure ex)
  | store {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : StoreCert op) (pre : oldStorePre root w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, oldStorePost w' op cert ans → OldTypedProg root w' ty (k ans)) :
      OldTypedProg root w ty (.vis (.inl op) k)
  | fiber {w : W} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : FiberCert op) (pre : fiberPre root w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, oldFiberPost w' op cert ans →
        OldTypedProg root w' ty (k ans)) :
      OldTypedProg root w ty (.vis (.inr op) k)
  | guard {w : W} {ty : EffTy} {kind : GuardKind} {k : Option ExitV → RProgram}
      (mid : EffTy) (body : OldTypedProg root w mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, oldFiberPost w' (.guard_ kind) mid (some ex) →
        OldTypedProg root w' ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) :
      OldTypedProg root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : OldTypedProg root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : OldTypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : W} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, OldTypedProg root w' ty (k ans)) :
      OldTypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

theorem OldTypedProg.pure_inv {root : ProgramSource} {w : W} {ty : EffTy} {ex : ExitV}
    (h : OldTypedProg root w ty (.pure ex)) : ExitOk w ty ex := by
  cases h with
  | pure exit => exact exit

theorem OldTypedProg.guard_inv {root : ProgramSource} {w : W} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : OldTypedProg root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, OldTypedProg root w mid (k none) ∧
      ∀ w', w.leHost w' → ∀ ex, oldFiberPost w' (.guard_ kind) mid (some ex) →
        OldTypedProg root w' ty (k (some ex)) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run _ => exact ⟨mid, body, run⟩

theorem unit_not_bool : ¬ ∃ b, (Val.unit : Val) = Val.bool b := by
  rintro ⟨b, h⟩
  cases h

/-! ## Three store rows answered `unit` where the old posts said `bool` -/

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
    ¬ oldStorePost w (.scopeRemove scope key) cert Val.unit := unit_not_bool

theorem scopeAdd_post_excludes (w : W) (scope : Nat) (fin : FinName)
    (cert : StoreCert (.scopeAdd scope fin)) :
    ¬ oldStorePost w (.scopeAdd scope fin) cert Val.unit := unit_not_bool

theorem awaitCleanup_post_excludes (w : W) (cell : DeferredKey) (waiter : FiberId) (token : Nat)
    (cert : StoreCert (.deferredAwaitCleanup cell waiter token)) :
    ¬ oldStorePost w (.deferredAwaitCleanup cell waiter token) cert Val.unit := unit_not_bool

/-- The flips: the current posts admit the store's answers. -/
theorem scopeRemove_post_admits (w : W) (scope key : Nat)
    (cert : StoreCert (.scopeRemove scope key)) :
    storePost w (.scopeRemove scope key) cert Val.unit := rfl

theorem scopeAdd_post_admits (w : W) (scope : Nat) (fin : FinName)
    (cert : StoreCert (.scopeAdd scope fin)) :
    storePost w (.scopeAdd scope fin) cert Val.unit := Or.inl rfl

theorem awaitCleanup_post_admits (w : W) (cell : DeferredKey) (waiter : FiberId) (token : Nat)
    (cert : StoreCert (.deferredAwaitCleanup cell waiter token)) :
    storePost w (.deferredAwaitCleanup cell waiter token) cert Val.unit := rfl

def natTy : EffTy := EffTy.pure .nat

/-- Answers a string at `unit`, which the machine gives, and a number at every `bool`, which it
never gives. -/
def k : Val → RProgram := fun v =>
  if v = Val.unit then .pure (.success (.str "x")) else .pure (.success (.nat 0))

def code : RProgram := .vis (.inl (.scopeRemove 0 1)) k

theorem admitted (root : ProgramSource) (w : W) : OldTypedProg root w natTy code := by
  refine OldTypedProg.store (cert := PUnit.unit) trivial ?_
  intro w' _ ans post
  obtain ⟨b, rfl⟩ := post
  have hk : k (Val.bool b) = .pure (.success (.nat 0)) := by
    unfold k
    rw [if_neg (by intro h; cases h)]
  rw [hk]
  exact OldTypedProg.pure ⟨trivial, trivial⟩

theorem next_untyped (root : ProgramSource) (w' : W) :
    ¬ OldTypedProg root w' natTy (k Val.unit) := by
  intro h
  have hk : k Val.unit = .pure (.success (.str "x")) := by
    unfold k
    rw [if_pos rfl]
  rw [hk] at h
  exact (OldTypedProg.pure_inv h).1

/-- Together, historical: a program the old judgment typed whose store step (on any store) leads
to an untyped program. -/
theorem store_step_leaves_typing (root : ProgramSource) (w : W) (st : Stores) :
    OldTypedProg root w natTy code ∧
      ∃ st', syncOpStep (.scopeRemove 0 1) st = some (st', Val.unit) ∧
        ∀ w', ¬ OldTypedProg root w' natTy (k Val.unit) :=
  ⟨admitted root w, (scopeRemove_answer st 0 1).elim fun st' h => ⟨st', h, next_untyped root⟩⟩

/-- The flip: the current judgment refuses that program, at a world whose store holds scope 0,
because the continuation must answer at `unit`. -/
theorem code_refused (root : ProgramSource) (w : W) : ¬ TypedProg root w natTy code := by
  intro h
  obtain ⟨_, _, next⟩ := TypedProg.store_inv h
  have hk : k Val.unit = .pure (.success (.str "x")) := by
    unfold k
    rw [if_pos rfl]
  have typed := next w (leHost_refl w) Val.unit rfl
  rw [hk] at typed
  exact (TypedProg.pure_inv typed).1

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
    ¬ oldStorePost w (.memoRelease [] ⟨0⟩) cert (Val.scopeHandle 1) := by
  intro h
  cases h

/-- The flip: the current post admits the layer scope's handle, at a world that holds that scope
(decisions row 156: the post carries presence; `memoRelease_implements` supplies it from the
store's memo clause). -/
theorem memoRelease_post_admits (w : W) (cert : StoreCert (.memoRelease [] ⟨0⟩))
    (live : ScopeLive w 1) :
    storePost w (.memoRelease [] ⟨0⟩) cert (Val.scopeHandle 1) :=
  Or.inr (fits_scopeHandle w 1 live)

def natTy : EffTy := EffTy.pure .nat

/-- Typed at the old post's `unit`; at the handle the machine gives, a string at `nat`. -/
def k : Val → RProgram := fun v =>
  if v = Val.unit then .pure (.success (.nat 0)) else .pure (.success (.str "x"))

def memoCode : RProgram := .vis (.inl (.memoRelease [] ⟨0⟩)) k

theorem memo_admitted (root : ProgramSource) (w : W) : OldTypedProg root w natTy memoCode := by
  refine OldTypedProg.store (cert := PUnit.unit) trivial ?_
  intro w' _ ans post
  have hans : ans = Val.unit := post
  subst hans
  have hk : k Val.unit = .pure (.success (.nat 0)) := by
    unfold k
    rw [if_pos rfl]
  rw [hk]
  exact OldTypedProg.pure ⟨trivial, trivial⟩

theorem memo_next_untyped (root : ProgramSource) (w' : W) :
    ¬ OldTypedProg root w' natTy (k (Val.scopeHandle 1)) := by
  intro h
  have hk : k (Val.scopeHandle 1) = .pure (.success (.str "x")) := by
    unfold k
    rw [if_neg (by intro e; cases e)]
  rw [hk] at h
  exact (OldTypedProg.pure_inv h).1

/-- The flip: the current judgment refuses the program, since the handle is now an answer (at a
world that holds the layer scope, which the store's memo clause guarantees after a build). -/
theorem memoCode_refused (root : ProgramSource) (w : W) (live : ScopeLive w 1) :
    ¬ TypedProg root w natTy memoCode := by
  intro h
  obtain ⟨_, _, next⟩ := TypedProg.store_inv h
  have hk : k (Val.scopeHandle 1) = .pure (.success (.str "x")) := by
    unfold k
    rw [if_neg (by intro e; cases e)]
  have typed := next w (leHost_refl w) (Val.scopeHandle 1) (Or.inr (fits_scopeHandle w 1 live))
  rw [hk] at typed
  exact (TypedProg.pure_inv typed).1

end Memo

/-! ## `refModify`: the old pre admitted a cell at any type -/

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
    oldStorePre root wb (.refModify ⟨0⟩ .incr) cert := ⟨.bool, rfl⟩

theorem refModify_post_excludes (w' : W) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    ¬ storePost w' (.refModify ⟨0⟩ .incr) cert (Val.bool true) := by
  rintro ⟨n, h⟩
  cases h

/-- Historical: adequacy at this row under the old pre is false: the pre holds, the handler
answers, and no world admits the answer. -/
theorem adequacy_false_refModify (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    oldStorePre root wb (.refModify ⟨0⟩ .incr) cert ∧
      ((syncOpStep (.refModify ⟨0⟩ .incr) boolCellStore).map (·.2)) = some (Val.bool true) ∧
      ¬ ∃ w', storePost w' (.refModify ⟨0⟩ .incr) cert (Val.bool true) :=
  ⟨refModify_pre root cert, refModify_bool_answer,
    fun ⟨w', h⟩ => refModify_post_excludes w' cert h⟩

theorem refModifySome_post_excludes (w' : W) (cert : StoreCert (.refModifySome ⟨0⟩ .noChange)) :
    ¬ storePost w' (.refModifySome ⟨0⟩ .noChange) cert (Val.bool true) := by
  rintro ⟨n, h⟩
  cases h

/-- The flip on the real answer: at a cell declared at the native row's type the handler answers
the old `nat`, which the post admits (`refModify_implements`, `Typed/Adequacy.lean`, for every
such cell). -/
theorem refModify_post_admits (w' : W) (n : Nat) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    storePost w' (.refModify ⟨0⟩ .incr) cert (Val.nat n) := ⟨n, rfl⟩

/-- The flip: the current pre, at the native row's declared cell type, refuses the `bool` cell. -/
theorem refModify_pre_refuses (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    ¬ storePre root wb (.refModify ⟨0⟩ .incr) cert := by
  intro h
  obtain ⟨t, ht, sub, _⟩ : RefDeclared wb ⟨0⟩ .nat := h
  change tableInsert (fun _ : RefKey => (none : Option Ty)) ⟨0⟩ Ty.bool ⟨0⟩ = some t at ht
  rw [insert_here] at ht
  cases ht
  exact absurd sub (by decide +kernel)

theorem refModifySome_pre_refuses (root : ProgramSource)
    (cert : StoreCert (.refModifySome ⟨0⟩ .noChange)) :
    ¬ storePre root wb (.refModifySome ⟨0⟩ .noChange) cert := by
  intro h
  obtain ⟨t, ht, sub, _⟩ : RefDeclared wb ⟨0⟩ .nat := h
  change tableInsert (fun _ : RefKey => (none : Option Ty)) ⟨0⟩ Ty.bool ⟨0⟩ = some t at ht
  rw [insert_here] at ht
  cases ht
  exact absurd sub (by decide +kernel)

end Modify

/-! ## The frontier arm: an unknown scope steps to `none`, which the evaluator answers `unit` -/

namespace Frontier

theorem scopeIsClosed_unknown : syncOpStep (.scopeIsClosed 7) Stores.empty = none := rfl

theorem scopeIsClosed_pre (root : ProgramSource) (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    oldStorePre root w (.scopeIsClosed 7) cert := trivial

theorem scopeIsClosed_post_excludes_unit (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    ¬ storePost w (.scopeIsClosed 7) cert Val.unit := by
  rintro ⟨b, h⟩
  cases h

/-- The flip on the real answer: a live scope answers its flag, which the post admits. -/
theorem scopeIsClosed_post_admits (w : W) (b : Bool) (cert : StoreCert (.scopeIsClosed 7)) :
    storePost w (.scopeIsClosed 7) cert (Val.bool b) := ⟨b, rfl⟩

/-- The flip: the current pre requires the scope to be live, so at a world whose store holds no
scope 7 the row is refused and the frontier is never reached. -/
theorem scopeIsClosed_pre_refuses (root : ProgramSource) (cert : StoreCert (.scopeIsClosed 7)) :
    ¬ storePre root (initialWorld (EffTy.pure .unit)) (.scopeIsClosed 7) cert := by
  intro h
  change (Stores.empty.scopes.entryAt 7).isSome = true at h
  exact Bool.noConfusion h

end Frontier

/-! ## `Scope.close` answers `void`, not the closing argument -/

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
    ¬ oldFiberPost w' (.closeScope 0 failed) cert (.success .unit) := by
  intro h
  cases h

theorem close_code_refused (root : ProgramSource) (w : W) :
    ¬ OldTypedProg root w (EffTy.pure .unit) closeCode := by
  intro h
  cases h with
  | fiber _ _ _ _ cert _ next =>
    have hnext := next w (leHost_refl w) failed rfl
    have fits := OldTypedProg.pure_inv hnext
    have clean := cleanExit_of_never_fits w (EffTy.pure .unit) (Cause.fail (.tag 1)) rfl fits.1
    exact Bool.noConfusion clean

/-- The flips: the current post admits the close's answer, and the denoted close code is typed at
the checker's `pure unit` at every world whose store holds the scope. Row 139's pre on the
close-scope row (seat I, 2026-10-01) restated the second from "at every world": closing an absent
scope halts (`FiberAction.closeScope`, `Machine/Fibers.lean:1514-1523`), and at such a world the
code is now refused (`close_code_refused_absent`). -/
theorem post_admits_answer (w' : W) (cert : FiberCert (.closeScope 0 failed)) :
    fiberPost w' (.closeScope 0 failed) cert (.success .unit) := ⟨trivial, trivial⟩

theorem close_code_typed (root : ProgramSource) (w : W)
    (live : (w.state.scopes.entryAt 0).isSome = true) :
    TypedProg root w (EffTy.pure .unit) closeCode :=
  TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) () live (fun _ _ _ post => TypedProg.pure post)

/-- Row 139: at a world whose store holds no scope 0 the close code is refused, so the halting
arm `FiberAction.closeScope` is unreachable from typed code. -/
theorem close_code_refused_absent (root : ProgramSource) :
    ¬ TypedProg root (initialWorld (EffTy.pure .unit)) (EffTy.pure .unit) closeCode := by
  intro h
  obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change (Stores.empty.scopes.entryAt 0).isSome = true at pre
  exact Bool.noConfusion pre

/-- The positive instance: over a store holding one open scope at 0 the close code is typed. -/
theorem close_code_typed_live (root : ProgramSource) :
    TypedProg root { initialWorld (EffTy.pure .unit) with state := StoreUnit.oneScope }
      (EffTy.pure .unit) closeCode :=
  close_code_typed root _ (by decide +kernel)

/-- Red control (found landing row 136; history since decisions row 151 (a″)): a scope's lone
finalizer is the close's program, so a scope holding one `release` finalizer that fails answers a
typed failure, outside the close-scope post (`lone_release_outside_post`). The base's `scopeAdd`
pre (scope liveness) admitted registering it (`old_release_registration_admitted`); the pre now
refuses it (`release_registration_refused`) and the scope store's typing refuses it
(`failing_release_untyped`), so no typed state holds it. -/
def releaseStore : Stores :=
  ((syncOpStep (.scopeAdd 0 (.release 7 true)) StoreUnit.oneScope).map (·.1)).getD Stores.empty

def failedSeven : ExitV := .failure (Cause.fail (.tag 7))

def isFailedSeven : Option (Stores × RProgram) → Bool
  | some (_, .pure (.failure c)) => c == Cause.fail (.tag 7)
  | _ => false

/-- Since decisions row 151 (a″) the close runs the lone finalizer and then answers `void`
(`closeScopeR`), and a failure passes through the void: the close's code, its control markers
erased (`eraseControl`), is the release's failure. -/
theorem lone_release_answer :
    isFailedSeven ((closeScopeR 0 failed true releaseStore).map fun r => (r.1, eraseControl r.2)) =
      true := by
  decide +kernel

theorem lone_release_outside_post (w' : W) (cert : FiberCert (.closeScope 0 failed)) :
    ¬ fiberPost w' (.closeScope 0 failed) cert failedSeven := by
  intro h
  have clean := cleanExit_of_never_fits w' (EffTy.pure .unit) (Cause.fail (.tag 7)) rfl h.1
  exact Bool.noConfusion clean

/-- The registration pre before decisions row 151 (a″), kept local: the scope's presence alone
(rows 139 and 156). -/
def OldScopeAddPre (w : W) (scope : Nat) : Prop := ScopeLive w scope

/-- History (the base's `release_registration_admitted`): the old pre admitted registering the
failing release on the open scope. The same script against the current pre is pinned failing at
the foot of this file. -/
theorem old_release_registration_admitted (w : W) (store : w.state = StoreUnit.oneScope) :
    OldScopeAddPre w 0 := by
  change (w.state.scopes.entryAt 0).isSome = true
  rw [store]
  decide +kernel

/-- **The flip** (decisions row 151 (a″)): the registration pre refuses the failing release, whose
program answers a `Fail` that no `never` error column admits (`FinalizerAdmitted`'s `release`
arm). -/
theorem release_registration_refused (root : ProgramSource) (w : W)
    (cert : StoreCert (.scopeAdd 0 (.release 7 true))) :
    ¬ storePre root w (.scopeAdd 0 (.release 7 true)) cert := by
  intro h
  exact Bool.noConfusion h.2

/-- **Red** (decisions row 151 (a″)): the scope store's typing refuses the failing release: at the
closing exit `void`, which fits `Exit<unknown, unknown>`, its program answers `Fail 7`, which no
`never` error column admits. -/
theorem failing_release_untyped (root : ProgramSource) (w : W) :
    ¬ FinalizerTyped root w (.release 7 true) := by
  intro h
  have typed := h w (leHost_refl w) (.success .unit)
    ((fitsExit_success_iff w _ _).mpr (live_of_keys_nil rfl))
  have clean := cleanExit_of_never_fits w ⟨.unknown, .never, Env.Requirement.empty⟩
    (Cause.fail (.tag 7)) rfl (TypedProg.pure_inv typed).1
  exact Bool.noConfusion clean

/-! ### The second refused shape: a lone `acquireRelease` release that answers a value

Receipt B's finding 1 read this shape off the code; proved here. `acquireRelease(succeed 1, (a,
exit) => succeed 5)` is checked (`acq_checked`): the release may answer any value
(`Effect<unknown, never, R2>`, `Program/Checker.lean:201-209`; rc.112 `internal/effect.ts:3973`).
Before decisions row 151 (a″) a scope whose lone finalizer is its capture closed to that
finalizer's program (rc.112 `internal/effect.ts:3795`), which answers the release's value, typed
at no type whose answer column is `unit` (`foreign_untyped`), so `closeScope_installs`' former
`lone` premise failed for it. Since (a″) `Scope.close` voids the value (`closeScopeR`), the
finalizer is typed at `⟨unknown, never⟩` (`foreign_typed_unknown`) and its close at
`⟨unit, never⟩` (`foreign_close_typed`). -/

/-- `acquireRelease(succeed 1, (a, exit) => succeed 5)`. -/
def acqProg : NativeEff := .acquireRelease (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 5)))

/-- The checker admits it, at the scope service's row. -/
theorem acq_checked : Program.typeOfProgram (acqProg : ProgramSource).signature acqProg =
    some ⟨.nat, .never, Env.Requirement.single nativeScopeKey⟩ := by
  decide +kernel

/-- The capture its masked half registers (the acquired value `1`, the empty context). -/
def acqCapture : Capture := { path := [], env := [Val.nat 1], fuel := 10, tape := [], ctx := emptyCtx }

/-- The release's node checks at `nat` in every environment. -/
theorem release_check (env : List Ty) :
    Checker.check (acqProg : ProgramSource).signature env [1]
      (Eff.expandIn acqProg (.succeed (.lit (.nat 5)))) = .ok (EffTy.pure .nat) := rfl

/-- **Red** (proved): the foreign finalizer's program for this capture is typed at no type whose
answer column is `unit`, at any world and closing exit: the masked release answers `5`. -/
theorem foreign_untyped (w : W) (ex : ExitV) (ty : EffTy) (unit : ty.answer = .unit) :
    ¬ TypedProg (acqProg : ProgramSource) w ty (denoteFin (.foreign acqCapture) ex) := by
  intro h
  -- the counted suspend before the release
  obtain ⟨_, _, next1⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have h1 := next1 w (leHost_refl w) Val.unit rfl
  -- the context read, under its guard
  obtain ⟨mid, body, run, _⟩ := TypedProg.guard_inv h1
  obtain ⟨certG, preG, nextG⟩ := TypedProg.fiber_inv body (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  change certG = .handle Ty.contextTarget at preG
  subst preG
  have services : ServicesFit w emptyCtx.services := fun key sv sty hget _ => by
    change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
    rw [Env.Context.getV_empty] at hget
    cases hget
  have live : Live w (Val.context emptyCtx) := live_of_keys_nil rfl
  have hG := nextG w (leHost_refl w) (Val.context emptyCtx)
    (getContext_answers (acqProg : ProgramSource) w emptyCtx services live)
  have hmid := unguard_payload_inv _ _ _ _ _ hG
  have h2 := run w (leHost_refl w) (.success (Val.context emptyCtx)) ⟨rfl, hmid⟩
  -- the captured context set, under its guard
  obtain ⟨mid2, body2, run2, _⟩ := TypedProg.guard_inv h2
  obtain ⟨_, _, next2⟩ := TypedProg.fiber_inv body2 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have hS := next2 w (leHost_refl w) Val.unit rfl
  have hmid2 := unguard_payload_inv _ _ _ _ _ hS
  have h3 := run2 w (leHost_refl w) (.success Val.unit) ⟨rfl, hmid2⟩
  -- the construction query, then the masked release
  obtain ⟨_, _, next3⟩ := TypedProg.fiber_inv h3 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have h4 := next3 w (leHost_refl w) [] (fun _ hp => nomatch hp)
  obtain ⟨cert4, pre4, next4⟩ := TypedProg.fiber_inv h4 (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  cases pre4 with
  | release _ _ _ hp =>
    obtain ⟨e, env, hat, hcheck, _⟩ := hp
    change some (Node.eff (.succeed (.lit (.nat 5)))) = some (.eff e) at hat
    cases hat
    have hcert : Except.ok (EffTy.pure .nat) = Except.ok cert4 :=
      (release_check env).symm.trans hcheck
    cases hcert
    have h5 := next4 w (leHost_refl w) (.success (Val.nat 5)) ⟨trivial, trivial⟩
    have hfit := (TypedProg.pure_inv h5).1
    rw [fitsExit_success_iff, unit] at hfit
    exact hfit

/-- The capture is typed (`CaptureTyped`): the `acquireRelease` at the root checks under the empty
environment, its acquire at `nat`, the acquired `1` fits it, and the empty context's services fit. -/
theorem acq_capture_typed (w : W) : CaptureTyped (acqProg : ProgramSource) w acqCapture := by
  refine ⟨.succeed (.lit (.nat 1)), .succeed (.lit (.nat 5)), [],
    ⟨.nat, .never, Env.Requirement.single nativeScopeKey⟩, EffTy.pure .nat, rfl, ?_, rfl, ?_, ?_⟩
  · decide +kernel
  · refine ⟨rfl, fun i ty v hi hv => ?_⟩
    cases i with
    | zero =>
      cases hi
      cases hv
      trivial
    | succ k => cases hi
  · intro key sv sty hget _
    change (Env.Context.empty : Env.Ctx).getV key = some sv at hget
    rw [Env.Context.getV_empty] at hget
    cases hget

/-- **Positive, the finalizer's own program** (decisions row 151 (a″)): the same capture's program
is typed at rc.112's finalizer type `⟨unknown, never⟩`, at every world and every closing exit
that fits `Exit<unknown, unknown>` (`finalizerTyped_of_admitted`): `5` is below `unknown`. -/
theorem foreign_typed_unknown (w : W) : FinalizerTyped (acqProg : ProgramSource) w (.foreign acqCapture) :=
  finalizerTyped_of_admitted _ w _ (acq_capture_typed w)

/-! ### `Scope.close` with zero, one and several finalizers (positive controls)

Decisions row 151's acceptance keeps these positive under every option: the close installs a
program typed at the close-scope row's `⟨unit, never⟩` (`closeScope_installs`,
`Typed/Adequacy.lean`) with no finalizer (`void`), with one finalizer whose program is typed at
`⟨unknown, never⟩` (a `release` that succeeds; the close voids its answer, row 151 (a″)), and
with two (the walk, `closeWalk_typed`). -/

/-- One `release` finalizer that succeeds, registered on the open scope 0. -/
def okReleaseStore : Stores :=
  ((syncOpStep (.scopeAdd 0 (.release 7 false)) StoreUnit.oneScope).map (·.1)).getD Stores.empty

/-- A second one on top. -/
def twoReleaseStore : Stores :=
  ((syncOpStep (.scopeAdd 0 (.release 8 false)) okReleaseStore).map (·.1)).getD Stores.empty

theorem zero_order : (scopeCloseSnapshot 0 failed StoreUnit.oneScope).map (·.2.2) = some [] := by
  decide +kernel

theorem one_order :
    (scopeCloseSnapshot 0 failed okReleaseStore).map (·.2.2) = some [.release 7 false] := by
  decide +kernel

theorem two_order :
    ((scopeCloseSnapshot 0 failed twoReleaseStore).map (·.2.2)).map List.length = some 2 := by
  decide +kernel

/-- A lone-finalizer snapshot names the order's one finalizer. -/
theorem lone_of_order {st : Stores} {order : List FinName}
    (horder : (scopeCloseSnapshot 0 failed st).map (·.2.2) = some order)
    {state : Stores} {strategy : FinalizerStrategy} {fin : FinName}
    (hs : scopeCloseSnapshot 0 failed st = some (state, strategy, [fin])) : order = [fin] := by
  rw [hs] at horder
  exact (Option.some.inj horder).symm

/-- The closing exit `failed` fits `Exit<unknown, unknown>` at every world: its one reason is a
`Fail` of a live error value, and it carries no shape defect. -/
theorem failed_fits (w : W) : FitsExit w ⟨.unknown, .unknown, Env.Requirement.empty⟩ failed := by
  refine (fitsExit_failure_iff w _ _).mpr ⟨fun r hr => ?_, fun r hr => ?_⟩
  · cases hr with
    | head => exact ⟨_, rfl, live_of_keys_nil rfl⟩
    | tail _ h => cases h
  · cases hr with
    | head => trivial
    | tail _ h => cases h

/-- The stores' finalizers, read off by the kernel: none on the open scope, one succeeding
`release`, two. -/
theorem zero_fins : ∀ entry ∈ StoreUnit.oneScope.scopes.entries, entry.scope.closeOrder = [] := by
  decide +kernel

theorem one_fins : ∀ entry ∈ okReleaseStore.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
    fin = .release 7 false := by
  decide +kernel

theorem two_fins : ∀ entry ∈ twoReleaseStore.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
    fin = .release 7 false ∨ fin = .release 8 false := by
  decide +kernel

/-- Positive controls under row 151 (a″): the close-scope row's post `⟨unit, never⟩` at zero, one
and two finalizers, the store's typing given by the registration pre's admission
(`finalizerTyped_of_admitted`: a succeeding `release` is admitted), the closing exit by
`failed_fits`. -/
theorem close_zero_typed (root : ProgramSource) (w : W) (st' : Stores) (code : RProgram)
    (h : closeScopeR 0 failed true StoreUnit.oneScope = some (st', code)) :
    TypedProg root w (EffTy.pure .unit) code :=
  closeScope_installs root w 0 failed true _ st' code
    (fun entry he fin hfin => by
      rw [zero_fins entry he] at hfin
      cases hfin)
    (failed_fits w) h

theorem close_one_typed (root : ProgramSource) (w : W) (st' : Stores) (code : RProgram)
    (h : closeScopeR 0 failed true okReleaseStore = some (st', code)) :
    TypedProg root w (EffTy.pure .unit) code :=
  closeScope_installs root w 0 failed true _ st' code
    (fun entry he fin hfin => by
      rw [one_fins entry he fin hfin]
      exact finalizerTyped_of_admitted root w _ rfl)
    (failed_fits w) h

theorem close_two_typed (root : ProgramSource) (w : W) (st' : Stores) (code : RProgram)
    (h : closeScopeR 0 failed true twoReleaseStore = some (st', code)) :
    TypedProg root w (EffTy.pure .unit) code :=
  closeScope_installs root w 0 failed true _ st' code
    (fun entry he fin hfin => by
      rcases two_fins entry he fin hfin with rfl | rfl
      · exact finalizerTyped_of_admitted root w _ rfl
      · exact finalizerTyped_of_admitted root w _ rfl)
    (failed_fits w) h

/-! ### The closing corollary for the value-answering capture (decisions row 151 (a″))

`foreign_untyped` stands: the capture's own program answers `5`, typed at no type whose answer
column is `unit`. The close of a scope whose lone finalizer it is voids that value, so the
installed program is typed at the close-scope row's `⟨unit, never⟩`. -/

/-- The capture registered on the open scope 0 by the store's own registration step. -/
def foreignStore : Stores :=
  ((syncOpStep (.scopeAdd 0 (.foreign acqCapture)) StoreUnit.oneScope).map (·.1)).getD Stores.empty

theorem foreign_fins : ∀ entry ∈ foreignStore.scopes.entries, ∀ fin ∈ entry.scope.closeOrder,
    fin = .foreign acqCapture := by
  decide +kernel

/-- **The corollary** (positive): the voided close of the scope holding the `5`-answering capture
is typed at `⟨unit, never⟩`. -/
theorem foreign_close_typed (w : W) (st' : Stores) (code : RProgram)
    (h : closeScopeR 0 failed true foreignStore = some (st', code)) :
    TypedProg (acqProg : ProgramSource) w (EffTy.pure .unit) code :=
  closeScope_installs _ w 0 failed true _ st' code
    (fun entry he fin hfin => by
      rw [foreign_fins entry he fin hfin]
      exact foreign_typed_unknown w)
    (failed_fits w) h

/-! ### The close-scope row's pre and the closing exit (found landing row 151 (a″))

`fiberPre`'s `closeScope` arm reads the scope's presence only (`Typed/Residual.lean`), so code
closing a present scope with a reified `badName` failure is typed, while the scope store's typing
types a closed scope's exit at `Exit<unknown, unknown>` (`ScopeExitOk`, decisions row 140), which
refuses it (row 152's `ShapeFree`): `FiberAction.closeScope` writes `closed badClose` and no later
world types the store. The same fit is `closeScope_installs`' one premise beside the store's
typing (a lone foreign finalizer's release reads the exit at that type). A decisions row is
proposed: the arm demands `FitsExit w ⟨unknown, unknown⟩ ex` (seat D4's receipt). -/

def badClose : ExitV := .failure (Cause.die .badName)

/-- The world over the store holding the open scope 0. -/
def oneScopeWorld : W := { initialWorld (EffTy.pure .unit) with state := StoreUnit.oneScope }

theorem oneScope_live : ScopeLive oneScopeWorld 0 := by
  decide +kernel

/-- **Red**: at a world whose store holds the open scope 0, the code closing it with `badClose`
is typed, and the closed-scope clause refuses `badClose` at every world. -/
theorem closeScope_pre_admits_unfit_exit (root : ProgramSource) :
    TypedProg root oneScopeWorld (EffTy.pure .unit)
        (.vis (.inr (.closeScope 0 badClose)) Effects.Program.pure) ∧
      ∀ (w : W) (e : Expect), ¬ (preds root).ScopeExitOk w e badClose :=
  ⟨TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () oneScope_live (fun _ _ _ post => TypedProg.pure post),
    fun w _ => Test.Program.H2PartOne.base_badName_refused w ⟨.unknown, .unknown, Env.Requirement.empty⟩⟩

/-! ### A lone finalizer answering a value closes to `unit` (decisions row 151 (a″))

rc.112 answers the lone release's `5` here: `Scope.close` is declared `Effect<void>`
(`Scope.ts:567`) but passes on the lone finalizer's effect (`internal/effect.ts:3775-3776`,
`:3788-3789`, `:3794-3795`); the pinned source's run is row `inline` of
`docs/research/2026-10-01-landing/seat-D4/vendor-scope-close.json` (the signed divergence
`U-02`, `docs/UPSTREAM-BACKLOG.md`). Both machines answer `unit`, the type the checker gives the
program. -/

/-- `scoped(acquireRelease(succeed 1, (a, exit) => succeed 5) >> Scope.close(scope, exit(void)))`,
the ambient scope read back through the `Scope` service: the release is the scope's one
finalizer when it closes. -/
def closeLone : NativeEff :=
  .scoped
    (.bind (.acquireRelease (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 5))))
      (.bind (.service nativeScopeKey)
        (.bind (.exit (.succeed (.lit .unit)))
          (.withFiber (.closeScope (.var 1) (.var 2))))))

def machineOf : RReplay → RState
  | .finished m | .frontier _ m | .stuck _ m => m

/-- The root's exit on the term machine and on the frame machine. -/
def termExit (p : NativeEff) (tape : List Api.Decision) : Option ExitV :=
  ((machineOf (replayR p 200 tape)).fiber? Api.root).bind RunFiber.exit
def frameExit (p : NativeEff) (tape : List Api.Decision) : Option ExitV :=
  (Api.replay p 200 tape).exit

#guard Program.typeOfProgram (closeLone : ProgramSource).signature closeLone ==
  some ⟨.unit, .never, .empty⟩
#guard frameExit closeLone [Api.evaluate, Api.flush] == some (.success .unit)
#guard termExit closeLone [Api.evaluate, Api.flush] == some (.success .unit)

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
    ¬ oldFiberPost w (.closeIter .sequential [] failed) cert (.success .unit) := by
  intro h
  cases h

theorem closeIter_post_admits (w : W) (cert : FiberCert (.closeIter .sequential [] failed)) :
    fiberPost w (.closeIter .sequential [] failed) cert (.success .unit) := ⟨trivial, trivial⟩

/-- A reified `badName` failure: the shape decisions row 152 settles. Found landing row 136: the
close walk passes each finalizer's exit on reified as a value, so the iterator protocol's step
reads value membership at an exit type; before row 152 that membership admitted every defect. -/
def badNameExit : Val := reifyExitVal (.failure (Cause.die .badName))

/-- History (red against the current judgment; decisions row 152's red control): over the old
`exitOf` arm (`H2PartOne.oldExitFits`, a local copy) a reified `badName` failure fit
`exitOf unit never`. -/
theorem old_badName_fits (w : W) : Test.Program.H2PartOne.oldExitFits w badNameExit .unit .never :=
  Test.Program.H2PartOne.old_base_badName_fits w (EffTy.pure .unit)

/-- History: the step clause of `IteratorProtocol` at the walk's exit type, over the old
membership (the current clause with `oldExitFits` for `Fits`). -/
def OldCloseStep (root : ProgramSource) (w : W) (name : EffName) : Prop :=
  ∀ w', w.leHost w' → ∀ v, Test.Program.H2PartOne.oldExitFits w' v .unit .never →
    IteratorAnswer root w' (EffTy.pure .unit) ((interpR root.program).iterNext name v).2

/-- History (the refutation found landing row 136, restated over the old membership): the walk
halts with the admitted `badName` failure, which `ExitOk` at `⟨unit, never⟩` refuses, so no step
over the old membership types the walk at the exact post. -/
theorem old_closeSeq_protocol_refused (root : ProgramSource) (w : W) (ex : ExitV) :
    ¬ OldCloseStep root w (.store (.closeSeq [] ex [])) := by
  intro next
  have answer := next w (leHost_refl w) badNameExit (old_badName_fits w)
  have step : ((interpR root.program).iterNext (.store (.closeSeq [] ex [])) badNameExit).2 =
      .halt ⟨[.die .badName .empty]⟩ := by
    change closeDone ([] ++ reasonsOfVal (Val.exitErr (Cause.die .badName))) = _
    rw [reasonsOfVal_exitErr]
    rfl
  rw [step] at answer
  cases answer with
  | halt cause typed =>
    have excluded := typed.2 (.die .badName .empty) (List.mem_singleton_self _)
    exact excluded.1 rfl

/-- The flip of `badName_fits` (decisions row 152, proved): membership at an exit type refuses a
reified `badName` failure. -/
theorem badName_refused (w : W) : ¬ Fits w badNameExit (.exitOf .unit .never) :=
  Test.Program.H2PartOne.base_badName_refused w (EffTy.pure .unit)

/-! ### The positive control: the walk types at the exact post for clean finalizers

A finalizer typed at `⟨unit, never⟩` is typed under the `Exit` primitive at `Exit<unit, never>`
(`exitR_typed`), and the walk's captured reasons stay clean and shape-free (`CapturedOk`), so
every step answers within the iterator protocol from `Exit<unit, never>` to the close-walk row's
post `⟨unit, never⟩` (`closeSeq_protocol`). Its instance with no finalizer left is the negation
of the historical refutation (`closeSeq_protocol_typed`). -/

/-- **The `Exit` primitive keeps a typed program typed** at the exit type of its columns: the
`all` guard's body closes with `unguard` at the program's type (`close_typed`), its run arm
answers the reified exit, and its skip arm is never taken. -/
theorem exitR_typed (root : ProgramSource) {w : W} {a e : Ty} {req : Env.Requirement}
    {body : RProgram} (h : TypedProg root w ⟨a, e, req⟩ body) :
    TypedProg root w (EffTy.pure (.exitOf a e)) (exitR body) := by
  refine TypedProg.guard ⟨a, e, req⟩ ?_ ?_ ?_
  · show TypedProg root w ⟨a, e, req⟩
      ((body.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind
        fun ex => .pure (.success (reifyExitVal ex)))
    rw [Effects.Program.bind_assoc]
    exact close_typed root h fun x => .pure (.success (reifyExitVal x))
  · intro w' _ ex hpost
    exact TypedProg.pure ⟨hpost.2.1, trivial⟩
  · intro w' _ ex _ hmiss
    cases ex <;> exact Bool.noConfusion hmiss

/-- The walk's captured reasons fit the close's `⟨unit, never⟩` failure column: no typed failure
and no shape defect. -/
def CapturedOk (captured : List (Reason Err Defect FiberId Ann)) : Prop :=
  cleanExit (.failure ⟨captured⟩) = true ∧ ShapeFree ⟨captured⟩

theorem capturedOk_nil : CapturedOk [] := ⟨rfl, fun _ hr => nomatch hr⟩

/-- A step's input at `Exit<unit, never>` adds only clean, shape-free reasons. -/
theorem capturedOk_append {w : W} {captured : List (Reason Err Defect FiberId Ann)} {v : Val}
    (h : CapturedOk captured) (hv : Fits w v (.exitOf .unit .never)) :
    CapturedOk (captured ++ reasonsOfVal v) := by
  simp only [Typed.Fits] at hv
  split at hv
  · rename_i x
    show CapturedOk (captured ++ [])
    rw [List.append_nil]
    exact h
  · rename_i written
    split at hv
    · rename_i c hc
      have hreasons : reasonsOfVal (Value.exitErr written) = c.reasons := by
        show ((causeImage.ofVal written).map Cause.reasons).getD [] = c.reasons
        rw [hc]
        rfl
      rw [hreasons]
      have clean : cleanExit (.failure c) = true :=
        cleanExit_of_never_fits w (EffTy.pure .unit) c rfl
          ((fitsExit_failure_iff w (EffTy.pure .unit) c).mpr hv)
      refine ⟨?_, ?_⟩
      · show (captured ++ c.reasons).all (fun r => r.tag != .fail) = true
        rw [List.all_append, Bool.and_eq_true]
        exact ⟨h.1, clean⟩
      · intro r hr
        rcases List.mem_append.mp hr with hr | hr
        · exact h.2 r hr
        · exact hv.2 r hr
    · exact hv.elim
  · exact hv.elim

/-- **The close walk types at the exact post for clean finalizers (proved).** Every remaining
finalizer typed at `⟨unit, never⟩` at every later world, and clean, shape-free reasons captured so
far: the sequential walk meets the iterator protocol from `Exit<unit, never>` to `⟨unit, never⟩`. -/
theorem closeSeq_protocol (root : ProgramSource) (ex : ExitV) :
    ∀ (remaining : List FinName) (captured : List (Reason Err Defect FiberId Ann)) (w : W),
      CapturedOk captured →
      (∀ w', w.leHost w' → ∀ fin ∈ remaining,
        TypedProg root w' (EffTy.pure .unit) (denoteFin fin ex)) →
      IteratorProtocol root w (EffTy.pure (.exitOf .unit .never)) (EffTy.pure .unit)
        (.store (.closeSeq remaining ex captured))
  | [], captured, w, hcap, _ => by
    refine .step rfl (fun _ => rfl) fun w' _ v hv => ?_
    have hcap' := capturedOk_append hcap hv
    show IteratorAnswer root w' (EffTy.pure .unit) (closeDone (captured ++ reasonsOfVal v))
    generalize captured ++ reasonsOfVal v = all at hcap'
    cases all with
    | nil => exact .done Val.unit ⟨trivial, trivial⟩
    | cons r rest =>
      exact .halt ⟨r :: rest⟩
        ⟨fitsExit_of_clean w' _ _ hcap'.1 hcap'.2, hcap'.2⟩
  | fin :: rest, captured, w, hcap, hfins => by
    refine .step rfl (fun _ => rfl) fun w' hw' v hv => ?_
    have hcap' := capturedOk_append hcap hv
    show IteratorAnswer root w' (EffTy.pure .unit)
      (.resume (exitR (denoteFin fin ex)) (.store (.closeSeq rest ex (captured ++ reasonsOfVal v))))
    refine .resume _ _ (EffTy.pure (.exitOf .unit .never))
      (exitR_typed root (hfins w' hw' fin List.mem_cons_self)) ?_
    exact closeSeq_protocol root ex rest _ w' hcap' fun w'' hw'' fin' hfin' =>
      hfins w'' (leHost_trans _ _ _ hw' hw'') fin' (List.mem_cons_of_mem fin hfin')

/-- **The flip of the historical refutation** (decisions row 152, proved): with no finalizer
left and nothing captured, the walk's last step types at the exact post at every world. -/
theorem closeSeq_protocol_typed (root : ProgramSource) (w : W) (ex : ExitV) :
    IteratorProtocol root w (EffTy.pure (.exitOf .unit .never)) (EffTy.pure .unit)
      (.store (.closeSeq [] ex [])) :=
  closeSeq_protocol root ex [] [] w capturedOk_nil fun _ _ _ hfin => nomatch hfin

/-- With the release finalizer that succeeds (`FinName.release 3 false`), the two-step walk types:
the finalizer is typed at `⟨unit, never⟩` at every world. -/
theorem closeSeq_release_typed (root : ProgramSource) (w : W) (ex : ExitV) :
    IteratorProtocol root w (EffTy.pure (.exitOf .unit .never)) (EffTy.pure .unit)
      (.store (.closeSeq [.release 3 false, .release 4 false] ex [])) :=
  closeSeq_protocol root ex _ [] w capturedOk_nil fun w' _ fin hfin => by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hfin
    rcases hfin with rfl | rfl <;> exact TypedProg.pure ⟨trivial, trivial⟩

end CloseIter

/-! ## The await-by-value post read the answer column (`E4-TYPED-CE-010`) -/

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

/-- Historical: at the world where the target is declared at `pure nat`, the old post refused
the delivered value. -/
theorem post_excludes_delivered (cert : FiberCert (.await target .awaitValue)) :
    ¬ oldFiberPost w (.await target .awaitValue) cert delivered := by
  rintro ⟨ty, hty, h⟩
  rw [target_declared] at hty
  cases hty
  exact h

theorem await_code_refused (root : ProgramSource) : ¬ OldTypedProg root w checkedTy awaitCode := by
  intro h
  cases h with
  | fiber _ _ _ _ cert _ next =>
    have hnext := next w (leHost_refl w) (Val.nat 5) ⟨EffTy.pure .nat, target_declared, trivial⟩
    exact (OldTypedProg.pure_inv hnext).1

/-- The flips: the current post admits the delivered value, and the denoted await code is typed
at the checker's type at that world. -/
theorem post_admits_delivered (cert : FiberCert (.await target .awaitValue)) :
    fiberPost w (.await target .awaitValue) cert delivered :=
  awaitValue_delivered cert target_declared trivial

theorem await_code_typed (root : ProgramSource) : TypedProg root w checkedTy awaitCode := by
  have pre : fiberPre root w (.await target .awaitValue) PUnit.unit := by
    show (w.Γ target).isSome = true
    rw [target_declared]
    rfl
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) PUnit.unit pre ?_
  intro w' ord ans post
  obtain ⟨ty, hty, fits⟩ := post
  rw [ord.1.2.1 _ _ target_declared] at hty
  cases hty
  exact TypedProg.pure ⟨fits, trivial⟩

end AwaitValue

/-! ## The program level, historical: the corpus's `awaitFiber.value` under the old post

The program is `Test/Program/TypedCorpus.lean:62`'s `awaitFiber.value`, checked at
`pure (exitOf nat never)`. Under the old post its denoted root was refused at every world where
the forked fiber is fresh, so M5's load proposition was false there (`typedState_load_false`,
checked at `eb3ab9a9` and in `ports-at-dceae006/HeadAwaitLoad.lean`). -/

namespace AwaitLoad

def n (i : Nat) : Term := .lit (.nat i)
def v (i : Nat) : Term := .var i
def opts : Supervision.ForkOptions := ⟨true, false, .inherit⟩
def forked : NativeEff := .withFiber (.fork (.succeed (n 1)) opts)
/-- `Test/Program/TypedCorpus.lean:62`, `awaitFiber.value`. -/
def awaitProg : NativeEff := .bind forked (.awaitFiber (v 0) .awaitValue)
def rootTy : EffTy := EffTy.pure (.exitOf .nat .never)

theorem typed_source : Api.typeOf awaitProg = some rootTy := by rfl'

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

/-- **Historical: under the old post the denoted root is not typed at its checked type, at any
world where the forked fiber is fresh.** -/
theorem root_code_refused (w : W) (fresh : w.Γ ⟨1⟩ = none) :
    ¬ OldTypedProg (awaitProg : ProgramSource) w rootTy code := by
  intro h
  rw [code_eq] at h
  obtain ⟨mid, body, run⟩ := OldTypedProg.guard_inv h
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
        exact (OldTypedProg.pure_inv hp).1

/-- The loaded root is not inert under the code clause of the typed state as of `bb269fde`
(local copies of `TerminalFiber`, `TerminalPosition` and `CodeInert`). -/
def OldTerminalFiber (m : RState) (commands : List RCmd) (id : FiberId) : Prop :=
  (∃ exit, .finish id exit ∈ commands) ∨ ∃ fiber ∈ m.fibers, fiber.id = id ∧ fiber.exit.isSome = true

def OldTerminalPosition (m : RState) (commands : List RCmd) : Expect → Prop
  | .root => OldTerminalFiber m commands Api.root
  | .fiber id => OldTerminalFiber m commands id
  | .hook _ => False

def OldCodeInert (m : RState) (commands : List RCmd) (position : Expect) : Prop :=
  m.stuck.isSome = true ∨ OldTerminalPosition m commands position

/-- The typed state's saved position with the code clause over the old judgment. -/
def OldSavedPosition (root : ProgramSource) (w : W) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ OldCodeInert m commands position → OldTypedProg root w tin saved.current) ∧
    Contracts.StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final saved.stack ∧
    Contracts.InterruptProvenance saved

def oldStatePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds W :=
  { preds root with
    SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      OldSavedPosition root w m commands position ty saved }

/-- The load interface of the typed state, with its code clause over the old judgment: world
validity and the generated whole-state predicate. (The remaining conjuncts of `TypedState` are
not read by the refutation.) -/
def OldLoaded (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (oldStatePreds root m []) w m

theorem load_not_inert (p : NativeEff) (fuel compileFuel : Nat) :
    ¬ OldCodeInert (loadR p fuel compileFuel) [] .root := by
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

theorem closed_root : ClosedEff rootTy := ⟨rfl, rfl⟩

/-- **Historical: under the old post, M5's load proposition is false for this program** (fuel
5; `E4-TYPED-CE-010`, the program level): no world loads it with its code clause satisfied. -/
theorem typedState_load_false :
    ¬ (Api.typeOf awaitProg [] = some rootTy → ClosedEff rootTy →
        ∃ w, OldLoaded (awaitProg : ProgramSource) rootTy w (loadR awaitProg 5 5)) := by
  intro h
  obtain ⟨w, valid, ok⟩ := h typed_source closed_root
  have fresh : w.Γ ⟨1⟩ = none := by
    cases hg : w.Γ ⟨1⟩ with
    | none => rfl
    | some t =>
      exact absurd ((valid.fibers ⟨1⟩).mp (by rw [hg]; rfl)) one_not_loaded
  have hroot : (loadR awaitProg 5 5).fibers =
      [RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx] := rfl
  have hmemb : RunFiber.make Api.root code true (stores.budgetOf emptyCtx) emptyCtx ∈
      (loadR awaitProg 5 5).fibers := by rw [hroot]; exact List.mem_singleton_self _
  have saved := ((ok.c0 _ hmemb).c0).c0 rootTy valid.root
  obtain ⟨tin, hcode0, hstack, _⟩ := saved
  have hcode := hcode0 (load_not_inert awaitProg 5 5)
  cases hstack
  exact root_code_refused w fresh hcode

end AwaitLoad

/-! ## `deferredCompleteWith`: the old pre admitted a completion no later world types

Red control (found landing row 136). The old pre asked only that the promise be declared. A
completion with an ill-typed value then leaves no later world over the new store: the world order
keeps every declared promise's stored completion typed (`CellCompatible`). The current pre types
the completion at the promise's declared columns. -/

namespace CompleteWith

/-- A store with one empty Deferred cell, and a world declaring it at `(nat, nat)`. -/
def cellStore : Stores := { Stores.empty with deferreds := Stores.empty.deferreds.make.2 }

def wp : W := { initialWorld (EffTy.pure .unit) with
  state := cellStore, «Π» := tableInsert (fun _ => none) ⟨0⟩ (Ty.nat, Ty.nat) }

def badCompletion : Completion Val Err Defect FiberId Ann := .ofExit (.success (.str "x"))

theorem old_pre (root : ProgramSource) (cert : StoreCert (.deferredCompleteWith ⟨0⟩ badCompletion)) :
    oldStorePre root wp (.deferredCompleteWith ⟨0⟩ badCompletion) cert := rfl

def completed : Stores :=
  ((syncOpStep (.deferredCompleteWith ⟨0⟩ badCompletion) cellStore).map (·.1)).getD Stores.empty

theorem completes :
    syncOpStep (.deferredCompleteWith ⟨0⟩ badCompletion) wp.state = some (completed, Val.bool true) :=
  rfl

theorem completion_stored : completed.deferreds.cellAt ⟨0⟩ =
    some ⟨some badCompletion, (WakeList.empty.wakeAll).2⟩ := rfl

/-- Historical: under the old pre, no later world lies over the completed store. -/
theorem completeWith_old_adequacy_false :
    ¬ ∃ w', wp.leHost w' ∧ w'.state = completed := by
  rintro ⟨w', ord, hstate⟩
  have declared : PromiseTypedAt wp ⟨0⟩ (Ty.nat, Ty.nat) := by
    refine ⟨insert_here (fun _ : DeferredKey => (none : Option (Ty × Ty))) ⟨0⟩ (Ty.nat, Ty.nat),
      fun c hc completion hcomp => ?_⟩
    change Stores.empty.deferreds.make.2.cellAt ⟨0⟩ = some c at hc
    cases hc
    cases hcomp
  have later := ord.1.2.2.2.2.1.2 ⟨0⟩ (Ty.nat, Ty.nat) declared
  have typed := later.2 _ (by rw [hstate]; exact completion_stored) badCompletion rfl
  exact Bool.noConfusion typed

/-- The flip: the current pre refuses the ill-typed completion. -/
theorem completeWith_pre_refuses (root : ProgramSource)
    (cert : StoreCert (.deferredCompleteWith ⟨0⟩ badCompletion)) :
    ¬ storePre root wp (.deferredCompleteWith ⟨0⟩ badCompletion) cert := by
  intro h
  obtain ⟨a, e, hkey, typed⟩ : ∃ a e, wp.«Π» ⟨0⟩ = some (a, e) ∧
      ExitOk wp ⟨a, e, Env.Requirement.empty⟩ (.success (Val.str "x")) := h
  change tableInsert (fun _ : DeferredKey => (none : Option (Ty × Ty))) ⟨0⟩ (Ty.nat, Ty.nat) ⟨0⟩ =
    some (a, e) at hkey
  rw [insert_here] at hkey
  cases hkey
  exact typed.1

end CompleteWith

/-! ## Red fixtures: the old proofs against the current rows

Each old exclusion, and each proof of an old pre, run against the current row: the store answer,
the close-walk answer and the delivered value are now admitted, and the bool cell, the unknown
scope and the ill-typed completion are now refused. -/

/--
error: Type mismatch
  unit_not_bool
has type
  ¬∃ b, Val.unit = Val.bool b
but is expected to have type
  ¬storePost w (SyncOp.scopeRemove scope key) cert Val.unit
-/
#guard_msgs (error) in
example (w : W) (scope key : Nat) (cert : StoreCert (.scopeRemove scope key)) :
    ¬ storePost w (.scopeRemove scope key) cert Val.unit := unit_not_bool

/--
error: Type mismatch
  unit_not_bool
has type
  ¬∃ b, Val.unit = Val.bool b
but is expected to have type
  ¬storePost w (SyncOp.scopeAdd scope fin) cert Val.unit
-/
#guard_msgs (error) in
example (w : W) (scope : Nat) (fin : FinName) (cert : StoreCert (.scopeAdd scope fin)) :
    ¬ storePost w (.scopeAdd scope fin) cert Val.unit := unit_not_bool

/--
error: Type mismatch
  unit_not_bool
has type
  ¬∃ b, Val.unit = Val.bool b
but is expected to have type
  ¬storePost w (SyncOp.deferredAwaitCleanup cell waiter token) cert Val.unit
-/
#guard_msgs (error) in
example (w : W) (cell : DeferredKey) (waiter : FiberId) (token : Nat)
    (cert : StoreCert (.deferredAwaitCleanup cell waiter token)) :
    ¬ storePost w (.deferredAwaitCleanup cell waiter token) cert Val.unit := unit_not_bool

/--
error: unsolved goals
case inl
w : W
cert : StoreCert (SyncOp.memoRelease [] { index := 0 })
h✝ : Val.scopeHandle 1 = Val.unit
⊢ False

case inr
w : W
cert : StoreCert (SyncOp.memoRelease [] { index := 0 })
h✝ : Typed.Fits w (Val.scopeHandle 1) Ty.scope
⊢ False
-/
#guard_msgs (error) in
example (w : W) (cert : StoreCert (.memoRelease [] ⟨0⟩)) :
    ¬ storePost w (.memoRelease [] ⟨0⟩) cert (Val.scopeHandle 1) := by
  intro h
  cases h

/--
error: unsolved goals
case intro
w' : W
cert : FiberCert (FiberOp.closeScope 0 CloseScope.failed)
left✝ : FitsExit w' (EffTy.pure Ty.unit) (Exit.success Val.unit)
right✝ : NoShapeDefect (EffTy.pure Ty.unit) (Exit.success Val.unit)
⊢ False
-/
#guard_msgs (error) in
example (w' : W) (cert : FiberCert (.closeScope 0 CloseScope.failed)) :
    ¬ fiberPost w' (.closeScope 0 CloseScope.failed) cert (.success .unit) := by
  intro h
  cases h

/--
error: unsolved goals
case intro
w : W
cert : FiberCert (FiberOp.closeIter FinalizerStrategy.sequential [] CloseIter.failed)
left✝ : FitsExit w (EffTy.pure Ty.unit) (Exit.success Val.unit)
right✝ : NoShapeDefect (EffTy.pure Ty.unit) (Exit.success Val.unit)
⊢ False
-/
#guard_msgs (error) in
example (w : W) (cert : FiberCert (.closeIter .sequential [] CloseIter.failed)) :
    ¬ fiberPost w (.closeIter .sequential [] CloseIter.failed) cert (.success .unit) := by
  intro h
  cases h

/--
error: Type mismatch
  h
has type
  Typed.Fits AwaitValue.w AwaitValue.delivered ((EffTy.pure Ty.nat).answer.exitOf (EffTy.pure Ty.nat).error)
but is expected to have type
  False
-/
#guard_msgs (error) in
example (cert : FiberCert (.await AwaitValue.target .awaitValue)) :
    ¬ fiberPost AwaitValue.w (.await AwaitValue.target .awaitValue) cert AwaitValue.delivered := by
  rintro ⟨ty, hty, h⟩
  rw [AwaitValue.target_declared] at hty
  cases hty
  exact h

/--
error: Application type mismatch: The argument
  rfl
has type
  ?m.8 = ?m.8
but is expected to have type
  Modify.wb.Ρ { index := 0 } = some Ty.bool ∧ Equiv Ty.bool Ty.nat
in the application
  Exists.intro Ty.bool rfl
-/
#guard_msgs (error) in
example (root : ProgramSource) (cert : StoreCert (.refModify ⟨0⟩ .incr)) :
    storePre root Modify.wb (.refModify ⟨0⟩ .incr) cert := ⟨.bool, rfl⟩

/--
error: Type mismatch
  trivial
has type
  True
but is expected to have type
  storePre root w (SyncOp.scopeIsClosed 7) cert
-/
#guard_msgs (error) in
example (root : ProgramSource) (w : W) (cert : StoreCert (.scopeIsClosed 7)) :
    storePre root w (.scopeIsClosed 7) cert := trivial

/--
error: Type mismatch
  rfl
has type
  ?m.6 = ?m.6
but is expected to have type
  storePre root CompleteWith.wp (SyncOp.deferredCompleteWith { index := 0 } CompleteWith.badCompletion) cert
-/
#guard_msgs (error) in
example (root : ProgramSource) (cert : StoreCert (.deferredCompleteWith ⟨0⟩ CompleteWith.badCompletion)) :
    storePre root CompleteWith.wp (.deferredCompleteWith ⟨0⟩ CompleteWith.badCompletion) cert := rfl

/--
error: 'change' tactic failed, pattern
  (w.state.scopes.entryAt 0).isSome = true
is not definitionally equal to target
  storePre root w (SyncOp.scopeAdd 0 (FinName.release 7 true)) cert
-/
#guard_msgs (error) in
example (root : ProgramSource) (w : W) (store : w.state = StoreUnit.oneScope)
    (cert : StoreCert (.scopeAdd 0 (.release 7 true))) :
    storePre root w (.scopeAdd 0 (.release 7 true)) cert := by
  change (w.state.scopes.entryAt 0).isSome = true
  rw [store]
  decide +kernel

/--
error: Tactic `introN` failed: There are no additional binders or `let` bindings in the goal to introduce

w : W
⊢ Typed.Fits w CloseIter.badNameExit (Ty.unit.exitOf Ty.never)
-/
#guard_msgs (error) in
example (w : W) : Fits w CloseIter.badNameExit (.exitOf .unit .never) := by
  intro r hr
  simp only [List.mem_singleton] at hr
  subst hr
  trivial

end Test.Program.ProtocolPosts
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeRemove_post_excludes
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeAdd_post_excludes
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.awaitCleanup_post_excludes
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeRemove_post_admits
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeAdd_post_admits
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.awaitCleanup_post_admits
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.scopeAdd_open_answer
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.store_step_leaves_typing
open Test.Program.ProtocolPosts in
#print axioms StoreUnit.code_refused
open Test.Program.ProtocolPosts in
#print axioms Memo.memoRelease_answers_scope
open Test.Program.ProtocolPosts in
#print axioms Memo.memoRelease_post_excludes
open Test.Program.ProtocolPosts in
#print axioms Memo.memoRelease_post_admits
open Test.Program.ProtocolPosts in
#print axioms Memo.memo_admitted
open Test.Program.ProtocolPosts in
#print axioms Memo.memo_next_untyped
open Test.Program.ProtocolPosts in
#print axioms Memo.memoCode_refused
open Test.Program.ProtocolPosts in
#print axioms Modify.adequacy_false_refModify
open Test.Program.ProtocolPosts in
#print axioms Modify.refModifySome_post_excludes
open Test.Program.ProtocolPosts in
#print axioms Modify.refModify_pre_refuses
open Test.Program.ProtocolPosts in
#print axioms Modify.refModifySome_pre_refuses
open Test.Program.ProtocolPosts in
#print axioms Frontier.scopeIsClosed_unknown
open Test.Program.ProtocolPosts in
#print axioms Frontier.scopeIsClosed_post_excludes_unit
open Test.Program.ProtocolPosts in
#print axioms Frontier.scopeIsClosed_pre_refuses
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_no_finalizer
open Test.Program.ProtocolPosts in
#print axioms CloseScope.post_excludes_answer
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_code_refused
open Test.Program.ProtocolPosts in
#print axioms CloseScope.post_admits_answer
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_code_typed
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_code_refused_absent
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_code_typed_live
open Test.Program.ProtocolPosts in
#print axioms CloseScope.lone_release_answer
open Test.Program.ProtocolPosts in
#print axioms CloseScope.lone_release_outside_post
open Test.Program.ProtocolPosts in
#print axioms CloseScope.old_release_registration_admitted
open Test.Program.ProtocolPosts in
#print axioms CloseScope.release_registration_refused
open Test.Program.ProtocolPosts in
#print axioms CloseScope.failing_release_untyped
open Test.Program.ProtocolPosts in
#print axioms CloseScope.acq_capture_typed
open Test.Program.ProtocolPosts in
#print axioms CloseScope.foreign_typed_unknown
open Test.Program.ProtocolPosts in
#print axioms CloseScope.failed_fits
open Test.Program.ProtocolPosts in
#print axioms CloseScope.zero_fins
open Test.Program.ProtocolPosts in
#print axioms CloseScope.one_fins
open Test.Program.ProtocolPosts in
#print axioms CloseScope.two_fins
open Test.Program.ProtocolPosts in
#print axioms CloseScope.foreign_fins
open Test.Program.ProtocolPosts in
#print axioms CloseScope.foreign_close_typed
open Test.Program.ProtocolPosts in
#print axioms CloseScope.oneScope_live
open Test.Program.ProtocolPosts in
#print axioms CloseScope.closeScope_pre_admits_unfit_exit
open Test.Program.ProtocolPosts in
#print axioms CloseScope.acq_checked
open Test.Program.ProtocolPosts in
#print axioms CloseScope.release_check
open Test.Program.ProtocolPosts in
#print axioms CloseScope.foreign_untyped
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_zero_typed
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_one_typed
open Test.Program.ProtocolPosts in
#print axioms CloseScope.close_two_typed
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeSeq_done
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeIter_post_excludes
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeIter_post_admits
open Test.Program.ProtocolPosts in
#print axioms CloseIter.old_badName_fits
open Test.Program.ProtocolPosts in
#print axioms CloseIter.old_closeSeq_protocol_refused
open Test.Program.ProtocolPosts in
#print axioms CloseIter.badName_refused
open Test.Program.ProtocolPosts in
#print axioms CloseIter.exitR_typed
open Test.Program.ProtocolPosts in
#print axioms CloseIter.capturedOk_append
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeSeq_protocol
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeSeq_protocol_typed
open Test.Program.ProtocolPosts in
#print axioms CloseIter.closeSeq_release_typed
open Test.Program.ProtocolPosts in
#print axioms AwaitValue.post_excludes_delivered
open Test.Program.ProtocolPosts in
#print axioms AwaitValue.await_code_refused
open Test.Program.ProtocolPosts in
#print axioms AwaitValue.post_admits_delivered
open Test.Program.ProtocolPosts in
#print axioms AwaitValue.await_code_typed
open Test.Program.ProtocolPosts in
#print axioms AwaitLoad.root_code_refused
open Test.Program.ProtocolPosts in
#print axioms AwaitLoad.typedState_load_false
open Test.Program.ProtocolPosts in
#print axioms Modify.refModify_post_admits
open Test.Program.ProtocolPosts in
#print axioms Frontier.scopeIsClosed_post_admits
open Test.Program.ProtocolPosts in
#print axioms CompleteWith.completeWith_old_adequacy_false
open Test.Program.ProtocolPosts in
#print axioms CompleteWith.completeWith_pre_refuses

/-! The six read-modify-write store rows' adequacy, closed by integration seat I2
(`Typed/Adequacy.lean`). -/
#print axioms Effect4.Program.Typed.fits_total
#print axioms Effect4.Program.Typed.fits_partialUpdate
#print axioms Effect4.Program.Typed.refUpdate_implements
#print axioms Effect4.Program.Typed.refGetAndUpdate_implements
#print axioms Effect4.Program.Typed.refUpdateAndGet_implements
#print axioms Effect4.Program.Typed.refUpdateSome_implements
#print axioms Effect4.Program.Typed.refGetAndUpdateSome_implements
#print axioms Effect4.Program.Typed.refUpdateSomeAndGet_implements

/-! The scope-answering rows' adequacy, re-proved at decisions row 156 (integration seat I2): the
step installs or holds the scope it answers. -/
#print axioms Effect4.Program.Typed.scopeMake_implements
#print axioms Effect4.Program.Typed.scopeFork_implements
#print axioms Effect4.Program.Typed.memoBuild_implements
#print axioms Effect4.Program.Typed.memoRelease_implements
#print axioms Effect4.Program.Typed.ambientScope_answers
#print axioms Effect4.Program.Typed.restate_world
#print axioms Effect4.Program.Typed.poke_world
#print axioms Effect4.Program.Typed.complete_world
#print axioms Effect4.Program.Typed.refMake_implements
#print axioms Effect4.Program.Typed.deferredMake_implements
#print axioms Effect4.Machine.syncOpStep_memoValid
