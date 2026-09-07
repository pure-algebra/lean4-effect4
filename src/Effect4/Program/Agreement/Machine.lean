import Effect4.Program.Agreement
import Effect4.Machine.Clauses
import Effect4.Machine.Approximation
import Effect4.Api

/-!
# Program.Agreement.Machine — the command loop over one plain fiber is the local run

Packet: `Test/contracts/program-denotation.contract.md`; plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §9. This module is the machine half of
the packet's theorem. `Agreement.lean` showed that the frame machine, run locally over the
stores, takes a compiled straight-line program to its meaning. Here the fiber machine's
command loop (`Fibers.lean`, `driveState`) is shown to do exactly what the local run does, one
command per local step (two when a store `sync` owes a drain), for the one fiber `Api.load`
makes, and the packet's theorem `run_eq_meaning` follows over `Api.run`.

Three invariants carry the simulation, all decidable:

* `PlainCode`/`PlainFrame`: the primitives and frames a straight-line program compiles to
  and the hooks of `interpOf` answer with — no park and no `withFiber`, so the loop's
  fiber-level arms (`Fibers.lean:771-853`) never fire and `evaluatePrim` is the local step
  (`evaluatePrim_localStep`), the `onExit` frame's finalizer program included;
* `Quiet`: the stores owe no resume, so `Cmd.drainDue` changes nothing — a straight-line
  program never registers a waiter, and a completion with no waiter owes nothing;
* the op count is what the yield watches: under `defaultBudget` no yield is injected, and
  when the count reaches it the root parks on its own dispatcher (`Myield`), `flush` fires
  it back into the loop at count zero, and the rounds go on until the exit; each round that
  yields again has spent at least `defaultBudget - 1` steps of the run, so the rounds the
  fuel allows are enough (`E4-DEN-CE-005`, repaired).

The trace is never pinned: the commands emit frame events the algebra has no producer for
(`E4-DEN-CE-003`), and every equation here quantifies the trace away.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

/-! ## Plain code: what a straight-line program compiles to -/

/-- The continuation names a straight-line program's frames carry: the four compiled
continuations, the finalizer name, and the two continuations a finalizer runs under. -/
def PlainName : EffName → Bool
  | .cont _ | .caught _ | .onValue _ | .onCause _ | .fin _ | .restore _ | .merge _ => true
  | _ => false

/-- The primitives a straight-line program compiles to, and the hooks answer with. -/
def PlainCode : NCode → Bool
  | Prim.success _ => true
  | Prim.failure _ => true
  | Prim.yieldableError _ => true
  | Prim.sync (EffThunk.pure _) => true
  | Prim.sync (EffThunk.op _) => true
  | Prim.suspend (EffThunk.body _) => true
  | Prim.onSuccess b n => PlainCode b && PlainName n
  | Prim.onFailure b n => PlainCode b && PlainName n
  | Prim.onSuccessAndFailure b n₁ n₂ => PlainCode b && (PlainName n₁ && PlainName n₂)
  | Prim.exitFrame b => PlainCode b
  | Prim.onExit b (EffName.fin _) false => PlainCode b
  | _ => false

/-- The frames a straight-line program pushes, and the restoring frame a mask leaves. -/
def PlainFrame : NCode → Bool
  | Prim.onSuccess b n => PlainCode b && PlainName n
  | Prim.onFailure b n => PlainCode b && PlainName n
  | Prim.onSuccessAndFailure b n₁ n₂ => PlainCode b && (PlainName n₁ && PlainName n₂)
  | Prim.exitFrame b => PlainCode b
  | Prim.onExit b (EffName.fin _) false => PlainCode b
  | Prim.setInterruptible true => true
  | _ => false

/-- A stack of plain frames. -/
def PlainStack (K : List NCode) : Prop := ∀ f ∈ K, PlainFrame f = true

theorem PlainStack.nil : PlainStack [] := fun _ h => by simp at h

theorem PlainStack.cons {f : NCode} {K : List NCode} (hf : PlainFrame f = true)
    (hK : PlainStack K) : PlainStack (f :: K) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hK g hg

theorem PlainStack.head {f : NCode} {K : List NCode} (h : PlainStack (f :: K)) :
    PlainFrame f = true := h f (List.mem_cons_self ..)

theorem PlainStack.tail {f : NCode} {K : List NCode} (h : PlainStack (f :: K)) :
    PlainStack K := fun g hg => h g (List.mem_cons_of_mem _ hg)

theorem PlainStack.mask {K : List NCode} (i : Bool) (hK : PlainStack K) :
    PlainStack (maskStack i K) := by
  cases i
  · exact hK
  · exact hK.cons rfl

/-- Whether a primitive is a `sync`: the one plain shape the loop answers in two commands. -/
def isSync : NCode → Bool
  | Prim.sync _ => true
  | _ => false

theorem not_sync_of_isSync_false {cur : NCode} (h : isSync cur = false) :
    ∀ t, cur ≠ Prim.sync t := by
  intro t heq
  subst heq
  simp [isSync] at h

theorem eq_sync_of_isSync {cur : NCode} (h : isSync cur = true) : ∃ t, cur = Prim.sync t := by
  cases cur <;> first | exact ⟨_, rfl⟩ | simp [isSync] at h

/-! ### The compile stays plain -/

theorem compileEff_zero {p : Point} (e : NativeEff) (hf : p.fuel = 0) :
    compileEff e p = frontier p := by
  unfold compileEff
  simp only [hf]

theorem plainCode_compileEff : ∀ (e : NativeEff) (p : Point), Plain e = true →
    PlainCode (compileEff e p) = true
  | .succeed v, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_succeed v hf]; split <;> rfl
  | .fail e, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_fail e hf]; split <;> rfl
  | .failCause c, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_failCause c hf]; split <;> rfl
  | .yieldError e, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_yieldError e hf]; split <;> rfl
  | .sync t, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_sync t hf]; rfl
  | .suspend b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_suspend b hf]; rfl
  | .perform op r, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_perform_sync op r hf (Plain.perform_sync hpl)]
      split <;> (try split) <;> rfl
  | .bind a b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_bind a b hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff a (p.child 0) (Plain.bind hpl).1
  | .branch t a b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_branch t a b hf]; rfl
  | .exit b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
      · rw [compileEff_exit_frame b hf hx]
        exact plainCode_compileEff b (p.child 0) (Plain.exit hpl)
      · rw [compileEff_exit_fold b hf hx]; rfl
  | .catchCause b h, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_catchCause b h hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (Plain.catchCause hpl).1
  | .matchCause b v c, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_matchCause b v c hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (Plain.matchCause hpl).1
  | .onExit b f, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; rfl
    · rw [compileEff_onExit b f hf]
      exact plainCode_compileEff b (p.child 0) (Plain.onExit hpl).1
  | .gen _, _, hpl
  | .uninterruptible _, _, hpl
  | .interruptible _, _, hpl
  | .whileLoop _ _ _ _, _, hpl
  | .yieldNow _, _, hpl
  | .callback _ _, _, hpl
  | .awaitFiber _ _, _, hpl
  | .withFiber _, _, hpl
  | .scoped _, _, hpl
  | .acquireRelease _ _, _, hpl
  | .choose _ _ _, _, hpl => by simp [Plain] at hpl

/-! ### Every subterm of a straight-line program is straight-line -/

/-- A node that is a straight-line program. -/
def NodePlain : Node → Prop
  | Node.eff e => Plain e = true
  | _ => False

theorem child_plain {r : NativeEff} (hr : Plain r = true) {i : Nat} {m : Node}
    (h : (Node.eff r).child i = some m) : NodePlain m := by
  cases r <;> rcases i with _ | _ | _ | i <;> simp [Node.child] at h <;> subst h <;>
    simp_all [NodePlain, Plain]

theorem plain_at : ∀ (path : List Nat) (n : Node) (e : NativeEff), NodePlain n →
    Node.at_ n path = some (Node.eff e) → Plain e = true
  | [], n, e, hn, h => by
    simp only [Node.at_, Option.some.injEq] at h
    subst h
    exact hn
  | i :: rest, n, e, hn, h => by
    simp only [Node.at_] at h
    rcases hc : n.child i with _ | m
    · rw [hc] at h; simp at h
    · rw [hc] at h
      simp only [Option.bind] at h
      have hm : NodePlain m := by
        cases n
        · exact child_plain hn hc
        all_goals simp [NodePlain] at hn
      exact plain_at rest m e hm h

theorem plainCode_resolve {root : NativeEff} (hroot : Plain root = true) (q : Point) :
    PlainCode (resolve root q) = true := by
  unfold resolve
  rcases h : Node.at_ (Node.eff root) q.path with _ | n
  · rfl
  · cases n
    · rename_i e
      exact plainCode_compileEff e q (plain_at q.path (Node.eff root) e hroot h)
    all_goals rfl

/-! ### The hooks answer plain code -/

theorem suspendBodyAt_zero {root : NativeEff} {q : Point} (hf : q.fuel = 0) :
    suspendBodyAt root (EffThunk.body q) = frontier q := by
  simp [suspendBodyAt, hf]

theorem suspendBodyAt_missing {root : NativeEff} {q : Point} {k : Nat} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = none) :
    suspendBodyAt root (EffThunk.body q) = badShape := by
  simp [suspendBodyAt, hf, h]

theorem suspendBodyAt_other {root : NativeEff} {q : Point} {k : Nat} {n : Node}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some n)
    (hn : ∀ e, n ≠ Node.eff e) :
    suspendBodyAt root (EffThunk.body q) = badShape := by
  cases n
  · exact absurd rfl (hn _)
  all_goals simp [suspendBodyAt, hf, h]

theorem plainCode_suspendBodyAt {root : NativeEff} (hroot : Plain root = true) (q : Point) :
    PlainCode (suspendBodyAt root (EffThunk.body q)) = true := by
  rcases hf : q.fuel with _ | k
  · rw [suspendBodyAt_zero hf]; rfl
  · rcases h : Node.at_ (Node.eff root) q.path with _ | n
    · rw [suspendBodyAt_missing hf h]; rfl
    · cases n with
      | eff e =>
        have he : Plain e = true := plain_at q.path (Node.eff root) e hroot h
        cases hbr : isBranch e
        · rw [suspendBodyAt_of_at hf h (not_branch_of_isBranch_false hbr) (Plain.not_gen he)
            (Plain.not_whileLoop he)]
          exact plainCode_compileEff e q he
        · obtain ⟨t, a, b, rfl⟩ := eq_branch_of_isBranch hbr
          rcases hbo : boolOf (evalTerm q.env t) with _ | flag
          · rw [suspendBodyAt_branch_bad hf h (boolOf_none hbo)]; rfl
          · have ht := boolOf_some hbo
            cases flag
            · rw [suspendBodyAt_branch_false hf h ht]; exact plainCode_resolve hroot _
            · rw [suspendBodyAt_branch_true hf h ht]; exact plainCode_resolve hroot _
      | stmts _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | stmt _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | action _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | effs _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl

theorem plainCode_ofExit (ex : ExitV) : PlainCode (Prim.ofExit ex) = true := by
  cases ex <;> rfl

theorem plainCode_contAOf {root : NativeEff} (hroot : Plain root = true) {n : EffName}
    (hn : PlainName n = true) (v : Val) : PlainCode (contAOf root n v) = true := by
  cases n <;> simp [PlainName] at hn
  all_goals first
    | rfl
    | exact plainCode_resolve hroot _
    | exact plainCode_ofExit _

theorem plainCode_contEOf {root : NativeEff} (hroot : Plain root = true) {n : EffName}
    (hn : PlainName n = true) (c : CauseV) : PlainCode (contEOf root n c) = true := by
  cases n <;> simp [PlainName] at hn
  all_goals first
    | rfl
    | exact plainCode_resolve hroot _
    | exact plainCode_ofExit _

/-! ### The local step, by the shape of the current primitive -/

/-- The plain shapes the loop hands straight to the frame machine's `step`. -/
def StepShape : NCode → Bool
  | Prim.yieldableError _ => true
  | Prim.suspend _ => true
  | Prim.onSuccess _ _ => true
  | Prim.onFailure _ _ => true
  | Prim.onSuccessAndFailure _ _ _ => true
  | Prim.exitFrame _ => true
  | Prim.onExit _ _ _ => true
  | _ => false

theorem localStep_success (root : NativeEff) (v : Val) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.success v) K i) s =
      exitFrom root (Exit.success v) (popOf (fiberOf (Prim.success v) K i) (Exit.success v)) s :=
  rfl

theorem localStep_failure (root : NativeEff) (c : CauseV) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.failure c) K i) s =
      exitFrom root (Exit.failure c) (popOf (fiberOf (Prim.failure c) K i) (Exit.failure c)) s :=
  rfl

/-- Anything that is not a `sync` and not an exit is the frame machine's step. -/
theorem localStep_other (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (hns : ∀ t, cur ≠ Prim.sync t) (hnv : ∀ v, cur ≠ Prim.success v)
    (hnc : ∀ c, cur ≠ Prim.failure c) :
    localStep root (fiberOf cur K i) s = ofFrameStep ((fiberOf cur K i).step (primOf root)).1 s := by
  cases cur
  all_goals first
    | exact absurd rfl (hns _)
    | exact absurd rfl (hnv _)
    | exact absurd rfl (hnc _)
    | rfl

/-! ### The local step keeps the fiber plain -/

-- The `PlainFrame` argument is spent in some branches of the frame case split and not in
-- others; the linter reports the latter.
set_option linter.unusedSimpArgs false in
theorem localStep_plain {root : NativeEff} (hroot : Plain root = true) :
    ∀ (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores),
      PlainCode cur = true → PlainStack K →
      localStep root (fiberOf cur K i) s = .running fr' s' →
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K'
  | Prim.success v, K, i, s, fr', s', _, hK, h => by
    induction K generalizing i with
    | nil =>
      have he := step_exit_empty root (Exit.success v) i s
      simp only [Prim.ofExit] at he
      rw [he] at h
      cases h
    | cons f K ih =>
      have hf := hK.head
      have hK' := hK.tail
      cases f <;> (try simp only [PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf)
      · rw [step_success_onSuccess] at h
        cases h
        exact ⟨_, _, _, rfl, plainCode_contAOf hroot hf.2 v, hK'⟩
      · rw [step_success_pass_onFailure] at h
        exact ih i hK' h
      · rw [step_success_onSuccessAndFailure] at h
        cases h
        exact ⟨_, _, _, rfl, plainCode_contAOf hroot hf.2.1 v, hK'⟩
      · rw [step_success_exitFrame] at h
        cases h
        exact ⟨_, _, _, rfl, rfl, hK'⟩
      · next b n flag =>
        cases n <;> cases flag <;> simp only [PlainFrame] at hf
        all_goals try exact absurd hf (by decide)
        rename_i p
        have hm := step_ofExit_onExit root (Exit.success v) b p K i s
        simp only [Prim.ofExit] at hm
        rw [hm] at h
        cases h
        refine ⟨_, _, _, rfl, ?_, hK'.mask i⟩
        simp [PlainCode, PlainName, plainCode_resolve hroot]
      · next flag =>
        cases flag <;> simp only [PlainFrame] at hf
        all_goals try exact absurd hf (by decide)
        rw [step_success_pass_setInterruptible] at h
        exact ih true hK' h
  | Prim.failure c, K, i, s, fr', s', _, hK, h => by
    induction K generalizing i with
    | nil =>
      have he := step_exit_empty root (Exit.failure c) i s
      simp only [Prim.ofExit] at he
      rw [he] at h
      cases h
    | cons f K ih =>
      have hf := hK.head
      have hK' := hK.tail
      cases f <;> (try simp only [PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf)
      · rw [step_failure_pass_onSuccess] at h
        exact ih i hK' h
      · rw [step_failure_onFailure] at h
        cases h
        exact ⟨_, _, _, rfl, plainCode_contEOf hroot hf.2 c, hK'⟩
      · rw [step_failure_onSuccessAndFailure] at h
        cases h
        exact ⟨_, _, _, rfl, plainCode_contEOf hroot hf.2.2 c, hK'⟩
      · rw [step_failure_exitFrame] at h
        cases h
        exact ⟨_, _, _, rfl, rfl, hK'⟩
      · next b n flag =>
        cases n <;> cases flag <;> simp only [PlainFrame] at hf
        all_goals try exact absurd hf (by decide)
        rename_i p
        have hm := step_ofExit_onExit root (Exit.failure c) b p K i s
        simp only [Prim.ofExit] at hm
        rw [hm] at h
        cases h
        refine ⟨_, _, _, rfl, ?_, hK'.mask i⟩
        simp [PlainCode, PlainName, plainCode_resolve hroot]
      · next flag =>
        cases flag <;> simp only [PlainFrame] at hf
        all_goals try exact absurd hf (by decide)
        rw [step_failure_pass_setInterruptible] at h
        exact ih true hK' h
  | Prim.yieldableError e, K, i, s, fr', s', _, hK, h => by
    rw [step_yieldableError] at h
    cases h
    exact ⟨_, _, _, rfl, rfl, hK⟩
  | Prim.sync thunk, K, i, s, fr', s', hpl, hK, h => by
    cases thunk <;> simp only [PlainCode, Bool.false_eq_true] at hpl
    · rw [step_sync_pure] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK⟩
    · rw [step_sync_op] at h
      rcases hso : syncOpStep _ s with _ | ⟨s₁, v⟩ <;> rw [hso] at h
      · cases h
        exact ⟨_, _, _, rfl, rfl, hK⟩
      · cases h
        exact ⟨_, _, _, rfl, rfl, hK⟩
  | Prim.suspend thunk, K, i, s, fr', s', hpl, hK, h => by
    cases thunk <;> simp only [PlainCode, Bool.false_eq_true] at hpl
    rw [step_suspend] at h
    cases h
    exact ⟨_, _, _, rfl, plainCode_suspendBodyAt hroot _, hK⟩
  | Prim.onSuccess b n, K, i, s, fr', s', hpl, hK, h => by
    rw [step_push_onSuccess] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp [PlainFrame, hpl.1, hpl.2])⟩
  | Prim.onFailure b n, K, i, s, fr', s', hpl, hK, h => by
    rw [step_push_onFailure] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp [PlainFrame, hpl.1, hpl.2])⟩
  | Prim.onSuccessAndFailure b n₁ n₂, K, i, s, fr', s', hpl, hK, h => by
    rw [step_push_onSuccessAndFailure] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp [PlainFrame, hpl.1, hpl.2.1, hpl.2.2])⟩
  | Prim.exitFrame b, K, i, s, fr', s', hpl, hK, h => by
    rw [step_push_exitFrame] at h
    cases h
    exact ⟨_, _, _, rfl, hpl, hK.cons hpl⟩
  | Prim.onExit b n flag, K, i, s, fr', s', hpl, hK, h => by
    cases n <;> cases flag <;> simp only [PlainCode, Bool.false_eq_true] at hpl
    rw [step_push_onExit] at h
    cases h
    exact ⟨_, _, _, rfl, hpl, hK.cons hpl⟩
  | Prim.withFiber _, _, _, _, _, _, hpl, _, _
  | Prim.iterator _ _, _, _, _, _, _, hpl, _, _
  | Prim.setInterruptible _, _, _, _, _, _, hpl, _, _
  | Prim.whileLoop _ _, _, _, _, _, _, hpl, _, _
  | Prim.yieldNowWith _, _, _, _, _, _, hpl, _, _
  | Prim.async _ _ _, _, _, _, _, _, hpl, _, _
  | Prim.asyncFinalizer _, _, _, _, _, _, hpl, _, _ => by simp [PlainCode] at hpl

/-! ## Quiet stores: nothing owed to any waiter -/

/-- No resume is owed and no cell has a waiter. A straight-line program never registers a
waiter (`Deferred.await` is an `async` row), so the stores it reaches from `Stores.empty`
stay quiet, and `Cmd.drainDue` is the identity on them. -/
def Quiet (s : Stores) : Prop :=
  s.deferreds.due = [] ∧ ∀ c ∈ s.deferreds.cells, c.waiters = []

theorem Quiet.empty : Quiet Stores.empty := ⟨rfl, fun _ h => by simp [Stores.empty] at h⟩

theorem Quiet.of_deferreds_eq {s s' : Stores} (h : s'.deferreds = s.deferreds) (hq : Quiet s) :
    Quiet s' := by
  unfold Quiet
  rw [h]
  exact hq

theorem DeferredStore.make_quiet {d : DeferredStore} (hdue : d.due = [])
    (hcells : ∀ c ∈ d.cells, c.waiters = []) :
    (d.make).2.due = [] ∧ ∀ c ∈ (d.make).2.cells, c.waiters = [] := by
  refine ⟨hdue, fun c hc => ?_⟩
  simp only [DeferredStore.make, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hcells c hc
  · rfl

theorem DeferredStore.complete_quiet {d : DeferredStore} (hdue : d.due = [])
    (hcells : ∀ c ∈ d.cells, c.waiters = []) (cell : DeferredKey)
    (e : Effect4.Machine.Program) :
    (d.complete cell e).1.due = [] ∧ ∀ c ∈ (d.complete cell e).1.cells, c.waiters = [] := by
  unfold DeferredStore.complete
  split
  · exact ⟨hdue, hcells⟩
  · rename_i c hc
    split
    · exact ⟨hdue, hcells⟩
    · have hmem : c ∈ d.cells := List.mem_of_getElem? hc
      simp only [hcells c hmem, List.map_nil, List.append_nil, DeferredStore.setCell]
      refine ⟨hdue, fun c' hc' => ?_⟩
      rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
      · exact hcells c' hc'
      · rfl

theorem DeferredStore.cancel_quiet {d : DeferredStore} (hdue : d.due = [])
    (hcells : ∀ c ∈ d.cells, c.waiters = []) (cell : DeferredKey) (w : FiberId) (t : Nat) :
    (d.cancel cell w t).due = [] ∧ ∀ c ∈ (d.cancel cell w t).cells, c.waiters = [] := by
  unfold DeferredStore.cancel
  split
  · exact ⟨hdue, hcells⟩
  · rename_i c hc
    have hmem : c ∈ d.cells := List.mem_of_getElem? hc
    simp only [DeferredStore.setCell]
    refine ⟨hdue, fun c' hc' => ?_⟩
    rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
    · exact hcells c' hc'
    · simp [hcells c hmem]

/-- Every store step keeps the stores quiet. -/
theorem syncOpStep_quiet {o : SyncOp} {s s' : Stores} {v : Val}
    (h : syncOpStep o s = some (s', v)) (hq : Quiet s) : Quiet s' := by
  obtain ⟨hdue, hcells⟩ := hq
  cases o
  all_goals first
    | (simp only [syncOpStep, Option.map_eq_some_iff] at h
       obtain ⟨step, -, hstep⟩ := h
       simp only [Prod.mk.injEq] at hstep
       exact Quiet.of_deferreds_eq (by rw [← hstep.1]) ⟨hdue, hcells⟩)
    | (simp only [syncOpStep, Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨rfl, -⟩ := h
       first
         | exact ⟨hdue, hcells⟩
         | exact DeferredStore.make_quiet hdue hcells
         | exact DeferredStore.complete_quiet hdue hcells _ _
         | exact DeferredStore.cancel_quiet hdue hcells _ _ _)

theorem localStep_quiet {root : NativeEff} {cur : NCode} {K : List NCode} {i : Bool}
    {s s' : Stores} {fr' : NFiber} (h : localStep root (fiberOf cur K i) s = .running fr' s')
    (hq : Quiet s) : Quiet s' := by
  cases cur with
  | sync thunk =>
    cases thunk with
    | op o =>
      rw [step_sync_op] at h
      rcases hso : syncOpStep o s with _ | ⟨s₁, v⟩
      · rw [hso] at h; cases h; exact hq
      · rw [hso] at h; cases h; exact syncOpStep_quiet hso hq
    | _ =>
      simp only [localStep, fiberOf] at h
      cases h; exact hq
  | success v =>
    rw [localStep_success] at h
    rw [← exitFrom_running_stores h]; exact hq
  | failure c =>
    rw [localStep_failure] at h
    rw [← exitFrom_running_stores h]; exact hq
  | _ =>
    rw [localStep_other root _ K i s (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h)] at h
    unfold ofFrameStep at h
    split at h
    · cases h; exact hq
    · cases h

/-- The step of a plain fiber that is not a `sync` touches no store. -/
theorem localStep_stores {root : NativeEff} {cur : NCode} {K : List NCode} {i : Bool}
    {s s' : Stores} {fr' : NFiber} (hns : ∀ t, cur ≠ Prim.sync t)
    (h : localStep root (fiberOf cur K i) s = .running fr' s') : s = s' := by
  cases cur with
  | success v => rw [localStep_success] at h; exact exitFrom_running_stores h
  | failure c => rw [localStep_failure] at h; exact exitFrom_running_stores h
  | sync t => exact absurd rfl (hns t)
  | _ =>
    rw [localStep_other root _ K i s (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h)] at h
    unfold ofFrameStep at h
    split at h
    · cases h; rfl
    · cases h

theorem localStep_finished_stores {root : NativeEff} {cur : NCode} {K : List NCode} {i : Bool}
    {s s' : Stores} {ex : ExitV} (h : localStep root (fiberOf cur K i) s = .finished ex s') :
    s = s' := by
  cases cur with
  | sync thunk =>
    cases thunk with
    | op o =>
      rw [step_sync_op] at h
      rcases hso : syncOpStep o s with _ | ⟨s₁, v⟩
      · rw [hso] at h; cases h
      · rw [hso] at h; cases h
    | _ => simp only [localStep, fiberOf] at h; cases h
  | success v => rw [localStep_success] at h; exact exitFrom_finished_stores h
  | failure c => rw [localStep_failure] at h; exact exitFrom_finished_stores h
  | _ =>
    rw [localStep_other root _ K i s (fun _ h => by cases h) (fun _ h => by cases h)
      (fun _ h => by cases h)] at h
    unfold ofFrameStep at h
    split at h
    · cases h
    · cases h; rfl

/-- The drain of a quiet store owes nothing and changes nothing. -/
theorem dueResumes_quiet (root : NativeEff) {s : Stores} (hq : Quiet s) :
    (interpOf root).dueResumes s = ([], s) := by
  rcases s with ⟨refs, ⟨cells, due⟩, scopes, nextName⟩
  obtain ⟨hdue, -⟩ := hq
  simp only at hdue
  subst hdue
  rfl

/-! ## The machine over one plain fiber -/

abbrev NRunFiber := RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx
abbrev NTrace := List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx)
abbrev NCmd := Cmd EffName EffThunk Val Err Defect FiberId Ann
abbrev NIter := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- The root fiber, running at op count `k` over the frame `fr`: what `Cmd.evaluate` makes
of `Api.load`'s fiber (`Fibers.lean:1170-1173`), and what every iteration leaves. -/
def fiberAt (fr : NFiber) (k : Nat) : NRunFiber :=
  { RunFiber.make Api.root fr.current true (stores.budgetOf emptyCtx) emptyCtx with
    frame := fr, running := true, currentOpCount := k }

theorem fiberAt_frame (fr : NFiber) (k : Nat) : (fiberAt fr k).frame = fr := rfl

/-- The machine of the run: one fiber, nothing armed, no race, the stores `s`, the trace
`tr`, the next resume token `nt` (zero until the first yield; each yield takes one). -/
def M (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [fiberAt fr k], nextId := 1, nextToken := nt, trace := tr }

/-- The root fiber once its exit path has stored `ex` (`exitStore`, the else branch of
`exitFiber` at `Fibers.lean:1128-1141`). -/
def exitedAt (root : NativeEff) (ex : ExitV) (fr : NFiber) (k : Nat) : NRunFiber :=
  { fiberAt fr k with
    running := false
    exit := some ex
    finalizing := none
    frame := { fr with stack := [], deferredInterrupt := false }
    children := []
    parked := Parked.notParked
    pending := []
    context := (interpOf root).emptyContext
    observers := [] }

/-- The machine once the root has exited. -/
def Mexit (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace)
    (nt : Nat) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [exitedAt root ex fr k], nextId := 1, nextToken := nt, trace := tr }

/-- The root fiber parked behind the yield's resume guard `t` (`injectYield`,
`Fibers.lean:753-764`, then `settle` on `Outcome.parked`): not running, its current primitive
queued as a resume task at priority 0 on its own dispatcher, one pending entry on the
guard. -/
def parkedAt (fr : NFiber) (k : Nat) (t : Nat) : NRunFiber :=
  { fiberAt fr k with
    running := false
    parked := Parked.withGuard t
    pending := [⟨t, none, [], [], Resume.void, false⟩]
    dispatcher := Dispatcher.empty.enqueue 0 (Task.resume Api.root t fr.current) }

/-- The machine after a yield: the root parked on token `t`, its dispatcher armed, the next
token taken. -/
def Myield (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [parkedAt fr k t], nextId := 1, nextToken := t + 1, armed := [Api.root],
    trace := tr }

theorem M_stuck (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).stuck = none := rfl

theorem M_state (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).state = s := rfl

theorem M_middleware (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).middlewareInstalled = false := rfl

theorem M_fiber? (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).fiber? Api.root = some (fiberAt fr k) := by
  simp [M, RunMachine.fiber?, fiberAt, RunFiber.make]

theorem M_update (fr fr' : NFiber) (s : Stores) (k k' : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).update (fiberAt fr' k') = M fr' s k' tr nt := by
  simp [M, RunMachine.update, fiberAt, RunFiber.make]

theorem M_emit (fr : NFiber) (s : Stores) (k : Nat) (tr ev : NTrace) (nt : Nat) :
    (M fr s k tr nt).emit ev = M fr s k (tr ++ ev) nt := rfl

theorem Mexit_stuck (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).stuck = none := rfl

theorem Mexit_armed (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).armed = [] := rfl

theorem Mexit_state (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).state = s := rfl

theorem Mexit_finished (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).finished = true := by
  simp [Mexit, RunMachine.finished, exitedAt]

theorem Mexit_exit (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) :
    ((Mexit root ex fr s k tr nt).fiber? Api.root).bind RunFiber.exit = some ex := by
  simp [Mexit, RunMachine.fiber?, exitedAt, fiberAt, RunFiber.make]

theorem Myield_stuck (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).stuck = none := rfl

theorem Myield_state (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).state = s := rfl

theorem Myield_armed (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).armed = [Api.root] := rfl

theorem Myield_fiber? (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).fiber? Api.root = some (parkedAt fr k t) := by
  simp [Myield, RunMachine.fiber?, parkedAt, fiberAt, RunFiber.make]

/-! ### What the interp of a root program classifies -/

theorem parkOf_sync (root : NativeEff) (thunk : EffThunk) :
    (interpOf root).parkOf (Prim.sync thunk) = none := rfl

theorem parkOf_plain (root : NativeEff) {cur : NCode} (h : PlainCode cur = true) :
    (interpOf root).parkOf cur = none := by
  cases cur
  all_goals first
    | rfl
    | (rename_i thunk; cases thunk <;> first | rfl | simp [PlainCode] at h)

theorem syncState_op (root : NativeEff) (o : SyncOp) (s : Stores) :
    (interpOf root).syncState (EffThunk.op o) s = syncOpStep o s := rfl

theorem syncState_pure (root : NativeEff) (p : Point) (s : Stores) :
    (interpOf root).syncState (EffThunk.pure p) s = none := rfl

theorem syncValue_op (root : NativeEff) (o : SyncOp) :
    (interpOf root).syncValue (EffThunk.op o) = Val.unit := rfl

theorem syncValue_pure (root : NativeEff) (p : Point) :
    (interpOf root).syncValue (EffThunk.pure p) = syncValueAt root (EffThunk.pure p) := rfl

/-! ### `evaluatePrim` on a plain fiber is the local step -/

theorem evaluatePrim_stepShape (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (cur : NCode) (hcur : f.frame.current = cur) (hp : (interpOf root).parkOf cur = none)
    (hsh : StepShape cur = true) :
    evaluatePrim (interpOf root) m f false = evaluatePrim.stepFrame (interpOf root) m f false := by
  cases cur <;> simp [StepShape] at hsh <;> simp only [evaluatePrim, hcur, hp]

theorem evaluatePrim_success (root : NativeEff) (m : Api.Machine) (f : NRunFiber) (v : Val)
    (hcur : f.frame.current = Prim.success v) :
    evaluatePrim (interpOf root) m f false =
      evaluatePrim.finalizerOr (interpOf root) m f false (Exit.success v) := by
  simp only [evaluatePrim, hcur, parkOf_plain root (cur := Prim.success v) rfl]

theorem evaluatePrim_failure (root : NativeEff) (m : Api.Machine) (f : NRunFiber) (c : CauseV)
    (hcur : f.frame.current = Prim.failure c) :
    evaluatePrim (interpOf root) m f false =
      evaluatePrim.finalizerOr (interpOf root) m f false (Exit.failure c) := by
  simp only [evaluatePrim, hcur, parkOf_plain root (cur := Prim.failure c) rfl]

theorem evaluatePrim_sync_op (root : NativeEff) (m : Api.Machine) (f : NRunFiber) (o : SyncOp)
    (s₁ : Stores) (v : Val) (hcur : f.frame.current = Prim.sync (EffThunk.op o))
    (hs : syncOpStep o m.state = some (s₁, v)) :
    evaluatePrim (interpOf root) m f false =
      ⟨{ m with state := s₁ }, { f with frame := { f.frame with current := Prim.success v } },
        false, Outcome.answered, [Cmd.drainDue]⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_op, hs]

theorem evaluatePrim_sync_op_none (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (o : SyncOp) (hcur : f.frame.current = Prim.sync (EffThunk.op o))
    (hs : syncOpStep o m.state = none) :
    evaluatePrim (interpOf root) m f false =
      ⟨m, { f with frame := { f.frame with
          current := Prim.success ((interpOf root).syncValue (EffThunk.op o)) } },
        false, Outcome.answered, []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_op, hs]

theorem evaluatePrim_sync_pure (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (p : Point) (hcur : f.frame.current = Prim.sync (EffThunk.pure p)) :
    evaluatePrim (interpOf root) m f false =
      ⟨m, { f with frame := { f.frame with
          current := Prim.success ((interpOf root).syncValue (EffThunk.pure p)) } },
        false, Outcome.answered, []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_pure]

theorem stepFrame_eq (root : NativeEff) (m : Api.Machine) (f : NRunFiber) :
    evaluatePrim.stepFrame (interpOf root) m f false =
      evaluatePrim.finishFrame m f false (f.frame.step (primOf root)).1
        (f.frame.step (primOf root)).2 [] := rfl

/-- The frame machine's answer to a value, from the pop alone. -/
theorem step_fst_success (root : NativeEff) (v : Val) (K : List NCode) (i : Bool) :
    ((fiberOf (Prim.success v) K i).step (primOf root)).1 =
      resumeOf root (Exit.success v)
        ((fiberOf (Prim.success v) K i).getCont Effect4.Arm.contA false) := by
  show (FrameFiber.resumeValue (primOf root) (fiberOf (Prim.success v) K i) v
    (some (Exit.success v))).1 = _
  unfold FrameFiber.resumeValue resumeOf
  generalize (fiberOf (Prim.success v) K i).getCont Effect4.Arm.contA false = pop
  rcases pop with ⟨ans, _, _, fib⟩
  cases ans
  all_goals first
    | rfl
    | (rename_i fr
       dsimp only
       rcases Prim.armA (primOf root) fr v (some (Exit.success v)) with _ | ⟨_, _⟩ <;> rfl)

/-- The frame machine's answer to a cause, from the pop alone. -/
theorem step_fst_failure (root : NativeEff) (c : CauseV) (K : List NCode) (i : Bool) :
    ((fiberOf (Prim.failure c) K i).step (primOf root)).1 =
      resumeOf root (Exit.failure c)
        ((fiberOf (Prim.failure c) K i).getCont Effect4.Arm.contE true) := by
  show (FrameFiber.resumeCause (primOf root) (fiberOf (Prim.failure c) K i) c
    (some (Exit.failure c))).1 = _
  unfold FrameFiber.resumeCause resumeOf
  generalize (fiberOf (Prim.failure c) K i).getCont Effect4.Arm.contE true = pop
  rcases pop with ⟨ans, _, _, fib⟩
  cases ans
  all_goals first
    | rfl
    | (rename_i fr
       dsimp only
       rcases Prim.armE (primOf root) fr c (some (Exit.failure c)) with _ | ⟨_, _⟩ <;> rfl)

/-- The iteration a local step predicts, its events left open. -/
def iterOf (m : Api.Machine) (f : NRunFiber) (ev : NTrace) : LocalStep → NIter
  | .running fr' _ => ⟨m.emit ev, { f with frame := fr' }, false, Outcome.continue_, []⟩
  | .finished ex _ => ⟨m.emit ev, f, false, Outcome.finished ex, []⟩

/-- On a plain fiber whose current primitive is not a `sync`, `evaluatePrim` is the local
step: the frame machine's step, or — for an exit meeting an `onExit` frame — the finalizer
program under the mask, exactly as `exitFrom` spells it. -/
theorem evaluatePrim_localStep (root : NativeEff) (m : Api.Machine) (cur : NCode)
    (K : List NCode) (i : Bool) (k : Nat) (hpl : PlainCode cur = true)
    (hns : ∀ t, cur ≠ Prim.sync t) :
    ∃ ev, evaluatePrim (interpOf root) m (fiberAt (fiberOf cur K i) k) false =
      iterOf m (fiberAt (fiberOf cur K i) k) ev (localStep root (fiberOf cur K i) m.state) := by
  cases cur with
  | success v =>
    rw [evaluatePrim_success root m _ v rfl, localStep_success]
    unfold evaluatePrim.finalizerOr exitFrom popOf
    simp only [stepFrame_eq, fiberAt_frame, step_fst_success]
    generalize (fiberOf (Prim.success v) K i).getCont Effect4.Arm.contA false = pop
    rcases pop with ⟨ans, _, _, fib⟩
    cases ans
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · rename_i fr
      dsimp only [resumeOf]
      generalize Prim.armA (primOf root) fr v (some (Exit.success v)) = arm
      cases fr
      all_goals first
        | (rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩)
        | (rename_i fin _
           dsimp only
           rcases (interpOf root).finalizerProgram fin (Exit.success v) with _ | program
           · rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
           · exact ⟨_, rfl⟩)
    · exact ⟨_, rfl⟩
  | failure c =>
    rw [evaluatePrim_failure root m _ c rfl, localStep_failure]
    unfold evaluatePrim.finalizerOr exitFrom popOf
    simp only [stepFrame_eq, fiberAt_frame, step_fst_failure]
    generalize (fiberOf (Prim.failure c) K i).getCont Effect4.Arm.contE true = pop
    rcases pop with ⟨ans, _, _, fib⟩
    cases ans
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · rename_i fr
      dsimp only [resumeOf]
      generalize Prim.armE (primOf root) fr c (some (Exit.failure c)) = arm
      cases fr
      all_goals first
        | (rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩)
        | (rename_i fin _
           dsimp only
           rcases (interpOf root).finalizerProgram fin (Exit.failure c) with _ | program
           · rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
           · exact ⟨_, rfl⟩)
    · exact ⟨_, rfl⟩
  | sync t => exact absurd rfl (hns t)
  | _ =>
    first
      | (rw [evaluatePrim_stepShape root m _ _ rfl (parkOf_plain root hpl) rfl, stepFrame_eq,
          fiberAt_frame, localStep_other root _ K i m.state (fun _ h => by cases h)
            (fun _ h => by cases h) (fun _ h => by cases h)]
         rcases ((fiberOf _ K i).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩)
      | simp [PlainCode] at hpl

/-! ### One iteration under the budget: no yield, the primitive evaluated at count `k + 1` -/

theorem iteration_M (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores)
    (k : Nat) (tr : NTrace) (nt : Nat) (hk : k + 1 < defaultBudget) :
    iteration (interpOf root) (M (fiberOf cur K i) s k tr nt) (fiberAt (fiberOf cur K i) k) false =
      evaluatePrim (interpOf root) (M (fiberOf cur K i) s k tr nt)
        (fiberAt (fiberOf cur K i) (k + 1)) false := by
  have hidle : runloopTop (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) k :=
    runloopTop_idle _ rfl
  have hcount : countOp (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) (k + 1) := rfl
  have hno : injectYield (M (fiberOf cur K i) s k tr nt)
      (countOp (runloopTop (fiberAt (fiberOf cur K i) k))) false = none := by
    rw [hidle, hcount]
    apply injectYield_no_verdict
    rw [yieldVerdict_default _ rfl]
    exact decide_eq_false (by show ¬ (k + 1 ≥ defaultBudget); omega)
  rw [iteration_evaluates _ _ _ _ hno, hidle, hcount]

/-! ### The commands, one local step each -/

/-- The loop on a finished iteration, as `drive_loop_continues` for `Outcome.finished`. -/
theorem drive_loop_finished (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (fuel : Nat) (m : Api.Machine) (id : FiberId) (yielding : Bool) (f : NRunFiber)
    (rest : List NCmd) (ex : ExitV) (hs : m.stuck = none) (hf : m.fiber? id = some f)
    (h : (iteration interp m f yielding).outcome = Outcome.finished ex) :
    driveState interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      driveState interp fuel
        ((iteration interp m f yielding).machine.update (iteration interp m f yielding).fiber)
        ((iteration interp m f yielding).nested ++ [Cmd.finish id ex] ++ rest) := by
  simp [driveState, driveStep, settle, hs, hf, h]

/-- A store `sync` the store answers: the loop command answers it, then a drain and the
delivery are owed (`Fibers.lean:836-838`). -/
theorem drive_loop_sync_op (root : NativeEff) (o : SyncOp) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (s₁ : Stores) (v : Val)
    (hk : k + 1 < defaultBudget) (hs : syncOpStep o s = some (s₁, v)) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1)
        (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (interpOf root) n (M (fiberOf (Prim.success v) K i) s₁ (k + 1) tr' nt)
        (Cmd.drainDue :: Cmd.deliver Api.root false :: rest) := by
  refine ⟨tr, fun n => ?_⟩
  have hit : iteration (interpOf root) (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) k) false =
      ⟨M (fiberOf (Prim.sync (EffThunk.op o)) K i) s₁ k tr nt,
        fiberAt (fiberOf (Prim.success v) K i) (k + 1), false, Outcome.answered,
        [Cmd.drainDue]⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    exact evaluatePrim_sync_op root _ _ o s₁ v rfl hs
  rw [driveState_loop_answered _ _ _ _ _ _ rest rfl (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  dsimp only
  rw [M_update]
  rfl

/-- A store `sync` the store does not answer: the machine's `unit`, no drain owed. -/
theorem drive_loop_sync_op_none (root : NativeEff) (o : SyncOp) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hk : k + 1 < defaultBudget) (hs : syncOpStep o s = none) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1)
        (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (interpOf root) n (M (fiberOf (Prim.success Val.unit) K i) s (k + 1) tr' nt)
        (Cmd.deliver Api.root false :: rest) := by
  refine ⟨tr, fun n => ?_⟩
  have hit : iteration (interpOf root) (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) k) false =
      ⟨M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt,
        fiberAt (fiberOf (Prim.success Val.unit) K i) (k + 1), false, Outcome.answered, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    exact evaluatePrim_sync_op_none root _ _ o rfl hs
  rw [driveState_loop_answered _ _ _ _ _ _ rest rfl (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  dsimp only
  rw [M_update]
  rfl

/-- A pure `sync`: the term's value, no drain owed. -/
theorem drive_loop_sync_pure (root : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hk : k + 1 < defaultBudget) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1)
        (M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (interpOf root) n
        (M (fiberOf (Prim.success (syncValueAt root (EffThunk.pure p))) K i) s (k + 1) tr' nt)
        (Cmd.deliver Api.root false :: rest) := by
  refine ⟨tr, fun n => ?_⟩
  have hit : iteration (interpOf root) (M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.pure p)) K i) k) false =
      ⟨M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt,
        fiberAt (fiberOf (Prim.success (syncValueAt root (EffThunk.pure p))) K i) (k + 1), false,
        Outcome.answered, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    exact evaluatePrim_sync_pure root _ _ p rfl
  rw [driveState_loop_answered _ _ _ _ _ _ rest rfl (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  dsimp only
  rw [M_update]
  rfl

/-- The local step at the loop, running on: the fiber moves on, the count goes up. -/
theorem drive_loop_running (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (cur₁ : NCode)
    (K₁ : List NCode) (i₁ : Bool) (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t)
    (hk : k + 1 < defaultBudget)
    (hstep : localStep root (fiberOf cur K i) s = .running (fiberOf cur₁ K₁ i₁) s) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.loop Api.root false :: rest) =
      driveState (interpOf root) n (M (fiberOf cur₁ K₁ i₁) s (k + 1) tr' nt)
        (Cmd.loop Api.root false :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i (k + 1) hpl hns
  rw [M_state, hstep] at hev
  have hit : iteration (interpOf root) (M (fiberOf cur K i) s k tr nt)
      (fiberAt (fiberOf cur K i) k) false =
      ⟨M (fiberOf cur K i) s k (tr ++ ev) nt, fiberAt (fiberOf cur₁ K₁ i₁) (k + 1), false,
        Outcome.continue_, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk, hev]
    rfl
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_loop_continues _ _ _ _ _ _ rest rfl (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  dsimp only
  rw [M_update]
  rfl

/-- The local step at the loop, finishing: the exit path is owed. -/
theorem drive_loop_finish (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ex : ExitV)
    (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t) (hk : k + 1 < defaultBudget)
    (hstep : localStep root (fiberOf cur K i) s = .finished ex s) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.loop Api.root false :: rest) =
      driveState (interpOf root) n (M (fiberOf cur K i) s (k + 1) tr' nt)
        (Cmd.finish Api.root ex :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i (k + 1) hpl hns
  rw [M_state, hstep] at hev
  have hit : iteration (interpOf root) (M (fiberOf cur K i) s k tr nt)
      (fiberAt (fiberOf cur K i) k) false =
      ⟨M (fiberOf cur K i) s k (tr ++ ev) nt, fiberAt (fiberOf cur K i) (k + 1), false,
        Outcome.finished ex, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk, hev]
    rfl
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [drive_loop_finished _ _ _ _ _ _ rest ex rfl (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  dsimp only
  rw [M_update]
  rfl

/-- The delivery of an answered `sync` (`Cmd.deliver`, R2-1): the local step with no loop
top and no op count. -/
theorem drive_deliver_running (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (cur₁ : NCode)
    (K₁ : List NCode) (i₁ : Bool) (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t)
    (hstep : localStep root (fiberOf cur K i) s = .running (fiberOf cur₁ K₁ i₁) s) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.deliver Api.root false :: rest) =
      driveState (interpOf root) n (M (fiberOf cur₁ K₁ i₁) s k tr' nt)
        (Cmd.loop Api.root false :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i k hpl hns
  rw [M_state, hstep] at hev
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_deliver _ _ _ _ _ (fiberAt (fiberOf cur K i) k) rest rfl (M_fiber? _ _ _ _ _), hev]
  show driveState _ n
    ((M (fiberOf cur K i) s k (tr ++ ev) nt).update (fiberAt (fiberOf cur₁ K₁ i₁) k))
    ([] ++ [Cmd.loop Api.root false] ++ rest) = _
  rw [M_update]
  rfl

theorem drive_deliver_finish (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ex : ExitV)
    (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t)
    (hstep : localStep root (fiberOf cur K i) s = .finished ex s) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.deliver Api.root false :: rest) =
      driveState (interpOf root) n (M (fiberOf cur K i) s k tr' nt)
        (Cmd.finish Api.root ex :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i k hpl hns
  rw [M_state, hstep] at hev
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_deliver _ _ _ _ _ (fiberAt (fiberOf cur K i) k) rest rfl (M_fiber? _ _ _ _ _), hev]
  show driveState _ n ((M (fiberOf cur K i) s k (tr ++ ev) nt).update (fiberAt (fiberOf cur K i) k))
    ([] ++ [Cmd.finish Api.root ex] ++ rest) = _
  rw [M_update]
  rfl

/-- The drain of a quiet store is a command that does nothing. -/
theorem drive_drainDue (root : NativeEff) (n : Nat) (m : Api.Machine) (rest : List NCmd)
    (hs : m.stuck = none) (hq : Quiet m.state) :
    driveState (interpOf root) (n + 1) m (Cmd.drainDue :: rest) =
      driveState (interpOf root) n m rest := by
  rcases m with ⟨fibers, races, nextId, nextToken, nextRace, mw, armed, state, trace, stuck⟩
  simp only at hs hq
  subst hs
  simp only [driveState, driveStep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    dueResumes_quiet root hq, List.map_nil, List.nil_append]

/-- The exit path of the root: no middleware, no children, no observer — the exit is stored,
the drain is owed. -/
theorem drive_finish_M (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) (rest : List NCmd) :
    ∃ tr', ∀ n, driveState (interpOf root) (n + 1) (M fr s k tr nt) (Cmd.finish Api.root ex :: rest) =
      driveState (interpOf root) n (Mexit root ex fr s k tr' nt) (Cmd.drainDue :: rest) := by
  refine ⟨tr ++ [RunEvent.exited Api.root ex], fun n => ?_⟩
  rw [driveState_finish _ _ _ _ _ (fiberAt fr k) rest rfl (M_fiber? _ _ _ _ _),
    exitFiber_no_middleware _ _ _ _ rfl]
  rfl

/-- `Cmd.evaluate` on the loaded root: the fiber starts running at count zero. -/
theorem drive_evaluate_load (e : NativeEff) (fuel : Nat) (rest : List NCmd) :
    ∀ n, driveState (interpOf e) (n + 1) (Api.load e fuel) (Cmd.evaluate Api.root :: rest) =
      driveState (interpOf e) n (M (fiberOf (compile e fuel) []) Stores.empty 0
        [RunEvent.started Api.root] 0) (Cmd.loop Api.root false :: rest) := by
  intro n
  rw [driveState_evaluate_enters _ _ _ _
    (RunFiber.make Api.root (compile e fuel) true (stores.budgetOf emptyCtx) emptyCtx) rest
    rfl rfl rfl rfl]
  rfl

theorem drive_nil (root : NativeEff) (m : Api.Machine) :
    ∀ n, driveState (interpOf root) n m [] = (m, [])
  | 0 => rfl
  | _ + 1 => rfl

theorem flushAll_Mexit (root : NativeEff) (fuel : Nat) (ex : ExitV) (fr : NFiber) (s : Stores)
    (k : Nat) (tr : NTrace) (nt : Nat) :
    ∀ rounds, flushAllState (interpOf root) fuel rounds (Mexit root ex fr s k tr nt) =
      (Mexit root ex fr s k tr nt, true)
  | 0 => rfl
  | _ + 1 => rfl

/-! ### The yield: the count reaches the budget, the root parks, `flush` resumes it -/

/-- At the loop with the count about to reach `defaultBudget`, the iteration injects a
yield instead of evaluating: the root parks behind the fresh token, its dispatcher is
armed, the command is spent. -/
theorem drive_loop_yield (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hk : defaultBudget ≤ k + 1) :
    ∀ n, driveState (interpOf root) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.loop Api.root false :: rest) =
      driveState (interpOf root) n
        (Myield (fiberOf cur K i) s (k + 1)
          (tr ++ [RunEvent.yieldInjected Api.root (k + 1), RunEvent.parkedOn Api.root nt]) nt)
        rest := by
  intro n
  have hidle : runloopTop (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) k :=
    runloopTop_idle _ rfl
  have hcount : countOp (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) (k + 1) := rfl
  have hv : yieldVerdict (fiberAt (fiberOf cur K i) (k + 1)) = true := by
    rw [yieldVerdict_default _ rfl]
    exact decide_eq_true (by show k + 1 ≥ defaultBudget; omega)
  have hit : iteration (interpOf root) (M (fiberOf cur K i) s k tr nt)
      (fiberAt (fiberOf cur K i) k) false =
      ⟨(({ M (fiberOf cur K i) s k tr nt with nextToken := nt + 1 }).arm Api.root).emit
          [RunEvent.yieldInjected Api.root (k + 1), RunEvent.parkedOn Api.root nt],
        ({ fiberAt (fiberOf cur K i) (k + 1) with
            yieldOverride := none
            dispatcher := (fiberAt (fiberOf cur K i) (k + 1)).dispatcher.enqueue 0
              (Task.resume Api.root nt cur) }).park ⟨nt, none, [], [], Resume.void, false⟩,
        true, Outcome.parked, []⟩ := by
    apply iteration_injected
    rw [hidle, hcount]
    unfold injectYield
    rw [if_pos (by simp only [hv, Bool.not_false, Bool.true_and]; rfl)]
    rfl
  rw [driveState_loop_parked _ _ _ _ _ _ rest rfl (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  rfl

/-- `flush` fires the root's dispatcher (`fire`): the one queued task resumes the root on
its own guard with its own primitive, and the resume re-enters the loop at count zero. -/
theorem fire_Myield (root : NativeEff) (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace)
    (t : Nat) :
    ∃ tr', ∀ n, fireState (interpOf root) (n + 1 + 1) (Myield fr s k tr t) Api.root =
      stepDecisionState.loop
        (driveState (interpOf root) n (M fr s 0 tr' (t + 1))
          [Cmd.loop Api.root false, Cmd.drainDue]) := by
  refine ⟨tr ++ [RunEvent.ranTask Api.root (Task.resume Api.root t fr.current)] ++
    [RunEvent.resumedWith Api.root t fr.current] ++ [RunEvent.started Api.root], fun n => ?_⟩
  have hdrain : (parkedAt fr k t).dispatcher.drain =
      ([Task.resume Api.root t fr.current], Dispatcher.empty) := rfl
  unfold fireState
  simp only [Myield_fiber?, hdrain]
  dsimp only [List.foldl, fireStep, taskCmds, stepDecisionState.loop]
  rw [driveState_resume_guard _ _ _ _ _ _ _ _ rfl rfl rfl,
    driveState_evaluate_enters _ _ _ _ _ _ rfl rfl rfl rfl]
  congr 2
  simp [M, Myield, parkedAt, fiberAt, RunMachine.update, RunMachine.disarm, RunMachine.emit,
    RunMachine.empty, RunFiber.make, Dispatcher.empty]

/-! ## The simulation: the command loop is the local run -/

/-- The next command the loop owes: the loop itself, or the delivery of an answered `sync`. -/
def cmdOf : Bool → NCmd
  | false => Cmd.loop Api.root false
  | true => Cmd.deliver Api.root false

/-- What the command loop owes a local run of `n` steps from `cur` over `s` at count `k`:
within `2n` commands it either reaches the exit path of the run's exit over its stores, or
the count reaches `defaultBudget` first and the root parks on a yield with the rest of the
run — `n₁` steps, at least `defaultBudget - k - 1` fewer than `n` — still to do. -/
def Owes (root : NativeEff) (n : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores)
    (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (d : Bool) (ex : ExitV)
    (s' : Stores) : Prop :=
  ∃ c, c ≤ 2 * n ∧
    ((∃ fr k' tr', Quiet s' ∧ ∀ fuel,
        driveState (interpOf root) (fuel + c) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
          driveState (interpOf root) fuel (M fr s' k' tr' nt) (Cmd.finish Api.root ex :: rest)) ∨
      (∃ cur₁ K₁ i₁ s₁ n₁ k₁ tr', n₁ + defaultBudget ≤ n + k + 1 ∧
        PlainCode cur₁ = true ∧ PlainStack K₁ ∧ Quiet s₁ ∧
        localRun root n₁ (fiberOf cur₁ K₁ i₁) s₁ = some (ex, s') ∧ ∀ fuel,
          driveState (interpOf root) (fuel + c) (M (fiberOf cur K i) s k tr nt) (cmdOf d :: rest) =
            driveState (interpOf root) fuel (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' nt) rest))

/-- One or two commands in front of what is owed. -/
theorem Owes.step (root : NativeEff) {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool} {ex : ExitV}
    {s' : Stores} {cur₁ : NCode} {K₁ : List NCode} {i₁ : Bool} {s₁ : Stores} {k₁ : Nat}
    {tr₁ : NTrace} (d₁ : Bool) (a : Nat) (ha : a ≤ 2) (hk : k₁ ≤ k + 1)
    (hdrv : ∀ fuel, driveState (interpOf root) (fuel + a) (M (fiberOf cur K i) s k tr nt)
      (cmdOf d :: rest) =
      driveState (interpOf root) fuel (M (fiberOf cur₁ K₁ i₁) s₁ k₁ tr₁ nt) (cmdOf d₁ :: rest))
    (h : Owes root n cur₁ K₁ i₁ s₁ k₁ tr₁ nt rest d₁ ex s') :
    Owes root (n + 1) cur K i s k tr nt rest d ex s' := by
  obtain ⟨c, hc, h⟩ := h
  refine ⟨c + a, by omega, ?_⟩
  rcases h with ⟨fr, k', tr', hq', hrec⟩ |
    ⟨cur₂, K₂, i₂, s₂, n₂, k₂, tr', hn, hpl, hK, hq, hrun, hrec⟩
  · exact Or.inl ⟨fr, k', tr', hq', fun fuel => by
      rw [show fuel + (c + a) = fuel + c + a by omega, hdrv, hrec]⟩
  · exact Or.inr ⟨cur₂, K₂, i₂, s₂, n₂, k₂, tr', by omega, hpl, hK, hq, hrun, fun fuel => by
      rw [show fuel + (c + a) = fuel + c + a by omega, hdrv, hrec]⟩

/-- The exit path, one command away. -/
theorem Owes.finish (root : NativeEff) {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {d : Bool} {ex : ExitV}
    {k' : Nat} {tr' : NTrace} (hq : Quiet s)
    (hdrv : ∀ fuel, driveState (interpOf root) (fuel + 1) (M (fiberOf cur K i) s k tr nt)
      (cmdOf d :: rest) =
      driveState (interpOf root) fuel (M (fiberOf cur K i) s k' tr' nt)
        (Cmd.finish Api.root ex :: rest)) :
    Owes root (n + 1) cur K i s k tr nt rest d ex s :=
  ⟨1, by omega, Or.inl ⟨fiberOf cur K i, k', tr', hq, hdrv⟩⟩

/-- The yield, one command away: at the loop with the count about to reach the budget, the
root parks with the whole run still to do. -/
theorem Owes.yield (root : NativeEff) {n : Nat} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {k : Nat} {tr : NTrace} {nt : Nat} {rest : List NCmd} {ex : ExitV}
    {s' : Stores} (hk : defaultBudget ≤ k + 1) (hpl : PlainCode cur = true) (hK : PlainStack K)
    (hq : Quiet s) (hrun : localRun root (n + 1) (fiberOf cur K i) s = some (ex, s')) :
    Owes root (n + 1) cur K i s k tr nt rest false ex s' :=
  ⟨1, by omega, Or.inr ⟨cur, K, i, s, n + 1, k + 1, _, by omega, hpl, hK, hq, hrun,
    fun fuel => drive_loop_yield root cur K i s k tr nt rest hk fuel⟩⟩

/-- The command loop over one plain fiber does what the local run does: if the local run
finishes within `n` steps with `ex` over `s'`, the loop, from any count and any token,
either reaches the exit path of `ex` over `s'` within `2n` commands, or reaches the budget
first and parks the root on a yield with the rest of the run to do (`Owes`). -/
theorem drive_localRun (root : NativeEff) (hroot : Plain root = true) :
    ∀ (n : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat) (tr : NTrace)
      (nt : Nat) (rest : List NCmd) (d : Bool) (ex : ExitV) (s' : Stores),
      PlainCode cur = true → PlainStack K → Quiet s →
      (d = true → ∀ t, cur ≠ Prim.sync t) →
      localRun root n (fiberOf cur K i) s = some (ex, s') →
      Owes root n cur K i s k tr nt rest d ex s'
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hrun => by
    simp [localRun] at hrun
  | n + 1, cur, K, i, s, k, tr, nt, rest, d, ex, s', hpl, hK, hq, hd, hrun => by
    cases d with
    | true =>
      -- the delivery: no `sync` here, the step is the frame machine's, and no count
      have hns := hd rfl
      rcases hstep : localStep root (fiberOf cur K i) s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
      · rw [localRun_running hstep] at hrun
        have hs₁ := localStep_stores hns hstep
        subst hs₁
        obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
          localStep_plain hroot cur K i s fr₁ s hpl hK hstep
        obtain ⟨tr₁, hdrv⟩ :=
          drive_deliver_running root cur K i s k tr nt rest cur₁ K₁ i₁ hpl hns hstep
        exact Owes.step root false 1 (by omega) (by omega) hdrv
          (drive_localRun root hroot n cur₁ K₁ i₁ s k tr₁ nt rest false ex s' hpl₁ hK₁ hq
            (fun h => by cases h) hrun)
      · rw [localRun_finished hstep] at hrun
        simp only [Option.some.injEq, Prod.mk.injEq] at hrun
        have hex : ex = ex₁ := hrun.1.symm
        have hs' : s' = s₁ := hrun.2.symm
        subst hex
        subst hs'
        have hs₁ := localStep_finished_stores hstep
        subst hs₁
        obtain ⟨tr₁, hdrv⟩ := drive_deliver_finish root cur K i s k tr nt rest ex hpl hns hstep
        exact Owes.finish root hq hdrv
    | false =>
      rcases Nat.lt_or_ge (k + 1) defaultBudget with hk | hk
      · rcases hstep : localStep root (fiberOf cur K i) s with ⟨fr₁, s₁⟩ | ⟨ex₁, s₁⟩
        · -- one more local step at the loop
          rw [localRun_running hstep] at hrun
          cases hsy : isSync cur
          · have hns := not_sync_of_isSync_false hsy
            have hs₁ := localStep_stores hns hstep
            subst hs₁
            obtain ⟨cur₁, K₁, i₁, rfl, hpl₁, hK₁⟩ :=
              localStep_plain hroot cur K i s fr₁ s hpl hK hstep
            obtain ⟨tr₁, hdrv⟩ :=
              drive_loop_running root cur K i s k tr nt rest cur₁ K₁ i₁ hpl hns hk hstep
            exact Owes.step root false 1 (by omega) (by omega) hdrv
              (drive_localRun root hroot n cur₁ K₁ i₁ s (k + 1) tr₁ nt rest false ex s' hpl₁ hK₁
                hq (fun h => by cases h) hrun)
          · -- a `sync`: answered at the loop, delivered next
            obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsy
            cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
            · -- pure
              rename_i p
              rw [step_sync_pure] at hstep
              simp only [LocalStep.running.injEq] at hstep
              obtain ⟨hfr, hs⟩ := hstep
              subst hfr
              subst hs
              obtain ⟨tr₁, hdrv⟩ := drive_loop_sync_pure root p K i s k tr nt rest hk
              exact Owes.step root true 1 (by omega) (by omega) hdrv
                (drive_localRun root hroot n _ K i s (k + 1) tr₁ nt rest true ex s' rfl hK hq
                  (fun _ t h => by cases h) hrun)
            · -- a store operation
              rename_i o
              rw [step_sync_op] at hstep
              rcases hso : syncOpStep o s with _ | ⟨s₂, v⟩ <;> rw [hso] at hstep <;>
                simp only [LocalStep.running.injEq] at hstep <;> obtain ⟨hfr, hs⟩ := hstep <;>
                subst hfr <;> subst hs
              · obtain ⟨tr₁, hdrv⟩ := drive_loop_sync_op_none root o K i s k tr nt rest hk hso
                exact Owes.step root true 1 (by omega) (by omega) hdrv
                  (drive_localRun root hroot n _ K i s (k + 1) tr₁ nt rest true ex s' rfl hK hq
                    (fun _ t h => by cases h) hrun)
              · have hq₂ : Quiet s₂ := syncOpStep_quiet hso hq
                obtain ⟨tr₁, hdrv⟩ := drive_loop_sync_op root o K i s k tr nt rest s₂ v hk hso
                have hdrain := drive_drainDue root
                  (m := M (fiberOf (Prim.success v) K i) s₂ (k + 1) tr₁ nt)
                  (rest := Cmd.deliver Api.root false :: rest) (hs := rfl) (hq := hq₂)
                refine Owes.step root true 2 (by omega) (by omega) (fun fuel => ?_)
                  (drive_localRun root hroot n _ K i s₂ (k + 1) tr₁ nt rest true ex s' rfl hK hq₂
                    (fun _ t h => by cases h) hrun)
                simp only [cmdOf]
                rw [show fuel + 2 = fuel + 1 + 1 by omega, hdrv, hdrain]
        · -- the last local step at the loop: the exit
          rw [localRun_finished hstep] at hrun
          simp only [Option.some.injEq, Prod.mk.injEq] at hrun
          have hex : ex = ex₁ := hrun.1.symm
          have hs' : s' = s₁ := hrun.2.symm
          subst hex
          subst hs'
          have hs₁ := localStep_finished_stores hstep
          subst hs₁
          cases hsy : isSync cur
          · have hns := not_sync_of_isSync_false hsy
            obtain ⟨tr₁, hdrv⟩ :=
              drive_loop_finish root cur K i s k tr nt rest ex hpl hns hk hstep
            exact Owes.finish root hq hdrv
          · -- a `sync` never finishes the fiber
            obtain ⟨t, rfl⟩ := eq_sync_of_isSync hsy
            cases t <;> simp only [PlainCode, Bool.false_eq_true] at hpl
            · rw [step_sync_pure] at hstep
              cases hstep
            · rename_i o
              rw [step_sync_op] at hstep
              rcases hso : syncOpStep o s with _ | ⟨s₂, v⟩ <;> rw [hso] at hstep <;> cases hstep
      · -- the count is at the budget: the loop yields before anything else
        exact Owes.yield root hk hpl hK hq hrun

/-! ## The rounds of `flush` after a yield -/

/-- Each round of `flush` fires the root's dispatcher, which resumes the root at count zero,
and the loop runs on to the exit path or to the next yield; a round that yields again has
lost at least `defaultBudget - 1` steps of the run, so the rounds the fuel allows are
enough. -/
theorem flushAll_Myield (root : NativeEff) (hroot : Plain root = true) :
    ∀ (rounds n : Nat) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (k : Nat)
      (tr : NTrace) (nt : Nat) (ex : ExitV) (s' : Stores) (fuel : Nat),
      PlainCode cur = true → PlainStack K → Quiet s →
      localRun root n (fiberOf cur K i) s = some (ex, s') →
      n + 1 ≤ rounds → 2 * n + 5 ≤ fuel →
      ∃ fr k' tr' nt', flushAllState (interpOf root) fuel rounds
        (Myield (fiberOf cur K i) s k tr nt) = (Mexit root ex fr s' k' tr' nt', true)
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hr, _ => absurd hr (Nat.not_succ_le_zero _)
  | rounds + 1, n, cur, K, i, s, k, tr, nt, ex, s', fuel, hpl, hK, hq, hrun, hr, hf => by
    have hB : defaultBudget = 2048 := rfl
    obtain ⟨f₂, rfl⟩ : ∃ f₂, fuel = f₂ + 1 + 1 := ⟨fuel - 2, by omega⟩
    change ∃ fr k' tr' nt',
      (let r := fireState (interpOf root) (f₂ + 1 + 1)
          (Myield (fiberOf cur K i) s k tr nt) Api.root
       if r.2 then flushAllState (interpOf root) (f₂ + 1 + 1) rounds r.1 else r) =
        (Mexit root ex fr s' k' tr' nt', true)
    obtain ⟨tr₁, hfire⟩ := fire_Myield root (fiberOf cur K i) s k tr nt
    rw [hfire]
    obtain ⟨c, hc, h⟩ := drive_localRun root hroot n cur K i s 0 tr₁ (nt + 1) [Cmd.drainDue]
      false ex s' hpl hK hq (fun h => by cases h) hrun
    simp only [cmdOf] at h
    rcases h with ⟨fr, k', tr', hq', hrec⟩ |
      ⟨cur₁, K₁, i₁, s₁, n₁, k₁, tr', hn, hpl₁, hK₁, hq₁, hrun₁, hrec⟩
    · -- the exit path: the exit is stored, the two drains do nothing, nothing is armed
      obtain ⟨f₄, rfl⟩ : ∃ f₄, f₂ = f₄ + 1 + 1 + 1 + c := ⟨f₂ - 3 - c, by omega⟩
      obtain ⟨tr'', hfin⟩ := drive_finish_M root ex fr s' k' tr' (nt + 1) [Cmd.drainDue]
      rw [hrec, hfin, drive_drainDue root _ _ _ rfl hq', drive_drainDue root _ _ _ rfl hq',
        drive_nil]
      simp only [stepDecisionState.loop, settled, List.isEmpty_nil, Bool.true_or, ↓reduceIte]
      rw [flushAll_Mexit]
      exact ⟨fr, k', tr'', nt + 1, rfl⟩
    · -- another yield: the drain does nothing, the next round takes it from there
      obtain ⟨f₄, rfl⟩ : ∃ f₄, f₂ = f₄ + 1 + c := ⟨f₂ - 1 - c, by omega⟩
      rw [hrec, drive_drainDue root _ _ _ rfl hq₁, drive_nil]
      simp only [stepDecisionState.loop, settled, List.isEmpty_nil, Bool.true_or, ↓reduceIte]
      exact flushAll_Myield root hroot rounds n₁ cur₁ K₁ i₁ s₁ k₁ tr' (nt + 1) ex s' _
        hpl₁ hK₁ hq₁ hrun₁ (by omega) (by omega)

/-! ## The packet's theorem -/

theorem replayEval_cons (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
    (fuel : Nat) (d : Api.Decision) (tape : List Api.Decision) (m : Api.Machine)
    (hs : m.stuck = none) (hr : (stepDecisionState interp fuel m d).2 = true) :
    replayEval interp fuel (d :: tape) m =
      replayEval interp fuel tape (stepDecisionState interp fuel m d).1 := by
  simp [replayEval, hs, hr]

theorem replayEval_nil_finished
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores) (fuel : Nat)
    (m : Api.Machine) (hs : m.stuck = none) (hf : m.finished = true) :
    replayEval interp fuel [] m = ReplayResult.finished m := by
  simp [replayEval, hs, hf]

/-- The ordinary run ends in the exited machine of the meaning, whatever the road: under the
op budget, `evaluate` runs the root to its exit and `flush` finds nothing armed; past it,
the root yields, parks, and `flush` fires its dispatcher round after round until the exit. -/
theorem replay_Mexit (e : NativeEff) (fuel : Nat) (hpl : Plain e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    ∃ fr k' tr' nt', replayEval (interpOf e) fuel [Api.evaluate, Api.flush] (Api.load e fuel) =
      ReplayResult.finished
        (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr' nt') := by
  have hB : defaultBudget = 2048 := rfl
  have hrun := localRun_root e fuel hpl hd
  obtain ⟨c, hc, h⟩ :=
    drive_localRun e hpl (steps e + 1) (compile e fuel) [] true Stores.empty 0
      [RunEvent.started Api.root] 0 [Cmd.drainDue] false (meaning e [] Stores.empty).1
      (meaning e [] Stores.empty).2 (plainCode_compileEff e _ hpl) PlainStack.nil Quiet.empty
      (fun h => by cases h) hrun
  simp only [cmdOf] at h
  rcases h with ⟨fr, k', tr', hq', hsim⟩ |
    ⟨cur₁, K₁, i₁, s₁, n₁, k₁, tr', hn, hpl₁, hK₁, hq₁, hrun₁, hsim⟩
  · -- under the budget: `evaluate` reaches the exit, `flush` finds nothing armed
    obtain ⟨tr'', hfin⟩ := drive_finish_M e (meaning e [] Stores.empty).1 fr
      (meaning e [] Stores.empty).2 k' tr' 0 [Cmd.drainDue]
    have hchain : ∀ F, c + 4 ≤ F →
        driveState (interpOf e) F (Api.load e fuel) [Cmd.evaluate Api.root, Cmd.drainDue] =
          (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr'' 0, []) := by
      intro F hF
      obtain ⟨f₄, rfl⟩ : ∃ f₄, F = f₄ + 1 + 1 + 1 + c + 1 := ⟨F - (c + 4), by omega⟩
      rw [drive_evaluate_load e fuel _ _, hsim, hfin,
        drive_drainDue e _ _ _ rfl hq', drive_drainDue e _ _ _ rfl hq']
      exact drive_nil e _ _
    refine ⟨fr, k', tr'', 0, ?_⟩
    have heval : stepDecisionState (interpOf e) fuel (Api.load e fuel) Api.evaluate =
        (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr'' 0, true) := by
      change stepDecisionState.loop (driveState _ _ _ _) = _
      rw [hchain fuel (by omega)]
      rfl
    rw [replayEval_cons _ _ _ _ _ rfl (by rw [heval]), heval]
    have hflush : stepDecisionState (interpOf e) fuel
        (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr'' 0)
        Api.flush =
        (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr'' 0, true) :=
      flushAll_Mexit _ _ _ _ _ _ _ _ _
    rw [replayEval_cons _ _ _ _ _ rfl (by rw [hflush]), hflush]
    exact replayEval_nil_finished _ _ _ rfl (Mexit_finished _ _ _ _ _ _ _)
  · -- past the budget: `evaluate` parks the root on a yield, `flush` runs the rounds
    have hchain : ∀ F, c + 2 ≤ F →
        driveState (interpOf e) F (Api.load e fuel) [Cmd.evaluate Api.root, Cmd.drainDue] =
          (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' 0, []) := by
      intro F hF
      obtain ⟨f₄, rfl⟩ : ∃ f₄, F = f₄ + 1 + c + 1 := ⟨F - (c + 2), by omega⟩
      rw [drive_evaluate_load e fuel _ _, hsim, drive_drainDue e _ _ _ rfl hq₁]
      exact drive_nil e _ _
    obtain ⟨fr, k', tr'', nt', hfl⟩ :=
      flushAll_Myield e hpl fuel n₁ cur₁ K₁ i₁ s₁ k₁ tr' 0 (meaning e [] Stores.empty).1
        (meaning e [] Stores.empty).2 fuel hpl₁ hK₁ hq₁ hrun₁ (by omega) (by omega)
    refine ⟨fr, k', tr'', nt', ?_⟩
    have heval : stepDecisionState (interpOf e) fuel (Api.load e fuel) Api.evaluate =
        (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' 0, true) := by
      change stepDecisionState.loop (driveState _ _ _ _) = _
      rw [hchain fuel (by omega)]
      rfl
    rw [replayEval_cons _ _ _ _ _ rfl (by rw [heval]), heval]
    have hflush : stepDecisionState (interpOf e) fuel
        (Myield (fiberOf cur₁ K₁ i₁) s₁ k₁ tr' 0) Api.flush =
        (Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr'' nt', true) := hfl
    rw [replayEval_cons _ _ _ _ _ rfl (by rw [hflush]), hflush]
    exact replayEval_nil_finished _ _ _ rfl (Mexit_finished _ _ _ _ _ _ _)

/-- The ordinary run of a straight-line program, with fuel for its depth and its commands,
finishes with the exit and the stores of its meaning — under the op budget or past it, where
the root yields, parks, and `flush` fires its dispatcher round after round (`E4-DEN-CE-005`,
repaired). The trace is not pinned (`E4-DEN-CE-003`). -/
theorem run_eq_meaning (e : NativeEff) (fuel : Nat) (hs : Straight e = true)
    (hd : depth e ≤ fuel) (hfuel : 2 * steps e + 6 ≤ fuel) :
    (Api.run e fuel).outcome = Api.Outcome.finished ∧
      (Api.run e fuel).exit = some (meaning e [] Stores.empty).1 ∧
      (Api.run e fuel).stores = (meaning e [] Stores.empty).2 := by
  have hpl : Plain e = true := by rw [Plain_eq_Straight]; exact hs
  obtain ⟨fr, k', tr', nt', hrep⟩ := replay_Mexit e fuel hpl hd hfuel
  have hrun_eq : Api.run e fuel =
      ⟨Api.Outcome.finished,
        Mexit e (meaning e [] Stores.empty).1 fr (meaning e [] Stores.empty).2 k' tr' nt'⟩ := by
    unfold Api.run Api.replay
    rw [hrep]
  refine ⟨?_, ?_, ?_⟩
  · rw [hrun_eq]
  · rw [hrun_eq]
    exact Mexit_exit _ _ _ _ _ _ _
  · rw [hrun_eq]
    rfl

end Effect4.Program.Agreement
