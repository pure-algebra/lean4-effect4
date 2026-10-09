import Effect4.Laws.Program.Agreement
import Effect4.Laws.Program.DenoteB
import Effect4.Laws.Program.FragmentLoopedRows
import Effect4.Laws.Program.Agreement.LoopSteps
import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.Approximation
import Effect4.Api

/-!
# Program.Agreement.Machine — the command loop over one plain fiber, one command at a time

Packet: `Test/contracts/program-denotation.contract.md`; plan
`docs/research/2026-09-05-slice-1-compile-ground.md` §9. This module is the machine half of
the packet's theorem, one command at a time. `Agreement.lean` showed that the frame machine,
run locally over the stores, takes a compiled straight-line program to its meaning. Here each
command of the fiber machine's loop (`Fibers.lean`, `driveState`) is shown to do what one local
step does (two commands when a store `sync` owes a drain), for the one fiber `Api.load` makes.
`Agreement/Segment.lean` chains the commands into segments (`drive_seg`) and states the packet's
theorem `run_eq_meaning` over `Api.run`.

Three invariants carry the simulation, all decidable:

* `PlainCode`/`PlainFrame`: the primitives and frames a program of the fragment with host calls
  (`LoopedRows`) compiles to and the hooks of `interpAt root []` answer with — no `withFiber`
  and no park but a host call's (`IsCall`), so off a host call the loop's fiber-level arms
  (`Fibers.lean:771-853`) never fire and `evaluatePrim` is the local step
  (`evaluatePrim_localStep`), the `onExit` frame's finalizer program included. A host call
  parks the root (`drive_loop_call`, `Agreement/Segment.lean`);
* `Quiet`: the stores owe no resume, so `Cmd.drainDue` changes nothing — a straight-line
  program never registers a waiter, and a completion with no waiter owes nothing;
* the op count is what the yield watches: under `defaultBudget` no yield is injected, and
  when the count reaches it the root parks on its own dispatcher (`Myield`, `drive_loop_yield`),
  and `flush` fires it back into the loop at count zero (`fire_Myield`) (`E4-DEN-CE-005`,
  repaired).

The trace is never pinned: the commands emit frame events the algebra has no producer for
(`E4-DEN-CE-003`), and every equation here quantifies the trace away.
-/

set_option autoImplicit false

namespace Effect4.Program.Agreement

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote

-- The row table of the run: every lemma below holds at any table, since the local step
-- reads no row; a table changes only an external registration and its answer.
variable {table : RowTable}

/-! ## The fragment with host calls

`LoopedRows` (generated, `Laws/Program/FragmentLoopedRows.lean`) is `Looped` with a call of any
host row and `catchIf`, the two forms `StraightRows` adds to `Straight`. -/

/-- The loop-bearing fragment lies inside it. -/
theorem LoopedRows.of_looped : ∀ (e : NativeEff), Looped e = true → LoopedRows e = true
  | .succeed _, _ | .fail _, _ | .failCause _, _ | .sync _, _ => rfl
  | .perform op _, h => by
    cases op with
    | external _ => rfl
    | _ => exact h
  | .iterate _ _ _ _ _ b, h => LoopedRows.of_looped b (Looped.iterate h)
  | .suspend b, h => LoopedRows.of_looped b (Looped.suspend h)
  | .bind a b, h => by
    simp only [LoopedRows, LoopedRows.of_looped a (Looped.bind h).1, LoopedRows.of_looped b (Looped.bind h).2,
      Bool.and_self]
  | .select _ _ a b, h => by
    simp only [LoopedRows, LoopedRows.of_looped a (Looped.select h).1, LoopedRows.of_looped b (Looped.select h).2,
      Bool.and_self]
  | .exit b, h => LoopedRows.of_looped b (Looped.exit h)
  | .catchCause b h', h => by
    simp only [LoopedRows, LoopedRows.of_looped b (Looped.catchCause h).1,
      LoopedRows.of_looped h' (Looped.catchCause h).2, Bool.and_self]
  | .matchCause b v c, h => by
    simp only [LoopedRows, LoopedRows.of_looped b (Looped.matchCause h).1,
      LoopedRows.of_looped v (Looped.matchCause h).2.1, LoopedRows.of_looped c (Looped.matchCause h).2.2,
      Bool.and_self]
  | .onExit b f, h => by
    simp only [LoopedRows, LoopedRows.of_looped b (Looped.onExit h).1, LoopedRows.of_looped f (Looped.onExit h).2,
      Bool.and_self]
  | .gen _, h | .uninterruptible _, h | .interruptible _, h | .yieldNow _, h | .awaitFiber _ _, h
  | .withFiber _, h | .scoped _, h | .acquireRelease _ _, h | .provideLayer _ _ _, h | .service _, h
  | .provideService _ _ _, h | .catchIf _ _ _, h | .restore _ _, h | .defs _ _ _, h => by
    simp only [Looped, Bool.false_eq_true] at h

theorem LoopedRows.bind {a b : NativeEff} (h : LoopedRows (.bind a b) = true) :
    LoopedRows a = true ∧ LoopedRows b = true := by
  simpa only [LoopedRows, Bool.and_eq_true] using h

theorem LoopedRows.select {t : Term} {d : Decision} {a b : NativeEff}
    (h : LoopedRows (.select t d a b) = true) : LoopedRows a = true ∧ LoopedRows b = true := by
  simpa only [LoopedRows, Bool.and_eq_true] using h

theorem LoopedRows.catchCause {b h' : NativeEff} (h : LoopedRows (.catchCause b h') = true) :
    LoopedRows b = true ∧ LoopedRows h' = true := by
  simpa only [LoopedRows, Bool.and_eq_true] using h

theorem LoopedRows.catchIf {t : Term} {b h' : NativeEff} (h : LoopedRows (.catchIf t b h') = true) :
    LoopedRows b = true ∧ LoopedRows h' = true := by
  simpa only [LoopedRows, Bool.and_eq_true] using h

theorem LoopedRows.matchCause {b v c : NativeEff} (h : LoopedRows (.matchCause b v c) = true) :
    LoopedRows b = true ∧ LoopedRows v = true ∧ LoopedRows c = true := by
  simpa only [LoopedRows, Bool.and_eq_true, and_assoc] using h

theorem LoopedRows.onExit {b f : NativeEff} (h : LoopedRows (.onExit b f) = true) :
    LoopedRows b = true ∧ LoopedRows f = true := by
  simpa only [LoopedRows, Bool.and_eq_true] using h

theorem LoopedRows.exit {b : NativeEff} (h : LoopedRows (.exit b) = true) : LoopedRows b = true := h

/-- A call of a row that is no host's is a call of `Straight`. -/
theorem LoopedRows.straight_perform {op : NativeOp} {r : Term}
    (hl : LoopedRows (.perform op r) = true) (hop : ∀ j, op ≠ .external j) :
    Straight (.perform op r) = true := by
  cases op with
  | external j => exact absurd rfl (hop j)
  | _ => exact hl

/-- Where the fragment meets the heads whose suspension body the compile decides itself: a
source suspension, a decision, and a loop; a host call and `catchIf` are none. -/
theorem LoopedRows.suspendDecided_iff {e : NativeEff} (hl : LoopedRows e = true) :
    e.suspendDecided = true ↔
      (∃ b, e = .suspend b) ∨ (∃ s d a b, e = .select s d a b) ∨
        (∃ c i t st r b, e = .iterate c i t st r b) := by
  cases e with
  | perform op r =>
    cases op <;> simp only [LoopedRows, NativeOp.kind, Eff.suspendDecided, Bool.false_eq_true,
      reduceCtorEq, exists_false, or_self] at hl ⊢
  | suspend b => exact iff_of_true rfl (Or.inl ⟨b, rfl⟩)
  | select t d a b => exact iff_of_true rfl (Or.inr (Or.inl ⟨t, d, a, b, rfl⟩))
  | iterate c i t st r b => exact iff_of_true rfl (Or.inr (Or.inr ⟨c, i, t, st, r, b, rfl⟩))
  | _ => simp only [Eff.suspendDecided, LoopedRows, Bool.false_eq_true, reduceCtorEq, exists_false,
      or_self] at hl ⊢

/-! ## Plain code: what a straight-line program compiles to -/

/-- The continuation names a straight-line program's frames carry: the four compiled
continuations, `catchIf`'s handler, the finalizer name, and the two continuations a finalizer
runs under. -/
def PlainName : EffName → Bool
  | .cont _ | .caught _ | .caughtError _ | .onValue _ | .onCause _ | .fin _ | .restore _ | .merge _ => true
  | _ => false

/-- **A host call** as the compile writes it: `asyncRoute`'s external arm, an external
registration with no signal and no cancel. -/
def IsCall : NCode → Bool
  | Prim.async (EffName.external (.external _) _ _) false none => true
  | _ => false

/-- The primitives a program of the fragment compiles to, and the hooks answer with: a host
call among them. -/
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
  | Prim.whileLoop (EffName.loop _) _ => true
  | Prim.async n w c => IsCall (Prim.async n w c)
  | _ => false

/-- The frames a straight-line program pushes, and the restoring frame a mask leaves. -/
def PlainFrame : NCode → Bool
  | Prim.onSuccess b n => PlainCode b && PlainName n
  | Prim.onFailure b n => PlainCode b && PlainName n
  | Prim.onSuccessAndFailure b n₁ n₂ => PlainCode b && (PlainName n₁ && PlainName n₂)
  | Prim.exitFrame b => PlainCode b
  | Prim.onExit b (EffName.fin _) false => PlainCode b
  | Prim.setInterruptible true => true
  | Prim.whileLoop (EffName.loop _) _ => true
  | _ => false

/-- A plain finalizer frame has the compiled finalizer name and is uninterruptible. -/
theorem plainFrame_onExit {b : NCode} {n : EffName} {flag : Bool}
    (h : PlainFrame (Prim.onExit b n flag) = true) :
    ∃ p, n = .fin p ∧ flag = false ∧ PlainCode b = true := by
  cases n <;> cases flag <;> simp [PlainFrame] at h
  exact ⟨_, rfl, rfl, h⟩

theorem plainCode_onExit {b : NCode} {n : EffName} {flag : Bool}
    (h : PlainCode (Prim.onExit b n flag) = true) :
    ∃ p, n = .fin p ∧ flag = false ∧ PlainCode b = true := by
  cases n <;> cases flag <;> simp [PlainCode] at h
  exact ⟨_, rfl, rfl, h⟩

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
    PlainFrame f = true :=
  by aesop

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

theorem plainCode_compileEff : ∀ (e : NativeEff) (p : Point), LoopedRows e = true →
    PlainCode (compileEff e p) = true
  | .succeed v, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_succeed v hf]; split <;> rfl
  | .fail e, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_fail e hf]; split <;> rfl
  | .failCause c, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_failCause c hf]; split <;> rfl
  | .sync t, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_sync t hf]; rfl
  | .suspend b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_suspend b hf]; rfl
  | .perform op r, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · cases op with
      | external j =>
        -- a host call: `asyncRoute`'s external arm, or the wrong shape
        rw [compileEff_perform (.external j) r hf]
        show PlainCode (asyncRoute (.external j) r p) = true
        dsimp only [asyncRoute]
        rcases evalTerm p.env r with _ | v <;> rfl
      | _ =>
        rw [compileEff_perform_sync _ r hf
          (Straight.perform_sync (LoopedRows.straight_perform hpl (fun _ h => by cases h)))]
        split <;> (try split) <;> rfl
  | .bind a b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_bind a b hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff a (p.child 0) (LoopedRows.bind hpl).1
  | .select s d a b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_select s d a b hf]; rfl
  | .exit b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
      · rw [compileEff_exit_frame b hf hx]
        exact plainCode_compileEff b (p.child 0) (LoopedRows.exit hpl)
      · rw [compileEff_exit_fold b hf hx]; rfl
  | .catchCause b h, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_catchCause b h hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (LoopedRows.catchCause hpl).1
  | .catchIf t b h, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_catchIf t b h hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (LoopedRows.catchIf hpl).1
  | .matchCause b v c, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_matchCause b v c hf]
      simp only [PlainCode, PlainName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (LoopedRows.matchCause hpl).1
  | .onExit b f, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_onExit b f hf]
      exact plainCode_compileEff b (p.child 0) (LoopedRows.onExit hpl).1
  | .iterate c i t st r b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_iterate c i t st r b hf]; rfl
  | .gen _, _, hpl
  | .uninterruptible _, _, hpl
  | .interruptible _, _, hpl
  | .yieldNow _, _, hpl
  | .awaitFiber _ _, _, hpl
  | .withFiber _, _, hpl
  | .scoped _, _, hpl
  | .acquireRelease _ _, _, hpl
  | .provideLayer _ _ _, _, hpl
  | .service _, _, hpl
  | .provideService _ _ _, _, hpl
  | .restore _ _, _, hpl => by simp [LoopedRows] at hpl

/-! ### Every subterm of a straight-line program is straight-line -/

/-- A node that is a program of the fragment. -/
def NodePlain : Node NativeOp → Prop
  | Node.eff e => LoopedRows e = true
  | _ => False

theorem child_plain {r : NativeEff} (hr : LoopedRows r = true) {i : Nat} {m : Node NativeOp}
    (h : (Node.eff r).child i = some m) : NodePlain m := by
  -- a constructor that is not plain is refuted by `hr` before its children are looked at
  cases r <;> first
    | (simp [LoopedRows] at hr; done)
    | (rcases i with _ | _ | _ | i <;> simp [Node.child] at h <;> subst h <;>
        simp_all [NodePlain, LoopedRows])

theorem plain_at : ∀ (path : List Nat) (n : Node NativeOp) (e : NativeEff), NodePlain n →
    Node.at_ n path = some (Node.eff e) → LoopedRows e = true
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

theorem plainCode_resolve {root : NativeEff} (hroot : LoopedRows root = true) (q : Point) :
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

theorem suspendBodyAt_other {root : NativeEff} {q : Point} {k : Nat} {n : Node NativeOp}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some n)
    (hn : ∀ e, n ≠ Node.eff e) :
    suspendBodyAt root (EffThunk.body q) = badShape := by
  cases n
  · exact absurd rfl (hn _)
  all_goals simp [suspendBodyAt, hf, h]

/-- A loop's suspension answers the loop primitive at the initial cursor. -/
theorem suspendBodyAt_iterate_at {root : NativeEff} {q : Point} {k : Nat} {c : Option Ty}
    {i t s r : Term} {b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.iterate c i t s r b))) :
    suspendBodyAt root (EffThunk.body q) =
      (match evalTerm q.env i with
       | some cursor => Prim.whileLoop (EffName.loop q) cursor
       | none => badShape) := by
  simp [suspendBodyAt, hf, h]; rfl

theorem plainCode_suspendBodyAt {root : NativeEff} (hroot : LoopedRows root = true) (q : Point) :
    PlainCode (suspendBodyAt root (EffThunk.body q)) = true := by
  rcases hf : q.fuel with _ | k
  · rw [suspendBodyAt_zero hf]; rfl
  · rcases h : Node.at_ (Node.eff root) q.path with _ | n
    · rw [suspendBodyAt_missing hf h]; rfl
    · cases n with
      | eff e =>
        have he : LoopedRows e = true := plain_at q.path (Node.eff root) e hroot h
        rcases hd : e.suspendDecided with _ | _
        · -- outside the decided heads: the body is the node compiled at its point
          rw [suspendBodyAt_of_at hf h hd]
          exact plainCode_compileEff _ q he
        · -- a decided head of the fragment is a source suspension, a select, or a loop
          rcases (LoopedRows.suspendDecided_iff he).mp hd with
            ⟨b, rfl⟩ | ⟨s, d, a, b, rfl⟩ | ⟨c, i, t, st, r, b, rfl⟩
          · rw [suspendBodyAt_suspend hf h]
            exact plainCode_resolve hroot _
          · rcases hdec : (evalTerm q.env s).bind d.decide with _ | ⟨first, bound⟩
            · rw [suspendBodyAt_select_bad hf h hdec]; rfl
            · rw [suspendBodyAt_select_of_decide hf h hdec]
              exact plainCode_resolve hroot _
          · -- a loop: the loop primitive at the initial cursor, or the wrong shape
            rw [suspendBodyAt_iterate_at hf h]
            cases evalTerm q.env i <;> rfl
      | stmts _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | stmt _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | action _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | effs _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | layer _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | layers _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl

theorem plainCode_ofExit (ex : ExitV) : PlainCode (Prim.ofExit ex) = true := by
  cases ex <;> rfl

/-- `catchIf`'s handler answers its compiled handler at a represented, selected failure, and
the failure itself otherwise. -/
theorem plainCode_contEOf_caughtError {root : NativeEff} (hroot : LoopedRows root = true)
    (p : Point) (c : CauseV) : PlainCode (contEOf root (EffName.caughtError p) c) = true := by
  simp only [contEOf]
  split
  · split
    · exact plainCode_resolve hroot _
    · rfl
  · rfl

theorem plainCode_contAOf {root : NativeEff} (hroot : LoopedRows root = true) {n : EffName}
    (hn : PlainName n = true) (v : Val) : PlainCode (contAOf root n v) = true := by
  cases n <;> simp [PlainName] at hn
  all_goals first
    | rfl
    | exact plainCode_resolve hroot _
    | exact plainCode_ofExit _

theorem plainCode_contEOf {root : NativeEff} (hroot : LoopedRows root = true) {n : EffName}
    (hn : PlainName n = true) (c : CauseV) : PlainCode (contEOf root n c) = true := by
  cases n <;> simp [PlainName] at hn
  all_goals first
    | rfl
    | exact plainCode_resolve hroot _
    | exact plainCode_ofExit _
    | exact plainCode_contEOf_caughtError hroot _ _

/-- Fresh source callbacks still answer plain code at any captured point. -/
theorem plainCode_contAAt {root : NativeEff} (hroot : LoopedRows root = true) {n : EffName}
    (hn : PlainName n = true) (v : Val) : PlainCode ((interpAt root []).contA n v) = true := by
  cases n <;> simp [PlainName] at hn
  all_goals first
    | rfl
    | exact plainCode_resolve hroot _
    | exact plainCode_ofExit _

theorem plainCode_contEAt {root : NativeEff} (hroot : LoopedRows root = true) {n : EffName}
    (hn : PlainName n = true) (c : CauseV) : PlainCode ((interpAt root []).contE n c) = true := by
  cases n <;> simp [PlainName] at hn
  all_goals first
    | rfl
    | exact plainCode_resolve hroot _
    | exact plainCode_ofExit _
    | exact plainCode_contEOf_caughtError hroot _ _

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
  | Prim.whileLoop _ _ => true
  | _ => false

theorem localStep_success (root : NativeEff) (v : Val) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.success v) K i) s =
      exitFrom root (Exit.success v) (popOf (fiberOf (Prim.success v) K i) (Exit.success v)) s :=
  by aesop

theorem localStep_failure (root : NativeEff) (c : CauseV) (K : List NCode) (i : Bool)
    (s : Stores) :
    localStep root (fiberOf (Prim.failure c) K i) s =
      exitFrom root (Exit.failure c) (popOf (fiberOf (Prim.failure c) K i) (Exit.failure c)) s :=
  by aesop

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

/-- A registration is a self-loop of the frame machine: the local step leaves the fiber where
it is. -/
theorem localStep_async (root : NativeEff) (n : EffName) (w : Bool) (c : Option EffName)
    (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.async n w c) K i) s =
      .running (fiberOf (Prim.async n w c) K i) s := rfl

theorem eq_async_of_isCall {cur : NCode} (h : IsCall cur = true) :
    ∃ n w c, cur = Prim.async n w c := by
  cases cur with
  | async n w c => exact ⟨n, w, c, rfl⟩
  | _ => simp only [IsCall, Bool.false_eq_true] at h

/-- A fiber whose local step finishes is at no host call. -/
theorem isCall_false_of_finished {root : NativeEff} {cur : NCode} {K : List NCode} {i : Bool}
    {s : Stores} {ex : ExitV} {s' : Stores}
    (h : localStep root (fiberOf cur K i) s = .finished ex s') : IsCall cur = false := by
  cases hc : IsCall cur
  · rfl
  · obtain ⟨n', w, c, rfl⟩ := eq_async_of_isCall hc
    rw [localStep_async] at h
    cases h

/-! ### A loop's decisions are plain -/

theorem plainCode_loopFinishAt (root : NativeEff) (q : Point) (c : Val) :
    PlainCode (loopFinishAt root q c) = true := by
  unfold loopFinishAt
  split
  · split <;> rfl
  · rfl

/-- What a loop does next is plain code either way: the body resolved at the loop's child, or
a finishing exit. -/
theorem plainCode_loopNextAt {root : NativeEff} (hroot : LoopedRows root = true) (q : Point)
    (c : Val) : PlainCode (loopNextAt root q c).code = true := by
  unfold loopNextAt
  split
  · split
    · exact plainCode_resolve hroot _
    · exact plainCode_loopFinishAt root q c
    · rfl
  · rfl

theorem plainCode_loopResumeAt {root : NativeEff} (hroot : LoopedRows root = true) (q : Point)
    (c v : Val) : PlainCode (loopResumeAt root q c v).code = true := by
  unfold loopResumeAt
  split
  · split
    · exact plainCode_loopNextAt hroot q _
    · rfl
  · rfl

/-- Where a loop's decision leaves the fiber is a plain fiber over a plain stack. -/
theorem enter_plain (q : Point) (K : List NCode) (i : Bool)
    (ln : LoopNext Val NCode) (hcode : PlainCode ln.code = true) (hK : PlainStack K) :
    ∃ cur' K' i', enter q K i ln = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K' := by
  cases ln with
  | «continue» next body => exact ⟨_, _, _, rfl, hcode, hK.cons rfl⟩
  | finish code => exact ⟨_, _, _, rfl, hcode, hK⟩

/-! ### The local step keeps the fiber plain -/

set_option linter.unusedSimpArgs false in
theorem localStep_success_plain {root : NativeEff} (hroot : LoopedRows root = true)
    (v : Val) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores)
    (hK : PlainStack K)
    (h : localStep root (fiberOf (Prim.success v) K i) s = .running fr' s') :
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K' := by
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
      exact ⟨_, _, _, rfl, plainCode_contAAt hroot hf.2 v, hK'⟩
    · rw [step_success_pass_onFailure] at h
      exact ih i hK' h
    · rw [step_success_onSuccessAndFailure] at h
      cases h
      exact ⟨_, _, _, rfl, plainCode_contAAt hroot hf.2.1 v, hK'⟩
    · rw [step_success_exitFrame] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK'⟩
    · next b n flag =>
      obtain ⟨p, rfl, rfl, _⟩ := plainFrame_onExit hf
      have hm := step_ofExit_onExit root (Exit.success v) b p K i s
      simp only [Prim.ofExit] at hm
      rw [hm] at h
      cases h
      refine ⟨_, _, _, rfl, ?_, hK'.mask i⟩
      simp [finalizerCode, PlainCode, PlainName, plainCode_resolve hroot, interpAt, interpOf]
    · next flag =>
      cases flag <;> simp only [PlainFrame] at hf
      all_goals try exact absurd hf (by decide)
      rw [step_success_pass_setInterruptible] at h
      exact ih true hK' h
    · next loop cursor =>
      cases loop <;> simp only [PlainFrame, Bool.false_eq_true] at hf
      next q =>
      rw [step_success_enter_at root q cursor v K i s] at h
      cases h
      exact enter_plain q K i _ (plainCode_loopResumeAt hroot _ cursor v) hK'

set_option linter.unusedSimpArgs false in
theorem localStep_failure_plain {root : NativeEff} (hroot : LoopedRows root = true)
    (c : CauseV) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores)
    (hK : PlainStack K)
    (h : localStep root (fiberOf (Prim.failure c) K i) s = .running fr' s') :
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K' := by
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
      exact ⟨_, _, _, rfl, plainCode_contEAt hroot hf.2 c, hK'⟩
    · rw [step_failure_onSuccessAndFailure] at h
      cases h
      exact ⟨_, _, _, rfl, plainCode_contEAt hroot hf.2.2 c, hK'⟩
    · rw [step_failure_exitFrame] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK'⟩
    · next b n flag =>
      obtain ⟨p, rfl, rfl, _⟩ := plainFrame_onExit hf
      have hm := step_ofExit_onExit root (Exit.failure c) b p K i s
      simp only [Prim.ofExit] at hm
      rw [hm] at h
      cases h
      refine ⟨_, _, _, rfl, ?_, hK'.mask i⟩
      simp [finalizerCode, PlainCode, PlainName, plainCode_resolve hroot, interpAt, interpOf]
    · next flag =>
      cases flag <;> simp only [PlainFrame] at hf
      all_goals try exact absurd hf (by decide)
      rw [step_failure_pass_setInterruptible] at h
      exact ih true hK' h
    · next loop cursor =>
      cases loop <;> simp only [PlainFrame, Bool.false_eq_true] at hf
      next q =>
      rw [step_failure_pass_whileLoop] at h
      exact ih i hK' h

-- The `PlainFrame` argument is spent in some branches of the frame case split and not in
-- others; the linter reports the latter.
set_option linter.unusedSimpArgs false in
theorem localStep_plain {root : NativeEff} (hroot : LoopedRows root = true) :
    ∀ (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores),
      PlainCode cur = true → PlainStack K →
      localStep root (fiberOf cur K i) s = .running fr' s' →
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K' := by
  intro cur K i s fr' s' hpl hK h
  cases cur with
  | success v =>
    exact localStep_success_plain hroot v K i s fr' s' hK h
  | failure c =>
    exact localStep_failure_plain hroot c K i s fr' s' hK h
  | yieldableError e =>
    rw [step_yieldableError] at h
    cases h
    exact ⟨_, _, _, rfl, rfl, hK⟩
  | sync thunk =>
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
  | suspend thunk =>
    cases thunk <;> simp only [PlainCode, Bool.false_eq_true] at hpl
    rw [step_suspend] at h
    cases h
    exact ⟨_, _, _, rfl, plainCode_suspendBodyAt hroot _, hK⟩
  | onSuccess b n =>
    rw [step_push_onSuccess] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp [PlainFrame, hpl.1, hpl.2])⟩
  | onFailure b n =>
    rw [step_push_onFailure] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp [PlainFrame, hpl.1, hpl.2])⟩
  | onSuccessAndFailure b n₁ n₂ =>
    rw [step_push_onSuccessAndFailure] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp [PlainFrame, hpl.1, hpl.2.1, hpl.2.2])⟩
  | exitFrame b =>
    rw [step_push_exitFrame] at h
    cases h
    exact ⟨_, _, _, rfl, hpl, hK.cons hpl⟩
  | onExit b n flag =>
    obtain ⟨p, rfl, rfl, hb⟩ := plainCode_onExit hpl
    rw [step_push_onExit] at h
    cases h
    exact ⟨_, _, _, rfl, hb, hK.cons hb⟩
  | whileLoop loop cursor =>
    cases loop <;> simp only [PlainCode, Bool.false_eq_true] at hpl
    next q =>
    rw [step_whileLoop_enter_at root q cursor K i s] at h
    cases h
    exact enter_plain q K i _ (plainCode_loopNextAt hroot _ cursor) hK
  | async n w c =>
    -- a host call: the self-loop
    rw [localStep_async] at h
    cases h
    exact ⟨_, _, _, rfl, hpl, hK⟩
  | withFiber _ | iterator _ _ | setInterruptible _
  | yieldNowWith _ | asyncFinalizer _ | onSuccessConst _ _ =>
    simp [PlainCode] at hpl

/-! ## Quiet stores: nothing owed to any waiter -/

/-- No resume is owed and no cell has a waiter. A straight-line program never registers a
waiter (`Deferred.await` is an `async` row), so the stores it reaches from `Stores.empty`
stay quiet, and `Cmd.drainDue` is the identity on them. -/
def Quiet (s : Stores) : Prop :=
  s.deferreds.due = [] ∧ ∀ c ∈ s.deferreds.cells, c.wake.waiters = [] ∧ c.wake.batch = none

theorem Quiet.empty : Quiet Stores.empty := ⟨rfl, fun _ h => by simp [Stores.empty] at h⟩

theorem Quiet.of_deferreds_eq {s s' : Stores} (h : s'.deferreds = s.deferreds) (hq : Quiet s) :
    Quiet s' := by
  unfold Quiet
  rw [h]
  exact hq

theorem DeferredStore.make_quiet {d : DeferredStore} (hdue : d.due = [])
    (hcells : ∀ c ∈ d.cells, c.wake.waiters = [] ∧ c.wake.batch = none) :
    (d.make).2.due = [] ∧
      ∀ c ∈ (d.make).2.cells, c.wake.waiters = [] ∧ c.wake.batch = none := by
  refine ⟨hdue, fun c hc => ?_⟩
  simp only [DeferredStore.make, List.mem_append, List.mem_singleton] at hc
  rcases hc with hc | rfl
  · exact hcells c hc
  · exact ⟨rfl, rfl⟩

@[aesop safe -100 apply (rule_sets := [Effect4.Fibers])]
theorem DeferredStore.complete_quiet {d : DeferredStore} (hdue : d.due = [])
    (hcells : ∀ c ∈ d.cells, c.wake.waiters = [] ∧ c.wake.batch = none) (cell : DeferredKey)
    (e : Completion Val Err Defect FiberId Ann) :
    (d.complete cell e).1.due = [] ∧
      ∀ c ∈ (d.complete cell e).1.cells, c.wake.waiters = [] ∧ c.wake.batch = none := by
  unfold DeferredStore.complete
  split
  · exact ⟨hdue, hcells⟩
  · rename_i c hc
    split
    · exact ⟨hdue, hcells⟩
    · have hmem : c ∈ d.cells := List.mem_of_getElem? hc
      simp only [WakeList.wakeAll, (hcells c hmem).1, List.map_nil, List.append_nil,
        DeferredStore.setCell]
      refine ⟨hdue, fun c' hc' => ?_⟩
      rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
      · exact hcells c' hc'
      · exact ⟨rfl, (hcells c hmem).2⟩

theorem DeferredStore.cancel_quiet {d : DeferredStore} (hdue : d.due = [])
    (hcells : ∀ c ∈ d.cells, c.wake.waiters = [] ∧ c.wake.batch = none) (cell : DeferredKey)
    (w : FiberId) (t : Nat) :
    (d.cancel cell w t).due = [] ∧
      ∀ c ∈ (d.cancel cell w t).cells, c.wake.waiters = [] ∧ c.wake.batch = none := by
  unfold DeferredStore.cancel
  split
  · exact ⟨hdue, hcells⟩
  · rename_i c hc
    have hmem : c ∈ d.cells := List.mem_of_getElem? hc
    simp only [DeferredStore.setCell]
    refine ⟨hdue, fun c' hc' => ?_⟩
    rcases List.mem_or_eq_of_mem_set hc' with hc' | rfl
    · exact hcells c' hc'
    · simp [WakeList.cancel, WakeList.pending, (hcells c hmem).1, (hcells c hmem).2]

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
    -- `scopeAdd` (V1): three branches, none touching the Deferred store
    | (simp only [syncOpStep] at h
       split at h
       · cases h
       · split at h
         · simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, -⟩ := h
           exact ⟨hdue, hcells⟩
         · simp only [Option.some.injEq, Prod.mk.injEq] at h
           obtain ⟨rfl, -⟩ := h
           exact ⟨hdue, hcells⟩)
    -- the join's arms (`scopeFork`, the memo world): a store match, at most one `if` under it;
    -- only `memoBuild` (`make`) and `memoComplete` (`complete`) reach the Deferred store
    | (simp only [syncOpStep] at h
       split at h <;> (try split at h) <;> first
         | (simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            first
              | exact ⟨hdue, hcells⟩
              | exact DeferredStore.complete_quiet hdue hcells _ _)
         | cases h)

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
    (interpOf root table).dueResumes s = ([], s) := by
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

theorem fiberAt_frame (fr : NFiber) (k : Nat) : (fiberAt fr k).frame = fr :=
  by aesop

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

/-- The root fiber parked by the injected Yield (`effect.ts:647-655,982-990`):
the success-only frame retains the previous program, and the dispatcher answers
with success unit. The next entry delivers that answer before returning to the
saved program. -/
def parkedAt (fr : NFiber) (k : Nat) (t : Nat) : NRunFiber :=
  { fiberAt fr k with
    running := false
    frame := { fr with
      current := Prim.success Val.unit
      stack := Prim.onSuccessConst (Prim.yieldNowWith 0) fr.current :: fr.stack }
    parked := Parked.withGuard t
    pending := [⟨t, none, [], [], Resume.void, false⟩]
    dispatcher := Dispatcher.empty.enqueue 0 (Task.resume Api.root t (Prim.success Val.unit)) }

/-- The machine after a yield: the root parked on token `t`, its dispatcher armed, the next
token taken. -/
def Myield (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [parkedAt fr k t], nextId := 1, nextToken := t + 1, armed := [Api.root],
    trace := tr }

/-- No completed exit is visible while the single root fiber is running. -/
theorem M_completedExits (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).completedExits = [] :=
  by aesop

theorem Myield_completedExits (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).completedExits = [] :=
  by aesop

theorem M_stuck (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).stuck = none :=
  by aesop

theorem M_state (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).state = s :=
  by aesop

theorem M_middleware (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).middlewareInstalled = false :=
  by aesop

theorem M_fiber? (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).fiber? Api.root = some (fiberAt fr k) :=
  by aesop

theorem M_update (fr fr' : NFiber) (s : Stores) (k k' : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt).update (fiberAt fr' k') = M fr' s k' tr nt :=
  by aesop

theorem M_emit (fr : NFiber) (s : Stores) (k : Nat) (tr ev : NTrace) (nt : Nat) :
    (M fr s k tr nt).emit ev = M fr s k (tr ++ ev) nt := by
  -- the field-local guard on an empty emit (direction L4): the trace is the trace
  cases ev with
  | nil => simp [M, RunMachine.emit]
  | cons _ _ => rfl

theorem Mexit_stuck (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).stuck = none :=
  by aesop

theorem Mexit_armed (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).armed = [] :=
  by aesop

theorem Mexit_state (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).state = s :=
  by aesop

theorem Mexit_finished (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt).finished = true :=
  by aesop

theorem Mexit_exit (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) :
    ((Mexit root ex fr s k tr nt).fiber? Api.root).bind RunFiber.exit = some ex :=
  by aesop

theorem Myield_stuck (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).stuck = none :=
  by aesop

theorem Myield_state (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).state = s :=
  by aesop

theorem Myield_armed (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).armed = [Api.root] :=
  by aesop

theorem Myield_fiber? (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t).fiber? Api.root = some (parkedAt fr k t) :=
  by aesop

/-! ### What the interp of a root program classifies -/

theorem parkOf_sync (root : NativeEff) (thunk : EffThunk) :
    (interpAt root []).parkOf (Prim.sync thunk) = none :=
  by aesop

theorem parkOf_plain (root : NativeEff) {cur : NCode} (h : PlainCode cur = true) :
    (interpAt root []).parkOf cur = none := by
  cases cur
  all_goals first
    | rfl
    | (rename_i thunk; cases thunk <;> first | rfl | simp [PlainCode] at h)

theorem syncState_op (root : NativeEff) (o : SyncOp) (s : Stores) :
    (interpAt root []).syncState (EffThunk.op o) s = syncOpStep o s :=
  by aesop

theorem syncState_pure (root : NativeEff) (p : Point) (s : Stores) :
    (interpAt root []).syncState (EffThunk.pure p) s = none :=
  by aesop

theorem syncValue_op (root : NativeEff) (o : SyncOp) :
    (interpAt root []).syncValue (EffThunk.op o) = Val.unit :=
  by aesop

theorem syncValue_pure (root : NativeEff) (p : Point) :
    (interpAt root []).syncValue (EffThunk.pure p) = syncValueAt root (EffThunk.pure p) :=
  by aesop

/-! ### `evaluatePrim` on a plain fiber is the local step -/

theorem evaluatePrim_stepShape (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (cur : NCode) (hcur : f.frame.current = cur) (hp : (interpAt root []).parkOf cur = none)
    (hsh : StepShape cur = true) :
    evaluatePrim (interpAt root []) m f false = evaluatePrim.stepFrame (interpAt root []) m f false := by
  cases cur <;> simp [StepShape] at hsh <;> simp only [evaluatePrim, hcur, hp]

theorem evaluatePrim_success (root : NativeEff) (m : Api.Machine) (f : NRunFiber) (v : Val)
    (hcur : f.frame.current = Prim.success v) :
    evaluatePrim (interpAt root []) m f false =
      evaluatePrim.finalizerOr (interpAt root []) m f false (Exit.success v) := by
  simp only [evaluatePrim, hcur, parkOf_plain root (cur := Prim.success v) rfl]

theorem evaluatePrim_failure (root : NativeEff) (m : Api.Machine) (f : NRunFiber) (c : CauseV)
    (hcur : f.frame.current = Prim.failure c) :
    evaluatePrim (interpAt root []) m f false =
      evaluatePrim.finalizerOr (interpAt root []) m f false (Exit.failure c) := by
  simp only [evaluatePrim, hcur, parkOf_plain root (cur := Prim.failure c) rfl]

theorem evaluatePrim_sync_op (root : NativeEff) (m : Api.Machine) (f : NRunFiber) (o : SyncOp)
    (s₁ : Stores) (v : Val) (hcur : f.frame.current = Prim.sync (EffThunk.op o))
    (hs : syncOpStep o m.state = some (s₁, v)) :
    evaluatePrim (interpAt root []) m f false =
      ⟨{ m with state := s₁ }, { f with frame := { f.frame with current := Prim.success v } },
        false, Outcome.answered, [Cmd.drainDue]⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_op, hs]

theorem evaluatePrim_sync_op_none (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (o : SyncOp) (hcur : f.frame.current = Prim.sync (EffThunk.op o))
    (hs : syncOpStep o m.state = none) :
    evaluatePrim (interpAt root []) m f false =
      ⟨m, { f with frame := { f.frame with
          current := Prim.success ((interpAt root []).syncValue (EffThunk.op o)) } },
        false, Outcome.answered, []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_op, hs]

theorem evaluatePrim_sync_pure (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (p : Point) (hcur : f.frame.current = Prim.sync (EffThunk.pure p)) :
    evaluatePrim (interpAt root []) m f false =
      ⟨m, { f with frame := { f.frame with
          current := Prim.success ((interpAt root []).syncValue (EffThunk.pure p)) } },
        false, Outcome.answered, []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_pure]

theorem stepFrame_eq (root : NativeEff) (m : Api.Machine) (f : NRunFiber) :
    evaluatePrim.stepFrame (interpAt root []) m f false =
      evaluatePrim.finishFrame m f false (f.frame.step (primOf root)).1
        (f.frame.step (primOf root)).2 [] :=
  by aesop

/-- The frame machine's answer to a value, from the pop alone. -/
theorem step_fst_success (root : NativeEff) (v : Val) (K : List NCode) (i : Bool) :
    ((fiberOf (Prim.success v) K i).step (primOf root)).1 =
      resumeOf root (Exit.success v)
        ((fiberOf (Prim.success v) K i).getCont Effect4.Arm.contA false) := by
  show (FrameFiber.resumeValue (primOf root) (fiberOf (Prim.success v) K i) v
    (some (Exit.success v))).1 = _
  unfold FrameFiber.resumeValue resumeOf
  generalize (fiberOf (Prim.success v) K i).getCont Effect4.Arm.contA false = pop
  rcases pop with ⟨ans, _, _, fib, carried⟩
  cases ans with
  | frame fr =>
    dsimp only
    rcases Prim.armA (primOf root) fr v (some (Exit.success v)) with _ | ⟨_, _⟩ <;> rfl
  | _ => rfl

/-- The frame machine's answer to a cause, from the pop alone. -/
theorem step_fst_failure (root : NativeEff) (c : CauseV) (K : List NCode) (i : Bool) :
    ((fiberOf (Prim.failure c) K i).step (primOf root)).1 =
      resumeOf root (Exit.failure c)
        ((fiberOf (Prim.failure c) K i).getCont Effect4.Arm.contE true) := by
  show (FrameFiber.resumeCause (primOf root) (fiberOf (Prim.failure c) K i) c
    (some (Exit.failure c))).1 = _
  unfold FrameFiber.resumeCause resumeOf
  rw [FrameFiber.getCont_no_pending _ _ _ (some c) rfl]
  simp only [FramePop.deliveredExit, Option.getD_some, Option.map_some]
  generalize (fiberOf (Prim.failure c) K i).getCont Effect4.Arm.contE true = pop
  rcases pop with ⟨ans, _, _, fib, carried⟩
  cases ans with
  | frame fr =>
    dsimp only
    rcases Prim.armE (primOf root) fr c (some (Exit.failure c)) with _ | ⟨_, _⟩ <;> rfl
  | _ => rfl

/-- The iteration a local step predicts, its events left open. -/
def iterOf (m : Api.Machine) (f : NRunFiber) (ev : NTrace) : LocalStep → NIter
  | .running fr' _ => ⟨m.emit ev, { f with frame := fr' }, false, Outcome.continue_, []⟩
  | .finished ex _ =>
    ⟨m.emit ev, { f with frame := frameExitState f.frame }, false, Outcome.finished ex, []⟩

/-- On a plain fiber whose current primitive is not a `sync`, `evaluatePrim` is the local
step: the frame machine's step, or — for an exit meeting an `onExit` frame — the finalizer
program under the mask, exactly as `exitFrom` spells it. -/
theorem evaluatePrim_localStep (root : NativeEff) (m : Api.Machine) (cur : NCode)
    (K : List NCode) (i : Bool) (k : Nat) (hpl : PlainCode cur = true)
    (hns : ∀ t, cur ≠ Prim.sync t) (hnc : IsCall cur = false) :
    ∃ ev, evaluatePrim (interpAt root []) m (fiberAt (fiberOf cur K i) k) false =
      iterOf m (fiberAt (fiberOf cur K i) k) ev (localStep root (fiberOf cur K i) m.state) := by
  cases cur with
  | success v =>
    rw [evaluatePrim_success root m _ v rfl, localStep_success]
    unfold evaluatePrim.finalizerOr exitFrom popOf
    simp only [stepFrame_eq, fiberAt_frame, step_fst_success]
    simp only [FramePop.deliveredExit]
    unfold iterOf evaluatePrim.finishFrame
    have hcur : (fiberOf (Prim.success v) K i).current = Prim.success v := rfl
    simp only [fiberAt_frame, frameExitState, hcur]
    generalize (fiberOf (Prim.success v) K i).getCont Effect4.Arm.contA false = pop
    rcases pop with ⟨ans, _, _, fib, carried⟩
    cases ans
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · rename_i fr
      dsimp only [resumeOf]
      generalize Prim.armA (primOf root) fr v (some (Exit.success v)) = arm
      cases fr with
      | onExit body fin flag =>
        dsimp only
        rcases (interpAt root []).finalizerProgram fin (Exit.success v) with _ | program
        · rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      | _ => rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | failure c =>
    rw [evaluatePrim_failure root m _ c rfl, localStep_failure]
    unfold evaluatePrim.finalizerOr exitFrom popOf
    simp only [stepFrame_eq, fiberAt_frame, step_fst_failure]
    rw [FrameFiber.getCont_no_pending _ _ _ (some c) rfl]
    simp only [FramePop.deliveredExit, Option.getD_some]
    unfold iterOf evaluatePrim.finishFrame
    have hcur : (fiberOf (Prim.failure c) K i).current = Prim.failure c := rfl
    simp only [fiberAt_frame, frameExitState, hcur]
    generalize (fiberOf (Prim.failure c) K i).getCont Effect4.Arm.contE true = pop
    rcases pop with ⟨ans, _, _, fib, carried⟩
    cases ans
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
    · rename_i fr
      dsimp only [resumeOf]
      generalize Prim.armE (primOf root) fr c (some (Exit.failure c)) = arm
      cases fr with
      | onExit body fin flag =>
        dsimp only
        rcases (interpAt root []).finalizerProgram fin (Exit.failure c) with _ | program
        · rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
        · exact ⟨_, rfl⟩
      | _ => rcases arm with _ | ⟨_, _⟩ <;> exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩
  | sync t => exact absurd rfl (hns t)
  | yieldableError _ | suspend _ | onSuccess _ _ | onFailure _ _
  | onSuccessAndFailure _ _ _ | exitFrame _ | onExit _ _ _ | whileLoop _ _ =>
    rw [evaluatePrim_stepShape root m _ _ rfl (parkOf_plain root hpl) rfl, stepFrame_eq,
      fiberAt_frame, localStep_other root _ K i m.state (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h)]
    rcases ((fiberOf _ K i).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩
  | async n w c => cases hpl.symm.trans hnc
  | _ => simp only [PlainCode, Bool.false_eq_true] at hpl

/-! ### The native scope protocol does not intercept the plain run -/

/-- A plain stack cannot answer with the scoped callback name. Restoring mask
frames are passed using the same pop equations as the local run. -/
theorem popOf_plain_not_scoped (cur : NCode) (K : List NCode) (i : Bool)
    (hK : PlainStack K) (ex : ExitV) (body : NCode) (previous : Ctx) (scope : Nat)
    (flag : Bool) :
    (popOf (fiberOf cur K i) ex).answer ≠
      ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag) := by
  induction K generalizing i with
  | nil => cases ex <;> simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf]
  | cons frame K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases frame <;> (try simp only [PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf)
    · next b n =>
      cases ex with
      | success v =>
        simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf, Prim.ensure,
          Prim.answerOf, Prim.hasArm, Prim.arms]
      | failure c =>
        change (FrameFiber.popFrom Effect4.Arm.contE true (Prim.onSuccess b n :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass Effect4.Arm.contE true _ K cur i rfl rfl).1]
        exact ih i hK'
    · next b n =>
      cases ex with
      | success v =>
        change (FrameFiber.popFrom Effect4.Arm.contA false (Prim.onFailure b n :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass Effect4.Arm.contA false _ K cur i rfl rfl).1]
        exact ih i hK'
      | failure c =>
        simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf, Prim.ensure,
          Prim.answerOf, Prim.hasArm, Prim.arms, FrameFiber.interrupted]
    · cases ex <;>
        simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf, Prim.ensure,
          Prim.answerOf, Prim.hasArm, Prim.arms, FrameFiber.interrupted]
    · cases ex <;>
        simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf, Prim.ensure,
          Prim.answerOf, Prim.hasArm, Prim.arms, FrameFiber.interrupted]
    · next b n finalizerFlag =>
      cases n <;> cases finalizerFlag <;> simp only [Bool.false_eq_true] at hf
      cases ex <;> cases i <;>
        simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf, Prim.ensure,
          Prim.answerOf, Prim.hasArm, Prim.arms, FrameFiber.interrupted]
    · next restoreFlag =>
      cases restoreFlag <;> simp only [Bool.false_eq_true] at hf
      cases ex
      · change (FrameFiber.popFrom Effect4.Arm.contA false (Prim.setInterruptible true :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass_setInterruptible Effect4.Arm.contA false K cur i rfl).1]
        exact ih true hK'
      · change (FrameFiber.popFrom Effect4.Arm.contE true (Prim.setInterruptible true :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass_setInterruptible Effect4.Arm.contE true K cur i rfl).1]
        exact ih true hK'
    · next loop cursor =>
      cases ex with
      | success v =>
        simp [popOf, FrameFiber.getCont, FrameFiber.popFrom, fiberOf, Prim.ensure,
          Prim.answerOf, Prim.hasArm, Prim.arms]
      | failure c =>
        change (FrameFiber.popFrom Effect4.Arm.contE true (Prim.whileLoop loop cursor :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass Effect4.Arm.contE true _ K cur i rfl rfl).1]
        exact ih i hK'

/-- The native exit adapter is the ordinary evaluator when the actual pop does
not answer the scoped callback. -/
theorem exitScoped_eq_evaluatePrim (root : NativeEff) (m : Api.Machine)
    (f : NRunFiber) (yielding : Bool) (ex : ExitV)
    (h : ∀ body previous scope flag, (popOf f.frame ex).answer ≠
      ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag)) :
    exitScoped root m f yielding ex = evaluatePrim (interpAt root m.completedExits) m f yielding := by
  unfold exitScoped
  cases ex <;> dsimp only <;> split
  · next body previous scope flag hpop => exact False.elim (h body previous scope flag hpop)
  · rfl
  · next body previous scope flag hpop =>
    rw [FrameFiber.getCont_answer_cause] at hpop
    exact False.elim (h body previous scope flag hpop)
  · rfl

/-- Plain code and a plain stack exclude both native scoped entry and exit.
The construction view remains the machine's actual completed-exit view. -/
theorem evaluateNative_plain (root : NativeEff) (m : Api.Machine) (cur : NCode)
    (K : List NCode) (i : Bool) (k : Nat) (hpl : PlainCode cur = true) (hK : PlainStack K)
    (hnc : IsCall cur = false) :
    evaluateNative root m (fiberAt (fiberOf cur K i) k) false table =
      evaluatePrim (interpAt root m.completedExits) m (fiberAt (fiberOf cur K i) k) false := by
  cases cur with
  | success v =>
    change exitScoped root m _ false (Exit.success v) = _
    apply exitScoped_eq_evaluatePrim
    exact popOf_plain_not_scoped _ K i hK _
  | failure c =>
    change exitScoped root m _ false (Exit.failure c) = _
    apply exitScoped_eq_evaluatePrim
    exact popOf_plain_not_scoped _ K i hK _
  | async n w c => cases hpl.symm.trans hnc
  | _ => first | rfl | simp [PlainCode] at hpl

/-- The finished local-step hypothesis itself excludes an answering scoped
callback; the older stack need not be plain for this equation. -/
theorem evaluateNative_of_finished (root : NativeEff) (m : Api.Machine) (cur : NCode)
    (K : List NCode) (i : Bool) (k : Nat) (hpl : PlainCode cur = true)
    (ex : ExitV) (s' : Stores)
    (hstep : localStep root (fiberOf cur K i) m.state = .finished ex s') :
    evaluateNative root m (fiberAt (fiberOf cur K i) k) false table =
      evaluatePrim (interpAt root m.completedExits) m (fiberAt (fiberOf cur K i) k) false := by
  cases cur with
  | success v =>
    change exitScoped root m _ false (Exit.success v) = _
    apply exitScoped_eq_evaluatePrim
    intro body previous scope flag
    exact exitFrom_finished_not_onExit root _ _ _ ex s' hstep body
      (EffName.scopedExit previous scope) flag
  | failure c =>
    change exitScoped root m _ false (Exit.failure c) = _
    apply exitScoped_eq_evaluatePrim
    intro body previous scope flag
    exact exitFrom_finished_not_onExit root _ _ _ ex s' hstep body
      (EffName.scopedExit previous scope) flag
  | async n w c =>
    rw [localStep_async] at hstep
    cases hstep
  | _ => first | rfl | simp [PlainCode] at hpl

/-! ### One iteration under the budget: no yield, the primitive evaluated at count `k + 1` -/

theorem iteration_M (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool) (s : Stores)
    (k : Nat) (tr : NTrace) (nt : Nat) (hk : k + 1 < defaultBudget) :
    iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf cur K i) s k tr nt) (fiberAt (fiberOf cur K i) k) false =
      evaluateNative root (M (fiberOf cur K i) s k tr nt)
        (fiberAt (fiberOf cur K i) (k + 1)) false table := by
  have hidle : runloopTop (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) k :=
    runloopTop_idle _ rfl
  have hcount : countOp (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) (k + 1) := rfl
  have hno : injectYield (M (fiberOf cur K i) s k tr nt)
      (countOp (runloopTop (fiberAt (fiberOf cur K i) k))) false = none := by
    rw [hidle, hcount]
    apply injectYield_no_verdict
    rw [yieldVerdict_default _ rfl]
    exact decide_eq_false (by show ¬ (k + 1 ≥ defaultBudget); omega)
  unfold iteration
  dsimp only
  rw [hno]
  simp only [FiberEvaluator.evaluate, hidle, hcount]

/-! ### The commands, one local step each -/

/-- The loop on a finished iteration, as `drive_loop_continues` for `Outcome.finished`. -/
theorem drive_loop_finished [evaluator : FiberEvaluator EffName EffThunk Val Err Defect FiberId Ann Ctx Stores NCode NFiber
      (FrameEvent EffName EffThunk Val Err Defect FiberId Ann)]
    (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
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
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
        (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (fiberOf (Prim.success v) K i) s₁ (k + 1) tr' nt)
        (Cmd.drainDue :: Cmd.deliver Api.root false :: rest) := by
  refine ⟨tr, fun n => ?_⟩
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) k) false =
      ⟨M (fiberOf (Prim.sync (EffThunk.op o)) K i) s₁ k tr nt,
        fiberAt (fiberOf (Prim.success v) K i) (k + 1), false, Outcome.answered,
        [Cmd.drainDue]⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf, M_completedExits]
    exact evaluatePrim_sync_op root (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) (k + 1)) o s₁ v rfl hs
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle]
  try dsimp only
  rw [M_update]
  rfl

/-- A store `sync` the store does not answer: the machine's `unit`, no drain owed. -/
theorem drive_loop_sync_op_none (root : NativeEff) (o : SyncOp) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hk : k + 1 < defaultBudget) (hs : syncOpStep o s = none) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
        (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (fiberOf (Prim.success Val.unit) K i) s (k + 1) tr' nt)
        (Cmd.deliver Api.root false :: rest) := by
  refine ⟨tr, fun n => ?_⟩
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) k) false =
      ⟨M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt,
        fiberAt (fiberOf (Prim.success Val.unit) K i) (k + 1), false, Outcome.answered, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf, M_completedExits]
    exact evaluatePrim_sync_op_none root (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) (k + 1)) o rfl hs
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle]
  try dsimp only
  rw [M_update]
  rfl

/-- A pure `sync`: the term's value, no drain owed. -/
theorem drive_loop_sync_pure (root : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hk : k + 1 < defaultBudget) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
        (M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (M (fiberOf (Prim.success (syncValueAt root (EffThunk.pure p))) K i) s (k + 1) tr' nt)
        (Cmd.deliver Api.root false :: rest) := by
  refine ⟨tr, fun n => ?_⟩
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.pure p)) K i) k) false =
      ⟨M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt,
        fiberAt (fiberOf (Prim.success (syncValueAt root (EffThunk.pure p))) K i) (k + 1), false,
        Outcome.answered, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf, M_completedExits]
    exact evaluatePrim_sync_pure root (M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.pure p)) K i) (k + 1)) p rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle]
  try dsimp only
  rw [M_update]
  rfl

/-- The local step at the loop, running on: the fiber moves on, the count goes up. -/
theorem drive_loop_running (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (cur₁ : NCode)
    (K₁ : List NCode) (i₁ : Bool) (hpl : PlainCode cur = true) (hK : PlainStack K)
    (hns : ∀ t, cur ≠ Prim.sync t) (hnc : IsCall cur = false)
    (hk : k + 1 < defaultBudget)
    (hstep : localStep root (fiberOf cur K i) s = .running (fiberOf cur₁ K₁ i₁) s) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (fiberOf cur₁ K₁ i₁) s (k + 1) tr' nt)
        (Cmd.loop Api.root false :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i (k + 1) hpl hns hnc
  rw [M_state, hstep] at hev
  have hraw := evaluateNative_plain (table := table) root (M (fiberOf cur K i) s k tr nt)
    cur K i (k + 1) hpl hK hnc
  rw [M_completedExits] at hraw
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf cur K i) s k tr nt)
      (fiberAt (fiberOf cur K i) k) false =
      ⟨M (fiberOf cur K i) s k (tr ++ ev) nt, fiberAt (fiberOf cur₁ K₁ i₁) (k + 1), false,
        Outcome.continue_, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk, hraw, hev]
    simp only [iterOf, M_emit]
    rfl
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle]
  try dsimp only
  rw [M_update]
  rfl

/-- The local step at the loop, finishing: the exit path is owed. -/
theorem drive_loop_finish (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ex : ExitV)
    (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t) (hk : k + 1 < defaultBudget)
    (hstep : localStep root (fiberOf cur K i) s = .finished ex s) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (frameExitState (fiberOf cur K i)) s (k + 1) tr' nt)
        (Cmd.finish Api.root ex :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i (k + 1) hpl hns
      (isCall_false_of_finished hstep)
  rw [M_state, hstep] at hev
  have hraw := evaluateNative_of_finished (table := table) root (M (fiberOf cur K i) s k tr nt)
    cur K i (k + 1) hpl ex s hstep
  rw [M_completedExits] at hraw
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf cur K i) s k tr nt)
      (fiberAt (fiberOf cur K i) k) false =
      ⟨M (fiberOf cur K i) s k (tr ++ ev) nt, fiberAt (frameExitState (fiberOf cur K i)) (k + 1), false,
        Outcome.finished ex, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk, hraw, hev]
    simp only [iterOf, M_emit]
    rfl
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [drive_loop_finished (evaluator := evaluatorFor root table) _ _ _ _ _ _ rest ex rfl
    (M_fiber? _ _ _ _ _) (by rw [hit]), hit]
  try dsimp only
  rw [M_update]
  rfl

/-- The delivery of an answered `sync` (`Cmd.deliver`, R2-1): the local step with no loop
top and no op count. -/
theorem drive_deliver_running (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (cur₁ : NCode)
    (K₁ : List NCode) (i₁ : Bool) (hpl : PlainCode cur = true) (hK : PlainStack K)
    (hns : ∀ t, cur ≠ Prim.sync t) (hnc : IsCall cur = false)
    (hstep : localStep root (fiberOf cur K i) s = .running (fiberOf cur₁ K₁ i₁) s) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.deliver Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (fiberOf cur₁ K₁ i₁) s k tr' nt)
        (Cmd.loop Api.root false :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i k hpl hns hnc
  rw [M_state, hstep] at hev
  have hraw := evaluateNative_plain (table := table) root (M (fiberOf cur K i) s k tr nt)
    cur K i k hpl hK hnc
  rw [M_completedExits] at hraw
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?,
    FiberEvaluator.evaluate, hraw, hev, iterOf, M_emit]
  show driveState (evaluator := evaluatorFor root table) _ n
    ((M (fiberOf cur K i) s k (tr ++ ev) nt).update (fiberAt (fiberOf cur₁ K₁ i₁) k))
    ([] ++ [Cmd.loop Api.root false] ++ rest) = _
  rw [M_update]
  rfl

theorem drive_deliver_finish (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ex : ExitV)
    (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t)
    (hstep : localStep root (fiberOf cur K i) s = .finished ex s) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1) (M (fiberOf cur K i) s k tr nt)
        (Cmd.deliver Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (frameExitState (fiberOf cur K i)) s k tr' nt)
        (Cmd.finish Api.root ex :: rest) := by
  obtain ⟨ev, hev⟩ :=
    evaluatePrim_localStep root (M (fiberOf cur K i) s k tr nt) cur K i k hpl hns
      (isCall_false_of_finished hstep)
  rw [M_state, hstep] at hev
  have hraw := evaluateNative_of_finished (table := table) root (M (fiberOf cur K i) s k tr nt)
    cur K i k hpl ex s hstep
  rw [M_completedExits] at hraw
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?,
    FiberEvaluator.evaluate, hraw, hev, iterOf, M_emit]
  show driveState (evaluator := evaluatorFor root table) _ n ((M (fiberOf cur K i) s k (tr ++ ev) nt).update (fiberAt (frameExitState (fiberOf cur K i)) k))
    ([] ++ [Cmd.finish Api.root ex] ++ rest) = _
  rw [M_update]
  rfl

/-- The drain of a quiet store is a command that does nothing. -/
theorem drive_drainDue (root : NativeEff) (n : Nat) (m : Api.Machine) (rest : List NCmd)
    (hs : m.stuck = none) (hq : Quiet m.state) :
    driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1) m (Cmd.drainDue :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n m rest := by
  rcases m with ⟨fibers, races, nextId, nextToken, nextRace, mw, armed, state, trace, stuck⟩
  simp only at hs hq
  subst hs
  simp only [driveState, driveStep, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    dueResumes_quiet root hq, drainOwed, List.nil_append]

/-- The exit path of the root: no middleware, no children, no observer — the exit is stored,
the drain is owed. -/
theorem drive_finish_M (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) (rest : List NCmd) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1) (M fr s k tr nt) (Cmd.finish Api.root ex :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n (Mexit root ex fr s k tr' nt) (Cmd.drainDue :: rest) :=
  by aesop

/-- `Cmd.evaluate` on the loaded root: the fiber starts running at count zero. -/
theorem drive_evaluate_load (e : NativeEff) (fuel : Nat) (rest : List NCmd) :
    ∀ n, driveState (evaluator := evaluatorFor e table) (interpOf e table) (n + 1) (Api.load e fuel) (Cmd.evaluate Api.root :: rest) =
      driveState (evaluator := evaluatorFor e table) (interpOf e table) n (M (fiberOf (compile e fuel) []) Stores.empty 0
        [RunEvent.started Api.root] 0) (Cmd.loop Api.root false :: rest) :=
  by aesop

theorem drive_nil (root : NativeEff) (m : Api.Machine) :
    ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) n m [] = (m, [])
  | 0 => rfl
  | _ + 1 => rfl

theorem flushAll_Mexit (root : NativeEff) (fuel : Nat) (ex : ExitV) (fr : NFiber) (s : Stores)
    (k : Nat) (tr : NTrace) (nt : Nat) :
    ∀ rounds, flushAllState (evaluator := evaluatorFor root table) (interpOf root table) fuel rounds (Mexit root ex fr s k tr nt) =
      (Mexit root ex fr s k tr nt, true)
  | 0 => rfl
  | _ + 1 => rfl

/-! ### The yield: the count reaches the budget, the root parks, `flush` resumes it -/

/-- At the loop with the count about to reach `defaultBudget`, one iteration
enters the injected OnSuccess and the next evaluates Yield. Both checkpoints
are charged before the root parks (`effect.ts:647-655,982-990`). -/
theorem drive_loop_yield (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd)
    (hk : defaultBudget ≤ k + 1) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 2) (M (fiberOf cur K i) s k tr nt)
        (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (Myield (fiberOf cur K i) s (k + 2) tr' nt)
        rest := by
  let saved : NCode := Prim.onSuccessConst (Prim.yieldNowWith 0) cur
  let waiting := fiberOf (Prim.yieldNowWith 0) (saved :: K) i
  let tr₁ := tr ++ [RunEvent.yieldInjected Api.root (k + 1)] ++
    [RunEvent.frame Api.root (FrameEvent.pushed saved)]
  refine ⟨tr₁ ++ [RunEvent.parkedOn Api.root nt], fun n => ?_⟩
  have hidle : runloopTop (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) k :=
    runloopTop_idle _ rfl
  have hcount : countOp (fiberAt (fiberOf cur K i) k) = fiberAt (fiberOf cur K i) (k + 1) := rfl
  have hv : yieldVerdict (fiberAt (fiberOf cur K i) (k + 1)) = true := by
    rw [yieldVerdict_default _ rfl]
    exact decide_eq_true (by show k + 1 ≥ defaultBudget; omega)
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf cur K i) s k tr nt)
      (fiberAt (fiberOf cur K i) k) false =
      ⟨M (fiberOf cur K i) s k tr₁ nt, fiberAt waiting (k + 1),
        true, Outcome.continue_, []⟩ := by
    unfold iteration
    rw [hidle, hcount]
    unfold injectYield
    dsimp only
    rw [if_pos (by simp only [hv, Bool.not_false, Bool.true_and]; rfl)]
    rfl
  rw [show n + 2 = (n + 1) + 1 by omega]
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle]
  try dsimp only
  rw [M_update]
  simp only [List.nil_append, List.cons_append]
  have hpark : (iteration (evaluator := evaluatorFor root table) (interpOf root table) (M waiting s (k + 1) tr₁ nt)
      (fiberAt waiting (k + 1)) true).outcome = Outcome.parked := by
    simp only [iteration, injectYield_latched]
    rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, settle, hpark]
  rfl

/-- The dispatcher answers Yield with success unit and enters at count zero.
The saved constant continuation is still on the stack (`effect.ts:982-990`). -/
theorem fire_Myield_answer (root : NativeEff) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (t : Nat) :
    ∃ tr', ∀ n, fireState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1 + 1) (Myield fr s k tr t) Api.root =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (M { fr with
          current := Prim.success Val.unit
          stack := Prim.onSuccessConst (Prim.yieldNowWith 0) fr.current :: fr.stack } s 0 tr' (t + 1))
        [Cmd.loop Api.root false, Cmd.drainDue]) := by
  refine ⟨tr ++ [RunEvent.ranTask Api.root (Task.resume Api.root t (Prim.success Val.unit))] ++
    [RunEvent.resumedWith Api.root t (Prim.success Val.unit)] ++ [RunEvent.started Api.root], fun n => ?_⟩
  have hdrain : (parkedAt fr k t).dispatcher.drain =
      ([Task.resume Api.root t (Prim.success Val.unit)], Dispatcher.empty) := rfl
  unfold fireState
  simp only [Myield_fiber?, hdrain]
  dsimp only [List.foldl, fireStep, taskCmds, stepDecisionState.loop]
  simp [driveState_succ_cons, driveStep, M, Myield, parkedAt, fiberAt, RunMachine.fiber?,
    RunMachine.update, RunMachine.disarm, RunMachine.emit, RunMachine.empty, RunFiber.make, Dispatcher.empty]

/-- `flush` fires the root's dispatcher, enters at count zero and delivers its
success answer through the injected frame at count one (`effect.ts:629-655`). -/
theorem fire_Myield (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace)
    (t : Nat) :
    ∃ tr', ∀ n, fireState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1 + 1 + 1)
        (Myield (fiberOf cur K i) s k tr t) Api.root =
      stepDecisionState.loop
        (driveState (evaluator := evaluatorFor root table) (interpOf root table) n (M (fiberOf cur K i) s 1 tr' (t + 1))
          [Cmd.loop Api.root false, Cmd.drainDue]) := by
  let saved : NCode := Prim.onSuccessConst (Prim.yieldNowWith 0) cur
  let answered := fiberOf (Prim.success Val.unit) (saved :: K) i
  obtain ⟨tr₀, hstart⟩ := fire_Myield_answer root (fiberOf cur K i) s k tr t
  let popEvents : NTrace := [RunEvent.frame Api.root (FrameEvent.popped saved)]
  refine ⟨tr₀ ++ popEvents, fun n => ?_⟩
  rw [hstart]
  change stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1)
    (M answered s 0 tr₀ (t + 1)) [Cmd.loop Api.root false, Cmd.drainDue]) = _
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M answered s 0 tr₀ (t + 1)) (fiberAt answered 0) false =
      ⟨M answered s 0 (tr₀ ++ popEvents) (t + 1), fiberAt (fiberOf cur K i) 1,
        false, Outcome.continue_, []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ (by decide)]
    change exitScoped root (M answered s 0 tr₀ (t + 1)) (fiberAt answered 1) false
      (Exit.success Val.unit) = _
    rw [exitScoped_eq_evaluatePrim root _ _ _ _ (by
      intro body previous scope flag
      change ContAnswer.frame saved ≠
        ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag)
      intro h
      simp [saved] at h), M_completedExits]
    rw [evaluatePrim_success root _ _ Val.unit rfl]
    simp only [evaluatePrim.finalizerOr]
    rw [stepFrame_eq]
    have hstep : answered.step (primOf root) =
        (FrameStep.running (fiberOf cur K i), [FrameEvent.popped saved]) :=
      FrameFiber.step_success_onSuccessConst (primOf root) (fiberOf cur K i)
        (Prim.yieldNowWith 0) cur Val.unit rfl
    change evaluatePrim.finishFrame _ _ false (answered.step (primOf root)).1
      (answered.step (primOf root)).2 [] = _
    rw [hstep]
    rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle]
  try dsimp only
  rw [M_update]
  rfl

end Effect4.Program.Agreement
