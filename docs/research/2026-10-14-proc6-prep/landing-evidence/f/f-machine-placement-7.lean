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

* `ContextFreeCode`/`ContextFreeFrame`: the primitives and frames a program of the fragment with host calls
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
  | .provideService _ _ _, h | .catchIf _ _ _, h | .restore _ _, h | .defs _ _ _ _, h => by
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
def ContextFreeName : EffName → Bool
  | .cont _ | .caught _ | .caughtError _ | .onValue _ | .onCause _ | .fin _ | .restore _ | .merge _ => true
  | _ => false

/-- **A host call** as the compile writes it: `asyncRoute`'s external arm, an external
registration with no signal and no cancel. -/
def IsCall : NCode → Bool
  | Prim.async (EffName.external (.external _) _ _) false none => true
  | _ => false

/-- The primitives a program of the fragment compiles to, and the hooks answer with: a host
call among them. -/
def ContextFreeCode : NCode → Bool
  | Prim.success _ => true
  | Prim.failure _ => true
  | Prim.yieldableError _ => true
  | Prim.sync (EffThunk.pure _) => true
  | Prim.sync (EffThunk.op _) => true
  | Prim.suspend (EffThunk.body _) => true
  | Prim.onSuccess b n => ContextFreeCode b && ContextFreeName n
  | Prim.onFailure b n => ContextFreeCode b && ContextFreeName n
  | Prim.onSuccessAndFailure b n₁ n₂ => ContextFreeCode b && (ContextFreeName n₁ && ContextFreeName n₂)
  | Prim.exitFrame b => ContextFreeCode b
  | Prim.onExit b (EffName.fin _) false => ContextFreeCode b
  | Prim.whileLoop (EffName.loop _) _ => true
  | Prim.async n w c => IsCall (Prim.async n w c)
  | _ => false

/-- The frames a straight-line program pushes, and the restoring frame a mask leaves. -/
def ContextFreeFrame : NCode → Bool
  | Prim.onSuccess b n => ContextFreeCode b && ContextFreeName n
  | Prim.onFailure b n => ContextFreeCode b && ContextFreeName n
  | Prim.onSuccessAndFailure b n₁ n₂ => ContextFreeCode b && (ContextFreeName n₁ && ContextFreeName n₂)
  | Prim.exitFrame b => ContextFreeCode b
  | Prim.onExit b (EffName.fin _) false => ContextFreeCode b
  | Prim.setInterruptible true => true
  | Prim.whileLoop (EffName.loop _) _ => true
  | _ => false

/-- A plain finalizer frame has the compiled finalizer name and is uninterruptible. -/
theorem plainFrame_onExit {b : NCode} {n : EffName} {flag : Bool}
    (h : ContextFreeFrame (Prim.onExit b n flag) = true) :
    ∃ p, n = .fin p ∧ flag = false ∧ ContextFreeCode b = true := by
  cases n <;> cases flag <;> simp only [ContextFreeFrame, Bool.false_eq_true] at h
  exact ⟨_, rfl, rfl, h⟩

theorem plainCode_onExit {b : NCode} {n : EffName} {flag : Bool}
    (h : ContextFreeCode (Prim.onExit b n flag) = true) :
    ∃ p, n = .fin p ∧ flag = false ∧ ContextFreeCode b = true := by
  cases n <;> cases flag <;> simp only [ContextFreeCode, Bool.false_eq_true] at h
  exact ⟨_, rfl, rfl, h⟩

/-- A stack of plain frames. -/
def ContextFreeStack (K : List NCode) : Prop := ∀ f ∈ K, ContextFreeFrame f = true

theorem ContextFreeStack.nil : ContextFreeStack [] := fun _ h => by simp only [List.not_mem_nil] at h

theorem ContextFreeStack.cons {f : NCode} {K : List NCode} (hf : ContextFreeFrame f = true)
    (hK : ContextFreeStack K) : ContextFreeStack (f :: K) := by
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact hf
  · exact hK g hg

theorem ContextFreeStack.head {f : NCode} {K : List NCode} (h : ContextFreeStack (f :: K)) :
    ContextFreeFrame f = true :=
  by aesop

theorem ContextFreeStack.tail {f : NCode} {K : List NCode} (h : ContextFreeStack (f :: K)) :
    ContextFreeStack K := fun g hg => h g (List.mem_cons_of_mem _ hg)

theorem ContextFreeStack.mask {K : List NCode} (i : Bool) (hK : ContextFreeStack K) :
    ContextFreeStack (maskStack i K) := by
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
    ContextFreeCode (compileEff e p) = true
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
        show ContextFreeCode (asyncRoute (.external j) r p) = true
        dsimp only [asyncRoute]
        rcases evalTerm p.env r with _ | v <;> rfl
      | _ =>
        rw [compileEff_perform_sync _ r hf
          (Straight.perform_sync (LoopedRows.straight_perform hpl (fun _ h => by cases h)))]
        split
        · split <;> rfl
        · rfl
  | .bind a b, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_bind a b hf]
      simp only [ContextFreeCode, ContextFreeName, Bool.and_true]
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
      simp only [ContextFreeCode, ContextFreeName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (LoopedRows.catchCause hpl).1
  | .catchIf t b h, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_catchIf t b h hf]
      simp only [ContextFreeCode, ContextFreeName, Bool.and_true]
      exact plainCode_compileEff b (p.child 0) (LoopedRows.catchIf hpl).1
  | .matchCause b v c, p, hpl => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_matchCause b v c hf]
      simp only [ContextFreeCode, ContextFreeName, Bool.and_true]
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
  | .restore _ _, _, hpl => by simp only [LoopedRows, Bool.false_eq_true] at hpl

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

/-- The root's resolver and suspended-body hook always produce plain code. -/
structure ContextFreeHooks (root : NativeEff) : Prop where
  resolve : ∀ q, ContextFreeCode (resolve root q) = true
  suspend : ∀ q, ContextFreeCode (suspendBodyAt root (EffThunk.body q)) = true
  action : ∀ p, actionAt root p = none ∨ actionAt root p = some WithFiberAction.getContext
  noScoped : ∀ (p : Point) (body : NativeEff), Node.at_ (.eff root) p.path ≠ some (.eff (.scoped body))

private theorem loopedRows_plainCode_resolve {root : NativeEff} (hroot : LoopedRows root = true) (q : Point) :
    ContextFreeCode (resolve root q) = true := by
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

private theorem loopedRows_plainCode_suspendBodyAt {root : NativeEff} (hroot : LoopedRows root = true) (q : Point) :
    ContextFreeCode (suspendBodyAt root (EffThunk.body q)) = true := by
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
            exact loopedRows_plainCode_resolve hroot _
          · rcases hdec : (evalTerm q.env s).bind d.decide with _ | ⟨first, bound⟩
            · rw [suspendBodyAt_select_bad hf h hdec]; rfl
            · rw [suspendBodyAt_select_of_decide hf h hdec]
              exact loopedRows_plainCode_resolve hroot _
          · -- a loop: the loop primitive at the initial cursor, or the wrong shape
            rw [suspendBodyAt_iterate_at hf h]
            cases evalTerm q.env i <;> rfl
      | stmts _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | stmt _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | action _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | effs _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | layer _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | layers _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl

/-- The old fragment excludes fiber actions. Step of rows-block-host/R6;
consumer: the context-aware primitive bridge. -/
private theorem loopedRows_action {root : NativeEff} (hroot : LoopedRows root = true)
    (p : Point) : actionAt root p = none := by
  unfold actionAt
  cases h : Node.at_ (.eff root) p.path with
  | none => rfl
  | some n =>
    cases n with
    | eff e =>
      have he := plain_at p.path (.eff root) e hroot h
      cases e <;> simp only [LoopedRows, Bool.false_eq_true] at he <;> rfl
    | _ => rfl

/-- Every hook of a looped row program answers plain code.
Placement: translation-simulation, rows-block-host/R6; consumer: the hosted session laws.
Reach: the context-free fragment, with no progress or host-reply claim. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem ContextFreeHooks.of_loopedRows {root : NativeEff} (hroot : LoopedRows root = true) :
    ContextFreeHooks root where
  resolve := loopedRows_plainCode_resolve hroot
  suspend := loopedRows_plainCode_suspendBodyAt hroot
  action p := Or.inl (loopedRows_action hroot p)
  noScoped p body h := by
    have he := plain_at p.path (.eff root) (.scoped body) hroot h
    exact Bool.noConfusion he

/-! ### Plain code for the context-aware receipt lane

The context-free predicates above retain the old progress lane. These predicates
admit the context family without restricting values, service keys or budgets.
-/

/-- The continuation names admitted by the hosted context lane. -/
def PlainName : EffName → Bool
  | .cont _ | .caught _ | .caughtError _ | .onValue _ | .onCause _ | .fin _ | .restore _ | .merge _ => true
  | .provideMask _ (.program _) | .updateThen _ (.program _) _
  | .bodyThen (.program _) _ _ | .serviceLookup _ => true
  | _ => false

/-- The local code of the hosted context lane. Regions are source programs. -/
def PlainCode : NCode → Bool
  | .success _ | .failure _ | .yieldableError _ => true
  | .sync (.pure _) | .sync (.op _) | .suspend (.body _) => true
  | .onSuccess b n | .onFailure b n => PlainCode b && PlainName n
  | .onSuccessAndFailure b n m => PlainCode b && (PlainName n && PlainName m)
  | .exitFrame b => PlainCode b
  | .onExit b (.fin _) false => PlainCode b
  | .onExit b (.restoreCtx _) false => PlainCode b
  | .whileLoop (.loop _) _ => true
  | .async n w c => IsCall (.async n w c)
  | .withFiber (.act _) | .withFiber .getCtx | .withFiber .captureMask
  | .withFiber (.provideMasked _ (.program _) _)
  | .withFiber (.restoreRegion (.program _) _) | .withFiber (.setCtx _) => true
  | _ => false

/-- Frames of the context lane, including both physical mask flags and yield wrappers. -/
def PlainFrame : NCode → Bool
  | .onSuccess b n | .onFailure b n => PlainCode b && PlainName n
  | .onSuccessAndFailure b n m => PlainCode b && (PlainName n && PlainName m)
  | .exitFrame b => PlainCode b
  | .onExit b (.fin _) false => PlainCode b
  | .onExit b (.restoreCtx _) false => PlainCode b
  | .setInterruptible _ | .whileLoop (.loop _) _ => true
  | .onSuccessConst (.yieldNowWith 0) saved => PlainCode saved
  | _ => false

/-- Every frame in the context-aware stack is plain. -/
def PlainStack (K : List NCode) : Prop := ∀ f ∈ K, PlainFrame f = true

/-- Root hooks of the context lane. The native scoped interception stays excluded. -/
structure PlainHooks (root : NativeEff) : Prop where
  resolve : ∀ q, PlainCode (resolve root q) = true
  suspend : ∀ q, PlainCode (suspendBodyAt root (.body q)) = true
  action : ∀ p, actionAt root p = none ∨ actionAt root p = some WithFiberAction.getContext
  noScoped : ∀ (p : Point) (body : NativeEff),
    Node.at_ (.eff root) p.path ≠ some (.eff (.scoped body))

/-- Step of rows-block-host/R6; consumer: the code and frame adapters. -/
theorem ContextFreeName.toPlain {n : EffName} (h : ContextFreeName n = true) :
    PlainName n = true := by
  cases n <;> simp only [ContextFreeName, PlainName, Bool.false_eq_true] at h ⊢

/-- Step of rows-block-host/R6; consumer: the legacy-to-context adapters. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem ContextFreeCode.toPlain {cur : NCode} (h : ContextFreeCode cur = true) :
    PlainCode cur = true := by
  fun_induction ContextFreeCode cur
  all_goals simp only [PlainCode, Bool.and_eq_true, Bool.false_eq_true] at *
  all_goals aesop (add safe forward [ContextFreeName.toPlain])

/-- Step of rows-block-host/R6; consumer: the legacy-to-context adapters. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem ContextFreeFrame.toPlain {fr : NCode} (h : ContextFreeFrame fr = true) :
    PlainFrame fr = true := by
  cases fr
  all_goals simp only [ContextFreeFrame, PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at *
  all_goals aesop (add safe forward [ContextFreeName.toPlain, ContextFreeCode.toPlain])

/-- Step of rows-block-host/R6; consumer: the context-aware looped-row adapter. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem ContextFreeHooks.toPlain {root : NativeEff} (h : ContextFreeHooks root) : PlainHooks root where
  resolve q := ContextFreeCode.toPlain (h.resolve q)
  suspend q := ContextFreeCode.toPlain (h.suspend q)
  action := h.action
  noScoped := h.noScoped

/-- Step of rows-block-host/R6; consumer: existing looped-row sessions in the new lane. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem PlainHooks.of_loopedRows {root : NativeEff} (h : LoopedRows root = true) : PlainHooks root :=
  (ContextFreeHooks.of_loopedRows h).toPlain

/-- The resolver hook answers plain code. Consumer: the hosted step closure. -/
theorem plainCode_resolve {root : NativeEff} (hroot : ContextFreeHooks root) (q : Point) :
    ContextFreeCode (resolve root q) = true := hroot.resolve q

/-- The suspension hook answers plain code. Consumer: the hosted step closure. -/
theorem plainCode_suspendBodyAt {root : NativeEff} (hroot : ContextFreeHooks root) (q : Point) :
    ContextFreeCode (suspendBodyAt root (EffThunk.body q)) = true := hroot.suspend q

theorem plainCode_ofExit (ex : ExitV) : ContextFreeCode (Prim.ofExit ex) = true := by
  cases ex <;> rfl

/-- `catchIf`'s handler answers its compiled handler at a represented, selected failure, and
the failure itself otherwise. -/
theorem plainCode_contEOf_caughtError {root : NativeEff} (hroot : ContextFreeHooks root)
    (p : Point) (c : CauseV) : ContextFreeCode (contEOf root (EffName.caughtError p) c) = true := by
  simp only [contEOf]
  split
  · split
    · exact plainCode_resolve hroot _
    · rfl
  · rfl

theorem plainCode_contAOf {root : NativeEff} (hroot : ContextFreeHooks root) {n : EffName}
    (hn : ContextFreeName n = true) (v : Val) : ContextFreeCode (contAOf root n v) = true := by
  cases n <;> simp only [ContextFreeName, Bool.false_eq_true] at hn
  case cont p => exact plainCode_resolve hroot _
  case caught p => rfl
  case caughtError p => rfl
  case onValue p => exact plainCode_resolve hroot _
  case onCause p => rfl
  case fin p => rfl
  case restore ex => exact plainCode_ofExit _
  case merge ex => exact plainCode_ofExit _

theorem plainCode_contEOf {root : NativeEff} (hroot : ContextFreeHooks root) {n : EffName}
    (hn : ContextFreeName n = true) (c : CauseV) : ContextFreeCode (contEOf root n c) = true := by
  cases n <;> simp only [ContextFreeName, Bool.false_eq_true] at hn
  case cont p => rfl
  case caught p => exact plainCode_resolve hroot _
  case caughtError p => exact plainCode_contEOf_caughtError hroot _ _
  case onValue p => rfl
  case onCause p => exact plainCode_resolve hroot _
  case fin p => rfl
  case restore ex => exact plainCode_ofExit _
  case merge ex => exact plainCode_ofExit _

/-- Fresh source callbacks still answer plain code at any captured point. -/
theorem plainCode_contAAt {root : NativeEff} (hroot : ContextFreeHooks root) {n : EffName}
    (hn : ContextFreeName n = true) (v : Val) : ContextFreeCode ((interpAt root []).contA n v) = true := by
  cases n <;> simp only [ContextFreeName, Bool.false_eq_true] at hn
  case cont p => exact plainCode_resolve hroot _
  case caught p => rfl
  case caughtError p => rfl
  case onValue p => exact plainCode_resolve hroot _
  case onCause p => rfl
  case fin p => rfl
  case restore ex => exact plainCode_ofExit _
  case merge ex => exact plainCode_ofExit _

theorem plainCode_contEAt {root : NativeEff} (hroot : ContextFreeHooks root) {n : EffName}
    (hn : ContextFreeName n = true) (c : CauseV) : ContextFreeCode ((interpAt root []).contE n c) = true := by
  cases n <;> simp only [ContextFreeName, Bool.false_eq_true] at hn
  case cont p => rfl
  case caught p => exact plainCode_resolve hroot _
  case caughtError p => exact plainCode_contEOf_caughtError hroot _ _
  case onValue p => rfl
  case onCause p => exact plainCode_resolve hroot _
  case fin p => rfl
  case restore ex => exact plainCode_ofExit _
  case merge ex => exact plainCode_ofExit _

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
    ContextFreeCode (loopFinishAt root q c) = true := by
  unfold loopFinishAt
  split
  · split <;> rfl
  · rfl

/-- What a loop does next is plain code either way: the body resolved at the loop's child, or
a finishing exit. -/
theorem plainCode_loopNextAt {root : NativeEff} (hroot : ContextFreeHooks root) (q : Point)
    (c : Val) : ContextFreeCode (loopNextAt root q c).code = true := by
  unfold loopNextAt
  split
  · split
    · exact plainCode_resolve hroot _
    · exact plainCode_loopFinishAt root q c
    · rfl
  · rfl

theorem plainCode_loopResumeAt {root : NativeEff} (hroot : ContextFreeHooks root) (q : Point)
    (c v : Val) : ContextFreeCode (loopResumeAt root q c v).code = true := by
  unfold loopResumeAt
  split
  · split
    · exact plainCode_loopNextAt hroot q _
    · rfl
  · rfl

/-- Where a loop's decision leaves the fiber is a plain fiber over a plain stack. -/
theorem enter_plain (q : Point) (K : List NCode) (i : Bool)
    (ln : LoopNext Val NCode) (hcode : ContextFreeCode ln.code = true) (hK : ContextFreeStack K) :
    ∃ cur' K' i', enter q K i ln = fiberOf cur' K' i' ∧ ContextFreeCode cur' = true ∧ ContextFreeStack K' := by
  cases ln with
  | «continue» next body => exact ⟨_, _, _, rfl, hcode, hK.cons rfl⟩
  | finish code => exact ⟨_, _, _, rfl, hcode, hK⟩

/-! ### The local step keeps the fiber plain -/

set_option linter.unusedSimpArgs false in
theorem localStep_success_plain {root : NativeEff} (hroot : ContextFreeHooks root)
    (v : Val) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores)
    (hK : ContextFreeStack K)
    (h : localStep root (fiberOf (Prim.success v) K i) s = .running fr' s') :
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ ContextFreeCode cur' = true ∧ ContextFreeStack K' := by
  induction K generalizing i with
  | nil =>
    have he := step_exit_empty root (Exit.success v) i s
    simp only [Prim.ofExit] at he
    rw [he] at h
    cases h
  | cons f K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases f <;> simp only [ContextFreeFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
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
      simp only [finalizerCode, ContextFreeCode, ContextFreeName, plainCode_resolve hroot, interpAt, interpOf,
        Bool.true_and, Bool.and_true]
    · next flag =>
      cases flag <;> simp only [ContextFreeFrame, Bool.false_eq_true] at hf
      rw [step_success_pass_setInterruptible (flag := true)] at h
      exact ih true hK' h
    · next loop cursor =>
      cases loop <;> simp only [ContextFreeFrame, Bool.false_eq_true] at hf
      next q =>
      rw [step_success_enter_at root q cursor v K i s] at h
      cases h
      exact enter_plain q K i _ (plainCode_loopResumeAt hroot _ cursor v) hK'

set_option linter.unusedSimpArgs false in
theorem localStep_failure_plain {root : NativeEff} (hroot : ContextFreeHooks root)
    (c : CauseV) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores)
    (hK : ContextFreeStack K)
    (h : localStep root (fiberOf (Prim.failure c) K i) s = .running fr' s') :
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ ContextFreeCode cur' = true ∧ ContextFreeStack K' := by
  induction K generalizing i with
  | nil =>
    have he := step_exit_empty root (Exit.failure c) i s
    simp only [Prim.ofExit] at he
    rw [he] at h
    cases h
  | cons f K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases f <;> simp only [ContextFreeFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
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
      simp only [finalizerCode, ContextFreeCode, ContextFreeName, plainCode_resolve hroot, interpAt, interpOf,
        Bool.true_and, Bool.and_true]
    · next flag =>
      cases flag <;> simp only [ContextFreeFrame, Bool.false_eq_true] at hf
      rw [step_failure_pass_setInterruptible (flag := true)] at h
      exact ih true hK' h
    · next loop cursor =>
      cases loop <;> simp only [ContextFreeFrame, Bool.false_eq_true] at hf
      next q =>
      rw [step_failure_pass_whileLoop] at h
      exact ih i hK' h

-- The `ContextFreeFrame` argument is spent in some branches of the frame case split and not in
-- others; the linter reports the latter.
set_option linter.unusedSimpArgs false in
theorem localStep_plain {root : NativeEff} (hroot : ContextFreeHooks root) :
    ∀ (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores),
      ContextFreeCode cur = true → ContextFreeStack K →
      localStep root (fiberOf cur K i) s = .running fr' s' →
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ ContextFreeCode cur' = true ∧ ContextFreeStack K' := by
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
    cases thunk <;> simp only [ContextFreeCode, Bool.false_eq_true] at hpl
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
    cases thunk <;> simp only [ContextFreeCode, Bool.false_eq_true] at hpl
    rw [step_suspend] at h
    cases h
    exact ⟨_, _, _, rfl, plainCode_suspendBodyAt hroot _, hK⟩
  | onSuccess b n =>
    rw [step_push_onSuccess] at h
    cases h
    simp only [ContextFreeCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp only [ContextFreeFrame, hpl.1, hpl.2, Bool.and_self])⟩
  | onFailure b n =>
    rw [step_push_onFailure] at h
    cases h
    simp only [ContextFreeCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp only [ContextFreeFrame, hpl.1, hpl.2, Bool.and_self])⟩
  | onSuccessAndFailure b n₁ n₂ =>
    rw [step_push_onSuccessAndFailure] at h
    cases h
    simp only [ContextFreeCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp only [ContextFreeFrame, hpl.1, hpl.2.1, hpl.2.2, Bool.and_self])⟩
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
    cases loop <;> simp only [ContextFreeCode, Bool.false_eq_true] at hpl
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
    simp only [ContextFreeCode, Bool.false_eq_true] at hpl

/-! ### The live context of the hosted local step

Concept: translation-simulation. Claim: rows-block-host/R6.
Reach: one context-aware local step; no scheduler progress or reply admission.
The frame continuations and finalizers remain those of `localStep`.
-/

/-- Context actions use the same physical masks as `evaluatePrim.withFiber`.
Consumer: `localStepC` and the primitive-to-local bridge of rows-block-host/R6. -/
def contextStep (root : NativeEff) (fr : NFiber) (s : Stores) (ctx : Ctx) : LocalStep × Ctx :=
  match fr.current with
  | .withFiber thunk =>
    match (interpAt root []).withFiberOf thunk with
    | some .getContext => (.running { fr with current := .success (Val.context ctx) } s, ctx)
    | some .getInterruptible =>
      (.running { fr.uninterruptible with current := .success (Val.savedMask fr.interruptible) } s, ctx)
    | some (.setContext next) =>
      (.running { fr with current := .success Val.unit } s, next)
    | some (.setInterruptible body false) =>
      (.running { fr.uninterruptible with current := body } s, ctx)
    | some (.setInterruptible body true) =>
      let (masked, immediate) := fr.interruptibleRegion
      (.running { masked with current := immediate.getD body } s, ctx)
    | _ => (localStep root fr s, ctx)
  | _ => (localStep root fr s, ctx)

/-- Step of rows-block-host/R6; consumer: the source context leaf. -/
theorem contextStep_getCtx (root : NativeEff) (K : List NCode) (i : Bool)
    (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.withFiber .getCtx) K i) s ctx =
      (.running (fiberOf (.success (.context ctx)) K i) s, ctx) := by
  rfl

/-- Step of rows-block-host/R6; consumer: the source `Effect.context` leaf. -/
theorem contextStep_act_context (root : NativeEff) (p : Point) (K : List NCode) (i : Bool)
    (s : Stores) (ctx : Ctx) (h : actionAt root p = some WithFiberAction.getContext) :
    contextStep root (fiberOf (.withFiber (.act p)) K i) s ctx =
      (.running (fiberOf (.success (.context ctx)) K i) s, ctx) := by
  change (match actionAt root p with
    | some .getContext => _
    | some .getInterruptible => _
    | some (.setContext _) => _
    | some (.setInterruptible _ false) => _
    | some (.setInterruptible _ true) => _
    | _ => _) = _
  rw [h]
  rfl

/-- Step of rows-block-host/R6; consumer: the context bracket entrance. -/
theorem contextStep_captureMask (root : NativeEff) (K : List NCode) (i : Bool)
    (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.withFiber .captureMask) K i) s ctx =
      (.running (fiberOf (.success (.savedMask i)) (maskStack i K) false) s, ctx) := by
  cases i <;> rfl

/-- Step of rows-block-host/R6; consumer: the context bracket entrance. -/
theorem contextStep_provideMasked (root : NativeEff) (u : Env.ContextUpdate) (q : Point)
    (previous : Bool) (K : List NCode) (i : Bool) (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.withFiber (.provideMasked u (.program q) previous)) K i) s ctx =
      (.running (fiberOf (.onSuccess (.withFiber .getCtx) (.updateThen u (.program q) previous))
        (maskStack i K) false) s, ctx) := by
  cases i <;> rfl

/-- Step of rows-block-host/R6; consumer: the context bracket's context change. -/
theorem contextStep_setCtx (root : NativeEff) (next : Ctx) (K : List NCode) (i : Bool)
    (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.withFiber (.setCtx next)) K i) s ctx =
      (.running (fiberOf (.success .unit) K i) s, next) := by
  rfl

/-- Step of rows-block-host/R6; consumer: restoring a previously masked body. -/
theorem contextStep_restoreRegion_false (root : NativeEff) (q : Point)
    (K : List NCode) (i : Bool) (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.withFiber (.restoreRegion (.program q) false)) K i) s ctx =
      (.running (fiberOf (resolve root q) (maskStack i K) false) s, ctx) := by
  cases i <;> rfl

/-- Step of rows-block-host/R6; consumer: restoring a previously interruptible body. -/
theorem contextStep_restoreRegion_true (root : NativeEff) (q : Point)
    (K : List NCode) (i : Bool) (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.withFiber (.restoreRegion (.program q) true)) K i) s ctx =
      (.running (fiberOf (resolve root q) (if i then K else .setInterruptible false :: K) true) s,
        ctx) := by
  cases i <;> rfl

/-- Placement: rows-block-host/R6; consumer: the context-aware run.
Reach: every non-fiber-action primitive, including continuation and finalizer steps.
No progress is established. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextStep_fallback (root : NativeEff) (fr : NFiber) (s : Stores) (ctx : Ctx)
    (h : ∀ thunk, fr.current ≠ Prim.withFiber thunk) :
    contextStep root fr s ctx = (localStep root fr s, ctx) := by
  unfold contextStep
  split
  · next thunk hcur => exact False.elim (h thunk hcur)
  · rfl

/-- Placement: rows-block-host/R6; consumer: the hosted state invariant.
Reach: a context-aware step's stores; no progress or host admission. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextStep_finished_stores {root : NativeEff} {fr : NFiber} {s s' : Stores}
    {ctx ctx' : Ctx} {ex : ExitV}
    (h : contextStep root fr s ctx = (.finished ex s', ctx')) : s' = s ∧ ctx' = ctx
 := by
  have fallback (hs : (localStep root fr s, ctx) = (.finished ex s', ctx')) :
      s' = s ∧ ctx' = ctx := by
    obtain ⟨hstep, hctx⟩ := Prod.mk.inj hs
    refine ⟨?_, hctx.symm⟩
    unfold localStep at hstep
    split at hstep
    · split at hstep <;> cases hstep
    · cases hstep
    · exact (exitFrom_finished_stores hstep).symm
    · exact (exitFrom_finished_stores hstep).symm
    · unfold ofFrameStep at hstep
      split at hstep
      · cases hstep
      · cases hstep
        rfl
  unfold contextStep at h
  split at h
  · split at h
    · cases h
    · cases h
    · cases h
    · cases h
    · dsimp only at h
      cases h
    · exact fallback h
  · exact fallback h

/-- Placement: rows-block-host/R6; consumer: joinability in the hosted spine.
Reach: the exact saved code, stack, context and stores under one yield wrapper.
This is a local step, not a scheduler-progress statement. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextStep_yieldWrapper (root : NativeEff) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (ctx : Ctx) :
    contextStep root (fiberOf (.success Val.unit)
      (.onSuccessConst (.yieldNowWith 0) cur :: K) i) s ctx =
      (.running (fiberOf cur K i) s, ctx) := by
  rfl

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
def fiberAt (fr : NFiber) (k : Nat) (ctx : Ctx := emptyCtx) : NRunFiber :=
  { RunFiber.make Api.root fr.current true (stores.budgetOf ctx) ctx with
    frame := fr, running := true, currentOpCount := k }

theorem fiberAt_frame {ctx : Ctx} (fr : NFiber) (k : Nat) : (fiberAt fr k ctx).frame = fr :=
  by aesop

/-- The machine of the run: one fiber, nothing armed, no race, the stores `s`, the trace
`tr`, the next resume token `nt` (zero until the first yield; each yield takes one). -/
def M (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat)
    (ctx : Ctx := emptyCtx) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [fiberAt fr k ctx], nextId := 1, nextToken := nt, trace := tr }

/-- The root fiber once its exit path has stored `ex` (`exitStore`, the else branch of
`exitFiber` at `Fibers.lean:1128-1141`). -/
def exitedAt (root : NativeEff) (ex : ExitV) (fr : NFiber) (k : Nat)
    (previousCtx : Ctx := emptyCtx) : NRunFiber :=
  { fiberAt fr k previousCtx with
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
    (nt : Nat) (previousCtx : Ctx := emptyCtx) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [exitedAt root ex fr k previousCtx], nextId := 1, nextToken := nt, trace := tr }

/-- The root fiber parked by the injected Yield (`effect.ts:647-655,982-990`):
the success-only frame retains the previous program, and the dispatcher answers
with success unit. The next entry delivers that answer before returning to the
saved program. -/
def parkedAt (fr : NFiber) (k : Nat) (t : Nat) (ctx : Ctx := emptyCtx) : NRunFiber :=
  { fiberAt fr k ctx with
    running := false
    frame := { fr with
      current := Prim.success Val.unit
      stack := Prim.onSuccessConst (Prim.yieldNowWith 0) fr.current :: fr.stack }
    parked := Parked.withGuard t
    pending := [⟨t, none, [], [], Resume.void, false⟩]
    dispatcher := Dispatcher.empty.enqueue 0 (Task.resume Api.root t (Prim.success Val.unit)) }

/-- The machine after a yield: the root parked on token `t`, its dispatcher armed, the next
token taken. -/
def Myield (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat)
    (ctx : Ctx := emptyCtx) : Api.Machine :=
  { (RunMachine.empty s : Api.Machine) with
    fibers := [parkedAt fr k t ctx], nextId := 1, nextToken := t + 1, armed := [Api.root],
    trace := tr }

/-- No completed exit is visible while the single root fiber is running. -/
theorem M_completedExits {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).completedExits = [] :=
  by aesop

theorem Myield_completedExits {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t ctx).completedExits = [] :=
  by aesop

theorem M_stuck {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).stuck = none :=
  by aesop

theorem M_state {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).state = s :=
  by aesop

theorem M_middleware {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).middlewareInstalled = false :=
  by aesop

theorem M_fiber? {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).fiber? Api.root = some (fiberAt fr k ctx) :=
  by aesop

theorem M_update {ctx ctx' : Ctx} (fr fr' : NFiber) (s : Stores) (k k' : Nat) (tr : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).update (fiberAt fr' k' ctx') = M fr' s k' tr nt ctx' :=
  by aesop

theorem M_emit {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr ev : NTrace) (nt : Nat) :
    (M fr s k tr nt ctx).emit ev = M fr s k (tr ++ ev) nt ctx := by
  -- the field-local guard on an empty emit (direction L4): the trace is the trace
  cases ev with
  | nil => simp [M, RunMachine.emit]
  | cons _ _ => rfl

theorem Mexit_stuck {ctx : Ctx} (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt ctx).stuck = none :=
  by aesop

theorem Mexit_armed {ctx : Ctx} (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt ctx).armed = [] :=
  by aesop

theorem Mexit_state {ctx : Ctx} (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt ctx).state = s :=
  by aesop

theorem Mexit_finished {ctx : Ctx} (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) : (Mexit root ex fr s k tr nt ctx).finished = true :=
  by aesop

theorem Mexit_exit {ctx : Ctx} (root : NativeEff) (ex : ExitV) (fr : NFiber) (s : Stores) (k : Nat)
    (tr : NTrace) (nt : Nat) :
    ((Mexit root ex fr s k tr nt ctx).fiber? Api.root).bind RunFiber.exit = some ex :=
  by aesop

theorem Myield_stuck {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t ctx).stuck = none :=
  by aesop

theorem Myield_state {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t ctx).state = s :=
  by aesop

theorem Myield_armed {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t ctx).armed = [Api.root] :=
  by aesop

theorem Myield_fiber? {ctx : Ctx} (fr : NFiber) (s : Stores) (k : Nat) (tr : NTrace) (t : Nat) :
    (Myield fr s k tr t ctx).fiber? Api.root = some (parkedAt fr k t ctx) :=
  by aesop

/-! ### What the interp of a root program classifies -/

theorem parkOf_sync (root : NativeEff) (thunk : EffThunk) :
    (interpAt root []).parkOf (Prim.sync thunk) = none :=
  by aesop

theorem parkOf_plain (root : NativeEff) {cur : NCode} (h : ContextFreeCode cur = true) :
    (interpAt root []).parkOf cur = none := by
  cases cur with
  | suspend thunk =>
    cases thunk <;> simp only [ContextFreeCode, Bool.false_eq_true] at h
    rfl
  | _ => rfl

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
        false, Outcome.answered, [Cmd.drainDue], []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_op, hs]

theorem evaluatePrim_sync_op_none (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (o : SyncOp) (hcur : f.frame.current = Prim.sync (EffThunk.op o))
    (hs : syncOpStep o m.state = none) :
    evaluatePrim (interpAt root []) m f false =
      ⟨m, { f with frame := { f.frame with
          current := Prim.success ((interpAt root []).syncValue (EffThunk.op o)) } },
        false, Outcome.answered, [], []⟩ := by
  simp only [evaluatePrim, hcur, parkOf_sync, syncState_op, hs]

theorem evaluatePrim_sync_pure (root : NativeEff) (m : Api.Machine) (f : NRunFiber)
    (p : Point) (hcur : f.frame.current = Prim.sync (EffThunk.pure p)) :
    evaluatePrim (interpAt root []) m f false =
      ⟨m, { f with frame := { f.frame with
          current := Prim.success ((interpAt root []).syncValue (EffThunk.pure p)) } },
        false, Outcome.answered, [], []⟩ := by
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
  | .running fr' _ => ⟨m.emit ev, { f with frame := fr' }, false, Outcome.continue_, [], []⟩
  | .finished ex _ =>
    ⟨m.emit ev, { f with frame := frameExitState f.frame }, false, Outcome.finished ex, [], []⟩

/-- The context-aware local step predicts the live context and its cached budget.
Placement: rows-block-host/R6; consumer: the generalized hosted transitions. -/
def iterOfC (m : Api.Machine) (f : NRunFiber) (ev : NTrace)
    (result : LocalStep × Ctx) : NIter :=
  let (maxOps, prevent) := stores.budgetOf result.2
  match result.1 with
  | .running fr' _ =>
    ⟨m.emit ev, { f with
      frame := fr'
      context := result.2
      maxOpsBeforeYield := maxOps
      preventYield := prevent }, false, Outcome.continue_, [], []⟩
  | .finished ex _ =>
    ⟨m.emit ev, { f with
      frame := frameExitState f.frame
      context := result.2
      maxOpsBeforeYield := maxOps
      preventYield := prevent }, false, Outcome.finished ex, [], []⟩

/-- On a plain fiber whose current primitive is not a `sync`, `evaluatePrim` is the local
step: the frame machine's step, or — for an exit meeting an `onExit` frame — the finalizer
program under the mask, exactly as `exitFrom` spells it. -/
theorem evaluatePrim_localStep (root : NativeEff) (m : Api.Machine) (cur : NCode)
    (K : List NCode) (i : Bool) (k : Nat) (hpl : ContextFreeCode cur = true)
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
  | _ => simp only [ContextFreeCode, Bool.false_eq_true] at hpl

/-! ### The native scope protocol does not intercept the plain run -/

/-- A plain stack cannot answer with the scoped callback name. Restoring mask
frames are passed using the same pop equations as the local run. -/
theorem popOf_plain_not_scoped (cur : NCode) (K : List NCode) (i : Bool)
    (hK : ContextFreeStack K) (ex : ExitV) (body : NCode) (previous : Ctx) (scope : Nat)
    (flag : Bool) :
    (popOf (fiberOf cur K i) ex).answer ≠
      ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag) := by
  induction K generalizing i with
  | nil => cases ex <;> simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, ne_eq, reduceCtorEq, not_false_eq_true, Bool.not_true, Bool.and_self]
  | cons frame K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases frame <;> simp only [ContextFreeFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · next b n =>
      cases ex with
      | success v =>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true, Bool.false_and, List.nil_append, ne_eq, ContAnswer.frame.injEq, reduceCtorEq, not_false_eq_true]
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
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_true, Bool.and_self, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_false, List.nil_append, ne_eq, ContAnswer.frame.injEq, reduceCtorEq, not_false_eq_true]
    · cases ex <;>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_false, Bool.and_self, List.nil_append, ne_eq, ContAnswer.frame.injEq, not_false_eq_true, Bool.not_true, or_true]
    · cases ex <;>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_false, Bool.and_self, List.nil_append, ne_eq, ContAnswer.frame.injEq, not_false_eq_true, Bool.not_true, or_true]
    · next b n finalizerFlag =>
      cases n <;> cases finalizerFlag <;> simp only [Bool.false_eq_true] at hf
      cases ex <;> cases i <;>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_self, List.nil_append, ne_eq, ContAnswer.frame.injEq, Prim.onExit.injEq, Bool.false_eq, false_and, and_false, not_false_eq_true, List.cons_append, Bool.not_true, or_true, Bool.and_false]
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
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true, Bool.false_and, List.nil_append, ne_eq, ContAnswer.frame.injEq, reduceCtorEq, not_false_eq_true]
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
    (K : List NCode) (i : Bool) (k : Nat) (hpl : ContextFreeCode cur = true) (hK : ContextFreeStack K)
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
  | withFiber _ => simp only [ContextFreeCode, Bool.false_eq_true] at hpl
  | _ => rfl

/-- The finished local-step hypothesis itself excludes an answering scoped
callback; the older stack need not be plain for this equation. -/
theorem evaluateNative_of_finished (root : NativeEff) (m : Api.Machine) (cur : NCode)
    (K : List NCode) (i : Bool) (k : Nat) (hpl : ContextFreeCode cur = true)
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
  | withFiber _ => simp only [ContextFreeCode, Bool.false_eq_true] at hpl
  | _ => rfl

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
    (h : (iteration interp m f yielding).outcome = Outcome.finished ex)
    (noEdits : (iteration interp m f yielding).edits = []) :
    driveState interp (fuel + 1) m (Cmd.loop id yielding :: rest) =
      driveState interp fuel
        ((iteration interp m f yielding).machine.update (iteration interp m f yielding).fiber)
        ((iteration interp m f yielding).nested ++ [Cmd.finish id ex] ++ rest) := by
  rw [driveState_succ_cons]
  simp only [hs, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
    driveStep, hf, settle, noEdits, settleOutcome, h]

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
        [Cmd.drainDue], []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf, M_completedExits]
    exact evaluatePrim_sync_op root (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) (k + 1)) o s₁ v rfl hs
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
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
        fiberAt (fiberOf (Prim.success Val.unit) K i) (k + 1), false, Outcome.answered, [], []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf, M_completedExits]
    exact evaluatePrim_sync_op_none root (M (fiberOf (Prim.sync (EffThunk.op o)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.op o)) K i) (k + 1)) o rfl hs
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
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
        Outcome.answered, [], []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk]
    simp only [evaluateNative, fiberAt_frame, fiberOf, M_completedExits]
    exact evaluatePrim_sync_pure root (M (fiberOf (Prim.sync (EffThunk.pure p)) K i) s k tr nt)
      (fiberAt (fiberOf (Prim.sync (EffThunk.pure p)) K i) (k + 1)) p rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
  rw [M_update]
  rfl

/-- The local step at the loop, running on: the fiber moves on, the count goes up. -/
theorem drive_loop_running (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (cur₁ : NCode)
    (K₁ : List NCode) (i₁ : Bool) (hpl : ContextFreeCode cur = true) (hK : ContextFreeStack K)
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
        Outcome.continue_, [], []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk, hraw, hev]
    simp only [iterOf, M_emit]
    rfl
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
  rw [M_update]
  rfl

/-- The local step at the loop, finishing: the exit path is owed. -/
theorem drive_loop_finish (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ex : ExitV)
    (hpl : ContextFreeCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t) (hk : k + 1 < defaultBudget)
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
        Outcome.finished ex, [], []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ hk, hraw, hev]
    simp only [iterOf, M_emit]
    rfl
  refine ⟨tr ++ ev, fun n => ?_⟩
  rw [drive_loop_finished (evaluator := evaluatorFor root table) _ _ _ _ _ _ rest ex rfl
    (M_fiber? _ _ _ _ _) (by rw [hit]) (by rw [hit]), hit]
  rw [M_update]
  rfl

/-- The delivery of an answered `sync` (`Cmd.deliver`, R2-1): the local step with no loop
top and no op count. -/
theorem drive_deliver_running (root : NativeEff) (cur : NCode) (K : List NCode) (i : Bool)
    (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (cur₁ : NCode)
    (K₁ : List NCode) (i₁ : Bool) (hpl : ContextFreeCode cur = true) (hK : ContextFreeStack K)
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
    (hpl : ContextFreeCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t)
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
        true, Outcome.continue_, [], []⟩ := by
    unfold iteration
    rw [hidle, hcount]
    unfold injectYield
    dsimp only
    rw [if_pos (by simp only [hv, Bool.not_false, Bool.true_and]; rfl)]
    rfl
  rw [show n + 2 = (n + 1) + 1 by omega]
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
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
  simp only [↓reduceIte, RunMachine.emit, RunMachine.disarm, RunMachine.update, parkedAt, fiberAt, RunFiber.make, Dispatcher.empty, Myield, RunMachine.empty, List.map_cons, List.map_nil, ne_eq, decide_not, decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil, List.isEmpty_cons, driveState_succ_cons, Option.isSome_none, driveStep, RunMachine.fiber?, List.find?_cons_of_pos, List.append_assoc, List.cons_append, List.nil_append, Bool.or_self, bne_self_eq_false, M]

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
        false, Outcome.continue_, [], []⟩ := by
    rw [iteration_M root _ _ _ _ _ _ _ (by decide)]
    change exitScoped root (M answered s 0 tr₀ (t + 1)) (fiberAt answered 1) false
      (Exit.success Val.unit) = _
    rw [exitScoped_eq_evaluatePrim root _ _ _ _ (by
      intro body previous scope flag
      change ContAnswer.frame saved ≠
        ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag)
      intro h
      simp only [ContAnswer.frame.injEq, reduceCtorEq, saved] at h), M_completedExits]
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
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
  rw [M_update]
  rfl

/-! ## Stage 4 obligations for the hosted context lane

Concept: translation-simulation. Claim: rows-block-host/R6.
Reach: one plain fiber, arbitrary context and row table, explicit finite steps.
Consumers: the context-aware segments and the receipt-conditioned H9Blocks.
No theorem here establishes scheduler progress or admits a host reply.
-/

theorem PlainStack.nil : PlainStack [] := fun _ h => by simp only [List.not_mem_nil] at h

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

/-- Step of rows-block-host/R6; consumer: the context-aware continuation closure. -/
theorem plainContext_resolve {root : NativeEff} (h : PlainHooks root) (q : Point) :
    PlainCode (resolve root q) = true := h.resolve q

/-- Step of rows-block-host/R6; consumer: the context-aware suspension closure. -/
theorem plainContext_suspendBodyAt {root : NativeEff} (h : PlainHooks root) (q : Point) :
    PlainCode (suspendBodyAt root (.body q)) = true := h.suspend q

/-- Step of rows-block-host/R6; consumer: the context-aware exit closure. -/
theorem plainContext_ofExit (ex : ExitV) : PlainCode (Prim.ofExit ex) = true := by
  cases ex <;> rfl

/-- Step of rows-block-host/R6; consumer: the context-aware finalizer closure.
Source context brackets use a restoreRegion body; any already plain body is administrative closure. -/
theorem plainFrame_onExit_context {b : NCode} {n : EffName} {flag : Bool}
    (h : PlainFrame (.onExit b n flag) = true) :
    ((∃ p, n = .fin p) ∨ (∃ ctx, n = .restoreCtx ctx)) ∧ flag = false ∧ PlainCode b = true := by
  cases n <;> cases flag <;> simp only [PlainFrame, Bool.false_eq_true] at h
  · exact ⟨Or.inl ⟨_, rfl⟩, rfl, h⟩
  · exact ⟨Or.inr ⟨_, rfl⟩, rfl, h⟩

/-- Step of rows-block-host/R6; consumer: pushing the two admitted finalizer kinds. -/
theorem plainCode_onExit_context {b : NCode} {n : EffName} {flag : Bool}
    (h : PlainCode (.onExit b n flag) = true) :
    ((∃ p, n = .fin p) ∨ (∃ ctx, n = .restoreCtx ctx)) ∧ flag = false ∧ PlainCode b = true := by
  cases n <;> cases flag <;> simp only [PlainCode, Bool.false_eq_true] at h
  · exact ⟨Or.inl ⟨_, rfl⟩, rfl, h⟩
  · exact ⟨Or.inr ⟨_, rfl⟩, rfl, h⟩

/-- Step of rows-block-host/R6; consumer: the context-aware finalizer closure. -/
theorem plainContext_finalizerCode (root : NativeEff) (ex : ExitV) (program : NCode)
    (h : PlainCode program = true) : PlainCode (finalizerCode (interpAt root []) ex program) = true := by
  cases ex
  · change PlainCode program && true = true
    rw [h]
    rfl
  · change (PlainCode program && true) && true = true
    rw [h]
    rfl

/-- Step of rows-block-host/R6; consumer: the context-aware finalizer closure. -/
theorem step_ofExit_restoreCtx (root : NativeEff) (ex : ExitV) (body : NCode) (previous : Ctx)
    (K : List NCode) (i : Bool) (s : Stores) :
    localStep root (fiberOf (Prim.ofExit ex) (.onExit body (.restoreCtx previous) false :: K) i) s =
      .running (fiberOf (finalizerCode (interpAt root []) ex (.withFiber (.setCtx previous)))
        (maskStack i K) false) s := by
  cases ex <;> cases i <;> rfl

/-- Step of rows-block-host/R6; consumer: the local wrapper closure. -/
theorem step_success_yieldWrapper (root : NativeEff) (v : Val) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (.success v) (.onSuccessConst (.yieldNowWith 0) cur :: K) i) s =
      .running (fiberOf cur K i) s := by
  rfl

/-- Step of rows-block-host/R6; consumer: the local wrapper closure. -/
theorem step_failure_yieldWrapper (root : NativeEff) (c : CauseV) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) :
    localStep root (fiberOf (.failure c) (.onSuccessConst (.yieldNowWith 0) cur :: K) i) s =
      localStep root (fiberOf (.failure c) K i) s := by
  aesop

/-- `catchIf`'s handler answers its compiled handler at a represented, selected failure, and
the failure itself otherwise. -/
theorem plainContext_contEOf_caughtError {root : NativeEff} (hroot : PlainHooks root)
    (p : Point) (c : CauseV) : PlainCode (contEOf root (EffName.caughtError p) c) = true := by
  simp only [contEOf]
  split
  · split
    · exact plainContext_resolve hroot _
    · rfl
  · rfl

theorem plainContext_contAOf {root : NativeEff} (hroot : PlainHooks root) {n : EffName}
    (hn : PlainName n = true) (v : Val) : PlainCode (contAOf root n v) = true := by
  cases n <;> simp only [PlainName, Bool.false_eq_true] at hn
  case cont p => exact plainContext_resolve hroot _
  case caught p => rfl
  case caughtError p => rfl
  case onValue p => exact plainContext_resolve hroot _
  case onCause p => rfl
  case fin p => rfl
  case restore ex => exact plainContext_ofExit _
  case merge ex => exact plainContext_ofExit _
  case provideMask u region =>
    cases region <;> simp only [Bool.false_eq_true] at hn
    case program q =>
      simp only [contAOf]
      split <;> rfl
  case updateThen u region flag =>
    cases region <;> simp only [Bool.false_eq_true] at hn
    case program q =>
      rw [contAOf_updateThen]
      unfold updateThenK
      split
      · split <;> rfl
      · rfl
  case bodyThen region previous flag =>
    cases region <;> simp only [Bool.false_eq_true] at hn
    rfl
  case serviceLookup key =>
    rw [contAOf_serviceLookup]
    unfold serviceLookupK
    split
    · split <;> rfl
    · rfl

theorem plainContext_contEOf {root : NativeEff} (hroot : PlainHooks root) {n : EffName}
    (hn : PlainName n = true) (c : CauseV) : PlainCode (contEOf root n c) = true := by
  cases n <;> simp only [PlainName, Bool.false_eq_true] at hn
  case cont p => rfl
  case caught p => exact plainContext_resolve hroot _
  case caughtError p => exact plainContext_contEOf_caughtError hroot _ _
  case onValue p => rfl
  case onCause p => exact plainContext_resolve hroot _
  case fin p => rfl
  case restore ex => exact plainContext_ofExit _
  case merge ex => exact plainContext_ofExit _
  case provideMask u region => rfl
  case updateThen u region flag => rfl
  case bodyThen region previous flag => rfl
  case serviceLookup key => rfl

/-- Fresh source callbacks still answer plain code at any captured point. -/
theorem plainContext_contAAt {root : NativeEff} (hroot : PlainHooks root) {n : EffName}
    (hn : PlainName n = true) (v : Val) : PlainCode ((interpAt root []).contA n v) = true := by
  cases n <;> simp only [PlainName, Bool.false_eq_true] at hn
  case cont p => exact plainContext_resolve hroot _
  case caught p => rfl
  case caughtError p => rfl
  case onValue p => exact plainContext_resolve hroot _
  case onCause p => rfl
  case fin p => rfl
  case restore ex => exact plainContext_ofExit _
  case merge ex => exact plainContext_ofExit _
  case provideMask u region => exact plainContext_contAOf hroot hn v
  case updateThen u region flag => exact plainContext_contAOf hroot hn v
  case bodyThen region previous flag => exact plainContext_contAOf hroot hn v
  case serviceLookup key => exact plainContext_contAOf hroot (n := .serviceLookup key) rfl v

theorem plainContext_contEAt {root : NativeEff} (hroot : PlainHooks root) {n : EffName}
    (hn : PlainName n = true) (c : CauseV) : PlainCode ((interpAt root []).contE n c) = true := by
  cases n <;> simp only [PlainName, Bool.false_eq_true] at hn
  case cont p => rfl
  case caught p => exact plainContext_resolve hroot _
  case caughtError p => exact plainContext_contEOf_caughtError hroot _ _
  case onValue p => rfl
  case onCause p => exact plainContext_resolve hroot _
  case fin p => rfl
  case restore ex => exact plainContext_ofExit _
  case merge ex => exact plainContext_ofExit _

  case provideMask u region => rfl
  case updateThen u region flag => rfl
  case bodyThen region previous flag => rfl
  case serviceLookup key => rfl
/-! ### A loop's decisions are plain -/

theorem plainContext_loopFinishAt (root : NativeEff) (q : Point) (c : Val) :
    PlainCode (loopFinishAt root q c) = true := by
  unfold loopFinishAt
  split
  · split <;> rfl
  · rfl

/-- What a loop does next is plain code either way: the body resolved at the loop's child, or
a finishing exit. -/
theorem plainContext_loopNextAt {root : NativeEff} (hroot : PlainHooks root) (q : Point)
    (c : Val) : PlainCode (loopNextAt root q c).code = true := by
  unfold loopNextAt
  split
  · split
    · exact plainContext_resolve hroot _
    · exact plainContext_loopFinishAt root q c
    · rfl
  · rfl

theorem plainContext_loopResumeAt {root : NativeEff} (hroot : PlainHooks root) (q : Point)
    (c v : Val) : PlainCode (loopResumeAt root q c v).code = true := by
  unfold loopResumeAt
  split
  · split
    · exact plainContext_loopNextAt hroot q _
    · rfl
  · rfl

/-- Where a loop's decision leaves the fiber is a plain fiber over a plain stack. -/
theorem context_enter_plain (q : Point) (K : List NCode) (i : Bool)
    (ln : LoopNext Val NCode) (hcode : PlainCode ln.code = true) (hK : PlainStack K) :
    ∃ cur' K' i', enter q K i ln = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K' := by
  cases ln with
  | «continue» next body => exact ⟨_, _, _, rfl, hcode, hK.cons rfl⟩
  | finish code => exact ⟨_, _, _, rfl, hcode, hK⟩

/-! ### The local step keeps the fiber plain -/

set_option linter.unusedSimpArgs false in
theorem context_localStep_success_plain {root : NativeEff} (hroot : PlainHooks root)
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
    cases f <;> simp only [PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · rw [step_success_onSuccess] at h
      cases h
      exact ⟨_, _, _, rfl, plainContext_contAAt hroot hf.2 v, hK'⟩
    · next body saved =>
      cases body with
      | yieldNowWith priority =>
        cases priority with
        | zero =>
          rw [step_success_yieldWrapper] at h
          cases h
          exact ⟨_, _, _, rfl, hf, hK'⟩
        | succ _ => exact Bool.noConfusion hf
      | _ => exact Bool.noConfusion hf
    · rw [step_success_pass_onFailure] at h
      exact ih i hK' h
    · rw [step_success_onSuccessAndFailure] at h
      cases h
      exact ⟨_, _, _, rfl, plainContext_contAAt hroot hf.2.1 v, hK'⟩
    · rw [step_success_exitFrame] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK'⟩
    · next b n flag =>
      obtain ⟨kind, rfl, _⟩ := plainFrame_onExit_context hf
      rcases kind with ⟨p, rfl⟩ | ⟨previous, rfl⟩
      · have hm := step_ofExit_onExit root (Exit.success v) b p K i s
        simp only [Prim.ofExit] at hm
        rw [hm] at h
        cases h
        exact ⟨_, _, _, rfl, plainContext_finalizerCode root _ _ (hroot.resolve _), hK'.mask i⟩
      · have hm := step_ofExit_restoreCtx root (Exit.success v) b previous K i s
        simp only [Prim.ofExit] at hm
        rw [hm] at h
        cases h
        exact ⟨_, _, _, rfl, plainContext_finalizerCode root _ _ rfl, hK'.mask i⟩
    · next flag =>
      rw [step_success_pass_setInterruptible (flag := flag)] at h
      exact ih flag hK' h
    · next loop cursor =>
      cases loop <;> simp only [PlainFrame, Bool.false_eq_true] at hf
      next q =>
      rw [step_success_enter_at root q cursor v K i s] at h
      cases h
      exact context_enter_plain q K i _ (plainContext_loopResumeAt hroot _ cursor v) hK'



set_option linter.unusedSimpArgs false in
theorem context_localStep_failure_plain {root : NativeEff} (hroot : PlainHooks root)
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
    cases f <;> simp only [PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · rw [step_failure_pass_onSuccess] at h
      exact ih i hK' h
    · next body saved =>
      cases body with
      | yieldNowWith priority =>
        cases priority with
        | zero =>
          rw [step_failure_yieldWrapper] at h
          exact ih i hK' h
        | succ _ => exact Bool.noConfusion hf
      | _ => exact Bool.noConfusion hf
    · rw [step_failure_onFailure] at h
      cases h
      exact ⟨_, _, _, rfl, plainContext_contEAt hroot hf.2 c, hK'⟩
    · rw [step_failure_onSuccessAndFailure] at h
      cases h
      exact ⟨_, _, _, rfl, plainContext_contEAt hroot hf.2.2 c, hK'⟩
    · rw [step_failure_exitFrame] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK'⟩
    · next b n flag =>
      obtain ⟨kind, rfl, _⟩ := plainFrame_onExit_context hf
      rcases kind with ⟨p, rfl⟩ | ⟨previous, rfl⟩
      · have hm := step_ofExit_onExit root (Exit.failure c) b p K i s
        simp only [Prim.ofExit] at hm
        rw [hm] at h
        cases h
        exact ⟨_, _, _, rfl, plainContext_finalizerCode root _ _ (hroot.resolve _), hK'.mask i⟩
      · have hm := step_ofExit_restoreCtx root (Exit.failure c) b previous K i s
        simp only [Prim.ofExit] at hm
        rw [hm] at h
        cases h
        exact ⟨_, _, _, rfl, plainContext_finalizerCode root _ _ rfl, hK'.mask i⟩
    · next flag =>
      rw [step_failure_pass_setInterruptible (flag := flag)] at h
      exact ih flag hK' h
    · next loop cursor =>
      cases loop <;> simp only [PlainFrame, Bool.false_eq_true] at hf
      next q =>
      rw [step_failure_pass_whileLoop] at h
      exact ih i hK' h



-- The `PlainFrame` argument is spent in some branches of the frame case split and not in
-- others; the linter reports the latter.
set_option linter.unusedSimpArgs false in
theorem context_localStep_plain {root : NativeEff} (hroot : PlainHooks root) :
    ∀ (cur : NCode) (K : List NCode) (i : Bool) (s : Stores) (fr' : NFiber) (s' : Stores),
      PlainCode cur = true → PlainStack K →
      localStep root (fiberOf cur K i) s = .running fr' s' →
      ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K' := by
  intro cur K i s fr' s' hpl hK h
  cases cur with
  | success v =>
    exact context_localStep_success_plain hroot v K i s fr' s' hK h
  | failure c =>
    exact context_localStep_failure_plain hroot c K i s fr' s' hK h
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
    exact ⟨_, _, _, rfl, plainContext_suspendBodyAt hroot _, hK⟩
  | onSuccess b n =>
    rw [step_push_onSuccess] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp only [PlainFrame, hpl.1, hpl.2, Bool.and_self])⟩
  | onFailure b n =>
    rw [step_push_onFailure] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp only [PlainFrame, hpl.1, hpl.2, Bool.and_self])⟩
  | onSuccessAndFailure b n₁ n₂ =>
    rw [step_push_onSuccessAndFailure] at h
    cases h
    simp only [PlainCode, Bool.and_eq_true] at hpl
    exact ⟨_, _, _, rfl, hpl.1, hK.cons (by simp only [PlainFrame, hpl.1, hpl.2.1, hpl.2.2, Bool.and_self])⟩
  | exitFrame b =>
    rw [step_push_exitFrame] at h
    cases h
    exact ⟨_, _, _, rfl, hpl, hK.cons hpl⟩
  | onExit b n flag =>
    obtain ⟨kind, rfl, hb⟩ := plainCode_onExit_context hpl
    rw [step_push_onExit] at h
    cases h
    rcases kind with ⟨p, rfl⟩ | ⟨previous, rfl⟩
    · exact ⟨_, _, _, rfl, hb, hK.cons hb⟩
    · exact ⟨_, _, _, rfl, hb, hK.cons hb⟩
  | whileLoop loop cursor =>
    cases loop <;> simp only [PlainCode, Bool.false_eq_true] at hpl
    next q =>
    rw [step_whileLoop_enter_at root q cursor K i s] at h
    cases h
    exact context_enter_plain q K i _ (plainContext_loopNextAt hroot _ cursor) hK
  | async n w c =>
    -- a host call: the self-loop
    rw [localStep_async] at h
    cases h
    exact ⟨_, _, _, rfl, hpl, hK⟩
  | withFiber thunk =>
    have hl : localStep root (fiberOf (.withFiber thunk) K i) s =
        .running (fiberOf (.failure (Cause.die Defect.notImplemented)) K i) s := by
      cases thunk with
      | act _ | getCtx | captureMask | setCtx _ | provideMasked _ _ _ | restoreRegion _ _ => rfl
      | _ => simp only [PlainCode, Bool.false_eq_true] at hpl
    rw [hl] at h
    cases h
    exact ⟨_, _, _, rfl, rfl, hK⟩
  | iterator _ _ | setInterruptible _ | yieldNowWith _ | asyncFinalizer _ | onSuccessConst _ _ =>
    simp only [PlainCode, Bool.false_eq_true] at hpl

/-- Placement: rows-block-host/R6; consumer: the hosted store invariant.
Reach: a running non-sync local step; no scheduler or host-reply claim. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextStep_stores {root : NativeEff} {cur : NCode} {K : List NCode} {i : Bool}
    {s s' : Stores} {ctx ctx' : Ctx} {fr' : NFiber} (hns : ∀ t, cur ≠ .sync t)
    (h : contextStep root (fiberOf cur K i) s ctx = (.running fr' s', ctx')) : s' = s
 := by
  have fallback (hs : (localStep root (fiberOf cur K i) s, ctx) = (.running fr' s', ctx')) : s' = s := by
    have hstep := congrArg Prod.fst hs
    exact (localStep_stores hns hstep).symm
  unfold contextStep at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
      rfl
    · cases h
      rfl
    · cases h
      rfl
    · dsimp only at h
      cases h
      rfl
    · exact fallback h
  · exact fallback h

/-- Placement: rows-block-host/R6; consumer: the hosted quiet-store invariant.
Reach: every running local step; no scheduler progress or reply admission. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextStep_quiet {root : NativeEff} {cur : NCode} {K : List NCode} {i : Bool}
    {s s' : Stores} {ctx ctx' : Ctx} {fr' : NFiber} (hq : Quiet s)
    (h : contextStep root (fiberOf cur K i) s ctx = (.running fr' s', ctx')) : Quiet s'
 := by
  have fallback (hs : (localStep root (fiberOf cur K i) s, ctx) = (.running fr' s', ctx')) : Quiet s' := by
    have hstep := congrArg Prod.fst hs
    exact localStep_quiet hstep hq
  unfold contextStep at h
  split at h
  · split at h
    · cases h
      exact hq
    · cases h
      exact hq
    · cases h
      exact hq
    · cases h
      exact hq
    · dsimp only at h
      cases h
      exact hq
    · exact fallback h
  · exact fallback h

/-- The context-aware step keeps a running plain fiber plain.
Placement: rows-block-host/R6; consumer: the hosted run invariant. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem contextStep_plain {root : NativeEff} (hroot : PlainHooks root)
    (cur : NCode) (K : List NCode) (i : Bool) (s s' : Stores) (ctx ctx' : Ctx)
    (fr' : NFiber) (hpl : PlainCode cur = true) (hK : PlainStack K)
    (h : contextStep root (fiberOf cur K i) s ctx = (.running fr' s', ctx')) :
    ∃ cur' K' i', fr' = fiberOf cur' K' i' ∧ PlainCode cur' = true ∧ PlainStack K'
 := by
  cases cur with
  | withFiber thunk =>
    cases thunk with
    | act p =>
      rcases hroot.action p with ha | ha
      · have hs : contextStep root (fiberOf (.withFiber (.act p)) K i) s ctx =
            (.running (fiberOf (.failure (Cause.die Defect.notImplemented)) K i) s, ctx) := by
          simp only [contextStep, fiberOf, interpAt, interpOf, ha]
          rfl
        rw [hs] at h
        cases h
        exact ⟨_, _, _, rfl, rfl, hK⟩
      · rw [contextStep_act_context root p K i s ctx ha] at h
        cases h
        exact ⟨_, _, _, rfl, rfl, hK⟩
    | getCtx =>
      rw [contextStep_getCtx] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK⟩
    | captureMask =>
      rw [contextStep_captureMask] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK.mask i⟩
    | setCtx next =>
      rw [contextStep_setCtx] at h
      cases h
      exact ⟨_, _, _, rfl, rfl, hK⟩
    | provideMasked u region flag =>
      cases region <;> simp only [PlainCode, Bool.false_eq_true] at hpl
      case program q =>
        rw [contextStep_provideMasked] at h
        cases h
        exact ⟨_, _, _, rfl, rfl, hK.mask i⟩
    | restoreRegion region flag =>
      cases region <;> simp only [PlainCode, Bool.false_eq_true] at hpl
      case program q =>
        cases flag with
        | false =>
          rw [contextStep_restoreRegion_false] at h
          cases h
          exact ⟨_, _, _, rfl, hroot.resolve _, hK.mask i⟩
        | true =>
          rw [contextStep_restoreRegion_true] at h
          cases h
          refine ⟨_, _, _, rfl, hroot.resolve _, ?_⟩
          cases i
          · exact hK.cons rfl
          · exact hK
    | _ => simp only [PlainCode, Bool.false_eq_true] at hpl
  | _ =>
    rw [contextStep_fallback root _ _ _ (fun _ h => by cases h)] at h
    exact context_localStep_plain hroot _ K i s fr' s' hpl hK (congrArg Prod.fst h)

/-- Step of rows-block-host/R6; consumer: the context-aware primitive bridge. -/
theorem parkOf_plain_context (root : NativeEff) {cur : NCode} (h : PlainCode cur = true) :
    (interpAt root []).parkOf cur = none := by
  cases cur with
  | suspend thunk =>
    cases thunk <;> simp only [PlainCode, Bool.false_eq_true] at h
    rfl
  | _ => rfl

/-- Step of rows-block-host/R6; consumer: the context-aware primitive bridge. -/
theorem iterOfC_sameCtx (m : Api.Machine) (fr : NFiber) (k : Nat) (ctx : Ctx)
    (ev : NTrace) (step : LocalStep) :
    iterOfC m (fiberAt fr k ctx) ev (step, ctx) = iterOf m (fiberAt fr k ctx) ev step := by
  cases step <;> rfl

/-- Step of rows-block-host/R6; consumer: excluding native scoped callbacks. -/
theorem popFrom_pass_setInterruptible_context (demand : Effect4.Arm) (skip : Bool)
    (K : List NCode) (cur : NCode) (i flag : Bool)
    (hno : (Prim.setInterruptible flag : NCode).hasArm demand = false) :
    (FrameFiber.popFrom demand skip (.setInterruptible flag :: K) (fiberOf cur [] i)).answer =
      (FrameFiber.popFrom demand skip K (fiberOf cur [] flag)).answer := by
  have he : (Prim.setInterruptible flag : NCode).ensure (fiberOf cur [] i) =
      (fiberOf cur [] flag, none) := by cases flag <;> rfl
  have hn : (Prim.setInterruptible flag : NCode).answerOf demand
      ((Prim.setInterruptible flag : NCode).ensure (fiberOf cur [] i)).snd = none := by
    rw [he]
    exact Prim.answerOf_missing _ demand hno
  have hp := FrameFiber.popFrom_pass_no_push demand skip (.setInterruptible flag) K
    (fiberOf cur [] i) rfl (by rw [he]; rfl)
  rw [he] at hp
  rw [FrameFiber.popFrom_continue_answer demand skip _ K _ (Or.inl hn), hp]

theorem popOf_plain_not_scoped_context (cur : NCode) (K : List NCode) (i : Bool)
    (hK : PlainStack K) (ex : ExitV) (body : NCode) (previous : Ctx) (scope : Nat)
    (flag : Bool) :
    (popOf (fiberOf cur K i) ex).answer ≠
      ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag) := by
  induction K generalizing i with
  | nil => cases ex <;> simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, ne_eq, reduceCtorEq, not_false_eq_true, Bool.not_true, Bool.and_self]
  | cons frame K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases frame <;> simp only [PlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · next b n =>
      cases ex with
      | success v =>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true, Bool.false_and, List.nil_append, ne_eq, ContAnswer.frame.injEq, reduceCtorEq, not_false_eq_true]
      | failure c =>
        change (FrameFiber.popFrom Effect4.Arm.contE true (Prim.onSuccess b n :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass Effect4.Arm.contE true _ K cur i rfl rfl).1]
        exact ih i hK'
    · next b n =>
      cases ex with
      | success v =>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true,
          ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm,
          Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil,
          or_self, or_false, decide_true, ContAnswer.frame.injEq, Prim.onSuccessConst.injEq]
      | failure c =>
        change (FrameFiber.popFrom Effect4.Arm.contE true (.onSuccessConst b n :: K)
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
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_true, Bool.and_self, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_false, List.nil_append, ne_eq, ContAnswer.frame.injEq, reduceCtorEq, not_false_eq_true]
    · cases ex <;>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_false, Bool.and_self, List.nil_append, ne_eq, ContAnswer.frame.injEq, not_false_eq_true, Bool.not_true, or_true]
    · cases ex <;>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_false, Bool.and_self, List.nil_append, ne_eq, ContAnswer.frame.injEq, not_false_eq_true, Bool.not_true, or_true]
    · next b n finalizerFlag =>
      cases n <;> cases finalizerFlag <;> simp only [Bool.false_eq_true] at hf
      all_goals cases ex <;> cases i <;>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, reduceCtorEq, List.not_mem_nil, or_self, or_false, decide_true, FrameFiber.interrupted, Option.isSome_none, Bool.and_self, List.nil_append, ne_eq, ContAnswer.frame.injEq, Prim.onExit.injEq, Bool.false_eq, false_and, and_false, not_false_eq_true, List.cons_append, Bool.not_true, or_true, Bool.and_false]
    · next restoreFlag =>
      cases ex
      · change (FrameFiber.popFrom Effect4.Arm.contA false (.setInterruptible restoreFlag :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [popFrom_pass_setInterruptible_context Effect4.Arm.contA false K cur i restoreFlag rfl]
        exact ih restoreFlag hK'
      · change (FrameFiber.popFrom Effect4.Arm.contE true (.setInterruptible restoreFlag :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [popFrom_pass_setInterruptible_context Effect4.Arm.contE true K cur i restoreFlag rfl]
        exact ih restoreFlag hK'
    · next loop cursor =>
      cases ex with
      | success v =>
        simp only [popOf, FrameFiber.getCont, fiberOf, Bool.not_false, Bool.and_true, Bool.false_eq_true, ↓reduceIte, FrameFiber.popFrom, Prim.answerOf, Prim.ensure, Prim.hasArm, Prim.arms, List.contains_eq_mem, List.mem_cons, List.not_mem_nil, or_false, decide_true, Bool.false_and, List.nil_append, ne_eq, ContAnswer.frame.injEq, reduceCtorEq, not_false_eq_true]
      | failure c =>
        change (FrameFiber.popFrom Effect4.Arm.contE true (Prim.whileLoop loop cursor :: K)
          (fiberOf cur [] i)).answer ≠ _
        rw [(popFrom_pass Effect4.Arm.contE true _ K cur i rfl rfl).1]
        exact ih i hK'


/-- Placement: rows-block-host/R6; consumer: the generalized command transitions.
Reach: plain stacks and the no-scoped root hook, at every live context. -/
@[semantics "translation-simulation" (requirement := R6)]
proof_goal evaluateNative_plain_context (root : NativeEff) (hroot : PlainHooks root)
    (m : Api.Machine) (cur : NCode) (K : List NCode) (i : Bool) (k : Nat) (ctx : Ctx)
    (hK : PlainStack K) :
    evaluateNative root m (fiberAt (fiberOf cur K i) k ctx) false table =
      evaluatePrim (interpAt root m.completedExits table) m (fiberAt (fiberOf cur K i) k ctx) false

/-- The primitive evaluator agrees with the single context-aware step.
Placement: rows-block-host/R6; consumer: the hosted one-command transitions.
Reach: non-sync, non-call plain code and the actual live context. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem evaluatePrim_contextStep (root : NativeEff) (hroot : PlainHooks root)
    (m : Api.Machine) (cur : NCode) (K : List NCode) (i : Bool) (k : Nat) (ctx : Ctx)
    (hpl : PlainCode cur = true) (hns : ∀ t, cur ≠ Prim.sync t) (hnc : IsCall cur = false) :
    ∃ ev, evaluatePrim (interpAt root []) m (fiberAt (fiberOf cur K i) k ctx) false =
      iterOfC m (fiberAt (fiberOf cur K i) k ctx) ev
        (contextStep root (fiberOf cur K i) m.state ctx)
 := by
  cases cur with
  | success v =>
    rw [contextStep_fallback root _ _ _ (fun _ h => by cases h)]
    simp only [iterOfC_sameCtx]
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
    rw [contextStep_fallback root _ _ _ (fun _ h => by cases h)]
    simp only [iterOfC_sameCtx]
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
    rw [contextStep_fallback root _ _ _ (fun _ h => by cases h)]
    simp only [iterOfC_sameCtx]
    rw [evaluatePrim_stepShape root m _ _ rfl (parkOf_plain_context root hpl) rfl, stepFrame_eq,
      fiberAt_frame, localStep_other root _ K i m.state (fun _ h => by cases h)
        (fun _ h => by cases h) (fun _ h => by cases h)]
    rcases ((fiberOf _ K i).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩
  | async n w c => cases hpl.symm.trans hnc
  | withFiber thunk =>
    cases thunk with
    | act p =>
      rcases hroot.action p with ha | ha
      · simp only [evaluatePrim, fiberAt_frame, fiberOf, interpAt, interpOf, ha, contextStep]
        exact ⟨[], rfl⟩
      · simp only [evaluatePrim, fiberAt_frame, fiberOf, interpAt, interpOf, ha, contextStep]
        exact ⟨[], rfl⟩
    | getCtx => exact ⟨[], rfl⟩
    | captureMask => cases i <;> exact ⟨[], rfl⟩
    | setCtx next => exact ⟨[RunEvent.contextSet Api.root next], rfl⟩
    | provideMasked update region flag =>
      cases region <;> simp only [PlainCode, Bool.false_eq_true] at hpl
      case program q => cases i <;> exact ⟨[], rfl⟩
    | restoreRegion region flag =>
      cases region <;> simp only [PlainCode, Bool.false_eq_true] at hpl
      case program q => cases flag <;> cases i <;> exact ⟨[], rfl⟩
    | _ => simp only [PlainCode, Bool.false_eq_true] at hpl
  | _ => simp only [PlainCode, Bool.false_eq_true] at hpl

/-- A non-yielding checkpoint evaluates the current primitive at the next count.
Placement: rows-block-host/R6; consumer: generalized hosted segments.
Reach: every context; prevented yielding supplies no termination claim. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem iteration_M_context (root : NativeEff) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (ctx : Ctx)
    (hk : (stores.budgetOf ctx).2 = true ∨ k + 1 < (stores.budgetOf ctx).1) :
    iteration (evaluator := evaluatorFor root table) (interpOf root table)
      (M (fiberOf cur K i) s k tr nt ctx) (fiberAt (fiberOf cur K i) k ctx) false =
      evaluateNative root (M (fiberOf cur K i) s k tr nt ctx)
        (fiberAt (fiberOf cur K i) (k + 1) ctx) false table
 := by
  have hidle : runloopTop (fiberAt (fiberOf cur K i) k ctx) = fiberAt (fiberOf cur K i) k ctx :=
    runloopTop_idle _ rfl
  have hcount : countOp (fiberAt (fiberOf cur K i) k ctx) =
      fiberAt (fiberOf cur K i) (k + 1) ctx := rfl
  have hno : injectYield (M (fiberOf cur K i) s k tr nt ctx)
      (countOp (runloopTop (fiberAt (fiberOf cur K i) k ctx))) false = none := by
    rw [hidle, hcount]
    unfold injectYield
    have guard : (!false && !(stores.budgetOf ctx).2 &&
        yieldVerdict (fiberAt (fiberOf cur K i) (k + 1) ctx)) = false := by
      change (!false && !(stores.budgetOf ctx).2 &&
        decide (k + 1 ≥ (stores.budgetOf ctx).1)) = false
      rcases hk with hp | hk
      · rw [hp]
        rfl
      · rw [decide_eq_false (Nat.not_le.mpr hk)]
        exact Bool.and_false _
    have guard' : (!false && !(fiberAt (fiberOf cur K i) (k + 1) ctx).preventYield &&
        yieldVerdict (fiberAt (fiberOf cur K i) (k + 1) ctx)) = false := guard
    rw [guard']
    rfl
  unfold iteration
  dsimp only
  rw [hno]
  simp only [FiberEvaluator.evaluate, hidle, hcount]

/-- An enabled yielding checkpoint parks the exact saved frame and context.
Placement: rows-block-host/R6; consumer: generalized hosted segments.
Reach: two actual commands, including budgets zero and one; no local progress. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem drive_loop_yield_context (root : NativeEff) (cur : NCode) (K : List NCode)
    (i : Bool) (s : Stores) (k : Nat) (tr : NTrace) (nt : Nat) (rest : List NCmd) (ctx : Ctx)
    (hp : (stores.budgetOf ctx).2 = false) (hk : (stores.budgetOf ctx).1 ≤ k + 1) :
    ∃ tr', ∀ n, driveState (evaluator := evaluatorFor root table) (interpOf root table)
      (n + 2) (M (fiberOf cur K i) s k tr nt ctx) (Cmd.loop Api.root false :: rest) =
      driveState (evaluator := evaluatorFor root table) (interpOf root table) n
        (Myield (fiberOf cur K i) s (k + 2) tr' nt ctx) rest
 := by
  let saved : NCode := Prim.onSuccessConst (Prim.yieldNowWith 0) cur
  let waiting := fiberOf (Prim.yieldNowWith 0) (saved :: K) i
  let tr₁ := tr ++ [RunEvent.yieldInjected Api.root (k + 1)] ++
    [RunEvent.frame Api.root (FrameEvent.pushed saved)]
  refine ⟨tr₁ ++ [RunEvent.parkedOn Api.root nt], fun n => ?_⟩
  have hidle : runloopTop (fiberAt (fiberOf cur K i) k ctx) = fiberAt (fiberOf cur K i) k ctx :=
    runloopTop_idle _ rfl
  have hcount : countOp (fiberAt (fiberOf cur K i) k ctx) = fiberAt (fiberOf cur K i) (k + 1) ctx := rfl
  have hv : yieldVerdict (fiberAt (fiberOf cur K i) (k + 1) ctx) = true := by
    change decide (k + 1 ≥ (stores.budgetOf ctx).1) = true
    exact decide_eq_true hk
  have hit : iteration (evaluator := evaluatorFor root table) (interpOf root table) (M (fiberOf cur K i) s k tr nt ctx)
      (fiberAt (fiberOf cur K i) k ctx) false =
      ⟨M (fiberOf cur K i) s k tr₁ nt ctx, fiberAt waiting (k + 1) ctx,
        true, Outcome.continue_, [], []⟩ := by
    unfold iteration
    rw [hidle, hcount]
    unfold injectYield
    dsimp only
    rw [if_pos (by change (!false && !(stores.budgetOf ctx).2 && _) = true; rw [hp, hv]; rfl)]
    rfl
  rw [show n + 2 = (n + 1) + 1 by omega]
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, hit, settle, settleOutcome]
  rw [M_update]
  simp only [List.nil_append, List.cons_append]
  have hpark : (iteration (evaluator := evaluatorFor root table) (interpOf root table) (M waiting s (k + 1) tr₁ nt ctx)
      (fiberAt waiting (k + 1) ctx) true).outcome = Outcome.parked := by
    simp only [iteration, injectYield_latched]
    rfl
  rw [driveState_succ_cons (evaluator := evaluatorFor root table)]
  simp only [M_stuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, driveStep, M_fiber?, settle, hpark]
  rfl

/-- Firing a parked yield starts the exact wrapped success at count zero.
Placement: rows-block-host/R6; consumer: the receipt-conditioned finite-round proof.
Reach: the dispatcher answer only; subsequent checkpoints may yield again. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem fire_Myield_answer_context (root : NativeEff) (fr : NFiber) (s : Stores)
    (k : Nat) (tr : NTrace) (t : Nat) (ctx : Ctx) :
    ∃ tr', ∀ n, fireState (evaluator := evaluatorFor root table) (interpOf root table) (n + 1 + 1)
      (Myield fr s k tr t ctx) Api.root =
      stepDecisionState.loop (driveState (evaluator := evaluatorFor root table) (interpOf root table)
        n (M { fr with
          current := .success Val.unit
          stack := .onSuccessConst (.yieldNowWith 0) fr.current :: fr.stack }
          s 0 tr' (t + 1) ctx) [Cmd.loop Api.root false, Cmd.drainDue])
 := by
  refine ⟨tr ++ [RunEvent.ranTask Api.root (Task.resume Api.root t (Prim.success Val.unit))] ++
    [RunEvent.resumedWith Api.root t (Prim.success Val.unit)] ++ [RunEvent.started Api.root], fun n => ?_⟩
  have hdrain : (parkedAt fr k t ctx).dispatcher.drain =
      ([Task.resume Api.root t (Prim.success Val.unit)], Dispatcher.empty) := rfl
  unfold fireState
  simp only [Myield_fiber?, hdrain]
  dsimp only [List.foldl, fireStep, taskCmds, stepDecisionState.loop]
  simp only [↓reduceIte, RunMachine.emit, RunMachine.disarm, RunMachine.update, parkedAt, fiberAt,
    RunFiber.make, Dispatcher.empty, Myield, RunMachine.empty, List.map_cons, List.map_nil, ne_eq, decide_not,
    decide_true, Bool.not_true, Bool.false_eq_true, not_false_eq_true, List.filter_cons_of_neg, List.filter_nil,
    List.isEmpty_cons, driveState_succ_cons, Option.isSome_none, driveStep, RunMachine.fiber?, List.find?_cons_of_pos,
    List.append_assoc, List.cons_append, List.nil_append, Bool.or_self, bne_self_eq_false, M]

end Effect4.Program.Agreement
