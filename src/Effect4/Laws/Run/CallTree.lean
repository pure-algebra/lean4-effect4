import Effect4.Laws.Api.SessionMeaning
import Effect4.Laws.Program.Agreement.HostedLoop
import Effect4.Laws.Run.JournalPrefix
import Effect4.Laws.Auto.Obligations
import Effect4.Program.Fold
import Effect4.Laws.Program.HostReplyTape

/-!
# Recorded calls and the admitted call tree

Concept: translation-simulation, R6. Claim: recorded-call-tree-prefix, role inversion.
Consumer: `Routing.unauthorized_calls_nothing`, through its proved token check in the call tree.
Reach: `StraightRows`, no cause handlers, external-only source operations, concrete reply columns, every recorded script and every command budget.
The claim extends `rows_loop_frontier` to calls observed before a run settles.
It establishes no progress, fairness, fork behavior, scope behavior, or outside-host agreement.
The host boundary remains `docs/core/host-boundary.md`.
-/

set_option autoImplicit false

namespace Effect4.Run.CallTree

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement
open Effect4.Api.HostSession (Call)
open Effect4.Api.Runner (Command)

/-- The generated fold rejects each source form that can observe an interruption. -/
def NoCauseHandler (program : NativeEff) : Bool :=
  foldMap_eff true (· && ·) program fun
    | .catchCause _ _ | .matchCause _ _ _ | .onExit _ _ | .exit _ => false
    | _ => true

/-- A reply-only tape cannot describe external clock advances.
Consumer: the retained clock boundary control; `ExternalOnly` supplies the active source restriction. -/
def NoClockRead (program : NativeEff) : Bool :=
  foldMap_eff true (· && ·) program fun
    | .perform .clockNow _ => false
    | _ => true

/-- The reply host that answers a call with the tape's next exit only where the row's own
columns admit it (`externalAdmits`). It is the reply tape as the session reads it. -/
def admittedTapeHost (table : RowTable) : Effects.Comodel (RowSig table) ReplyTape where
  answer op tape :=
    match tape with
    | [] => none
    | ex :: rest => if externalAdmits table op.1.val (.ofExit ex) then some (ex, rest) else none

/-- Where a tree waits under a tape: the row and the request of the call that found the tape
empty, or no wait. -/
def treeWaits (table : RowTable) (program : NativeEff) (T : ReplyTape) : RowsStop :=
  (observeRows (admittedTapeHost table) (some <$> denoteRows table program []) Stores.empty T).stop

/-- An empty admitted reply tape answers no call.
Consumer: `tree_wait_of_leads`. -/
theorem admitted_tape_empty (table : RowTable) (code : NCode) :
    hostAnswer (admittedTapeHost table) code [] = none := by
  unfold hostAnswer
  split
  · show (if _ : _ < table.length then (none : Option (ExitV × ReplyTape)) else none) = none
    split <;> rfl
  · rfl

/-- Existing local agreement fixes the row and request of a straight call-tree wait.
Consumer: `request_in_tree`; no settled-machine or sufficient-budget premise enters this reader. -/
theorem tree_wait_of_leads (table : RowTable) (program : NativeEff)
    (fragment : StraightRows table program = true) (compileFuel : Nat) (tape : ReplyTape)
    (frame : NFiber) (stores : Stores) (row : Nat) (request : Val)
    (leads : Leads (admittedTapeHost table) program
      (.live (fiberOf (compile program compileFuel) []) Stores.empty) tape
      (.live frame stores) [])
    (call : IsCall frame.current = true)
    (atCall : callOf frame.current = some (row, request)) :
    treeWaits table program tape = .waiting row request := by
  obtain ⟨lower, waiting⟩ := localWaitC_to_rowsB (admittedTapeHost table) program
    (loopedDataRows_of_straightRows program fragment) compileFuel tape [] leads call
    (admitted_tape_empty table frame.current) atCall
  have actual := waiting lower (Nat.le_refl lower)
  rw [denoteRowsB_straight table lower program [] fragment] at actual
  unfold treeWaits
  rw [observeRows_eq_runRowsO, actual]
  rfl

/-! ## The external-only straight fragment without cause handlers -/

/-- The straight-row fragment without cause handlers, restricted to external operations. -/
def ExtRows (table : RowTable) : NativeEff → Bool
  | .succeed _ | .fail _ | .failCause _ | .sync _ => true
  | .suspend a => ExtRows table a
  | .perform (.external i) _ => dataRow table i
  | .bind a b => ExtRows table a && ExtRows table b
  | .catchIf _ a b => ExtRows table a && ExtRows table b
  | .select _ _ a b => ExtRows table a && ExtRows table b
  | _ => false

theorem node_at_append : ∀ (path : List Nat) (n m : Node NativeOp) (i : Nat),
    Node.at_ n path = some m → Node.at_ n (path ++ [i]) = m.child i
  | [], n, m, i, h => by
    change some n = some m at h
    cases h
    show (n.child i).bind (fun x => some x) = n.child i
    cases n.child i <;> rfl
  | j :: rest, n, m, i, h => by
    simp only [Node.at_, List.cons_append] at h ⊢
    rcases hc : n.child j with _ | n'
    · rw [hc] at h; cases h
    · rw [hc] at h
      exact node_at_append rest n' m i h

theorem extRows_of_at (table : RowTable) (root : NativeEff)
    (external : SourceScope.ExternalOnly root) :
    ∀ (e : NativeEff) (path : List Nat),
      Node.at_ (.eff root) path = some (.eff e) →
      StraightRows table e = true →
      NoCauseHandler e = true →
      ExtRows table e = true
  | .succeed _, _, _, _, _ => rfl
  | .fail _, _, _, _, _ => rfl
  | .failCause _, _, _, _, _ => rfl
  | .sync _, _, _, _, _ => rfl
  | .suspend a, path, hat, hstr, hnc => by
    have ha : Node.at_ (.eff root) (path ++ [0]) = some (.eff a) :=
      node_at_append path (.eff root) (.eff (.suspend a)) 0 hat
    exact extRows_of_at table root external a (path ++ [0]) ha hstr hnc
  | .perform op req, path, hat, hstr, _ => by
    obtain ⟨i, rfl⟩ := external.operation path op req hat
    exact hstr
  | .bind a b, path, hat, hstr, hnc => by
    have ha : Node.at_ (.eff root) (path ++ [0]) = some (.eff a) :=
      node_at_append path (.eff root) (.eff (.bind a b)) 0 hat
    have hb : Node.at_ (.eff root) (path ++ [1]) = some (.eff b) :=
      node_at_append path (.eff root) (.eff (.bind a b)) 1 hat
    change (StraightRows table a && StraightRows table b) = true at hstr
    simp only [Bool.and_eq_true] at hstr
    change (true && (NoCauseHandler a && NoCauseHandler b)) = true at hnc
    simp only [Bool.true_and, Bool.and_eq_true] at hnc
    simp only [ExtRows, Bool.and_eq_true]
    exact ⟨extRows_of_at table root external a (path ++ [0]) ha hstr.1 hnc.1,
      extRows_of_at table root external b (path ++ [1]) hb hstr.2 hnc.2⟩
  | .catchIf t a b, path, hat, hstr, hnc => by
    have ha : Node.at_ (.eff root) (path ++ [0]) = some (.eff a) :=
      node_at_append path (.eff root) (.eff (.catchIf t a b)) 0 hat
    have hb : Node.at_ (.eff root) (path ++ [1]) = some (.eff b) :=
      node_at_append path (.eff root) (.eff (.catchIf t a b)) 1 hat
    change (StraightRows table a && StraightRows table b) = true at hstr
    simp only [Bool.and_eq_true] at hstr
    change (true && (NoCauseHandler a && NoCauseHandler b)) = true at hnc
    simp only [Bool.true_and, Bool.and_eq_true] at hnc
    simp only [ExtRows, Bool.and_eq_true]
    exact ⟨extRows_of_at table root external a (path ++ [0]) ha hstr.1 hnc.1,
      extRows_of_at table root external b (path ++ [1]) hb hstr.2 hnc.2⟩
  | .select c d a b, path, hat, hstr, hnc => by
    have ha : Node.at_ (.eff root) (path ++ [0]) = some (.eff a) :=
      node_at_append path (.eff root) (.eff (.select c d a b)) 0 hat
    have hb : Node.at_ (.eff root) (path ++ [1]) = some (.eff b) :=
      node_at_append path (.eff root) (.eff (.select c d a b)) 1 hat
    change (StraightRows table a && StraightRows table b) = true at hstr
    simp only [Bool.and_eq_true] at hstr
    change (true && (NoCauseHandler a && NoCauseHandler b)) = true at hnc
    simp only [Bool.true_and, Bool.and_eq_true] at hnc
    simp only [ExtRows, Bool.and_eq_true]
    exact ⟨extRows_of_at table root external a (path ++ [0]) ha hstr.1 hnc.1,
      extRows_of_at table root external b (path ++ [1]) hb hstr.2 hnc.2⟩
  | .exit _, _, _, _, hnc
  | .catchCause _ _, _, _, _, hnc
  | .matchCause _ _ _, _, _, _, hnc
  | .onExit _ _, _, _, _, hnc => by
    cases hnc
  | .iterate _ _ _ _ _ _, _, _, hstr, _
  | .gen _, _, _, hstr, _
  | .uninterruptible _, _, _, hstr, _
  | .interruptible _, _, _, hstr, _
  | .yieldNow _, _, _, hstr, _
  | .awaitFiber _ _, _, _, hstr, _
  | .withFiber _, _, _, hstr, _
  | .scoped _, _, _, hstr, _
  | .acquireRelease _ _, _, _, hstr, _
  | .provideLayer _ _ _, _, _, hstr, _
  | .service _, _, _, hstr, _
  | .provideService _ _ _, _, _, hstr, _
  | .restore _ _, _, _, hstr, _
  | .defs _ _ _ _, _, _, hstr, _ => by
    cases hstr

theorem extRows_of_source (table : RowTable) (root : NativeEff)
    (hstr : StraightRows table root = true) (hnc : NoCauseHandler root = true)
    (external : SourceScope.ExternalOnly root) :
    ExtRows table root = true :=
  extRows_of_at table root external root [] rfl hstr hnc

theorem ExtRows.suspendDecided_iff {table : RowTable} {e : NativeEff} (he : ExtRows table e = true) :
    e.suspendDecided = true ↔
      (∃ b, e = .suspend b) ∨ (∃ s d a b, e = .select s d a b) := by
  cases e with
  | perform op r =>
    cases op <;> simp only [ExtRows, Eff.suspendDecided, Bool.false_eq_true,
      reduceCtorEq, exists_false, or_self] at he ⊢
  | suspend b => exact iff_of_true rfl (Or.inl ⟨b, rfl⟩)
  | select t d a b => exact iff_of_true rfl (Or.inr ⟨t, d, a, b, rfl⟩)
  | _ => simp only [Eff.suspendDecided, ExtRows, Bool.false_eq_true, reduceCtorEq, exists_false,
      or_self] at he ⊢

/-- Continuation names in `ExtRows`: only `cont` and `caughtError`. -/
def ExtPlainName : EffName → Bool
  | .cont _ | .caughtError _ => true
  | _ => false

/-- External call of a data row in `table`. -/
def ExtCall (table : RowTable) : NCode → Bool
  | Prim.async (EffName.external (.external i) _ _) false none => dataRow table i
  | _ => false

/-- Compiled primitives in `ExtRows`. -/
def ExtPlainCode (table : RowTable) : NCode → Bool
  | Prim.success _ | Prim.failure _ | Prim.yieldableError _ => true
  | Prim.sync (EffThunk.pure _) => true
  | Prim.suspend (EffThunk.body _) => true
  | Prim.onSuccess b n | Prim.onFailure b n => ExtPlainCode table b && ExtPlainName n
  | Prim.async n w c => ExtCall table (Prim.async n w c)
  | _ => false

/-- Stack frames in `ExtRows`: only `onSuccess` and `onFailure`. -/
def ExtPlainFrame (table : RowTable) : NCode → Bool
  | Prim.onSuccess b n | Prim.onFailure b n => ExtPlainCode table b && ExtPlainName n
  | _ => false

def ExtPlainStack (table : RowTable) (K : List NCode) : Prop :=
  ∀ fr ∈ K, ExtPlainFrame table fr = true

theorem ExtPlainName.toContextFree {n : EffName} (h : ExtPlainName n = true) : ContextFreeName n = true := by
  cases n <;> simp only [ExtPlainName, ContextFreeName, Bool.false_eq_true] at h ⊢

theorem ExtCall.toIsCall {table : RowTable} {c : NCode} (h : ExtCall table c = true) :
    IsCall c = true := by
  cases c with
  | async n w cancel =>
    cases n with
    | external op v p =>
      cases op <;> cases w <;> cases cancel <;>
        simp only [ExtCall, IsCall, Bool.false_eq_true] at h ⊢
    | _ => simp only [ExtCall, Bool.false_eq_true] at h
  | _ => simp only [ExtCall, Bool.false_eq_true] at h

theorem ExtPlainCode.toContextFree {table : RowTable} :
    ∀ {c : NCode}, ExtPlainCode table c = true → ContextFreeCode c = true
  | Prim.success _, _ | Prim.failure _, _ | Prim.yieldableError _, _
  | Prim.sync (EffThunk.pure _), _ | Prim.suspend (EffThunk.body _), _ => rfl
  | Prim.onSuccess b n, h | Prim.onFailure b n, h => by
    simp only [ExtPlainCode, ContextFreeCode, Bool.and_eq_true] at h ⊢
    exact ⟨ExtPlainCode.toContextFree h.1, ExtPlainName.toContextFree h.2⟩
  | Prim.async n w c, h => ExtCall.toIsCall h
  | Prim.sync (EffThunk.op _), h | Prim.sync (EffThunk.store _), h
  | Prim.suspend (EffThunk.store _), h
  | Prim.onSuccessAndFailure _ _ _, h | Prim.exitFrame _, h | Prim.onExit _ _ _, h
  | Prim.whileLoop _ _, h | Prim.withFiber _, h | Prim.iterator _ _, h
  | Prim.setInterruptible _, h | Prim.yieldNowWith _, h | Prim.asyncFinalizer _, h
  | Prim.onSuccessConst _ _, h => by
    simp only [ExtPlainCode, Bool.false_eq_true] at h

/-- Step of recorded-call-tree-prefix/R6; consumer: `LeadsTape.step`.
The external-only straight lane never interprets a fiber action. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem ExtPlainCode.noWithFiber {table : RowTable} {code : NCode}
    (h : ExtPlainCode table code = true) (thunk : EffThunk) : code ≠ Prim.withFiber thunk := by
  intro same
  subst code
  cases h

theorem ExtPlainCode.not_sync_op {table : RowTable} {c : NCode} (h : ExtPlainCode table c = true) :
    ∀ o, c ≠ Prim.sync (EffThunk.op o) := by
  intro o heq
  subst heq
  simp only [ExtPlainCode, Bool.false_eq_true] at h

theorem ExtPlainCode.extCall_of_isCall {table : RowTable} {c : NCode}
    (h : ExtPlainCode table c = true) (hc : IsCall c = true) : ExtCall table c = true := by
  cases c <;> simp only [IsCall, ExtPlainCode, Bool.false_eq_true] at hc h ⊢
  exact h

theorem ExtPlainFrame.toContextFree {table : RowTable} {fr : NCode} (h : ExtPlainFrame table fr = true) :
    ContextFreeFrame fr = true := by
  cases fr <;> simp only [ExtPlainFrame, ContextFreeFrame, Bool.and_eq_true, Bool.false_eq_true] at h ⊢
  · exact ⟨ExtPlainCode.toContextFree h.1, ExtPlainName.toContextFree h.2⟩
  · exact ⟨ExtPlainCode.toContextFree h.1, ExtPlainName.toContextFree h.2⟩

theorem ExtPlainFrame.not_contAll {table : RowTable} {fr : NCode}
    (h : ExtPlainFrame table fr = true) : fr.hasArm .contAll = false := by
  cases fr <;> simp only [ExtPlainFrame, Bool.false_eq_true] at h <;> rfl

theorem ExtPlainStack.nil (table : RowTable) : ExtPlainStack table [] :=
  fun _ h => absurd h List.not_mem_nil

theorem ExtPlainStack.cons {table : RowTable} {fr : NCode} {K : List NCode}
    (hK : ExtPlainStack table K) (hfr : ExtPlainFrame table fr = true) :
    ExtPlainStack table (fr :: K) := by
  intro f hf
  rcases List.mem_cons.mp hf with rfl | hf
  · exact hfr
  · exact hK f hf

theorem ExtPlainStack.head {table : RowTable} {fr : NCode} {K : List NCode}
    (hK : ExtPlainStack table (fr :: K)) : ExtPlainFrame table fr = true :=
  hK fr List.mem_cons_self

theorem ExtPlainStack.tail {table : RowTable} {fr : NCode} {K : List NCode}
    (hK : ExtPlainStack table (fr :: K)) : ExtPlainStack table K :=
  fun f hf => hK f (List.mem_cons_of_mem fr hf)

theorem ExtPlainStack.toContextFree {table : RowTable} {K : List NCode} (hK : ExtPlainStack table K) :
    ContextFreeStack K :=
  fun fr hfr => ExtPlainFrame.toContextFree (hK fr hfr)

theorem extPlainCode_compileEff (table : RowTable) :
    ∀ (e : NativeEff) (p : Point), ExtRows table e = true →
      ExtPlainCode table (compileEff e p) = true
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
  | .perform op r, p, he => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · cases op with
      | external j =>
        rw [compileEff_perform (.external j) r hf]
        show ExtPlainCode table (asyncRoute (.external j) r p) = true
        dsimp only [asyncRoute]
        rcases evalTerm p.env r with _ | v
        · rfl
        · exact he
      | _ => simp only [ExtRows, Bool.false_eq_true] at he
  | .bind a b, p, he => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_bind a b hf]
      simp only [ExtPlainCode, ExtPlainName, Bool.and_true]
      simp only [ExtRows, Bool.and_eq_true] at he
      exact extPlainCode_compileEff table a (p.child 0) he.1
  | .select s d a b, p, _ => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_select s d a b hf]; rfl
  | .catchIf t b h, p, he => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_at_zero _ hf]; rfl
    · rw [compileEff_catchIf t b h hf]
      simp only [ExtPlainCode, ExtPlainName, Bool.and_true]
      simp only [ExtRows, Bool.and_eq_true] at he
      exact extPlainCode_compileEff table b (p.child 0) he.1
  | .exit _, _, he | .catchCause _ _, _, he | .matchCause _ _ _, _, he
  | .onExit _ _, _, he | .iterate _ _ _ _ _ _, _, he | .gen _, _, he
  | .uninterruptible _, _, he | .interruptible _, _, he | .yieldNow _, _, he
  | .awaitFiber _ _, _, he | .withFiber _, _, he | .scoped _, _, he
  | .acquireRelease _ _, _, he | .provideLayer _ _ _, _, he | .service _, _, he
  | .provideService _ _ _, _, he | .restore _ _, _, he | .defs _ _ _ _, _, he => by
    simp only [ExtRows, Bool.false_eq_true] at he

def NodeExt (table : RowTable) : Node NativeOp → Prop
  | Node.eff e => ExtRows table e = true
  | _ => False

theorem child_ext {table : RowTable} {r : NativeEff} (hr : ExtRows table r = true) {i : Nat}
    {m : Node NativeOp} (h : (Node.eff r).child i = some m) : NodeExt table m := by
  cases r with
  | suspend a =>
    rcases i with _ | i <;> simp only [Node.child, Option.some.injEq, reduceCtorEq] at h
    subst h
    exact hr
  | bind a b | catchIf _ a b | select _ _ a b =>
    simp only [ExtRows, Bool.and_eq_true] at hr
    rcases i with _ | _ | i <;> simp only [Node.child, Option.some.injEq, reduceCtorEq] at h
    · subst h; exact hr.1
    · subst h; exact hr.2
  | perform op _ =>
    cases op <;> simp only [ExtRows, Node.child, reduceCtorEq, Bool.false_eq_true] at hr h
  | _ =>
    simp only [ExtRows, Node.child, reduceCtorEq, Bool.false_eq_true] at hr h

theorem ext_at {table : RowTable} :
    ∀ (path : List Nat) (n : Node NativeOp) (e : NativeEff), NodeExt table n →
      Node.at_ n path = some (Node.eff e) → ExtRows table e = true
  | [], n, e, hn, h => by
    simp only [Node.at_, Option.some.injEq] at h
    subst h
    exact hn
  | i :: rest, n, e, hn, h => by
    simp only [Node.at_] at h
    rcases hc : n.child i with _ | m
    · rw [hc] at h; cases h
    · rw [hc] at h
      simp only [Option.bind] at h
      have hm : NodeExt table m := by
        cases n
        · exact child_ext hn hc
        all_goals simp only [NodeExt] at hn
      exact ext_at rest m e hm h

theorem extPlainCode_resolve {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) (q : Point) :
    ExtPlainCode table (resolve root q) = true := by
  unfold resolve
  rcases h : Node.at_ (Node.eff root) q.path with _ | n
  · rfl
  · cases n
    · rename_i e
      exact extPlainCode_compileEff table e q (ext_at q.path (Node.eff root) e hroot h)
    all_goals rfl

theorem extPlainCode_suspendBodyAt {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) (q : Point) :
    ExtPlainCode table (suspendBodyAt root (EffThunk.body q)) = true := by
  rcases hf : q.fuel with _ | k
  · rw [suspendBodyAt_zero hf]; rfl
  · rcases h : Node.at_ (Node.eff root) q.path with _ | n
    · rw [suspendBodyAt_missing hf h]; rfl
    · cases n with
      | eff e =>
        have he : ExtRows table e = true := ext_at q.path (Node.eff root) e hroot h
        rcases hd : e.suspendDecided with _ | _
        · rw [suspendBodyAt_of_at hf h hd]
          exact extPlainCode_compileEff table _ q he
        · rcases (ExtRows.suspendDecided_iff he).mp hd with ⟨b, rfl⟩ | ⟨s, d, a, b, rfl⟩
          · rw [suspendBodyAt_suspend hf h]
            exact extPlainCode_resolve hroot _
          · rcases hdec : (evalTerm q.env s).bind d.decide with _ | ⟨first, bound⟩
            · rw [suspendBodyAt_select_bad hf h hdec]; rfl
            · rw [suspendBodyAt_select_of_decide hf h hdec]
              exact extPlainCode_resolve hroot _
      | stmts _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | stmt _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | action _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | effs _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | layer _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl
      | layers _ => rw [suspendBodyAt_other hf h (fun _ h => by cases h)]; rfl

theorem extPlainCode_ofExit (table : RowTable) (ex : ExitV) :
    ExtPlainCode table (Prim.ofExit ex) = true := by
  cases ex <;> rfl

theorem extPlainCode_contEOf_caughtError {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) (p : Point) (c : CauseV) :
    ExtPlainCode table (Program.contEOf root (EffName.caughtError p) c) = true := by
  simp only [Program.contEOf]
  split
  · split
    · exact extPlainCode_resolve hroot _
    · rfl
  · rfl

theorem extPlainCode_contAAt {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) {n : EffName}
    (hn : ExtPlainName n = true) (v : Val) :
    ExtPlainCode table ((interpAt root []).contA n v) = true := by
  cases n <;> simp only [ExtPlainName, Bool.false_eq_true] at hn
  · exact extPlainCode_resolve hroot _
  · rfl

theorem extPlainCode_contEAt {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) {n : EffName}
    (hn : ExtPlainName n = true) (c : CauseV) :
    ExtPlainCode table ((interpAt root []).contE n c) = true := by
  cases n <;> simp only [ExtPlainName, Bool.false_eq_true] at hn
  · rfl
  · exact extPlainCode_contEOf_caughtError hroot _ _

theorem localStep_success_ext {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) (v : Val) (K : List NCode) (s : Stores)
    (fr' : NFiber) (s' : Stores) (hK : ExtPlainStack table K)
    (h : localStep root (fiberOf (Prim.success v) K true) s = .running fr' s') :
    s' = s ∧ ∃ cur' K', fr' = fiberOf cur' K' true ∧
      ExtPlainCode table cur' = true ∧ ExtPlainStack table K' := by
  induction K with
  | nil =>
    have he := step_exit_empty root (Exit.success v) true s
    simp only [Prim.ofExit] at he
    rw [he] at h
    cases h
  | cons f K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases f <;> simp only [ExtPlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · rw [step_success_onSuccess] at h
      cases h
      exact ⟨rfl, _, _, rfl, extPlainCode_contAAt hroot hf.2 v, hK'⟩
    · rw [step_success_pass_onFailure] at h
      exact ih hK' h

theorem localStep_failure_ext {table : RowTable} {root : NativeEff}
    (hroot : ExtRows table root = true) (c : CauseV) (K : List NCode) (s : Stores)
    (fr' : NFiber) (s' : Stores) (hK : ExtPlainStack table K)
    (h : localStep root (fiberOf (Prim.failure c) K true) s = .running fr' s') :
    s' = s ∧ ∃ cur' K', fr' = fiberOf cur' K' true ∧
      ExtPlainCode table cur' = true ∧ ExtPlainStack table K' := by
  induction K with
  | nil =>
    have he := step_exit_empty root (Exit.failure c) true s
    simp only [Prim.ofExit] at he
    rw [he] at h
    cases h
  | cons f K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases f <;> simp only [ExtPlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · rw [step_failure_pass_onSuccess] at h
      exact ih hK' h
    · rw [step_failure_onFailure] at h
      cases h
      exact ⟨rfl, _, _, rfl, extPlainCode_contEAt hroot hf.2 c, hK'⟩

theorem localStep_ext {table : RowTable} {root : NativeEff} (hroot : ExtRows table root = true)
    (cur : NCode) (K : List NCode) (s : Stores) (fr' : NFiber) (s' : Stores)
    (hpl : ExtPlainCode table cur = true) (hK : ExtPlainStack table K)
    (h : localStep root (fiberOf cur K true) s = .running fr' s') :
    s' = s ∧ ∃ cur' K', fr' = fiberOf cur' K' true ∧
      ExtPlainCode table cur' = true ∧ ExtPlainStack table K' := by
  cases cur with
  | success v => exact localStep_success_ext hroot v K s fr' s' hK h
  | failure c => exact localStep_failure_ext hroot c K s fr' s' hK h
  | yieldableError e =>
    rw [step_yieldableError] at h
    cases h
    exact ⟨rfl, _, _, rfl, rfl, hK⟩
  | sync thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    rw [step_sync_pure] at h
    cases h
    exact ⟨rfl, _, _, rfl, rfl, hK⟩
  | suspend thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    rw [step_suspend] at h
    cases h
    exact ⟨rfl, _, _, rfl, extPlainCode_suspendBodyAt hroot _, hK⟩
  | onSuccess b n =>
    rw [step_push_onSuccess] at h
    cases h
    simp only [ExtPlainCode, Bool.and_eq_true] at hpl
    exact ⟨rfl, _, _, rfl, hpl.1, hK.cons (by simp only [ExtPlainFrame, hpl.1, hpl.2, Bool.and_self])⟩
  | onFailure b n =>
    rw [step_push_onFailure] at h
    cases h
    simp only [ExtPlainCode, Bool.and_eq_true] at hpl
    exact ⟨rfl, _, _, rfl, hpl.1, hK.cons (by simp only [ExtPlainFrame, hpl.1, hpl.2, Bool.and_self])⟩
  | async n w c =>
    rw [localStep_async] at h
    cases h
    exact ⟨rfl, _, _, rfl, hpl, hK⟩
  | onSuccessAndFailure _ _ _ | exitFrame _ | onExit _ _ _ | whileLoop _ _
  | withFiber _ | iterator _ _ | setInterruptible _ | yieldNowWith _
  | asyncFinalizer _ | onSuccessConst _ _ =>
    simp only [ExtPlainCode, Bool.false_eq_true] at hpl

/-- The stack wrapper produced by one or more injected yields around a base `(cur, K)`. -/
inductive YieldStack (cur : NCode) (K : List NCode) : NCode → List NCode → Prop where
  | plain : YieldStack cur K cur K
  | yielding {c : NCode} {S : List NCode} :
      YieldStack cur K c S →
      YieldStack cur K (Prim.yieldNowWith 0) (Prim.onSuccessConst (Prim.yieldNowWith 0) c :: S)
  | resuming {c : NCode} {S : List NCode} :
      YieldStack cur K c S →
      YieldStack cur K (Prim.success Val.unit) (Prim.onSuccessConst (Prim.yieldNowWith 0) c :: S)

theorem YieldStack.not_contAll {cur : NCode} {K : List NCode} {cur' : NCode} {K' : List NCode}
    (hys : YieldStack cur K cur' K') (hK : ∀ fr ∈ K, fr.hasArm .contAll = false) :
    ∀ fr ∈ K', fr.hasArm .contAll = false := by
  induction hys with
  | plain => exact hK
  | yielding _ ih =>
    intro fr hfr
    rcases List.mem_cons.mp hfr with rfl | hfr
    · rfl
    · exact ih fr hfr
  | resuming _ ih =>
    intro fr hfr
    rcases List.mem_cons.mp hfr with rfl | hfr
    · rfl
    · exact ih fr hfr

theorem YieldStack.eq_of_isCall {cur : NCode} {K : List NCode} {cur' : NCode} {K' : List NCode}
    (hys : YieldStack cur K cur' K') (hc : IsCall cur' = true) :
    cur' = cur ∧ K' = K := by
  cases hys with
  | plain => exact ⟨rfl, rfl⟩
  | yielding _ => simp only [IsCall, Bool.false_eq_true] at hc
  | resuming _ => simp only [IsCall, Bool.false_eq_true] at hc

/-- Reaching a live local fiber under any suffix of the reply tape. -/
def LeadsTape (table : RowTable) (root : NativeEff)
    (fr₀ : NFiber) (s₀ : Stores) (tape : ReplyTape) (fr : NFiber) (s : Stores) : Prop :=
  ∃ c, ∀ rest : ReplyTape,
    ReachesC (admittedTapeHost table) root c fr₀ s₀ (tape ++ rest) fr s rest

theorem LeadsTape.refl (table : RowTable) (root : NativeEff) (fr₀ : NFiber) (s₀ : Stores) :
    LeadsTape table root fr₀ s₀ [] fr₀ s₀ :=
  ⟨0, fun rest => ReachesC.refl (admittedTapeHost table) root fr₀ s₀ rest⟩

theorem LeadsTape.step {table : RowTable} {root : NativeEff}
    {fr₀ fr fr' : NFiber} {s₀ s s' : Stores} {tape : ReplyTape}
    (hL : LeadsTape table root fr₀ s₀ tape fr s)
    (hstep : localStep root fr s = .running fr' s')
    (hcall : IsCall fr.current = false) (hwith : ∀ thunk, fr.current ≠ Prim.withFiber thunk) :
    LeadsTape table root fr₀ s₀ tape fr' s' := by
  obtain ⟨c, hc⟩ := hL
  exact ⟨c + 1, fun rest => (hc rest).trans (ReachesC.step hstep hcall hwith rest)⟩

theorem LeadsTape.answer {table : RowTable} {root : NativeEff}
    {fr₀ fr : NFiber} {s₀ s : Stores} {tape : ReplyTape} {ex : ExitV}
    (hL : LeadsTape table root fr₀ s₀ tape fr s)
    (hcall : IsCall fr.current = true)
    (hadm : ∀ rest : ReplyTape,
      hostAnswer (admittedTapeHost table) fr.current (ex :: rest) = some (ex, rest))
    (hp : prepareExternalAnswer table (some fr.current) (.ofExit ex) s = (s, Prim.ofExit ex)) :
    LeadsTape table root fr₀ s₀ (tape ++ [ex]) { fr with current := Prim.ofExit ex } s := by
  obtain ⟨c, hc⟩ := hL
  refine ⟨c + 1, fun rest => ?_⟩
  rw [List.append_assoc, List.singleton_append]
  exact (hc (ex :: rest)).trans (ReachesC.answer s hcall (hadm rest) hp)

theorem LeadsTape.toLeads {table : RowTable} {root : NativeEff}
    {fr₀ fr : NFiber} {s₀ s : Stores} {tape : ReplyTape}
    (hL : LeadsTape table root fr₀ s₀ tape fr s) :
    Leads (admittedTapeHost table) root (.live fr₀ s₀) tape (.live fr s) [] := by
  obtain ⟨c, hc⟩ := hL
  have h0 := hc []
  rw [List.append_nil] at h0
  exact h0.join

/-! ## Single-step evaluation on `YieldStack`, interrupted fibers, and `ExtPlainCode` -/

theorem evaluateNative_onSuccessConst (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (c : NCode) (S : List NCode) (ic? : Option CauseV)
    (hf : f.frame = ⟨Prim.onSuccessConst (Prim.yieldNowWith 0) c, S, true, ic?, false⟩) :
    evaluateNative root m f yielding table =
      ⟨m.emit [RunEvent.frame f.id (FrameEvent.pushed (Prim.onSuccessConst (Prim.yieldNowWith 0) c))],
        { f with frame := ⟨Prim.yieldNowWith 0,
            Prim.onSuccessConst (Prim.yieldNowWith 0) c :: S, true, ic?, false⟩ },
        yielding, Outcome.continue_, [], []⟩ := by
  unfold evaluateNative evaluatePrim evaluatePrim.stepFrame FrameFiber.step evaluatePrim.finishFrame
  simp only [hf]
  rfl

theorem evaluateNative_yieldNow (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (S : List NCode) (ic? : Option CauseV)
    (hf : f.frame = ⟨Prim.yieldNowWith 0, S, true, ic?, false⟩) :
    evaluateNative root m f yielding table =
      ⟨(({ m with nextToken := m.nextToken + 1 }).arm f.id).emit [RunEvent.parkedOn f.id m.nextToken],
        ({ f with
            frame := (⟨Prim.success Val.unit, S, true, ic?, false⟩ : NFiber),
            dispatcher := f.dispatcher.enqueue 0 (.resume f.id m.nextToken (Prim.success Val.unit)) }).park
          ⟨m.nextToken, none, [], [], Resume.void, false⟩,
        yielding, Outcome.parked, [], []⟩ := by
  unfold evaluateNative evaluatePrim
  simp only [hf]
  rfl

theorem evaluateNative_resuming (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (c : NCode) (S : List NCode) (ic? : Option CauseV)
    (hf : f.frame = ⟨Prim.success Val.unit,
        Prim.onSuccessConst (Prim.yieldNowWith 0) c :: S, true, ic?, false⟩) :
    evaluateNative root m f yielding table =
      ⟨m.emit [RunEvent.frame f.id (FrameEvent.popped (Prim.onSuccessConst (Prim.yieldNowWith 0) c))],
        { f with frame := ⟨c, S, true, ic?, false⟩ },
        yielding, Outcome.continue_, [], []⟩ := by
  unfold evaluateNative exitScoped evaluatePrim evaluatePrim.finalizerOr
    evaluatePrim.stepFrame FrameFiber.step FrameFiber.resumeValue evaluatePrim.finishFrame
  simp only [hf]
  rfl

theorem evaluateNative_extCall (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (j : Nat) (v : Val) (p : List Nat) (K : List NCode)
    (hf : f.frame = fiberOf (Prim.async (EffName.external (.external j) v p) false none) K true) :
    evaluateNative root m f yielding table =
      ⟨({ m with state := m.state, nextToken := m.nextToken + 1 }).emit
          [RunEvent.parkedOn f.id m.nextToken],
        f.park ⟨m.nextToken, none, [], [], Resume.void, false⟩,
        yielding, Outcome.parked, [], []⟩ := by
  unfold evaluateNative evaluatePrim
  simp only [hf]
  rfl

theorem popFrom_interrupted_no_contAll (cur : NCode) (ic : CauseV) :
    ∀ (K : List NCode), (∀ fr ∈ K, fr.hasArm .contAll = false) →
      (FrameFiber.popFrom .contE true K ⟨cur, [], true, some ic, false⟩).answer = ContAnswer.empty
  | [], _ => rfl
  | frame :: rest, hK => by
    have hall : frame.hasArm .contAll = false := hK frame List.mem_cons_self
    have hrest : ∀ fr ∈ rest, fr.hasArm .contAll = false :=
      fun fr hfr => hK fr (List.mem_cons_of_mem frame hfr)
    have he := Prim.ensure_of_no_contAll frame ⟨cur, [], true, some ic, false⟩ hall
    have hskip : (true && (frame.ensure ⟨cur, [], true, some ic, false⟩).fst.interrupted) = true := by
      rw [he]
      rfl
    have hcont := FrameFiber.popFrom_pass_no_push .contE true frame rest
      ⟨cur, [], true, some ic, false⟩ rfl (by rw [he])
    rw [he] at hcont
    rw [FrameFiber.popFrom_continue_answer .contE true frame rest _ (Or.inr hskip), hcont]
    exact popFrom_interrupted_no_contAll cur ic rest hrest

theorem evaluateNative_interrupted_failure (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (c : CauseV) (K : List NCode) (ic : CauseV)
    (hf : f.frame = ⟨Prim.failure c, K, true, some ic, false⟩)
    (hK : ∀ fr ∈ K, fr.hasArm .contAll = false) :
    ∃ ev ex, evaluateNative root m f yielding table =
      ⟨m.emit ev, { f with frame := frameExitState f.frame },
        yielding, Outcome.finished ex, [], []⟩ := by
  have hans : (FrameFiber.getCont ⟨Prim.failure c, K, true, some ic, false⟩ .contE true (some c)).answer =
      ContAnswer.empty := by
    rw [FrameFiber.getCont_answer_cause, FrameFiber.getCont_skip_clears_deferred]
    exact popFrom_interrupted_no_contAll (Prim.failure c) ic K hK
  unfold evaluateNative exitScoped evaluatePrim evaluatePrim.finalizerOr
    evaluatePrim.stepFrame FrameFiber.step FrameFiber.resumeCause evaluatePrim.finishFrame
  simp only [hf, hans]
  exact ⟨_, _, rfl⟩

theorem evaluateNative_sync_pure (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (p : Point) (K : List NCode)
    (hf : f.frame = fiberOf (Prim.sync (EffThunk.pure p)) K true) :
    evaluateNative root m f yielding table =
      ⟨m, { f with frame := fiberOf (Prim.success (syncValueAt root (EffThunk.pure p))) K true },
        yielding, Outcome.answered, [], []⟩ := by
  unfold evaluateNative evaluatePrim
  simp only [hf]
  rfl

theorem evaluateNative_ext_nonSync (root : NativeEff) (table : RowTable)
    (m : Api.Machine) (f : NRunFiber) (yielding : Bool)
    (cur : NCode) (K : List NCode)
    (hf : f.frame = fiberOf cur K true)
    (hexits : m.completedExits = [])
    (hpl : ExtPlainCode table cur = true)
    (hK : ExtPlainStack table K)
    (hns : ∀ t, cur ≠ Prim.sync t)
    (hnc : IsCall cur = false) :
    ∃ ev, evaluateNative root m f yielding table =
      match localStep root (fiberOf cur K true) m.state with
      | .running fr' _ =>
        ⟨m.emit ev, { f with frame := fr' }, yielding, Outcome.continue_, [], []⟩
      | .finished ex _ =>
        ⟨m.emit ev, { f with frame := frameExitState f.frame }, yielding, Outcome.finished ex, [], []⟩ := by
  have hplain : ContextFreeCode cur = true := ExtPlainCode.toContextFree hpl
  have hKplain : ContextFreeStack K := hK.toContextFree
  have hnotScoped : ∀ ex body previous scope flag,
      (popOf f.frame ex).answer ≠
        ContAnswer.frame (Prim.onExit body (EffName.scopedExit previous scope) flag) := by
    intro ex body previous scope flag
    rw [hf]
    exact popOf_plain_not_scoped cur K true hKplain ex body previous scope flag
  have hcur : f.frame.current = cur := by rw [hf]; rfl
  have hsf : evaluatePrim.stepFrame (interpAt root [] table) m f yielding =
      evaluatePrim.finishFrame m f yielding (f.frame.step (primOf root)).1
        (f.frame.step (primOf root)).2 [] := rfl
  have hfin : (interpAt root [] table).finalizerProgram = (interpAt root []).finalizerProgram := rfl
  have hfc : finalizerCode (interpAt root [] table) = finalizerCode (interpAt root []) := rfl
  cases cur with
  | success v =>
    have heval : evaluateNative root m f yielding table =
        evaluatePrim.finalizerOr (interpAt root [] table) m f yielding (Exit.success v) := by
      unfold evaluateNative
      rw [hcur]
      change exitScoped root m f yielding (Exit.success v) = _
      rw [exitScoped_eq_evaluatePrim root m f yielding (Exit.success v) (hnotScoped (Exit.success v)),
        hexits]
      unfold evaluatePrim
      rw [hcur]
      rfl
    rw [heval, localStep_success]
    unfold evaluatePrim.finalizerOr exitFrom popOf
    rw [hsf, hfin, hfc]
    unfold evaluatePrim.finishFrame
    simp only [hf, step_fst_success, FramePop.deliveredExit]
    generalize (fiberOf (Prim.success v) K true).getCont Effect4.Arm.contA false = pop
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
    have heval : evaluateNative root m f yielding table =
        evaluatePrim.finalizerOr (interpAt root [] table) m f yielding (Exit.failure c) := by
      unfold evaluateNative
      rw [hcur]
      change exitScoped root m f yielding (Exit.failure c) = _
      rw [exitScoped_eq_evaluatePrim root m f yielding (Exit.failure c) (hnotScoped (Exit.failure c)),
        hexits]
      unfold evaluatePrim
      rw [hcur]
      rfl
    rw [heval, localStep_failure]
    unfold evaluatePrim.finalizerOr exitFrom popOf
    rw [hsf, hfin, hfc]
    unfold evaluatePrim.finishFrame
    simp only [hf, step_fst_failure]
    rw [FrameFiber.getCont_no_pending _ _ _ (some c) rfl]
    simp only [FramePop.deliveredExit, Option.getD_some]
    generalize (fiberOf (Prim.failure c) K true).getCont Effect4.Arm.contE true = pop
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
  | yieldableError e =>
    have heval : evaluateNative root m f yielding table =
        evaluatePrim.stepFrame (interpAt root [] table) m f yielding := by
      unfold evaluateNative
      rw [hcur, hexits]
      unfold evaluatePrim
      rw [hcur]
      rfl
    rw [heval, hsf]
    unfold evaluatePrim.finishFrame
    rw [hf, localStep_other root _ K true m.state (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ h => by cases h)]
    rcases ((fiberOf _ K true).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩
  | suspend thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    next p =>
    have heval : evaluateNative root m f yielding table =
        evaluatePrim.stepFrame (interpAt root [] table) m f yielding := by
      unfold evaluateNative
      rw [hcur, hexits]
      unfold evaluatePrim
      rw [hcur]
      rfl
    rw [heval, hsf]
    unfold evaluatePrim.finishFrame
    rw [hf, localStep_other root _ K true m.state (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ h => by cases h)]
    rcases ((fiberOf _ K true).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩
  | onSuccess b n =>
    have heval : evaluateNative root m f yielding table =
        evaluatePrim.stepFrame (interpAt root [] table) m f yielding := by
      unfold evaluateNative
      rw [hcur, hexits]
      unfold evaluatePrim
      rw [hcur]
      rfl
    rw [heval, hsf]
    unfold evaluatePrim.finishFrame
    rw [hf, localStep_other root _ K true m.state (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ h => by cases h)]
    rcases ((fiberOf _ K true).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩
  | onFailure b n =>
    have heval : evaluateNative root m f yielding table =
        evaluatePrim.stepFrame (interpAt root [] table) m f yielding := by
      unfold evaluateNative
      rw [hcur, hexits]
      unfold evaluatePrim
      rw [hcur]
      rfl
    rw [heval, hsf]
    unfold evaluatePrim.finishFrame
    rw [hf, localStep_other root _ K true m.state (fun _ h => by cases h)
      (fun _ h => by cases h) (fun _ h => by cases h)]
    rcases ((fiberOf _ K true).step (primOf root)).1 with _ | _ <;> exact ⟨_, rfl⟩
  | async n w c => cases hplain.symm.trans hnc
  | _ => simp only [ExtPlainCode, Bool.false_eq_true] at hpl

/-! ## The machine invariant across arbitrary budgets and control decisions -/

private theorem localStep_success_independent {table : RowTable} (root : NativeEff)
    (v : Val) (K : List NCode) (s₁ s₂ : Stores) (hK : ExtPlainStack table K) :
    (∀ fr' s', localStep root (fiberOf (Prim.success v) K true) s₁ = .running fr' s' →
      localStep root (fiberOf (Prim.success v) K true) s₂ = .running fr' s₂ ∧ s' = s₁) ∧
    (∀ ex s', localStep root (fiberOf (Prim.success v) K true) s₁ = .finished ex s' →
      localStep root (fiberOf (Prim.success v) K true) s₂ = .finished ex s₂ ∧ s' = s₁) := by
  induction K with
  | nil =>
    have he₁ := step_exit_empty root (Exit.success v) true s₁
    have he₂ := step_exit_empty root (Exit.success v) true s₂
    simp only [Prim.ofExit] at he₁ he₂
    refine ⟨fun fr' s' h => ?_, fun ex s' h => ?_⟩
    · rw [he₁] at h
      cases h
    · rw [he₁] at h
      rw [he₂]
      cases h
      exact ⟨rfl, rfl⟩
  | cons f K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases f <;> simp only [ExtPlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · refine ⟨fun fr' s' h => ?_, fun ex s' h => ?_⟩
      · rw [step_success_onSuccess] at h ⊢
        cases h
        exact ⟨rfl, rfl⟩
      · rw [step_success_onSuccess] at h
        cases h
    · refine ⟨fun fr' s' h => ?_, fun ex s' h => ?_⟩
      · rw [step_success_pass_onFailure] at h ⊢
        exact (ih hK').1 fr' s' h
      · rw [step_success_pass_onFailure] at h ⊢
        exact (ih hK').2 ex s' h

private theorem localStep_failure_independent {table : RowTable} (root : NativeEff)
    (c : CauseV) (K : List NCode) (s₁ s₂ : Stores) (hK : ExtPlainStack table K) :
    (∀ fr' s', localStep root (fiberOf (Prim.failure c) K true) s₁ = .running fr' s' →
      localStep root (fiberOf (Prim.failure c) K true) s₂ = .running fr' s₂ ∧ s' = s₁) ∧
    (∀ ex s', localStep root (fiberOf (Prim.failure c) K true) s₁ = .finished ex s' →
      localStep root (fiberOf (Prim.failure c) K true) s₂ = .finished ex s₂ ∧ s' = s₁) := by
  induction K with
  | nil =>
    have he₁ := step_exit_empty root (Exit.failure c) true s₁
    have he₂ := step_exit_empty root (Exit.failure c) true s₂
    simp only [Prim.ofExit] at he₁ he₂
    refine ⟨fun fr' s' h => ?_, fun ex s' h => ?_⟩
    · rw [he₁] at h
      cases h
    · rw [he₁] at h
      rw [he₂]
      cases h
      exact ⟨rfl, rfl⟩
  | cons f K ih =>
    have hf := hK.head
    have hK' := hK.tail
    cases f <;> simp only [ExtPlainFrame, Bool.and_eq_true, Bool.false_eq_true] at hf
    · refine ⟨fun fr' s' h => ?_, fun ex s' h => ?_⟩
      · rw [step_failure_pass_onSuccess] at h ⊢
        exact (ih hK').1 fr' s' h
      · rw [step_failure_pass_onSuccess] at h ⊢
        exact (ih hK').2 ex s' h
    · refine ⟨fun fr' s' h => ?_, fun ex s' h => ?_⟩
      · rw [step_failure_onFailure] at h ⊢
        cases h
        exact ⟨rfl, rfl⟩
      · rw [step_failure_onFailure] at h
        cases h

/-- A running `localStep` on `ExtPlainCode` preserves the stores and agrees with `Stores.empty`.
Consumer: `driveStep_inv` on `Cmd.loop`. -/
private theorem localStep_running_stores (root : NativeEff) (table : RowTable)
    (cur : NCode) (K : List NCode) (s s' : Stores) (fr' : NFiber)
    (hpl : ExtPlainCode table cur = true) (hK : ExtPlainStack table K)
    (hstep : localStep root (fiberOf cur K true) s = .running fr' s') :
    localStep root (fiberOf cur K true) Stores.empty = .running fr' Stores.empty ∧ s' = s := by
  cases cur with
  | success v => exact (localStep_success_independent root v K s Stores.empty hK).1 fr' s' hstep
  | failure c => exact (localStep_failure_independent root c K s Stores.empty hK).1 fr' s' hstep
  | yieldableError e =>
    rw [step_yieldableError] at hstep ⊢
    cases hstep
    exact ⟨rfl, rfl⟩
  | sync thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    rw [step_sync_pure] at hstep ⊢
    cases hstep
    exact ⟨rfl, rfl⟩
  | suspend thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    rw [step_suspend] at hstep ⊢
    cases hstep
    exact ⟨rfl, rfl⟩
  | onSuccess b n =>
    rw [step_push_onSuccess] at hstep ⊢
    cases hstep
    exact ⟨rfl, rfl⟩
  | onFailure b n =>
    rw [step_push_onFailure] at hstep ⊢
    cases hstep
    exact ⟨rfl, rfl⟩
  | async n w c =>
    rw [localStep_async] at hstep ⊢
    cases hstep
    exact ⟨rfl, rfl⟩
  | _ => simp only [ExtPlainCode, Bool.false_eq_true] at hpl

/-- A finished `localStep` on `ExtPlainCode` preserves the stores and agrees with `Stores.empty`.
Consumer: `driveStep_inv` on `Cmd.loop`. -/
private theorem localStep_finished_stores (root : NativeEff) (table : RowTable)
    (cur : NCode) (K : List NCode) (s s' : Stores) (ex : ExitV)
    (hpl : ExtPlainCode table cur = true) (hK : ExtPlainStack table K)
    (hstep : localStep root (fiberOf cur K true) s = .finished ex s') :
    localStep root (fiberOf cur K true) Stores.empty = .finished ex Stores.empty ∧ s' = s := by
  cases cur with
  | success v => exact (localStep_success_independent root v K s Stores.empty hK).2 ex s' hstep
  | failure c => exact (localStep_failure_independent root c K s Stores.empty hK).2 ex s' hstep
  | yieldableError e =>
    rw [step_yieldableError] at hstep
    cases hstep
  | sync thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    rw [step_sync_pure] at hstep
    cases hstep
  | suspend thunk =>
    cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
    rw [step_suspend] at hstep
    cases hstep
  | onSuccess b n =>
    rw [step_push_onSuccess] at hstep
    cases hstep
  | onFailure b n =>
    rw [step_push_onFailure] at hstep
    cases hstep
  | async n w c =>
    rw [localStep_async] at hstep
    cases hstep
  | _ => simp only [ExtPlainCode, Bool.false_eq_true] at hpl

/-- The store invariant for an external-only straight program: no refs, no allocated handles,
no due deferred waiters, and no timer waiters. -/
private def StoreInv (s : Stores) : Prop :=
  s.refs = [] ∧
  s.externals.allocated = [] ∧
  s.deferreds.due = [] ∧
  s.timers.wake.waiters = []

private theorem StoreInv.empty : StoreInv Stores.empty :=
  ⟨rfl, rfl, rfl, rfl⟩

private theorem StoreInv.dueResumes (root : NativeEff) (table : RowTable) {s : Stores}
    (hs : StoreInv s) :
    (interpOf root table).dueResumes s = ([], s) := by
  rcases s with ⟨refs, ⟨cells, due⟩, timers, externals, scopeExits⟩
  rcases hs with ⟨_, _, hdue, _⟩
  dsimp only at hdue
  subst hdue
  rfl

private theorem StoreInv.clockStep (root : NativeEff) (table : RowTable) (millis : ClockMillis)
    {s : Stores} (hs : StoreInv s) :
    (interpOf root table).clockStep millis s =
      (none, { s with timers := { s.timers with
        now := s.timers.target.getD (s.timers.now + millis), target := none } }) := by
  have hwait : s.timers.wake.waiters = [] := hs.2.2.2
  have hdue : TimerStore.dueMin (s.timers.target.getD (s.timers.now + millis))
      s.timers.wake.waiters = none := by
    rw [hwait]
    rfl
  unfold interpOf
  dsimp only
  rw [TimerStore.clockStep_finish s.timers millis _ hdue]
  rfl

private theorem StoreInv.clockStep_none (root : NativeEff) (table : RowTable) (millis : ClockMillis)
    {s st : Stores} (hs : StoreInv s)
    (hc : (interpOf root table).clockStep millis s = (none, st)) :
    StoreInv st := by
  rw [StoreInv.clockStep root table millis hs] at hc
  cases hc
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2⟩

private theorem StoreInv.clockStep_some_false (root : NativeEff) (table : RowTable)
    (millis : ClockMillis) {s st : Stores} {owed : Owed NCode} (hs : StoreInv s)
    (hc : (interpOf root table).clockStep millis s = (some owed, st)) : False := by
  rw [StoreInv.clockStep root table millis hs] at hc
  cases hc

/-- Every task in a dispatcher is a yield resume for the root fiber with a token below `nt`. -/
private def DispInv (nt : Nat)
    (d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann NCode) : Prop :=
  ∀ b ∈ d.buckets, ∀ t ∈ b.tasks,
    ∃ tok, tok < nt ∧ t = .resume Api.root tok (Prim.success Val.unit)

/-- Every task in a drained snapshot is a yield resume for the root fiber with a token below `nt`. -/
private def TasksInv (nt : Nat)
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)) : Prop :=
  ∀ t ∈ ts, ∃ tok, tok < nt ∧ t = .resume Api.root tok (Prim.success Val.unit)

/-- A command in the queue that is either `drainDue`, `evaluate`, or a yield `resume` below `nt`. -/
private def PassiveCmd (nt : Nat)
    (c : Cmd EffName EffThunk Val Err Defect FiberId Ann NCode) : Prop :=
  c = .drainDue ∨
  (∃ id, c = .evaluate id) ∨
  (∃ id tok, tok < nt ∧ c = .resume id tok (Prim.success Val.unit))

private theorem DispInv.mono {nt nt' : Nat} (hle : nt ≤ nt')
    {d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann NCode} (hd : DispInv nt d) :
    DispInv nt' d := by
  intro b hb t ht
  obtain ⟨tok, hlt, heq⟩ := hd b hb t ht
  exact ⟨tok, Nat.lt_of_lt_of_le hlt hle, heq⟩

private theorem TasksInv.mono {nt nt' : Nat} (hle : nt ≤ nt')
    {ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)}
    (hts : TasksInv nt ts) : TasksInv nt' ts := by
  intro t ht
  obtain ⟨tok, hlt, heq⟩ := hts t ht
  exact ⟨tok, Nat.lt_of_lt_of_le hlt hle, heq⟩

private theorem PassiveCmd.mono {nt nt' : Nat} (hle : nt ≤ nt')
    {c : Cmd EffName EffThunk Val Err Defect FiberId Ann NCode} (hc : PassiveCmd nt c) :
    PassiveCmd nt' c := by
  rcases hc with rfl | ⟨id, rfl⟩ | ⟨id, tok, hlt, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨id, rfl⟩)
  · exact Or.inr (Or.inr ⟨id, tok, Nat.lt_of_lt_of_le hlt hle, rfl⟩)

private theorem insert_inv {nt : Nat} (p : Nat)
    (task : Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)
    (htask : ∃ tok, tok < nt ∧ task = .resume Api.root tok (Prim.success Val.unit))
    (bs : List (Bucket EffName EffThunk Val Err Defect FiberId Ann NCode))
    (hbs : ∀ b ∈ bs, ∀ t ∈ b.tasks,
      ∃ tok, tok < nt ∧ t = .resume Api.root tok (Prim.success Val.unit)) :
    ∀ b ∈ Dispatcher.insert p task bs, ∀ t ∈ b.tasks,
      ∃ tok, tok < nt ∧ t = .resume Api.root tok (Prim.success Val.unit) := by
  induction bs with
  | nil =>
    intro b hb t ht
    simp only [Dispatcher.insert, List.mem_singleton] at hb
    subst hb
    simp only [List.mem_singleton] at ht
    subst ht
    exact htask
  | cons hd tl ih =>
    intro b hb t ht
    unfold Dispatcher.insert at hb
    split at hb
    · simp only [List.mem_cons] at hb
      rcases hb with rfl | hb
      · rw [List.mem_append] at ht
        rcases ht with ht | ht
        · exact hbs hd (List.mem_cons_self ..) t ht
        · simp only [List.mem_singleton] at ht
          subst ht
          exact htask
      · exact hbs b (List.mem_cons_of_mem hd hb) t ht
    · split at hb
      · simp only [List.mem_cons] at hb
        rcases hb with rfl | rfl | hb
        · simp only [List.mem_singleton] at ht
          subst ht
          exact htask
        · exact hbs b (List.mem_cons_self ..) t ht
        · exact hbs b (List.mem_cons_of_mem hd hb) t ht
      · simp only [List.mem_cons] at hb
        rcases hb with rfl | hb
        · exact hbs b (List.mem_cons_self ..) t ht
        · exact ih (fun b' hb' => hbs b' (List.mem_cons_of_mem hd hb')) b hb t ht

private theorem DispInv.enqueue {nt : Nat} (p : Nat) (tok : Nat) (htok : tok < nt)
    {d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann NCode} (hd : DispInv nt d) :
    DispInv nt (d.enqueue p (.resume Api.root tok (Prim.success Val.unit))) :=
  insert_inv p _ ⟨tok, htok, rfl⟩ d.buckets hd

private theorem DispInv.drain {nt : Nat}
    {d : Dispatcher EffName EffThunk Val Err Defect FiberId Ann NCode} (hd : DispInv nt d) :
    TasksInv nt d.drain.1 ∧ DispInv nt d.drain.2 := by
  refine ⟨?_, ?_⟩
  · intro t ht
    unfold Dispatcher.drain at ht
    dsimp only at ht
    rw [List.mem_flatten] at ht
    obtain ⟨ts, hts, ht⟩ := ht
    rw [List.mem_map] at hts
    obtain ⟨b, hb, rfl⟩ := hts
    exact hd b hb t ht
  · intro b hb
    unfold Dispatcher.drain at hb
    cases hb

/-- Every exit on the reply tape was submitted in the session journal. -/
private def TapeSubmitted (journal : List Command) (tape : ReplyTape) : Prop :=
  ∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ journal ∧ reply.completion = .ofExit ex

/-- The structural fields of the single root fiber. -/
private def FiberBase (nt : Nat) (f : NRunFiber) : Prop :=
  f.id = Api.root ∧
  f.children = [] ∧
  f.observers = [] ∧
  f.finalizing = none ∧
  DispInv nt f.dispatcher

/-- The three sub-states of an active (un-interrupted, un-exited) root fiber. -/
private inductive ActiveSub (nt : Nat) (cur : NCode) (K : List NCode) (f : NRunFiber) : Prop
  | unparked (hp : f.parked = .notParked)
      (hys : YieldStack cur K f.frame.current f.frame.stack)
  | parkedYield (tok : Nat) (htok : tok < nt) (hp : f.parked = .withGuard tok)
      (hrun : f.running = false) (hcur : f.frame.current = Prim.success Val.unit)
      (hys : YieldStack cur K f.frame.current f.frame.stack)
  | parkedCall (tok : Nat) (htok : tok < nt) (hp : f.parked = .withGuard tok)
      (hrun : f.running = false) (hcall : IsCall cur = true)
      (hcur : f.frame.current = cur) (hstk : f.frame.stack = K)
      (hdisp : DispInv tok f.dispatcher)

/-- The three modes of the root fiber across arbitrary machine execution. -/
private inductive FiberMode (root : NativeEff) (table : RowTable) (cf : Nat)
    (journal : List Command) (nt : Nat) (f : NRunFiber) : Prop
  | active (cur : NCode) (K : List NCode) (tape : ReplyTape)
      (hexit : f.exit = none)
      (hintr : f.frame.interruptible = true)
      (hic : f.frame.interruptedCause = none)
      (hdef : f.frame.deferredInterrupt = false)
      (hpl : ExtPlainCode table cur = true)
      (hK : ExtPlainStack table K)
      (htape : TapeSubmitted journal tape)
      (hleads : LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
        tape (fiberOf cur K true) Stores.empty)
      (hsub : ActiveSub nt cur K f)
  | interrupted (ic c : CauseV) (K₀ : List NCode)
      (hexit : f.exit = none)
      (hintr : f.frame.interruptible = true)
      (hic : f.frame.interruptedCause = some ic)
      (hdef : f.frame.deferredInterrupt = false)
      (hK₀ : ∀ fr ∈ K₀, fr.hasArm .contAll = false)
      (hys : YieldStack (Prim.failure c) K₀ f.frame.current f.frame.stack)
      (hpark : ∀ tok, f.parked = .withGuard tok →
        tok < nt ∧ f.running = false ∧ f.frame.current = Prim.success Val.unit)
  | halted (hp : f.parked = .notParked) (hdone : f.exit.isSome = true ∨ f.running = true)

private theorem ActiveSub.mono {nt nt' : Nat} (hle : nt ≤ nt') {cur : NCode} {K : List NCode}
    {f : NRunFiber} (hs : ActiveSub nt cur K f) : ActiveSub nt' cur K f := by
  rcases hs with ⟨hp, hys⟩ | ⟨tok, htok, hp, hrun, hcur, hys⟩ |
    ⟨tok, htok, hp, hrun, hcall, hcur, hstk, hdisp⟩
  · exact .unparked hp hys
  · exact .parkedYield tok (Nat.lt_of_lt_of_le htok hle) hp hrun hcur hys
  · exact .parkedCall tok (Nat.lt_of_lt_of_le htok hle) hp hrun hcall hcur hstk hdisp

private theorem FiberMode.mono {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} {nt nt' : Nat} (hle : nt ≤ nt') {f : NRunFiber}
    (hm : FiberMode root table cf journal nt f) :
    FiberMode root table cf journal nt' f := by
  rcases hm with ⟨cur, K, tape, hexit, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
    ⟨ic, c, K₀, hexit, hintr, hic, hdef, hK₀, hys, hpark⟩ | ⟨hp, hdone⟩
  · exact .active cur K tape hexit hintr hic hdef hpl hK htape hleads (hsub.mono hle)
  · exact .interrupted ic c K₀ hexit hintr hic hdef hK₀ hys (fun tok hp => by
      obtain ⟨htok, hrun, hcur⟩ := hpark tok hp
      exact ⟨Nat.lt_of_lt_of_le htok hle, hrun, hcur⟩)
  · exact .halted hp hdone

private theorem FiberMode.mono_journal {root : NativeEff} {table : RowTable} {cf : Nat}
    {j₁ j₂ : List Command} (hj : ∀ c ∈ j₁, c ∈ j₂) {nt : Nat} {f : NRunFiber}
    (hm : FiberMode root table cf j₁ nt f) :
    FiberMode root table cf j₂ nt f := by
  rcases hm with ⟨cur, K, tape, hexit, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
    ⟨ic, c, K₀, hexit, hintr, hic, hdef, hK₀, hys, hpark⟩ | ⟨hp, hdone⟩
  · refine .active cur K tape hexit hintr hic hdef hpl hK (fun ex hex => ?_) hleads hsub
    obtain ⟨reply, hmem, hcomp⟩ := htape ex hex
    exact ⟨reply, hj _ hmem, hcomp⟩
  · exact .interrupted ic c K₀ hexit hintr hic hdef hK₀ hys hpark
  · exact .halted hp hdone

/-- The machine invariant for an external-only straight program without cause handlers. -/
private structure MachineInv (root : NativeEff) (table : RowTable) (cf : Nat)
    (journal : List Command) (m : NativeMachine) : Prop where
  notStuck : m.stuck = none
  noRaces : m.races = []
  store : StoreInv m.state
  fiber : ∃ f, m.fibers = [f] ∧ FiberBase m.nextToken f ∧
    FiberMode root table cf journal m.nextToken f

private theorem MachineInv.mono_journal {root : NativeEff} {table : RowTable} {cf : Nat}
    {j₁ j₂ : List Command} (hj : ∀ c ∈ j₁, c ∈ j₂) {m : NativeMachine}
    (hm : MachineInv root table cf j₁ m) : MachineInv root table cf j₂ m := by
  obtain ⟨hs, hr, hst, f, hf, hbase, hmode⟩ := hm
  exact ⟨hs, hr, hst, f, hf, hbase, hmode.mono_journal hj⟩

/-- When the root fiber is parked at an external call on token `tok`, `P tok` holds. -/
private def CallParkBound (m : NativeMachine) (P : Nat → Prop) : Prop :=
  ∀ f, m.fibers = [f] → ∀ tok, f.parked = .withGuard tok → IsCall f.frame.current = true → P tok

/-- The snapshot invariant for drained dispatcher tasks. -/
private def SnapshotInv (m : NativeMachine)
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)) : Prop :=
  TasksInv m.nextToken ts ∧ CallParkBound m (fun tok => TasksInv tok ts)

/-- The active or interrupted state of a running root fiber during `Cmd.loop`. -/
private def LoopActiveOrInterrupted (root : NativeEff) (table : RowTable) (cf : Nat)
    (journal : List Command) (f : NRunFiber) : Prop :=
  (∃ cur K tape,
    f.frame.interruptedCause = none ∧
    ExtPlainCode table cur = true ∧ ExtPlainStack table K ∧
    TapeSubmitted journal tape ∧
    LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
      tape (fiberOf cur K true) Stores.empty ∧
    YieldStack cur K f.frame.current f.frame.stack) ∨
  (∃ ic c K₀,
    f.frame.interruptedCause = some ic ∧
    (∀ fr ∈ K₀, fr.hasArm .contAll = false) ∧
    YieldStack (Prim.failure c) K₀ f.frame.current f.frame.stack)

private theorem LoopActiveOrInterrupted.toFiberMode {root : NativeEff} {table : RowTable}
    {cf : Nat} {journal : List Command} {f : NRunFiber} (nt : Nat)
    (hexit : f.exit = none) (hintr : f.frame.interruptible = true)
    (hdef : f.frame.deferredInterrupt = false) (hp : f.parked = .notParked)
    (hl : LoopActiveOrInterrupted root table cf journal f) :
    FiberMode root table cf journal nt f := by
  rcases hl with ⟨cur, K, tape, hic, hpl, hK, htape, hleads, hys⟩ | ⟨ic, c, K₀, hic, hK₀, hys⟩
  · exact .active cur K tape hexit hintr hic hdef hpl hK htape hleads (.unparked hp hys)
  · exact .interrupted ic c K₀ hexit hintr hic hdef hK₀ hys (fun tok h => by rw [hp] at h; cases h)

private theorem FiberMode.toLoopActiveOrInterrupted {root : NativeEff} {table : RowTable}
    {cf : Nat} {journal : List Command} {nt : Nat} {f : NRunFiber}
    (hm : FiberMode root table cf journal nt f)
    (hexit : f.exit = none) (hrun : f.running = false) (hp : f.parked = .notParked) :
    f.frame.interruptible = true ∧ f.frame.deferredInterrupt = false ∧
      LoopActiveOrInterrupted root table cf journal f := by
  rcases hm with ⟨cur, K, tape, _, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
    ⟨ic, c, K₀, _, hintr, hic, hdef, hK₀, hys, _⟩ | ⟨_, hdone⟩
  · rcases hsub with ⟨_, hys⟩ | ⟨_, _, hp', _, _, _⟩ | ⟨_, _, hp', _, _, _, _, _⟩
    · exact ⟨hintr, hdef, Or.inl ⟨cur, K, tape, hic, hpl, hK, htape, hleads, hys⟩⟩
    · rw [hp] at hp'; cases hp'
    · rw [hp] at hp'; cases hp'
  · exact ⟨hintr, hdef, Or.inr ⟨ic, c, K₀, hic, hK₀, hys⟩⟩
  · rcases hdone with h | h
    · rw [hexit] at h; cases h
    · rw [hrun] at h; cases h

/-- The command-queue invariant during `driveState`. -/
private inductive CmdQueueInv (root : NativeEff) (table : RowTable) (cf : Nat)
    (journal : List Command) (m : NativeMachine) :
    List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode) → Prop
  | passive (cmds : List _)
      (hpass : ∀ c ∈ cmds, PassiveCmd m.nextToken c)
      (hcall : CallParkBound m (fun tok => ∀ c ∈ cmds, PassiveCmd tok c)) :
      CmdQueueInv root table cf journal m cmds
  | loop (yielding : Bool) (rest : List _)
      (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
      (hrun : ∀ f, m.fibers = [f] →
        f.exit = none ∧ f.running = true ∧ f.parked = .notParked ∧
        f.frame.interruptible = true ∧ f.frame.deferredInterrupt = false ∧
        LoopActiveOrInterrupted root table cf journal f) :
      CmdQueueInv root table cf journal m (Cmd.loop Api.root yielding :: rest)
  | deliver (yielding : Bool) (rest : List _)
      (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
      (hdel : ∀ f, m.fibers = [f] → ∃ K tape v,
        f.exit = none ∧ f.running = true ∧ f.parked = .notParked ∧
        f.frame = fiberOf (Prim.success v) K true ∧
        ExtPlainStack table K ∧ TapeSubmitted journal tape ∧
        LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
          tape (fiberOf (Prim.success v) K true) Stores.empty) :
      CmdQueueInv root table cf journal m (Cmd.deliver Api.root yielding :: rest)
  | finish (ex : ExitV) (rest : List _)
      (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
      (hfin : ∀ f, m.fibers = [f] →
        f.parked = .notParked ∧ (f.exit.isSome = true ∨ f.running = true)) :
      CmdQueueInv root table cf journal m (Cmd.finish Api.root ex :: rest)

/-- The decision admission predicate for `DecisionLift`. -/
private def CallTreeDecision (table : RowTable) (journal : List Command) (m : NativeMachine) :
    NativeDecision → Prop
  | .answerAsync f t a =>
    ∃ (ex : ExitV) (reply : Api.HostSession.Reply) (i : Nat) (v : Val) (row : Program.Row),
      a = .ofExit ex ∧
      Command.submit reply ∈ journal ∧
      reply.completion = .ofExit ex ∧
      Program.requestOf m f t = some (.external i, v) ∧
      externalRow table i = some row ∧
      externalAdmits table i (.ofExit ex) [] = true
  | _ => True

/-- Answering an external call on `admittedTapeHost` with an admitted exit at the head of a tape
returns that exit and the tail of the tape. -/
private theorem admittedTapeHost_cons (table : RowTable) (i : Nat) (v : Val) (w : List Nat)
    (ex : ExitV) (rest : ReplyTape) (hi : i < table.length)
    (hadm : externalAdmits table i (.ofExit ex) [] = true) :
    hostAnswer (admittedTapeHost table)
      (Prim.async (.external (.external i) v w) false none) (ex :: rest) =
      some (ex, rest) := by
  unfold hostAnswer
  show (if _ : i < table.length then
      (if externalAdmits table i (.ofExit ex) [] then some (ex, rest) else none)
    else none) = some (ex, rest)
  rw [dif_pos hi, if_pos hadm]

/-- A machine satisfying `MachineInv` that has a live `requestOf` is in `FiberMode.active` and
`ActiveSub.parkedCall` on the root fiber.
Consumer: `request_leads` and the `answer` field of `DecisionLift`. -/
private theorem frame_eta {fr : NFiber} {c : NCode} {S : List NCode} {ic? : Option CauseV}
    (hc : fr.current = c) (hs : fr.stack = S) (hi : fr.interruptible = true)
    (hic : fr.interruptedCause = ic?) (hd : fr.deferredInterrupt = false) :
    fr = ⟨c, S, true, ic?, false⟩ := by
  rcases fr with ⟨c₀, s₀, i₀, ic₀, d₀⟩
  dsimp only at hc hs hi hic hd
  subst hc hs hi hic hd
  rfl

private theorem requestOf_active_parkedCall {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} {m : NativeMachine}
    (hm : MachineInv root table cf journal m)
    {fid : FiberId} {tok : Nat} {op : NativeOp} {req : Val}
    (hreq : Program.requestOf m fid tok = some (op, req)) :
    ∃ (f : NRunFiber) (cur : NCode) (K : List NCode) (tape : ReplyTape)
      (i : Nat) (w : List Nat) (row : Program.Row),
      m.fibers = [f] ∧ fid = Api.root ∧
      FiberBase m.nextToken f ∧
      f.exit = none ∧ f.running = false ∧ f.parked = .withGuard tok ∧ tok < m.nextToken ∧
      f.frame = fiberOf cur K true ∧
      cur = Prim.async (.external (.external i) req w) false none ∧
      op = .external i ∧ dataRow table i = true ∧ externalRow table i = some row ∧
      IsCall cur = true ∧ callOf cur = some (i, req) ∧
      ExtPlainCode table cur = true ∧ ExtPlainStack table K ∧
      TapeSubmitted journal tape ∧
      LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
        tape (fiberOf cur K true) Stores.empty ∧
      DispInv tok f.dispatcher := by
  have hne : Program.requestOf m fid tok ≠ none := by
    rw [hreq]
    exact Option.some_ne_none _
  obtain ⟨g, hfg, hpg, _⟩ := requestOf_parked hne
  obtain ⟨g', hfg', w, c, d, hcurg⟩ := requestOf_current hreq
  rw [hfg] at hfg'
  cases hfg'
  obtain ⟨f, hmf, hbase, hmode⟩ := hm.fiber
  obtain ⟨heq, hfid⟩ := fiber?_one hmf hfg
  subst heq
  have hfid' : fid = Api.root := hfid.symm.trans hbase.1
  rcases hmode with ⟨cur, K, tape, hexit, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
    ⟨ic, c', K₀, hexit, hintr, hic, hdef, hK₀, hys, hpark⟩ | ⟨hp, hdone⟩
  · rcases hsub with ⟨hp, _⟩ | ⟨tok', _, hp, _, hcur, _⟩ |
      ⟨tok', htok, hp, hrun, hcall, hcur, hstk, hdisp⟩
    · rw [hp] at hpg
      cases hpg
    · rw [hcur] at hcurg
      cases hcurg
    · rw [hp] at hpg
      cases hpg
      rw [hcur] at hcurg
      have hext := ExtPlainCode.extCall_of_isCall hpl hcall
      subst hcurg
      cases op with
      | external i =>
        cases c with
        | true => simp only [ExtCall, Bool.false_eq_true] at hext
        | false =>
          cases d with
          | some _ => simp only [ExtCall, Bool.false_eq_true] at hext
          | none =>
            simp only [ExtCall] at hext
            have hrow_some : ∃ row, externalRow table i = some row := by
              unfold dataRow at hext
              rcases hr : externalRow table i with _ | row
              · rw [hr] at hext
                cases hext
              · exact ⟨row, rfl⟩
            obtain ⟨row, hrow⟩ := hrow_some
            exact ⟨g, _, K, tape, i, w, row, hmf, hfid', hbase, hexit, hrun, hp, htok,
              frame_eta hcur hstk hintr hic hdef, rfl, rfl, hext, hrow, hcall, rfl,
              hpl, hK, htape, hleads, hdisp⟩
      | _ => simp only [ExtCall, Bool.false_eq_true] at hext
  · obtain ⟨_, _, hcur⟩ := hpark tok hpg
    rw [hcur] at hcurg
    cases hcurg
  · rw [hp] at hpg
    cases hpg

private theorem update_one {m : NativeMachine} {f f' : NRunFiber}
    (hm : m.fibers = [f]) (hid : f'.id = f.id) :
    (m.update f').fibers = [f'] := by
  unfold RunMachine.update
  rw [hm, List.map_cons, List.map_nil, hid, if_pos rfl]

private theorem CallParkBound.of_notParked {m : NativeMachine} {f : NRunFiber}
    (hm : m.fibers = [f]) (hp : f.parked = .notParked) {P : Nat → Prop} :
    CallParkBound m P := by
  intro g hg tok hpg _
  rw [hm] at hg
  cases hg
  rw [hp] at hpg
  cases hpg

private theorem CallParkBound.of_not_isCall {m : NativeMachine} {f : NRunFiber}
    (hm : m.fibers = [f]) (hc : IsCall f.frame.current = false) {P : Nat → Prop} :
    CallParkBound m P := by
  intro g hg _ _ hcg
  rw [hm] at hg
  cases hg
  rw [hc] at hcg
  cases hcg

private theorem MachineInv.dispInv_of_callPark {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} {m : NativeMachine} (hm : MachineInv root table cf journal m) :
    CallParkBound m (fun tok => ∀ f, m.fibers = [f] → DispInv tok f.dispatcher) := by
  intro g hg tok hpg hcg f' hf'
  rw [hg] at hf'
  cases hf'
  obtain ⟨f, hmf, _, hmode⟩ := hm.fiber
  rw [hg] at hmf
  cases hmf
  rcases hmode with ⟨cur, K, tape, _, _, _, _, _, _, _, _, hsub⟩ |
    ⟨_, _, _, _, _, _, _, _, _, hpark⟩ | ⟨hp, _⟩
  · rcases hsub with ⟨hp, _⟩ | ⟨_, _, _, _, hcur, _⟩ |
      ⟨tok', _, hp, _, _, _, _, hdisp⟩
    · rw [hp] at hpg; cases hpg
    · rw [hcur] at hcg; cases hcg
    · rw [hp] at hpg; cases hpg; exact hdisp
  · obtain ⟨_, _, hcur⟩ := hpark tok hpg
    rw [hcur] at hcg; cases hcg
  · rw [hp] at hpg; cases hpg

private theorem lift_nil (_w : Unit) (m : NativeMachine) : SnapshotInv m [] :=
  ⟨fun _ h => (by cases h), fun _ _ _ _ _ _ h => (by cases h)⟩

private theorem lift_evaluate {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (id : FiberId) :
    CmdQueueInv root table cf journal m [Cmd.evaluate id, Cmd.drainDue] := by
  refine .passive _ (fun c hc => ?_) (fun _ _ _ _ _ c hc => ?_)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl ⟨id, rfl⟩)
    · exact Or.inl rfl
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inl ⟨id, rfl⟩)
    · exact Or.inl rfl

private theorem lift_drain {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (owner : FiberId) (f : NRunFiber)
    (hj : MachineInv root table cf journal m) (hf : m.fiber? owner = some f) :
    MachineInv root table cf journal
        ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner) ∧
      SnapshotInv ((m.update { f with dispatcher := (f.dispatcher.drain).2 }).disarm owner)
        (f.dispatcher.drain).1 := by
  obtain ⟨g, hmg, hbase, hmode⟩ := hj.fiber
  obtain ⟨rfl, _⟩ := fiber?_one hmg hf
  have hdrain := DispInv.drain hbase.2.2.2.2
  have hup := update_one (f' := { f with dispatcher := (f.dispatcher.drain).2 }) hmg rfl
  have hmode' : FiberMode root table cf journal m.nextToken
      { f with dispatcher := (f.dispatcher.drain).2 } := by
    rcases hmode with ⟨cur, K, tape, hexit, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
      ⟨ic, c, K₀, hexit, hintr, hic, hdef, hK₀, hys, hpark⟩ | ⟨hp, hdone⟩
    · refine .active cur K tape hexit hintr hic hdef hpl hK htape hleads ?_
      rcases hsub with ⟨hp, hys⟩ | ⟨tok, htok, hp, hrun, hcur, hys⟩ |
        ⟨tok, htok, hp, hrun, hcall, hcur, hstk, hdisp⟩
      · exact .unparked hp hys
      · exact .parkedYield tok htok hp hrun hcur hys
      · exact .parkedCall tok htok hp hrun hcall hcur hstk (DispInv.drain hdisp).2
    · exact .interrupted ic c K₀ hexit hintr hic hdef hK₀ hys hpark
    · exact .halted hp hdone
  refine ⟨⟨hj.notStuck, hj.noRaces, hj.store,
      { f with dispatcher := (f.dispatcher.drain).2 }, hup,
      ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hdrain.2⟩, hmode'⟩,
    ⟨hdrain.1, ?_⟩⟩
  intro g' hg' tok hpg' hcg'
  change (m.update { f with dispatcher := (f.dispatcher.drain).2 }).fibers = [g'] at hg'
  rw [hup] at hg'
  cases hg'
  have hdisp_tok := hj.dispInv_of_callPark f hmg tok hpg' hcg' f hmg
  exact (DispInv.drain hdisp_tok).1

private theorem lift_ran {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (owner : FiberId)
    (t : Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)
    (hj : MachineInv root table cf journal m) :
    MachineInv root table cf journal (m.emit [RunEvent.ranTask owner t]) :=
  ⟨hj.notStuck, hj.noRaces, hj.store, hj.fiber⟩

private theorem lift_task {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (owner : FiberId)
    (t : Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ho : SnapshotInv m (t :: ts)) :
    CmdQueueInv root table cf journal (m.emit [RunEvent.ranTask owner t]) (taskCmds t) ∧
      SnapshotInv (m.emit [RunEvent.ranTask owner t]) ts := by
  obtain ⟨hts, hcall⟩ := ho
  obtain ⟨tok₀, hlt₀, heq₀⟩ := hts t (List.mem_cons_self ..)
  refine ⟨.passive _ (fun c hc => ?_) (fun f hf tok hp hcur c hc => ?_),
    ⟨fun t' ht' => hts t' (List.mem_cons_of_mem t ht'),
      fun f hf tok hp hcur t' ht' => hcall f hf tok hp hcur t' (List.mem_cons_of_mem t ht')⟩⟩
  · subst heq₀
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inr ⟨Api.root, tok₀, hlt₀, rfl⟩)
    · exact Or.inl rfl
  · obtain ⟨tok₁, hlt₁, heq₁⟩ := hcall f hf tok hp hcur t (List.mem_cons_self ..)
    subst heq₁
    simp only [taskCmds, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact Or.inr (Or.inr ⟨Api.root, tok₁, hlt₁, rfl⟩)
    · exact Or.inl rfl

private theorem lift_skip (_w : Unit) (m : NativeMachine)
    (t : Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode)
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ho : SnapshotInv m (t :: ts)) :
    SnapshotInv m ts :=
  ⟨fun t' ht' => ho.1 t' (List.mem_cons_of_mem t ht'),
    fun f hf tok hp hcur t' ht' => ho.2 f hf tok hp hcur t' (List.mem_cons_of_mem t ht')⟩

private theorem lift_yield {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (id : FiberId) (v : Bool)
    (hj : MachineInv root table cf journal m) :
    MachineInv root table cf journal (m.modify id fun f => { f with yieldOverride := some v }) := by
  unfold RunMachine.modify
  cases hf : m.fiber? id with
  | none => exact hj
  | some g =>
    obtain ⟨f, hmf, hbase, hmode⟩ := hj.fiber
    obtain ⟨rfl, _⟩ := fiber?_one hmf hf
    have hup := update_one (f' := { g with yieldOverride := some v }) hmf rfl
    refine ⟨hj.notStuck, hj.noRaces, hj.store, { g with yieldOverride := some v }, hup, hbase, ?_⟩
    rcases hmode with ⟨cur, K, tape, hexit, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
      ⟨ic, c, K₀, hexit, hintr, hic, hdef, hK₀, hys, hpark⟩ | ⟨hp, hdone⟩
    · refine .active cur K tape hexit hintr hic hdef hpl hK htape hleads ?_
      rcases hsub with ⟨hp, hys⟩ | ⟨tok, htok, hp, hrun, hcur, hys⟩ |
        ⟨tok, htok, hp, hrun, hcall, hcur, hstk, hdisp⟩
      · exact .unparked hp hys
      · exact .parkedYield tok htok hp hrun hcur hys
      · exact .parkedCall tok htok hp hrun hcall hcur hstk hdisp
    · exact .interrupted ic c K₀ hexit hintr hic hdef hK₀ hys hpark
    · exact .halted hp hdone

private theorem FiberMode.not_contAll_of_unhalted {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} {nt : Nat} {f : NRunFiber}
    (hm : FiberMode root table cf journal nt f)
    (hexit : f.exit = none) (hrun : f.running = false) :
    f.frame.interruptible = true ∧ f.frame.deferredInterrupt = false ∧
      (∀ fr ∈ f.frame.stack, fr.hasArm .contAll = false) := by
  rcases hm with ⟨cur, K, tape, _, hintr, _, hdef, _, hK, _, _, hsub⟩ |
    ⟨_, _, K₀, _, hintr, _, hdef, hK₀, hys, _⟩ | ⟨_, hdone⟩
  · refine ⟨hintr, hdef, ?_⟩
    rcases hsub with ⟨_, hys⟩ | ⟨_, _, _, _, _, hys⟩ | ⟨_, _, _, _, _, _, hstk, _⟩
    · exact YieldStack.not_contAll hys (fun fr hfr => ExtPlainFrame.not_contAll (hK fr hfr))
    · exact YieldStack.not_contAll hys (fun fr hfr => ExtPlainFrame.not_contAll (hK fr hfr))
    · rw [hstk]; exact fun fr hfr => ExtPlainFrame.not_contAll (hK fr hfr)
  · exact ⟨hintr, hdef, YieldStack.not_contAll hys hK₀⟩
  · rcases hdone with h | h
    · rw [hexit] at h; cases h
    · rw [hrun] at h; cases h

private theorem FiberMode.notParked_of_running {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} {nt : Nat} {f : NRunFiber}
    (hm : FiberMode root table cf journal nt f) (hrun : f.running = true) :
    f.parked = .notParked := by
  rcases hm with ⟨_, _, _, _, _, _, _, _, _, _, _, hsub⟩ | ⟨_, _, _, _, _, _, _, _, _, hpark⟩ | ⟨hp, _⟩
  · rcases hsub with ⟨hp, _⟩ | ⟨_, _, _, hr, _, _⟩ | ⟨_, _, _, hr, _, _, _, _⟩
    · exact hp
    · rw [hrun] at hr; cases hr
    · rw [hrun] at hr; cases hr
  · cases hp : f.parked with
    | notParked => rfl
    | withGuard tok =>
      obtain ⟨_, hr, _⟩ := hpark tok hp
      rw [hrun] at hr; cases hr
  · exact hp

private theorem FiberMode.notParked_of_exit {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} {nt : Nat} {f : NRunFiber}
    (hm : FiberMode root table cf journal nt f) (hex : f.exit.isSome = true) :
    f.parked = .notParked := by
  rcases hm with ⟨_, _, _, hexit, _, _, _, _, _, _, _, _⟩ |
    ⟨_, _, _, hexit, _, _, _, _, _, _⟩ | ⟨hp, _⟩
  · rw [hexit] at hex; cases hex
  · rw [hexit] at hex; cases hex
  · exact hp

private theorem lift_interrupt {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (target : FiberId) (t : NRunFiber)
    (hj : MachineInv root table cf journal m) (ht : m.fiber? target = some t) :
    MachineInv root table cf journal (Lift.interruptEdit (interpOf root table) m who extra target t) := by
  obtain ⟨f, hmf, hbase, hmode⟩ := hj.fiber
  obtain ⟨rfl, _⟩ := fiber?_one hmf ht
  let r := interruptRecord (interpOf root table) who extra t
  have hform := Sched.interruptRecord_frame_eq (interpOf root table) who extra t
  have hhid : r.1.id = t.id := by
    unfold r
    rw [hform]
    split
    · rfl
    · split
      · split <;> rfl
      · rfl
  have hbase' : FiberBase m.nextToken r.1 := by
    unfold r
    rw [hform]
    split
    · exact hbase
    · split
      · split <;> exact hbase
      · exact hbase
  have hmode' : FiberMode root table cf journal m.nextToken r.1 := by
    unfold r
    rw [hform]
    by_cases hex : t.exit.isSome = true
    · rw [if_pos hex]
      exact hmode
    · rw [if_neg hex]
      have hexit_none : t.exit = none := Option.not_isSome_iff_eq_none.mp hex
      by_cases hrun : t.running = true
      · have hp := hmode.notParked_of_running hrun
        split <;> exact .halted hp (Or.inr hrun)
      · have hrun_false : t.running = false := Bool.eq_false_iff.mpr hrun
        obtain ⟨hintr, hdef, hK₀⟩ := hmode.not_contAll_of_unhalted hexit_none hrun_false
        rw [if_pos hintr, if_neg hrun]
        exact .interrupted _ _ t.frame.stack hexit_none hintr rfl hdef hK₀ .plain
          (fun tok h => by cases h)
  unfold Lift.interruptEdit
  dsimp only
  split
  · exact ⟨hj.notStuck, hj.noRaces, hj.store, r.1, update_one hmf hhid, hbase', hmode'⟩
  · exact ⟨hj.notStuck, hj.noRaces, hj.store, r.1, update_one hmf hhid, hbase', hmode'⟩

private theorem lift_middleware {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine)
    (hj : MachineInv root table cf journal m) :
    MachineInv root table cf journal { m with middlewareInstalled := true } :=
  ⟨hj.notStuck, hj.noRaces, hj.store, hj.fiber⟩

private theorem lift_clockNone {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (millis : ClockMillis) (st : Stores)
    (hj : MachineInv root table cf journal m)
    (hc : (interpOf root table).clockStep millis m.state = (none, st)) :
    ∃ w', Lift.unitOrder.le _w w' ∧ MachineInv root table cf journal { m with state := st } :=
  ⟨(), trivial, ⟨hj.notStuck, hj.noRaces, StoreInv.clockStep_none root table millis hj.store hc,
    hj.fiber⟩⟩

private theorem lift_clockSome {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (millis : ClockMillis)
    (owed : Owed NCode) (st : Stores)
    (hj : MachineInv root table cf journal m)
    (hc : (interpOf root table).clockStep millis m.state = (some owed, st)) :
    ∃ w', Lift.unitOrder.le _w w' ∧
      MachineInv root table cf journal (drainOwed { m with state := st } [owed]).1 ∧
      ((drainOwed { m with state := st } [owed]).1.stuck = none →
        CmdQueueInv root table cf journal (drainOwed { m with state := st } [owed]).1
          ((drainOwed { m with state := st } [owed]).2 ++ [Cmd.drainDue])) :=
  (StoreInv.clockStep_some_false root table millis hj.store hc).elim

private theorem lift_answer {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (_w : Unit) (m : NativeMachine) (id : FiberId) (token : Nat)
    (answer : Completion Val Err Defect FiberId Ann)
    (hj : MachineInv root table cf journal m)
    (ha : CallTreeDecision table journal m (.answerAsync id token answer)) :
    ∃ w', Lift.unitOrder.le _w w' ∧
      Lift.Guarded (fun _ => MachineInv root table cf journal)
        (fun _ => CmdQueueInv root table cf journal)
        (fun _ => SnapshotInv) [] w'
        (driveStep (interpOf root table)
          { m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1 }
          (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2)
          [Cmd.drainDue]).1
        (driveStep (interpOf root table)
          { m with state := (prepareAsyncAnswer (interpOf root table) m id token answer).1 }
          (.resume id token (prepareAsyncAnswer (interpOf root table) m id token answer).2)
          [Cmd.drainDue]).2 := by
  obtain ⟨ex, reply, i, v, row, rfl, hsub_mem, hsub_comp, hreq, hrow, hadm⟩ := ha
  obtain ⟨f, cur, K, tape, i', w', row', hmf, rfl, hbase, hexit, _hrun, hp, _htok,
    hf_frame, hcur_eq, hop_eq, hdrow, _, hcall, _, _hpl, hK, htape, hleads, _⟩ :=
    requestOf_active_parkedCall hj hreq
  cases hop_eq
  have hf_find : m.fiber? Api.root = some f := by
    unfold RunMachine.fiber?
    rw [hmf, List.find?_cons_of_pos (by simp only [hbase.1, decide_true])]
  have hcur : f.frame.current = cur := by rw [hf_frame]; rfl
  have hprep : prepareAsyncAnswer (interpOf root table) m Api.root token (.ofExit ex) =
      (m.state, Prim.ofExit ex) := by
    unfold prepareAsyncAnswer
    simp only [hj.notStuck, Option.isSome_none, Bool.false_eq_true, ↓reduceIte, hf_find, hp]
    change prepareExternalAnswer table (some f.frame.current) (.ofExit ex) m.state = _
    rw [hcur, hcur_eq]
    exact prepareExternalAnswer_data hdrow v w' ex m.state
  rw [hprep]
  dsimp only
  let f' : NRunFiber := { f with
    parked := .notParked
    pending := f.pending.filter fun p => p.token ≠ token
    frame := { f.frame with current := Prim.ofExit ex } }
  have hdrive : driveStep (interpOf root table) m (.resume Api.root token (Prim.ofExit ex))
      [Cmd.drainDue] =
      ((m.update f').emit [RunEvent.resumedWith Api.root token (Prim.ofExit ex)],
        [Cmd.evaluate Api.root, Cmd.drainDue]) := by
    unfold driveStep
    rw [hf_find]
    dsimp only
    rw [hp]
    dsimp only
    rw [if_pos rfl]
  rw [hdrive]
  dsimp only
  have hup := update_one (f' := f') hmf rfl
  have hframe' : f'.frame = fiberOf (Prim.ofExit ex) K true := by
    change { f.frame with current := Prim.ofExit ex } = _
    rw [hf_frame]
    rfl
  have htape' : TapeSubmitted journal (tape ++ [ex]) := by
    intro ex' hex'
    rw [List.mem_append] at hex'
    rcases hex' with hex' | hex'
    · exact htape ex' hex'
    · simp only [List.mem_singleton] at hex'
      subst hex'
      exact ⟨reply, hsub_mem, hsub_comp⟩
  have hhost : ∀ rest : ReplyTape,
      hostAnswer (admittedTapeHost table) (fiberOf cur K true).current (ex :: rest) =
        some (ex, rest) := by
    intro rest
    change hostAnswer (admittedTapeHost table) cur (ex :: rest) = some (ex, rest)
    rw [hcur_eq]
    exact admittedTapeHost_cons table i v w' ex rest (lt_of_externalRow hrow) hadm
  have hp_empty : prepareExternalAnswer table (some (fiberOf cur K true).current) (.ofExit ex)
      Stores.empty = (Stores.empty, Prim.ofExit ex) := by
    change prepareExternalAnswer table (some cur) (.ofExit ex) Stores.empty = _
    rw [hcur_eq]
    exact prepareExternalAnswer_data hdrow v w' ex Stores.empty
  have hleads' : LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
      (tape ++ [ex]) (fiberOf (Prim.ofExit ex) K true) Stores.empty :=
    LeadsTape.answer hleads hcall hhost hp_empty
  have hys' : YieldStack (Prim.ofExit ex) K f'.frame.current f'.frame.stack := by
    rw [hframe']
    exact .plain
  have hmode' : FiberMode root table cf journal m.nextToken f' :=
    .active (Prim.ofExit ex) K (tape ++ [ex]) hexit (by rw [hframe']; rfl)
      (by rw [hframe']; rfl) (by rw [hframe']; rfl) (extPlainCode_ofExit table ex) hK
      htape' hleads' (.unparked rfl hys')
  have hinv' : MachineInv root table cf journal
      ((m.update f').emit [RunEvent.resumedWith Api.root token (Prim.ofExit ex)]) :=
    ⟨hj.notStuck, hj.noRaces, hj.store, f', hup, hbase, hmode'⟩
  refine ⟨(), trivial, hinv', fun _ => ⟨lift_evaluate () _ Api.root, lift_nil () _⟩⟩

private theorem fiber?_root {m : NativeMachine} {f : NRunFiber}
    (hmf : m.fibers = [f]) (hid : f.id = Api.root) :
    m.fiber? Api.root = some f := by
  unfold RunMachine.fiber?
  rw [hmf, List.find?_cons_of_pos (by simp only [hid, decide_true])]

private theorem completedExits_nil {m : NativeMachine} {f : NRunFiber}
    (hmf : m.fibers = [f]) (hexit : f.exit = none) :
    m.completedExits = [] := by
  unfold RunMachine.completedExits
  rw [hmf, List.filterMap_cons, List.filterMap_nil, hexit]
  rfl

private theorem runloopTop_of_deferred_false {f : NRunFiber}
    (hd : f.frame.deferredInterrupt = false) :
    runloopTop f = f := by
  unfold runloopTop
  change (if f.frame.deferredInterrupt then _ else f) = f
  simp only [hd, Bool.false_eq_true, ↓reduceIte]

private def isSync : NCode → Bool
  | .sync _ => true
  | _ => false

private theorem LoopActiveOrInterrupted.yielding {root : NativeEff} {table : RowTable}
    {cf : Nat} {journal : List Command} {f f' : NRunFiber}
    (hl : LoopActiveOrInterrupted root table cf journal f)
    (hfr : f'.frame = ⟨Prim.yieldNowWith 0,
      Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current :: f.frame.stack,
      true, f.frame.interruptedCause, false⟩) :
    LoopActiveOrInterrupted root table cf journal f' := by
  rcases hl with ⟨cur, K, tape, hic, hpl, hK, htape, hleads, hys⟩ | ⟨ic, c, K₀, hic, hK₀, hys⟩
  · refine Or.inl ⟨cur, K, tape, ?_, hpl, hK, htape, hleads, ?_⟩
    · rw [hfr]; exact hic
    · rw [hfr]; exact .yielding hys
  · refine Or.inr ⟨ic, c, K₀, ?_, hK₀, ?_⟩
    · rw [hfr]; exact hic
    · rw [hfr]; exact .yielding hys

private theorem driveStep_passive {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (m : NativeMachine)
    (c : Cmd EffName EffThunk Val Err Defect FiberId Ann NCode)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (hj : MachineInv root table cf journal m)
    (hpass : ∀ c' ∈ c :: rest, PassiveCmd m.nextToken c')
    (hcall : CallParkBound m (fun tok => ∀ c' ∈ c :: rest, PassiveCmd tok c'))
    (ho : SnapshotInv m ts) :
    letI := evaluatorFor root table
    MachineInv root table cf journal (driveStep (interpOf root table) m c rest).1 ∧
      CmdQueueInv root table cf journal (driveStep (interpOf root table) m c rest).1
        (driveStep (interpOf root table) m c rest).2 ∧
      SnapshotInv (driveStep (interpOf root table) m c rest).1 ts := by
  letI := evaluatorFor root table
  have hc : PassiveCmd m.nextToken c := hpass c (List.mem_cons_self ..)
  have hrest : ∀ c' ∈ rest, PassiveCmd m.nextToken c' :=
    fun c' hc' => hpass c' (List.mem_cons_of_mem c hc')
  have hcall_rest : CallParkBound m (fun tok => ∀ c' ∈ rest, PassiveCmd tok c') :=
    fun f hf tok hp hcur c' hc' => hcall f hf tok hp hcur c' (List.mem_cons_of_mem c hc')
  rcases hc with rfl | ⟨id, rfl⟩ | ⟨id, tok, htok, rfl⟩
  · have hd : driveStep (interpOf root table) m .drainDue rest = (m, rest) := by
      unfold driveStep
      rw [StoreInv.dueResumes root table hj.store]
      rfl
    rw [hd]
    exact ⟨hj, .passive rest hrest hcall_rest, ho⟩
  · unfold driveStep
    cases hf : m.fiber? id with
    | none => exact ⟨hj, .passive rest hrest hcall_rest, ho⟩
    | some f =>
      dsimp only
      by_cases hcond : (f.exit.isSome || f.running || f.parked != Parked.notParked) = true
      · rw [if_pos hcond]
        exact ⟨hj, .passive rest hrest hcall_rest, ho⟩
      · rw [if_neg hcond]
        have hcond_f : (f.exit.isSome || f.running || f.parked != Parked.notParked) = false :=
          Bool.eq_false_iff.mpr hcond
        simp only [Bool.or_eq_false_iff, bne_eq_false_iff_eq] at hcond_f
        obtain ⟨⟨hexit_none, hrun_false⟩, hp_not⟩ := hcond_f
        have hexit : f.exit = none := by
          cases he : f.exit with
          | none => rfl
          | some _ => rw [he] at hexit_none; cases hexit_none
        obtain ⟨g, hmg, hbase, hmode⟩ := hj.fiber
        obtain ⟨rfl, hfid⟩ := fiber?_one hmg hf
        have hid : id = Api.root := hfid.symm.trans hbase.1
        subst hid
        obtain ⟨hintr, hdef, hl⟩ := hmode.toLoopActiveOrInterrupted hexit hrun_false hp_not
        let f' : NRunFiber := { f with running := true, currentOpCount := 0 }
        have hup := update_one (f' := f') hmg rfl
        have hmode' : FiberMode root table cf journal m.nextToken f' :=
          LoopActiveOrInterrupted.toFiberMode m.nextToken hexit hintr hdef hp_not hl
        have hj' : MachineInv root table cf journal
            ((m.update f').emit [RunEvent.started Api.root]) :=
          ⟨hj.notStuck, hj.noRaces, hj.store, f', hup, hbase, hmode'⟩
        have hq' : CmdQueueInv root table cf journal
            ((m.update f').emit [RunEvent.started Api.root]) (Cmd.loop Api.root false :: rest) := by
          refine .loop false rest hrest (fun g' hg' => ?_)
          change (m.update f').fibers = [g'] at hg'
          rw [hup] at hg'
          cases hg'
          exact ⟨hexit, rfl, hp_not, hintr, hdef, hl⟩
        have ho' : SnapshotInv ((m.update f').emit [RunEvent.started Api.root]) ts :=
          ⟨ho.1, CallParkBound.of_notParked hup hp_not⟩
        exact ⟨hj', hq', ho'⟩
  · unfold driveStep
    cases hf : m.fiber? id with
    | none => exact ⟨hj, .passive rest hrest hcall_rest, ho⟩
    | some f =>
      dsimp only
      cases hp : f.parked with
      | notParked => exact ⟨hj, .passive rest hrest hcall_rest, ho⟩
      | withGuard parkedToken =>
        dsimp only
        by_cases heq : parkedToken = tok
        · rw [if_pos heq]
          subst heq
          obtain ⟨g, hmg, hbase, hmode⟩ := hj.fiber
          obtain ⟨rfl, hfid⟩ := fiber?_one hmg hf
          have hid : id = Api.root := hfid.symm.trans hbase.1
          subst hid
          have hncall : IsCall f.frame.current = false := by
            cases hcall_b : IsCall f.frame.current with
            | false => rfl
            | true =>
              have hpc := hcall f hmg parkedToken hp hcall_b _ (List.mem_cons_self ..)
              rcases hpc with h | ⟨_, h⟩ | ⟨_, tok', hlt', h⟩
              · cases h
              · cases h
              · cases h
                exact absurd hlt' (Nat.lt_irrefl _)
          have hcur_unit : f.frame.current = Prim.success Val.unit := by
            rcases hmode with ⟨cur, K, tape, _, _, _, _, _, _, _, _, hsub⟩ |
              ⟨_, _, _, _, _, _, _, _, _, hpark⟩ | ⟨hp', _⟩
            · rcases hsub with ⟨hp', _⟩ | ⟨_, _, _, _, hcur, _⟩ | ⟨_, _, _, _, hcall_c, hcur, _, _⟩
              · rw [hp] at hp'; cases hp'
              · exact hcur
              · rw [hcur, hcall_c] at hncall; cases hncall
            · exact (hpark parkedToken hp).2.2
            · rw [hp] at hp'; cases hp'
          have hframe_eq : ({ f.frame with current := Prim.success Val.unit } : NFiber) = f.frame := by
            rw [← hcur_unit]
          let f' : NRunFiber := { f with
            parked := .notParked
            pending := f.pending.filter fun p => p.token ≠ parkedToken
            frame := { f.frame with current := Prim.success Val.unit } }
          have hup := update_one (f' := f') hmg rfl
          have hmode' : FiberMode root table cf journal m.nextToken f' := by
            rcases hmode with ⟨cur, K, tape, hexit, hintr, hic, hdef, hpl, hK, htape, hleads, hsub⟩ |
              ⟨ic, c', K₀, hexit, hintr, hic, hdef, hK₀, hys, _⟩ | ⟨hp', _⟩
            · rcases hsub with ⟨hp', _⟩ | ⟨_, _, _, _, _, hys⟩ | ⟨_, _, _, _, hcall_c, hcur, _, _⟩
              · rw [hp] at hp'; cases hp'
              · refine .active cur K tape hexit hintr hic hdef hpl hK htape hleads (.unparked rfl ?_)
                change YieldStack cur K ({ f.frame with current := Prim.success Val.unit } : NFiber).current
                  f.frame.stack
                rw [hframe_eq]; exact hys
              · rw [hcur, hcall_c] at hncall; cases hncall
            · refine .interrupted ic c' K₀ hexit hintr hic hdef hK₀ ?_ (fun t ht => by cases ht)
              change YieldStack (Prim.failure c') K₀
                ({ f.frame with current := Prim.success Val.unit } : NFiber).current
                f.frame.stack
              rw [hframe_eq]; exact hys
            · rw [hp] at hp'; cases hp'
          have hj' : MachineInv root table cf journal
              ((m.update f').emit [RunEvent.resumedWith Api.root parkedToken (Prim.success Val.unit)]) :=
            ⟨hj.notStuck, hj.noRaces, hj.store, f', hup, hbase, hmode'⟩
          have hpass' : ∀ c' ∈ Cmd.evaluate Api.root :: rest, PassiveCmd m.nextToken c' := by
            intro c' hc'
            rcases List.mem_cons.mp hc' with rfl | hc'
            · exact Or.inr (Or.inl ⟨Api.root, rfl⟩)
            · exact hrest c' hc'
          have hq' : CmdQueueInv root table cf journal
              ((m.update f').emit [RunEvent.resumedWith Api.root parkedToken (Prim.success Val.unit)])
              (Cmd.evaluate Api.root :: rest) :=
            .passive _ hpass' (CallParkBound.of_notParked hup rfl)
          have ho' : SnapshotInv
              ((m.update f').emit [RunEvent.resumedWith Api.root parkedToken (Prim.success Val.unit)]) ts :=
            ⟨ho.1, CallParkBound.of_notParked hup rfl⟩
          exact ⟨hj', hq', ho'⟩
        · rw [if_neg heq]
          exact ⟨hj, .passive rest hrest hcall_rest, ho⟩

private theorem settle_evaluateNative_ext_nonSync {root : NativeEff} {table : RowTable}
    {cf : Nat} {journal : List Command} (hroot : ExtRows table root = true)
    (m : NativeMachine) (f₀ f₁ : NRunFiber) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (cur : NCode) (K : List NCode) (tape : ReplyTape)
    (hj : MachineInv root table cf journal m)
    (ho : SnapshotInv m ts)
    (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
    (hmf₀ : m.fibers = [f₀]) (hbase₀ : FiberBase m.nextToken f₀)
    (hexit₀ : f₀.exit = none)
    (hbase₁ : FiberBase m.nextToken f₁)
    (hexit₁ : f₁.exit = none) (hrun₁ : f₁.running = true) (hp₁ : f₁.parked = .notParked)
    (hfr₁ : f₁.frame = fiberOf cur K true)
    (hpl : ExtPlainCode table cur = true) (hK : ExtPlainStack table K)
    (htape : TapeSubmitted journal tape)
    (hleads : LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
      tape (fiberOf cur K true) Stores.empty)
    (hns : ∀ t, cur ≠ Prim.sync t) (hnc : IsCall cur = false) :
    MachineInv root table cf journal (settle Api.root rest (evaluateNative root m f₁ yielding table)).1 ∧
      CmdQueueInv root table cf journal (settle Api.root rest (evaluateNative root m f₁ yielding table)).1
        (settle Api.root rest (evaluateNative root m f₁ yielding table)).2 ∧
      SnapshotInv (settle Api.root rest (evaluateNative root m f₁ yielding table)).1 ts := by
  obtain ⟨ev, heval⟩ := evaluateNative_ext_nonSync root table m f₁ yielding cur K
    hfr₁ (completedExits_nil hmf₀ hexit₀) hpl hK hns hnc
  rw [heval]
  have hid₁₀ : f₁.id = f₀.id := hbase₁.1.trans hbase₀.1.symm
  cases hstep : localStep root (fiberOf cur K true) m.state with
  | running fr' s' =>
    obtain ⟨hstep_empty, _⟩ := localStep_running_stores root table cur K m.state s' fr' hpl hK hstep
    obtain ⟨_, cur', K', rfl, hpl', hK'⟩ := localStep_ext hroot cur K Stores.empty fr' Stores.empty
      hpl hK hstep_empty
    dsimp only [settle, settleOutcome, List.nil_append]
    let f' : NRunFiber := { f₁ with frame := fiberOf cur' K' true }
    have hup : ((m.emit ev).update f').fibers = [f'] := update_one hmf₀ hid₁₀
    have hleads' := LeadsTape.step hleads hstep_empty hnc (fun thunk => ExtPlainCode.noWithFiber hpl thunk)
    have hl' : LoopActiveOrInterrupted root table cf journal f' :=
      Or.inl ⟨cur', K', tape, rfl, hpl', hK', htape, hleads', .plain⟩
    have hmode' : FiberMode root table cf journal m.nextToken f' :=
      LoopActiveOrInterrupted.toFiberMode m.nextToken hexit₁ rfl rfl hp₁ hl'
    refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f', hup, hbase₁, hmode'⟩,
      .loop yielding rest hrest (fun g hg => ?_),
      ⟨ho.1, CallParkBound.of_notParked hup hp₁⟩⟩
    rw [hup] at hg
    cases hg
    exact ⟨hexit₁, hrun₁, hp₁, rfl, rfl, hl'⟩
  | finished ex s' =>
    dsimp only [settle, settleOutcome, List.nil_append]
    let f' : NRunFiber := { f₁ with frame := frameExitState f₁.frame }
    have hup : ((m.emit ev).update f').fibers = [f'] := update_one hmf₀ hid₁₀
    have hmode' : FiberMode root table cf journal m.nextToken f' :=
      .halted hp₁ (Or.inr hrun₁)
    refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f', hup, hbase₁, hmode'⟩,
      .finish ex rest hrest (fun g hg => ?_),
      ⟨ho.1, CallParkBound.of_notParked hup hp₁⟩⟩
    rw [hup] at hg
    cases hg
    exact ⟨hp₁, Or.inr hrun₁⟩

private theorem driveStep_loop {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (hroot : ExtRows table root = true)
    (m : NativeMachine) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (hj : MachineInv root table cf journal m)
    (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
    (hrun : ∀ f, m.fibers = [f] →
      f.exit = none ∧ f.running = true ∧ f.parked = .notParked ∧
      f.frame.interruptible = true ∧ f.frame.deferredInterrupt = false ∧
      LoopActiveOrInterrupted root table cf journal f)
    (ho : SnapshotInv m ts) :
    letI := evaluatorFor root table
    MachineInv root table cf journal (driveStep (interpOf root table) m (Cmd.loop Api.root yielding) rest).1 ∧
      CmdQueueInv root table cf journal (driveStep (interpOf root table) m (Cmd.loop Api.root yielding) rest).1
        (driveStep (interpOf root table) m (Cmd.loop Api.root yielding) rest).2 ∧
      SnapshotInv (driveStep (interpOf root table) m (Cmd.loop Api.root yielding) rest).1 ts := by
  letI := evaluatorFor root table
  obtain ⟨f, hmf, hbase, _⟩ := hj.fiber
  obtain ⟨hexit, hrunning, hp, hintr, hdef, hl⟩ := hrun f hmf
  have hf_find := fiber?_root hmf hbase.1
  unfold driveStep
  rw [hf_find]
  dsimp only
  unfold iteration
  rw [runloopTop_of_deferred_false hdef]
  dsimp only
  let f₁ : NRunFiber := countOp f
  unfold injectYield
  by_cases hy : (!yielding && !f₁.preventYield && yieldVerdict f₁) = true
  · rw [if_pos hy]
    dsimp only
    let f₂ : NRunFiber := { f₁ with
      yieldOverride := none
      frame := { f.frame with current := Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current } }
    have hfr₂ : f₂.frame =
        ⟨Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current,
          f.frame.stack, true, f.frame.interruptedCause, false⟩ :=
      frame_eta rfl rfl hintr rfl hdef
    change MachineInv root table cf journal
        (settle Api.root rest (evaluateNative root
          (m.emit [RunEvent.yieldInjected f₁.id f₁.currentOpCount]) f₂ true table)).1 ∧
      CmdQueueInv root table cf journal
        (settle Api.root rest (evaluateNative root
          (m.emit [RunEvent.yieldInjected f₁.id f₁.currentOpCount]) f₂ true table)).1
        (settle Api.root rest (evaluateNative root
          (m.emit [RunEvent.yieldInjected f₁.id f₁.currentOpCount]) f₂ true table)).2 ∧
      SnapshotInv
        (settle Api.root rest (evaluateNative root
          (m.emit [RunEvent.yieldInjected f₁.id f₁.currentOpCount]) f₂ true table)).1 ts
    rw [evaluateNative_onSuccessConst root table
      (m.emit [RunEvent.yieldInjected f₁.id f₁.currentOpCount]) f₂ true
      f.frame.current f.frame.stack f.frame.interruptedCause hfr₂]
    dsimp only [settle, settleOutcome, List.nil_append]
    let f₃ : NRunFiber := { f₂ with frame := ⟨Prim.yieldNowWith 0,
      Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current :: f.frame.stack,
      true, f.frame.interruptedCause, false⟩ }
    have hup : (((m.emit [RunEvent.yieldInjected f₁.id f₁.currentOpCount]).emit
        [RunEvent.frame f₂.id (FrameEvent.pushed
          (Prim.onSuccessConst (Prim.yieldNowWith 0) f.frame.current))]).update f₃).fibers = [f₃] :=
      update_one hmf rfl
    have hl' : LoopActiveOrInterrupted root table cf journal f₃ := hl.yielding rfl
    have hmode' : FiberMode root table cf journal m.nextToken f₃ :=
      LoopActiveOrInterrupted.toFiberMode m.nextToken hexit rfl rfl hp hl'
    refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase, hmode'⟩,
      .loop true rest hrest (fun g hg => ?_),
      ⟨ho.1, CallParkBound.of_notParked hup hp⟩⟩
    rw [hup] at hg
    cases hg
    exact ⟨hexit, hrunning, hp, rfl, rfl, hl'⟩
  · rw [if_neg hy]
    dsimp only
    change MachineInv root table cf journal (settle Api.root rest (evaluateNative root m f₁ yielding table)).1 ∧
      CmdQueueInv root table cf journal (settle Api.root rest (evaluateNative root m f₁ yielding table)).1
        (settle Api.root rest (evaluateNative root m f₁ yielding table)).2 ∧
      SnapshotInv (settle Api.root rest (evaluateNative root m f₁ yielding table)).1 ts
    have hrest_succ : ∀ c ∈ rest, PassiveCmd (m.nextToken + 1) c :=
      fun c hc => (hrest c hc).mono (Nat.le_succ _)
    have hts_succ : TasksInv (m.nextToken + 1) ts := ho.1.mono (Nat.le_succ _)
    rcases hl with ⟨cur, K, tape, hic, hpl, hK, htape, hleads, hys⟩ | ⟨ic, c, K₀, hic, hK₀, hys⟩
    · generalize hcur_eq : f.frame.current = c_f at hys
      generalize hstk_eq : f.frame.stack = S_f at hys
      cases hys with
      | @yielding c₁ S₁ hys' =>
        have hfr₁ : f₁.frame =
            ⟨Prim.yieldNowWith 0, Prim.onSuccessConst (Prim.yieldNowWith 0) c₁ :: S₁,
              true, none, false⟩ :=
          frame_eta hcur_eq hstk_eq hintr hic hdef
        rw [evaluateNative_yieldNow root table m f₁ yielding _ none hfr₁]
        dsimp only [settle, settleOutcome, RunFiber.park, FiberCore.deferredInterrupt,
          Bool.false_eq_true, ↓reduceIte, List.nil_append]
        let f₃ : NRunFiber := { f₁ with
          frame := ⟨Prim.success Val.unit, Prim.onSuccessConst (Prim.yieldNowWith 0) c₁ :: S₁,
            true, none, false⟩
          dispatcher := f.dispatcher.enqueue 0 (.resume f.id m.nextToken (Prim.success Val.unit))
          parked := .withGuard m.nextToken
          pending := f.pending ++ [⟨m.nextToken, none, [], [], Resume.void, false⟩]
          running := false }
        have hup : (((({ m with nextToken := m.nextToken + 1 }).arm f₁.id).emit
            [RunEvent.parkedOn f₁.id m.nextToken]).update f₃).fibers = [f₃] :=
          update_one hmf rfl
        have hdisp' : DispInv (m.nextToken + 1) f₃.dispatcher := by
          change DispInv (m.nextToken + 1)
            (f.dispatcher.enqueue 0 (.resume f.id m.nextToken (Prim.success Val.unit)))
          rw [hbase.1]
          exact DispInv.enqueue 0 m.nextToken (Nat.lt_succ_self _) (hbase.2.2.2.2.mono (Nat.le_succ _))
        have hbase' : FiberBase (m.nextToken + 1) f₃ :=
          ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hdisp'⟩
        have hmode' : FiberMode root table cf journal (m.nextToken + 1) f₃ :=
          .active cur K tape hexit rfl rfl rfl hpl hK htape hleads
            (.parkedYield m.nextToken (Nat.lt_succ_self _) rfl rfl rfl (.resuming hys'))
        exact ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase', hmode'⟩,
          .passive rest hrest_succ (CallParkBound.of_not_isCall hup rfl),
          ⟨hts_succ, CallParkBound.of_not_isCall hup rfl⟩⟩
      | @resuming c₁ S₁ hys' =>
        have hfr₁ : f₁.frame =
            ⟨Prim.success Val.unit, Prim.onSuccessConst (Prim.yieldNowWith 0) c₁ :: S₁,
              true, none, false⟩ :=
          frame_eta hcur_eq hstk_eq hintr hic hdef
        rw [evaluateNative_resuming root table m f₁ yielding c₁ S₁ none hfr₁]
        dsimp only [settle, settleOutcome, List.nil_append]
        let f₃ : NRunFiber := { f₁ with frame := ⟨c₁, S₁, true, none, false⟩ }
        have hup : ((m.emit [RunEvent.frame f₁.id
            (FrameEvent.popped (Prim.onSuccessConst (Prim.yieldNowWith 0) c₁))]).update f₃).fibers = [f₃] :=
          update_one hmf rfl
        have hl' : LoopActiveOrInterrupted root table cf journal f₃ :=
          Or.inl ⟨cur, K, tape, rfl, hpl, hK, htape, hleads, hys'⟩
        have hmode' : FiberMode root table cf journal m.nextToken f₃ :=
          LoopActiveOrInterrupted.toFiberMode m.nextToken hexit rfl rfl hp hl'
        refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase, hmode'⟩,
          .loop yielding rest hrest (fun g hg => ?_),
          ⟨ho.1, CallParkBound.of_notParked hup hp⟩⟩
        rw [hup] at hg
        cases hg
        exact ⟨hexit, hrunning, hp, rfl, rfl, hl'⟩
      | plain =>
        have hfr₁ : f₁.frame = fiberOf cur K true :=
          frame_eta hcur_eq hstk_eq hintr hic hdef
        cases hs : isSync cur with
        | true =>
          cases cur <;> simp only [isSync, Bool.false_eq_true] at hs
          rename_i thunk
          cases thunk <;> simp only [ExtPlainCode, Bool.false_eq_true] at hpl
          rename_i p
          rw [evaluateNative_sync_pure root table m f₁ yielding p K hfr₁]
          dsimp only [settle, settleOutcome, List.nil_append]
          let v := syncValueAt root (EffThunk.pure p)
          let f₃ : NRunFiber := { f₁ with frame := fiberOf (Prim.success v) K true }
          have hup : (m.update f₃).fibers = [f₃] := update_one hmf rfl
          have hleads' : LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
              tape (fiberOf (Prim.success v) K true) Stores.empty :=
            LeadsTape.step hleads (step_sync_pure root p K true Stores.empty) rfl
              (by intros; intro h; cases h)
          have hmode' : FiberMode root table cf journal m.nextToken f₃ :=
            .active (Prim.success v) K tape hexit rfl rfl rfl rfl hK htape hleads'
              (.unparked hp .plain)
          refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase, hmode'⟩,
            .deliver yielding rest hrest (fun g hg => ?_),
            ⟨ho.1, CallParkBound.of_notParked hup hp⟩⟩
          rw [hup] at hg
          cases hg
          exact ⟨K, tape, v, hexit, hrunning, hp, rfl, hK, htape, hleads'⟩
        | false =>
          have hns : ∀ t, cur ≠ Prim.sync t := by rintro t rfl; cases hs
          cases hcall : IsCall cur with
          | true =>
            have hext := ExtPlainCode.extCall_of_isCall hpl hcall
            cases cur <;> simp only [IsCall, Bool.false_eq_true] at hcall
            rename_i effName sig can
            cases effName <;> simp only [ExtCall, Bool.false_eq_true] at hext
            rename_i op req w
            cases op <;> cases sig <;> cases can <;> simp only [Bool.false_eq_true] at hext
            rename_i j
            rw [evaluateNative_extCall root table m f₁ yielding j req w K hfr₁]
            dsimp only [settle, settleOutcome, RunFiber.park, List.nil_append]
            have hdef₁ : f₁.frame.deferredInterrupt = false := by rw [hfr₁]; rfl
            simp only [hdef₁, Bool.false_eq_true, ↓reduceIte]
            let f₃ : NRunFiber := { f₁ with
              parked := .withGuard m.nextToken
              pending := f.pending ++ [⟨m.nextToken, none, [], [], Resume.void, false⟩]
              running := false }
            have hup : ((({ m with state := m.state, nextToken := m.nextToken + 1 }).emit
                [RunEvent.parkedOn f₁.id m.nextToken]).update f₃).fibers = [f₃] :=
              update_one hmf rfl
            have hbase' : FiberBase (m.nextToken + 1) f₃ :=
              ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1,
                hbase.2.2.2.2.mono (Nat.le_succ _)⟩
            have hcur₃ : f₃.frame.current = Prim.async (EffName.external (.external j) req w) false none := by
              change f₁.frame.current = _
              rw [hfr₁]; rfl
            have hstk₃ : f₃.frame.stack = K := by
              change f₁.frame.stack = K
              rw [hfr₁]; rfl
            have hmode' : FiberMode root table cf journal (m.nextToken + 1) f₃ :=
              .active _ K tape hexit (by change f₁.frame.interruptible = true; rw [hfr₁]; rfl)
                (by change f₁.frame.interruptedCause = none; rw [hfr₁]; rfl)
                (by change f₁.frame.deferredInterrupt = false; rw [hfr₁]; rfl)
                hpl hK htape hleads
                (.parkedCall m.nextToken (Nat.lt_succ_self _) rfl rfl hcall hcur₃ hstk₃ hbase.2.2.2.2)
            refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase', hmode'⟩,
              .passive rest hrest_succ (fun g hg tok hpg _ c' hc' => ?_),
              ⟨hts_succ, fun g hg tok hpg _ => ?_⟩⟩
            · cases hg.symm.trans hup
              cases hpg
              exact hrest c' hc'
            · cases hg.symm.trans hup
              cases hpg
              exact ho.1
          | false =>
            exact settle_evaluateNative_ext_nonSync hroot m f f₁ yielding rest ts cur K tape
              hj ho hrest hmf hbase hexit hbase hexit hrunning hp hfr₁ hpl hK htape hleads hns hcall
    · generalize hcur_eq : f.frame.current = c_f at hys
      generalize hstk_eq : f.frame.stack = S_f at hys
      cases hys with
      | @yielding c₁ S₁ hys' =>
        have hfr₁ : f₁.frame =
            ⟨Prim.yieldNowWith 0, Prim.onSuccessConst (Prim.yieldNowWith 0) c₁ :: S₁,
              true, some ic, false⟩ :=
          frame_eta hcur_eq hstk_eq hintr hic hdef
        rw [evaluateNative_yieldNow root table m f₁ yielding _ (some ic) hfr₁]
        dsimp only [settle, settleOutcome, RunFiber.park, FiberCore.deferredInterrupt,
          Bool.false_eq_true, ↓reduceIte, List.nil_append]
        let f₃ : NRunFiber := { f₁ with
          frame := ⟨Prim.success Val.unit, Prim.onSuccessConst (Prim.yieldNowWith 0) c₁ :: S₁,
            true, some ic, false⟩
          dispatcher := f.dispatcher.enqueue 0 (.resume f.id m.nextToken (Prim.success Val.unit))
          parked := .withGuard m.nextToken
          pending := f.pending ++ [⟨m.nextToken, none, [], [], Resume.void, false⟩]
          running := false }
        have hup : (((({ m with nextToken := m.nextToken + 1 }).arm f₁.id).emit
            [RunEvent.parkedOn f₁.id m.nextToken]).update f₃).fibers = [f₃] :=
          update_one hmf rfl
        have hdisp' : DispInv (m.nextToken + 1) f₃.dispatcher := by
          change DispInv (m.nextToken + 1)
            (f.dispatcher.enqueue 0 (.resume f.id m.nextToken (Prim.success Val.unit)))
          rw [hbase.1]
          exact DispInv.enqueue 0 m.nextToken (Nat.lt_succ_self _) (hbase.2.2.2.2.mono (Nat.le_succ _))
        have hbase' : FiberBase (m.nextToken + 1) f₃ :=
          ⟨hbase.1, hbase.2.1, hbase.2.2.1, hbase.2.2.2.1, hdisp'⟩
        have hmode' : FiberMode root table cf journal (m.nextToken + 1) f₃ :=
          .interrupted ic c K₀ hexit rfl rfl rfl hK₀ (.resuming hys')
            (fun tok hpg => by cases hpg; exact ⟨Nat.lt_succ_self _, rfl, rfl⟩)
        exact ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase', hmode'⟩,
          .passive rest hrest_succ (CallParkBound.of_not_isCall hup rfl),
          ⟨hts_succ, CallParkBound.of_not_isCall hup rfl⟩⟩
      | @resuming c₁ S₁ hys' =>
        have hfr₁ : f₁.frame =
            ⟨Prim.success Val.unit, Prim.onSuccessConst (Prim.yieldNowWith 0) c₁ :: S₁,
              true, some ic, false⟩ :=
          frame_eta hcur_eq hstk_eq hintr hic hdef
        rw [evaluateNative_resuming root table m f₁ yielding c₁ S₁ (some ic) hfr₁]
        dsimp only [settle, settleOutcome, List.nil_append]
        let f₃ : NRunFiber := { f₁ with frame := ⟨c₁, S₁, true, some ic, false⟩ }
        have hup : ((m.emit [RunEvent.frame f₁.id
            (FrameEvent.popped (Prim.onSuccessConst (Prim.yieldNowWith 0) c₁))]).update f₃).fibers = [f₃] :=
          update_one hmf rfl
        have hl' : LoopActiveOrInterrupted root table cf journal f₃ :=
          Or.inr ⟨ic, c, K₀, rfl, hK₀, hys'⟩
        have hmode' : FiberMode root table cf journal m.nextToken f₃ :=
          LoopActiveOrInterrupted.toFiberMode m.nextToken hexit rfl rfl hp hl'
        refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase, hmode'⟩,
          .loop yielding rest hrest (fun g hg => ?_),
          ⟨ho.1, CallParkBound.of_notParked hup hp⟩⟩
        rw [hup] at hg
        cases hg
        exact ⟨hexit, hrunning, hp, rfl, rfl, hl'⟩
      | plain =>
        have hfr₁ : f₁.frame = ⟨Prim.failure c, K₀, true, some ic, false⟩ :=
          frame_eta hcur_eq hstk_eq hintr hic hdef
        obtain ⟨ev, ex, heval⟩ :=
          evaluateNative_interrupted_failure root table m f₁ yielding c K₀ ic hfr₁ hK₀
        rw [heval]
        dsimp only [settle, settleOutcome, List.nil_append]
        let f₃ : NRunFiber := { f₁ with frame := frameExitState f₁.frame }
        have hup : ((m.emit ev).update f₃).fibers = [f₃] := update_one hmf rfl
        have hmode' : FiberMode root table cf journal m.nextToken f₃ :=
          .halted hp (Or.inr hrunning)
        refine ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₃, hup, hbase, hmode'⟩,
          .finish ex rest hrest (fun g hg => ?_),
          ⟨ho.1, CallParkBound.of_notParked hup hp⟩⟩
        rw [hup] at hg
        cases hg
        exact ⟨hp, Or.inr hrunning⟩

private theorem driveStep_deliver {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (hroot : ExtRows table root = true)
    (m : NativeMachine) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (hj : MachineInv root table cf journal m)
    (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
    (hdel : ∀ f, m.fibers = [f] → ∃ K tape v,
      f.exit = none ∧ f.running = true ∧ f.parked = .notParked ∧
      f.frame = fiberOf (Prim.success v) K true ∧
      ExtPlainStack table K ∧ TapeSubmitted journal tape ∧
      LeadsTape table root (fiberOf (compile root cf) []) Stores.empty
        tape (fiberOf (Prim.success v) K true) Stores.empty)
    (ho : SnapshotInv m ts) :
    letI := evaluatorFor root table
    MachineInv root table cf journal (driveStep (interpOf root table) m (Cmd.deliver Api.root yielding) rest).1 ∧
      CmdQueueInv root table cf journal (driveStep (interpOf root table) m (Cmd.deliver Api.root yielding) rest).1
        (driveStep (interpOf root table) m (Cmd.deliver Api.root yielding) rest).2 ∧
      SnapshotInv (driveStep (interpOf root table) m (Cmd.deliver Api.root yielding) rest).1 ts := by
  letI := evaluatorFor root table
  obtain ⟨f, hmf, hbase, _⟩ := hj.fiber
  obtain ⟨K, tape, v, hexit, hrunning, hp, hfr, hK, htape, hleads⟩ := hdel f hmf
  have hf_find := fiber?_root hmf hbase.1
  unfold driveStep
  rw [hf_find]
  exact settle_evaluateNative_ext_nonSync hroot m f f yielding rest ts (Prim.success v) K tape
    hj ho hrest hmf hbase hexit hbase hexit hrunning hp hfr rfl hK htape hleads
    (fun _ h => by cases h) rfl

private theorem driveStep_finish {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (m : NativeMachine) (ex : ExitV)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann NCode))
    (ts : List (Machine.Task EffName EffThunk Val Err Defect FiberId Ann NCode))
    (hj : MachineInv root table cf journal m)
    (hrest : ∀ c ∈ rest, PassiveCmd m.nextToken c)
    (ho : SnapshotInv m ts) :
    letI := evaluatorFor root table
    MachineInv root table cf journal (driveStep (interpOf root table) m (Cmd.finish Api.root ex) rest).1 ∧
      CmdQueueInv root table cf journal (driveStep (interpOf root table) m (Cmd.finish Api.root ex) rest).1
        (driveStep (interpOf root table) m (Cmd.finish Api.root ex) rest).2 ∧
      SnapshotInv (driveStep (interpOf root table) m (Cmd.finish Api.root ex) rest).1 ts := by
  letI := evaluatorFor root table
  obtain ⟨f, hmf, hbase, _⟩ := hj.fiber
  have hf_find := fiber?_root hmf hbase.1
  let f₁ := ({ f with running := false } : NRunFiber).publish ex
  let f₂ := f₁.cleared (interpOf root table)
  have hexit_f : exitFiber (interpOf root table) m { f with running := false } ex =
      (((m.update f₁).emit [RunEvent.exited f₁.id ex]).update f₂, [Cmd.drainDue]) := by
    rw [exitFiber_no_children (interpOf root table) m ({ f with running := false } : NRunFiber) ex
        hbase.2.1,
      exitStore_no_observers (interpOf root table) m ({ f with running := false } : NRunFiber) ex
        hbase.2.2.1]
    rfl
  have hdrive : driveStep (interpOf root table) m (Cmd.finish Api.root ex) rest =
      (((m.update f₁).emit [RunEvent.exited f₁.id ex]).update f₂, Cmd.drainDue :: rest) := by
    unfold driveStep
    rw [hf_find]
    dsimp only
    rw [hexit_f]
    rfl
  rw [hdrive]
  dsimp only
  have hup₁ : ((m.update f₁).emit [RunEvent.exited f₁.id ex]).fibers = [f₁] :=
    update_one hmf rfl
  have hup₂ : (((m.update f₁).emit [RunEvent.exited f₁.id ex]).update f₂).fibers = [f₂] :=
    update_one hup₁ rfl
  have hmode₂ : FiberMode root table cf journal m.nextToken f₂ :=
    .halted rfl (Or.inl rfl)
  have hpass' : ∀ c' ∈ Cmd.drainDue :: rest, PassiveCmd m.nextToken c' := by
    intro c' hc'
    rcases List.mem_cons.mp hc' with rfl | hc'
    · exact Or.inl rfl
    · exact hrest c' hc'
  exact ⟨⟨hj.notStuck, hj.noRaces, hj.store, f₂, hup₂, ⟨hbase.1, rfl, rfl, rfl, hbase.2.2.2.2⟩,
      hmode₂⟩,
    .passive _ hpass' (CallParkBound.of_notParked hup₂ rfl),
    ⟨ho.1, CallParkBound.of_notParked hup₂ rfl⟩⟩

private theorem lift_step {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (hroot : ExtRows table root = true) :
    letI := evaluatorFor root table
    ∀ ts, Lift.StepKeeps Lift.unitOrder (interpOf root table)
      (Lift.Guarded (fun _ => MachineInv root table cf journal)
        (fun _ => CmdQueueInv root table cf journal)
        (fun _ => SnapshotInv) ts) := by
  letI := evaluatorFor root table
  intro ts _w m c rest _hstuck hguarded
  obtain ⟨hj, hqo⟩ := hguarded
  obtain ⟨hi, ho⟩ := hqo hj.notStuck
  have hstep :
      MachineInv root table cf journal (driveStep (interpOf root table) m c rest).1 ∧
        CmdQueueInv root table cf journal (driveStep (interpOf root table) m c rest).1
          (driveStep (interpOf root table) m c rest).2 ∧
        SnapshotInv (driveStep (interpOf root table) m c rest).1 ts := by
    rcases hi with ⟨_, hpass, hcall⟩ | ⟨yielding, _, hrest, hrun⟩ |
      ⟨yielding, _, hrest, hdel⟩ | ⟨ex, _, hrest, _⟩
    · exact driveStep_passive m c rest ts hj hpass hcall ho
    · exact driveStep_loop hroot m yielding rest ts hj hrest hrun ho
    · exact driveStep_deliver hroot m yielding rest ts hj hrest hdel ho
    · exact driveStep_finish m ex rest ts hj hrest ho
  exact ⟨(), trivial, hstep.1, fun _ => ⟨hstep.2.1, hstep.2.2⟩⟩

private theorem callTree_decision_lift {root : NativeEff} {table : RowTable} {cf : Nat}
    {journal : List Command} (hroot : ExtRows table root = true) :
    letI := evaluatorFor root table
    Lift.DecisionLift Lift.unitOrder (interpOf root table)
      (fun _ => MachineInv root table cf journal)
      (fun _ => CmdQueueInv root table cf journal)
      (fun _ => SnapshotInv)
      (fun _ => CallTreeDecision table journal) := by
  letI := evaluatorFor root table
  exact {
    step := lift_step hroot
    nil := lift_nil
    evaluate := fun w m id _ _ => lift_evaluate w m id
    drain := lift_drain
    ran := lift_ran
    task := fun w m owner t ts _ _ ho => lift_task w m owner t ts ho
    skip := lift_skip
    yield := lift_yield
    interrupt := lift_interrupt
    middleware := lift_middleware
    clockNone := fun w m millis st hj _ hc => lift_clockNone w m millis st hj hc
    clockSome := fun w m millis owed st hj _ hc => lift_clockSome w m millis owed st hj hc
    answer := fun w m id token answer hj _ ha => lift_answer w m id token answer hj ha
  }

/-! ## The invariant along a reached run -/

/-- The call-tree invariant holds at the load: one unparked root fiber at the compiled program,
the empty tape behind it. A step of `reached_inv`. -/
private theorem load_inv {root : NativeEff} {table : RowTable} (cf : Nat) (journal : List Command)
    (hroot : ExtRows table root = true) :
    MachineInv root table cf journal (Api.load root cf) :=
  ⟨rfl, rfl, StoreInv.empty, _, rfl, ⟨rfl, rfl, rfl, rfl, fun _ hb => nomatch hb⟩,
    .active (compile root cf) [] [] rfl rfl rfl rfl
      (extPlainCode_compileEff table root _ hroot) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (LeadsTape.refl table root _ _) (.unparked rfl .plain)⟩

/-- Every reply the session holds was submitted in the run's journal.
Consumer: `reached_inv`, at each applied reply. -/
private def HeldSubmitted (s : Run) : Prop :=
  ∀ slot ∈ s.session.pending, ∀ r, slot.reply = some r → Command.submit r ∈ s.journal

/-- A reply read at a key is held by some slot. A step of `applyReply_answer`. -/
private theorem readReply_mem :
    ∀ (slots : List Api.HostSession.ReplySlot) (key : Api.HostSession.Key)
      (r : Api.HostSession.Reply), Api.HostSession.readReply slots key = some r →
        ∃ slot ∈ slots, slot.reply = some r
  | [], _, _, h => nomatch h
  | slot :: rest, key, r, h => by
    unfold Api.HostSession.readReply at h
    split at h
    · exact ⟨slot, List.mem_cons_self, h⟩
    · obtain ⟨held, member, same⟩ := readReply_mem rest key r h
      exact ⟨held, List.mem_cons_of_mem _ member, same⟩

/-- Binding a call adds an empty slot. A step of `reached_held`. -/
private theorem bindCall_pending {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (call : Call) (token : Nat) :
    ∀ slot ∈ (Api.HostSession.bindCall s call token).session.pending,
      slot ∈ s.pending ∨ slot.reply = none := by
  unfold Api.HostSession.bindCall
  aesop

/-- Submitting a reply stores that reply and no other. A step of `reached_held`. -/
private theorem submit_pending {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (reply : Api.HostSession.Reply) :
    ∀ slot ∈ (Api.HostSession.submit s reply).session.pending,
      slot ∈ s.pending ∨ slot.reply = some reply := by
  intro slot held
  unfold Api.HostSession.submit at held
  split at held
  · exact Or.inl held
  · split at held
    · exact Or.inl held
    · split at held
      · exact Or.inl held
      · split at held
        · exact Or.inl held
        · obtain ⟨old, member, same⟩ := List.mem_map.mp held
          split at same
          · subst same
            exact Or.inr rfl
          · subst same
            exact Or.inl member

/-- Retiring keeps a subset of the slots. A step of `reached_held`. -/
private theorem retire_pending {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) :
    ∀ slot ∈ (Api.HostSession.retire s).pending, slot ∈ s.pending := by
  unfold Api.HostSession.retire
  aesop

/-- Applying a reply keeps a subset of the slots. A step of `reached_held`. -/
private theorem applyReply_pending {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (key : Api.HostSession.Key) (fuel : Nat) :
    ∀ slot ∈ (Api.HostSession.applyReply s key fuel).session.pending, slot ∈ s.pending := by
  cases fuel with
  | zero => exact fun _ h => h
  | succ fuel =>
    unfold Api.HostSession.applyReply
    aesop (add safe forward retire_pending)

/-- A control keeps a subset of the slots. A step of `reached_held`. -/
private theorem advance_pending {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (fuel : Nat) (d : NativeDecision) :
    ∀ slot ∈ (Api.HostSession.advance s fuel d).session.pending, slot ∈ s.pending := by
  unfold Api.HostSession.advance
  aesop (add safe forward retire_pending)

/-- **Every reply a reached run holds was submitted in its journal.**
Consumer: `reached_inv`. -/
private theorem reached_held (s : Run) (reached : Run.Reached s) : HeldSubmitted s := by
  induction reached with
  | opened b id budget profile => exact fun _ h => nomatch h
  | step s c _ ih =>
    intro slot held r hr
    rw [Run.step_journal]
    cases c with
    | bind call token =>
      rw [Run.step_session_bind] at held
      rcases bindCall_pending s.session call token slot held with old | none
      · exact List.mem_append_left _ (ih slot old r hr)
      · rw [none] at hr
        cases hr
    | submit reply =>
      rw [Run.step_session_submit] at held
      rcases submit_pending s.session reply slot held with old | new
      · exact List.mem_append_left _ (ih slot old r hr)
      · rw [new] at hr
        cases hr
        exact List.mem_append_right _ (List.mem_singleton_self _)
    | apply key =>
      rw [Run.step_session_apply] at held
      exact List.mem_append_left _ (ih slot (applyReply_pending _ _ _ slot held) r hr)
    | control d =>
      rw [Run.step_session_control] at held
      exact List.mem_append_left _ (ih slot (advance_pending _ _ _ slot held) r hr)

/-- `applyReply` leaves the machine, or steps it at the decision that `preflight` makes of a
reply the session holds. A step of `reached_inv`. -/
private theorem applyReply_answer {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (key : Api.HostSession.Key) (fuel : Nat) :
    (Api.HostSession.applyReply s key fuel).session.machine = s.machine ∨
      ∃ (n : Nat) (d : NativeDecision) (slot : Api.HostSession.ReplySlot)
        (reply : Api.HostSession.Reply),
        slot ∈ s.pending ∧ slot.reply = some reply ∧ Api.HostSession.preflight s reply = .ok d ∧
        (Api.HostSession.applyReply s key fuel).session.machine =
          steppedBy program n app.rows s.machine d := by
  unfold Api.HostSession.applyReply
  split
  · exact Or.inl rfl
  · split
    · rename_i fuel' _ _ bound reply _ hread
      obtain ⟨slot, member, same⟩ := readReply_mem s.pending key reply hread
      split
      · exact Or.inl rfl
      · rename_i decision hpre
        dsimp only
        split
        · exact Or.inl rfl
        · split
          · exact Or.inr ⟨_, decision, slot, reply, member, same, hpre, rfl⟩
          · exact Or.inr ⟨_, decision, slot, reply, member, same, hpre, rfl⟩
    · exact Or.inl rfl

/-- The decision `preflight` makes of a reply answers that reply's completion, accepted plainly
or at the call's checked instance. A step of `answer_decision`. -/
private theorem preflight_record {program : Api.Program} {app : SigApp}
    (s : Api.HostSession.Session program app) (reply : Api.HostSession.Reply)
    (d : NativeDecision) (h : Api.HostSession.preflight s reply = .ok d) :
    ∃ r : RecordedReply, r.completion = reply.completion ∧
      (acceptReply app s.machine r = some d ∨
        acceptAtInstance app s.callInstance s.machine r = some d) := by
  unfold Api.HostSession.preflight at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · rename_i decision hacc
              cases h
              exact ⟨_, rfl, Or.inl hacc⟩
            · split at h
              · rename_i decision hacc
                cases h
                exact ⟨_, rfl, Or.inr hacc⟩
              · cases h

/-- At an application with no named type, a host check reads the row table alone.
A step of `answer_decision`: the call tree's reply tape admits at the row table. -/
private theorem externalAdmits_untyped {app : SigApp} (untyped : app.types = []) (i : Nat)
    (answer : Completion Val Err Defect FiberId Ann) (allocated : List String) :
    externalAdmits app i answer allocated = externalAdmits app.rows i answer allocated := by
  unfold externalAdmits
  rw [untyped]

/-- **An applied reply's decision is admitted by the call tree**: an exit the journal submitted,
at a live external call, that the row admits. The application declares no named type: the call
tree's reply tape admits at the row table (decisions row 407 (5)). Consumer: `reached_inv`. -/
private theorem answer_decision {program : Api.Program} {app : SigApp} (untyped : app.types = [])
    (concrete : SourceScope.ConcreteReplies app.rows)
    (s : Api.HostSession.Session program app)
    (hcalls : s.calls = Api.HostSession.callTable program app)
    (hstore : StoreInv s.machine.state) (journal : List Command)
    (reply : Api.HostSession.Reply) (d : NativeDecision)
    (hpre : Api.HostSession.preflight s reply = .ok d)
    (submitted : Command.submit reply ∈ journal) :
    CallTreeDecision app.rows journal s.machine d := by
  obtain ⟨r, completion, plain | specialized⟩ := preflight_record s reply d hpre
  · have same := acceptReply_decision app s.machine r d plain
    have envelope := acceptReply_envelope app s.machine r d plain
    subst same
    obtain ⟨i, request, row, hreq, hrow, hadmit⟩ :=
      admitted_row app s.machine r.fiber r.token r.completion envelope.2.2
    obtain ⟨ex, hex⟩ := SourceScope.accepted_exit app s.calls s.machine r.fiber r.token
      r.completion hstore.1 (preflight_accepted s reply _ hpre)
    rw [hex] at hadmit
    have admits := SourceScope.admitted_exit_tape hrow hadmit
    rw [hstore.2.1, externalAdmits_untyped untyped] at admits
    exact ⟨ex, reply, i, request, row, hex, submitted, completion.symm.trans hex, hreq, hrow, admits⟩
  · rw [Api.HostSession.callInstance_callTable s hcalls] at specialized
    obtain ⟨envelope, same⟩ := acceptAtInstance_sound app _ s.machine r d specialized
    subst same
    obtain ⟨ex, hex⟩ := SourceScope.accepted_exit app s.calls s.machine r.fiber r.token
      r.completion hstore.1 (preflight_accepted s reply _ hpre)
    obtain ⟨index, hop, admits⟩ := SourceScope.instance_exit_tape concrete envelope hex
    obtain ⟨_, hreq, i, row, _, _, hopi, hrow, _⟩ := envelope
    rw [hopi] at hop
    injection hop with hi
    subst hi
    rw [hopi] at hreq
    rw [hstore.2.1, externalAdmits_untyped untyped] at admits
    exact ⟨ex, reply, i, r.request, row, hex, submitted, completion.symm.trans hex, hreq, hrow,
      admits⟩

/-- **The call-tree invariant holds along every reached run** of an external-only straight
program without cause handlers, with the journal's submitted exits as its tape.
Consumer: `request_leads`. -/
private theorem reached_inv (s : Run) (reached : Run.Reached s)
    (hroot : ExtRows s.built.table s.built.program = true)
    (concrete : SourceScope.ConcreteReplies s.built.table) (untyped : s.built.app.types = []) :
    MachineInv s.built.program s.built.table s.budget.compileFuel s.journal s.machine := by
  induction reached with
  | opened b id budget profile => exact load_inv budget.compileFuel [] hroot
  | step s c hs ih =>
    rw [Run.step_built] at hroot concrete untyped
    have inv := (ih hroot concrete untyped).mono_journal (j₂ := (s.step c).journal) (fun c' h => by
      rw [Run.step_journal]
      exact List.mem_append_left _ h)
    rw [Run.step_built, Run.step_budget]
    have stepped : ∀ n d, CallTreeDecision s.built.table (s.step c).journal s.machine d →
        MachineInv s.built.program s.built.table s.budget.compileFuel (s.step c).journal
          (steppedBy s.built.program n s.built.table s.machine d) := fun n d ha => by
      letI := evaluatorFor s.built.program s.built.table
      obtain ⟨_, _, moved⟩ := Lift.stepDecisionState_lift
        (callTree_decision_lift (cf := s.budget.compileFuel) (journal := (s.step c).journal) hroot)
        n () s.machine d inv ha
      exact moved
    cases c with
    | bind call token =>
      have same : (s.step (.bind call token)).machine = s.machine :=
        (congrArg Api.HostSession.Session.machine (Run.step_session_bind s call token)).trans
          (Run.bindCall_inert s.session call token).1
      rw [same]
      exact inv
    | submit reply =>
      have same : (s.step (.submit reply)).machine = s.machine :=
        (congrArg Api.HostSession.Session.machine (Run.step_session_submit s reply)).trans
          (Run.submit_inert s.session reply).1
      rw [same]
      exact inv
    | apply key =>
      have hs' := congrArg Api.HostSession.Session.machine (Run.step_session_apply s key)
      rcases applyReply_answer s.session key s.budget.fuel with same |
        ⟨n, d, slot, reply, member, held, hpre, moved⟩
      · have here : (s.step (.apply key)).machine = s.machine := hs'.trans same
        rw [here]
        exact inv
      · have here : (s.step (.apply key)).machine =
            steppedBy s.built.program n s.built.table s.machine d := hs'.trans moved
        rw [here]
        refine stepped n d (answer_decision untyped concrete s.session (Run.reached_history s hs).1
          inv.store _ reply d hpre ?_)
        rw [Run.step_journal]
        exact List.mem_append_left _ (reached_held s hs slot member reply held)
    | control d =>
      have hs' := congrArg Api.HostSession.Session.machine (Run.step_session_control s d)
      have moveBy : CallTreeDecision s.built.table (s.step (.control d)).journal s.machine d →
          MachineInv s.built.program s.built.table s.budget.compileFuel (s.step (.control d)).journal
            (s.step (.control d)).machine := fun ha => by
        rcases advance_machine s.session s.budget.fuel d with same | ⟨_, moved⟩
        · have here : (s.step (.control d)).machine = s.machine := hs'.trans same
          rw [here]
          exact inv
        · have here : (s.step (.control d)).machine =
              steppedBy s.built.program s.budget.fuel s.built.table s.machine d := hs'.trans moved
          rw [here]
          exact stepped _ _ ha
      cases d with
      | answerAsync f t a =>
        have here : (s.step (.control (.answerAsync f t a))).machine = s.machine := hs'
        rw [here]
        exact inv
      | fire _ => exact moveBy trivial
      | flush => exact moveBy trivial
      | evaluate _ => exact moveBy trivial
      | yieldVerdict _ _ => exact moveBy trivial
      | interruptFrom _ _ _ => exact moveBy trivial
      | installMiddleware => exact moveBy trivial
      | advance _ => exact moveBy trivial

/-- A live native request retains a local call position reached under submitted exits.
Consumer: `request_in_tree`, then the original routing clause.
The unresolved obligation includes arbitrary budget cuts and every permitted control decision.
The existing local agreement theorem supplies the subsequent call-tree observation. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem request_leads (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (external : SourceScope.ExternalOnly s.built.program)
    (concrete : SourceScope.ConcreteReplies s.built.table) (untyped : s.built.app.types = [])
    (call : Call) (token : Nat)
    (request : Program.requestOf s.machine call.fiber token = some (call.op, call.request)) :
    ∃ (i : Nat) (row : Program.Row) (tape : ReplyTape) (frame : NFiber) (stores : Stores),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ tape, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      Leads (admittedTapeHost s.built.table) s.built.program
        (.live (fiberOf (compile s.built.program s.budget.compileFuel) []) Stores.empty) tape
        (.live frame stores) [] ∧
      IsCall frame.current = true ∧ callOf frame.current = some (i, call.request) := by
  have hroot := extRows_of_at s.built.table s.built.program external s.built.program [] rfl
    fragment noCause
  obtain ⟨_, cur, K, tape, i, _, row, _, _, _, _, _, _, _, _, _, hop, _, hrow, hcall, hcallOf, _, _,
    htape, hleads, _⟩ :=
      requestOf_active_parkedCall (reached_inv s reached hroot concrete untyped) request
  exact ⟨i, row, tape, fiberOf cur K true, Stores.empty, hop, hrow, htape, hleads.toLeads, hcall,
    hcallOf⟩

/-- A live native request lies at a wait of the admitted call tree.
The operational prefix obligation remains explicit in `request_leads`. -/
theorem request_in_tree (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (external : SourceScope.ExternalOnly s.built.program)
    (concrete : SourceScope.ConcreteReplies s.built.table) (untyped : s.built.app.types = [])
    (call : Call) (token : Nat)
    (request : Program.requestOf s.machine call.fiber token = some (call.op, call.request)) :
    ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i call.request := by
  obtain ⟨i, row, tape, frame, stores, op, declared, submitted, leads, callAt, requestAt⟩ :=
    request_leads s reached fragment noCause external concrete untyped call token request
  exact ⟨i, row, tape, op, declared, submitted,
    tree_wait_of_leads s.built.table s.built.program fragment s.budget.compileFuel tape
      frame stores i call.request leads callAt requestAt⟩

/-- Every accepted call binding names a wait in the admitted call tree.
The tape contains only exits carried by submitted replies in this run.
This is the command-prefix connection consumed by the original routing clause. -/
@[semantics "translation-simulation" (requirement := R6)]
theorem bound_in_tree (s : Run) (reached : Run.Reached s)
    (fragment : StraightRows s.built.table s.built.program = true)
    (noCause : NoCauseHandler s.built.program = true)
    (external : SourceScope.ExternalOnly s.built.program)
    (concrete : SourceScope.ConcreteReplies s.built.table) (untyped : s.built.app.types = [])
    (call : Call) (token : Nat)
    (bound : ((Command.bind call token), .bound) ∈ s.journal.zip s.phases) :
    ∃ (i : Nat) (row : Program.Row) (T : ReplyTape),
      call.op = .external i ∧ externalRow s.built.table i = some row ∧
      (∀ ex ∈ T, ∃ reply, Command.submit reply ∈ s.journal ∧
        reply.completion = .ofExit ex) ∧
      treeWaits s.built.table s.built.program T = .waiting i call.request := by
  obtain ⟨before, actual, built, recordedBefore, request⟩ :=
    bound_request_prefix s reached call token bound
  have admitted : StraightRows before.built.table before.built.program = true := by
    rw [built]
    exact fragment
  have handlers : NoCauseHandler before.built.program = true := by
    rw [built]
    exact noCause
  have operations : SourceScope.ExternalOnly before.built.program := by
    rw [built]
    exact external
  have concreteRows : SourceScope.ConcreteReplies before.built.table := by
    rw [built]
    exact concrete
  have untypedBefore : before.built.app.types = [] := by
    rw [built]
    exact untyped
  obtain ⟨i, row, tape, op, declared, submitted, waiting⟩ :=
    request_in_tree before actual admitted handlers operations concreteRows untypedBefore call token
      request
  rw [built] at declared waiting
  refine ⟨i, row, tape, op, declared, ?_, waiting⟩
  intro ex member
  obtain ⟨reply, recorded, completion⟩ := submitted ex member
  exact ⟨reply, recordedBefore _ recorded, completion⟩

/-- A sequence's run waits where its first part waits, or where its rest waits after the first
part ended. -/
theorem andThen_eq_waiting {A B σ : Type} {r : RowsEnd A σ} {k : A → Stores → σ → RowsEnd B σ}
    {i : Nat} {v : Val} {s : Stores} {st : σ} (h : r.andThen k = .waiting i v s st) :
    r = .waiting i v s st ∨ ∃ a s' st', r = .done a s' st' ∧ k a s' st' = .waiting i v s st := by
  cases r with
  | done a s' st' => exact Or.inr ⟨a, s', st', rfl, h⟩
  | waiting i' v' s' st' =>
    cases h
    exact Or.inl rfl

/-- The detailed run of the tree's own bind. -/
theorem runRowsO_pbind {table : RowTable} {σ : Type} (host : Effects.Comodel (RowSig table) σ)
    {A B : Type} (p : Effects.Program (RowsSig table) A)
    (k : A → Effects.Program (RowsSig table) B) (s : Stores) (st : σ) :
    runRowsO host (Effects.Program.bind p k) s st =
      (runRowsO host p s st).andThen fun a s st => runRowsO host (k a) s st :=
  runRowsO_bind host k p s st

/-- Where a tree waits, read off its detailed run. -/
theorem treeWaits_eq (table : RowTable) (program : NativeEff) (T : ReplyTape) :
    treeWaits table program T =
      (match runRowsO (admittedTapeHost table) (denoteRows table program []) Stores.empty T with
        | .done a _ _ => RowsStop.finished a
        | .waiting i v _ _ => RowsStop.waiting i v) := by
  unfold treeWaits
  rw [observeRows_eq_runRowsO]
  show (RowsEnd.observe (runRowsO (admittedTapeHost table)
    (Effects.Program.bind (denoteRows table program []) fun a => Effects.Program.pure (some a))
    Stores.empty T)).stop = _
  rw [runRowsO_pbind]
  cases runRowsO (admittedTapeHost table) (denoteRows table program []) Stores.empty T <;> rfl

/-- The admitted reply host at a call: the tape's next exit where the row admits it, else a
wait. -/
theorem runRowsO_admitted_vis {table : RowTable} (op : (RowSig table).Op)
    (k : ExitV → Effects.Program (RowsSig table) ExitV) (s : Stores) (ex : ExitV)
    (rest : ReplyTape) :
    runRowsO (admittedTapeHost table) (.vis (.inr op) k) s (ex :: rest) =
      if externalAdmits table op.1.val (.ofExit ex) then
        runRowsO (admittedTapeHost table) (k ex) s rest
      else .waiting op.1.val op.2 s (ex :: rest) := by
  rw [runRowsO.eq_def]
  dsimp only
  unfold admittedTapeHost
  dsimp only
  cases externalAdmits table op.1.val (.ofExit ex) with
  | true => rfl
  | false => rfl

/-- A handler's continuation, as `denoteRows` writes it for `catchIf`. -/
def catchK (table : RowTable) (env : List Val) (test : Term) (h : NativeEff) :
    ExitV → Effects.Program (RowsSig table) ExitV
  | Exit.success v => pure (Exit.success v)
  | Exit.failure cause =>
    match caughtErrorValue? env test cause with
    | some value => denoteRows table h (env ++ [value])
    | none => pure (Exit.failure cause)

/-- A handler that answers a term never waits. -/
theorem catchK_done (table : RowTable) (env : List Val) (test response : Term) (a : ExitV)
    (s : Stores) (st : ReplyTape) :
    ∃ x s' st', runRowsO (admittedTapeHost table)
      (catchK table env test (.succeed response) a) s st = .done x s' st' := by
  cases a with
  | success v => exact ⟨_, _, _, rfl⟩
  | failure cause =>
    simp only [catchK]
    cases caughtErrorValue? env test cause with
    | some value => exact ⟨_, _, _, rfl⟩
    | none => exact ⟨_, _, _, rfl⟩

/-- A response after a sequence never waits. -/
theorem seqSucceed_done (table : RowTable) (term : Term) (a : ExitV) (s : Stores)
    (st : ReplyTape) :
    ∃ x s' st', runRowsO (admittedTapeHost table)
      (seqRows (fun v => denoteRows table (.succeed term) ([] ++ [v])) a) s st =
        .done x s' st' := by
  cases a with
  | success v => exact ⟨_, _, _, rfl⟩
  | failure cause => exact ⟨_, _, _, rfl⟩

end Effect4.Run.CallTree
