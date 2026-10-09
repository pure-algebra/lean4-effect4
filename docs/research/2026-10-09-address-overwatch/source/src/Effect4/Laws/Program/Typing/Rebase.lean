import Effect4.Laws.Program.Typing.Annotate
import Effect4.Laws.Auto.ExceptMap

/-!
# Laws.Program.Typing.Rebase — the checker is natural in its base path

The checker (`Checker.check` and its six siblings, `Program/Checker.lean`) carries the path of
the node it checks. It reads the path in one way only: a refusal records it. So checking a
program at `q ++ p` is checking it at `p`, with each refusal moved below `q`
(`Checker.check_rebase`). A table or a verdict computed once for a subtree stands at any address.

| Statement | In words |
| --- | --- |
| `TypeRefusal.rebase` | a refusal moved below a base |
| `Checker.check_rebase` and five siblings | the checker at `q ++ p` is the checker at `p`, its refusal moved below `q` |
| `Checker.checkStmt_rebase` | so is a statement's, whose `return` answer is moved too |
| `tableAt_rebase` | a subtree's table at `q ++ a` is its table at `a`, each entry moved below `q` |

The proof is one mutual induction over the seven functions. A generator body's `afterRet`
(the path of a `return` that ended the body) is `none` in every recursive call but one, which
refuses at once or answers the empty tail (`checkStmts_some_rebase`).

## Placement

Concept `initial-algebras-folds`; property: the path is an inherited attribute that only
locates refusals, so the checker is natural in its base. Requirement R14 (program as data).

- **`checker-base-natural`** (claim, role compatibility; pointer `Checker.check_rebase`). Reach:
  every alphabet, signature, environment, base, path and program, and the table at a node
  (`tableAt_rebase`). Not established: the
  verdict's correctness, which `check_sound` owns; the module check of a definition block,
  which checks at the root; any cost. Consumers: a table computed once and placed at any
  address (`tableAt_rebase`, seat ORG's L8, `docs/research/2026-10-08-seat-ORG-theory-map.md`
  §3.4), and a paste between programs.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- **A refusal moved below a base.** -/
def TypeRefusal.rebase (q : List Nat) (r : TypeRefusal) : TypeRefusal := ⟨q ++ r.path, r.reason⟩

/-- A statement's type moved below a base: a `return`'s answer, which may be a refusal. -/
def StmtTy.rebase (q : List Nat) : StmtTy → StmtTy
  | .ret answer => .ret (answer.mapError (TypeRefusal.rebase q))
  | s => s

namespace Checker

open Effect4.Laws.Auto

variable {Op : Type}

theorem StmtTy.rebase_step (q : List Nat) (g : GenTy) (binds : List Ty) :
    StmtTy.rebase q (.step g binds) = .step g binds := rfl

theorem StmtTy.rebase_ret (q : List Nat) (answer : Except TypeRefusal Ty) :
    StmtTy.rebase q (.ret answer) = .ret (answer.mapError (TypeRefusal.rebase q)) := rfl

theorem rebase_mk (q p : List Nat) (reason : TypeReason) :
    TypeRefusal.rebase q ⟨p, reason⟩ = ⟨q ++ p, reason⟩ := rfl

/-! ## The leaves: each refusal is located at the node -/

theorem term?_rebase (sig : Signature Op) (env : TyEnv) (q p : List Nat) (t : Term) :
    term? sig env (q ++ p) t = (term? sig env p t).mapError (TypeRefusal.rebase q) := by
  unfold term?
  split <;> rfl

theorem cause?_rebase (sig : Signature Op) (env : TyEnv) (q p : List Nat) (c : CauseTerm) :
    cause? sig env (q ++ p) c = (cause? sig env p c).mapError (TypeRefusal.rebase q) := by
  unfold cause?
  split <;> rfl

theorem expect_rebase {α : Type} (q p : List Nat) (reason : TypeReason) (o : Option α) :
    expect ⟨q ++ p, reason⟩ o = (expect ⟨p, reason⟩ o).mapError (TypeRefusal.rebase q) := by
  cases o <;> rfl

theorem rowCheck_rebase (row : Row) (r : Ty) (use : Option TermUse) (q p : List Nat) :
    rowCheck row r use (q ++ p) = (rowCheck row r use p).mapError (TypeRefusal.rebase q) := by
  unfold rowCheck
  split <;> rfl

/-- A body after a `return` refuses at the `return`, whatever its base: one unfolding, with no
recursion. A step of `checkStmts_rebase`. -/
theorem checkStmts_some_rebase (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (q r p : List Nat) (body : Stmts Op) :
    checkStmts sig env inLoop (some (q ++ r)) (q ++ p) body =
      (checkStmts sig env inLoop (some r) p body).mapError (TypeRefusal.rebase q) := by
  cases body <;> rfl

/-- The fold of a statement's type, moved below a base, against its continuations moved below
it. A step of `checkStmts_rebase`. -/
theorem bind_fold_rebase (q : List Nat) (m : Except TypeRefusal StmtTy)
    (k1 K1 : GenTy → List Ty → Except TypeRefusal GenTy)
    (k2 K2 : Except TypeRefusal Ty → Except TypeRefusal GenTy) (k3 K3 : Except TypeRefusal GenTy)
    (h1 : ∀ g binds, K1 g binds = (k1 g binds).mapError (TypeRefusal.rebase q))
    (h2 : ∀ a, K2 (a.mapError (TypeRefusal.rebase q)) = (k2 a).mapError (TypeRefusal.rebase q))
    (h3 : K3 = k3.mapError (TypeRefusal.rebase q)) :
    ((m.map (StmtTy.rebase q)).mapError (TypeRefusal.rebase q) >>= fun s => s.fold K1 K2 K3) =
      (m >>= fun s => s.fold k1 k2 k3).mapError (TypeRefusal.rebase q) := by
  rw [ExceptMap.mapError_map_bind, ExceptMap.mapError_bind]
  cases m with
  | error e => rfl
  | ok s =>
    cases s with
    | step g binds => exact h1 g binds
    | ret a => exact h2 a
    | pass => exact h3

/-! ## The checker -/

mutual

/-- **The checker at `q ++ p` is the checker at `p`, its refusal moved below `q`.** The pointer
of `checker-base-natural`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem check_rebase (sig : Signature Op) (q : List Nat) (env : TyEnv) (p : List Nat)
    (e : Eff Op) :
    check sig env (q ++ p) e = (check sig env p e).mapError (TypeRefusal.rebase q) := by
  cases e
  case awaitFiber fiber mode =>
    cases mode <;> simp only [check, term?_rebase, expect_rebase, ExceptMap.mapError_bind, ExceptMap.mapError_pure]
  all_goals simp only [check, List.append_assoc, check_rebase sig q, checkLayer_rebase sig q,
    checkStmts_rebase sig q, checkAction_rebase sig q, term?_rebase, cause?_rebase,
    expect_rebase, rowCheck_rebase, ExceptMap.mapError_bind, ExceptMap.mapError_pure, ExceptMap.mapError_throw, ExceptMap.mapError_ite,
    rebase_mk]

/-- `check_rebase` at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkLayer_rebase (sig : Signature Op) (q : List Nat) (p : List Nat) (l : LayerTerm Op) :
    checkLayer sig (q ++ p) l = (checkLayer sig p l).mapError (TypeRefusal.rebase q) := by
  cases l <;> simp only [checkLayer, List.append_assoc, check_rebase sig q,
    checkLayer_rebase sig q, checkLayers_rebase sig q, expect_rebase, ExceptMap.mapError_bind,
    ExceptMap.mapError_pure, ExceptMap.mapError_throw, ExceptMap.mapError_ite, rebase_mk]

/-- `check_rebase` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkLayers_rebase (sig : Signature Op) (q : List Nat) (p : List Nat)
    (ls : LayerTerms Op) :
    checkLayers sig (q ++ p) ls = (checkLayers sig p ls).mapError (TypeRefusal.rebase q) := by
  cases ls <;> simp only [checkLayers, List.append_assoc, checkLayer_rebase sig q,
    checkLayers_rebase sig q, ExceptMap.mapError_bind, ExceptMap.mapError_pure]

/-- `check_rebase` at a statement: its `return` answer moves too. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkStmt_rebase (sig : Signature Op) (q : List Nat) (env : TyEnv) (inLoop : Bool)
    (p : List Nat) (st : Stmt Op) :
    checkStmt sig env inLoop (q ++ p) st =
      ((checkStmt sig env inLoop p st).map (StmtTy.rebase q)).mapError
        (TypeRefusal.rebase q) := by
  cases st
  case breakLoop =>
    cases inLoop <;> rfl
  all_goals simp only [checkStmt, List.append_assoc, check_rebase sig q, checkStmts_rebase sig q,
    term?_rebase, ExceptMap.map_bind, ExceptMap.map_pure, ExceptMap.map_throw, ExceptMap.map_ite, StmtTy.rebase_step, StmtTy.rebase_ret,
    ExceptMap.mapError_bind, ExceptMap.mapError_pure, ExceptMap.mapError_throw, ExceptMap.mapError_ite, rebase_mk]

/-- `check_rebase` at a generator body that no `return` has ended. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkStmts_rebase (sig : Signature Op) (q : List Nat) (env : TyEnv) (inLoop : Bool)
    (p : List Nat) (body : Stmts Op) :
    checkStmts sig env inLoop none (q ++ p) body =
      (checkStmts sig env inLoop none p body).mapError (TypeRefusal.rebase q) := by
  cases body with
  | nil => rfl
  | cons head rest =>
    simp only [checkStmts, List.append_assoc, checkStmt_rebase sig q]
    exact bind_fold_rebase q _ _ _ _ _ _ _
      (fun g binds => by simp only [checkStmts_rebase sig q, ExceptMap.mapError_bind, ExceptMap.mapError_pure])
      (fun a => by simp only [checkStmts_some_rebase, ExceptMap.mapError_bind, ExceptMap.mapError_pure])
      (by simp only [checkStmts_rebase sig q, ExceptMap.mapError_bind, ExceptMap.mapError_pure])

/-- `check_rebase` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkEffs_rebase (sig : Signature Op) (q : List Nat) (env : TyEnv) (p : List Nat)
    (es : Effs Op) :
    checkEffs sig env (q ++ p) es = (checkEffs sig env p es).mapError (TypeRefusal.rebase q) := by
  cases es <;> simp only [checkEffs, List.append_assoc, check_rebase sig q,
    checkEffs_rebase sig q, ExceptMap.mapError_bind, ExceptMap.mapError_pure]

/-- `check_rebase` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem checkAction_rebase (sig : Signature Op) (q : List Nat) (env : TyEnv) (p : List Nat)
    (a : ActionTerm Op) :
    checkAction sig env (q ++ p) a = (checkAction sig env p a).mapError (TypeRefusal.rebase q) := by
  cases a
  case interruptAll targets interruptor =>
    cases interruptor <;> simp only [checkAction, term?_rebase, expect_rebase, ExceptMap.mapError_bind,
      ExceptMap.mapError_pure, ExceptMap.mapError_throw, ExceptMap.mapError_ite, rebase_mk]
  all_goals simp only [checkAction, List.append_assoc, check_rebase sig q,
    checkEffs_rebase sig q, term?_rebase, expect_rebase, ExceptMap.mapError_bind, ExceptMap.mapError_pure,
    ExceptMap.mapError_throw, ExceptMap.mapError_ite, rebase_mk]

end

end Checker

/-! ## The table at a base -/

/-- **A table entry moved below a base**: its address, and its answer's refusal. -/
def Table.Entry.rebase (q : List Nat) (e : Table.Entry) : Table.Entry :=
  ⟨q ++ e.path, e.env, e.result.map fun r => r.mapError (TypeRefusal.rebase q)⟩

/-- **A subtree's table at `q ++ a` is its table at `a`, each entry moved below `q`.** So a
table computed once for a subtree stands at any address. A step of `checker-base-natural`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_rebase {Op : Type} (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op)
    (q a : List Nat) :
    tableAt s ctx n (q ++ a) = (tableAt s ctx n a).map (Table.Entry.rebase q) := by
  unfold tableAt
  rw [List.map_map]
  refine List.map_congr_left fun b _ => ?_
  simp only [Function.comp_apply, tableEntryAt, Table.Entry.rebase, List.append_assoc]
  generalize n.at_ b = node
  generalize ctx.bind (fun c => n.envAt s c b) = env
  rcases node with _ | (_ | _ | _ | _ | _ | _ | _) <;> rcases env with _ | (_ | _ | _) <;>
    simp only [Checker.check_rebase, Option.map_some, Option.map_none]

end Effect4.Program
