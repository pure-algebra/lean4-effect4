import Effect4.Program.FoldOf
import Effect4.Program.Typing.Annotate
import Effect4.Laws.Program.Typing.Sound
import Effect4.Laws.Program.Address
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Program.Typing.Annotate — the one traversal answers the address table

`Program/Typing/Annotate.lean` computes the address table in one traversal (`annotate`): the
checker's own traversal, with a record at each node. This module proves it equal to the table,
its specification (`annotate_eq_table`).

## How it is proved

- **The table at a node** (`tableAt`) is the table at any node, from any environment, at any
  address. The environment `none` stands for a subtree that is not reached (`tableAt_none`).
  The address table is its instance at the root (`table_eq_tableAt`, by definition).
- **One step of it** (`tableAt_eq_cons`): the node's own entry, then each child's table at the
  child's address, from the environment that the step function (`Node.childEnv`) gives the
  child. The proof reads the address list one step down (`Node.addresses_eq_cons`). That rests
  on a shift of the address fold's base path (`foldMapAt_eff_paths_shift` and six siblings),
  the address yield's instance of the path fold's naturality (`Laws/Program/Address.lean`).
- **The traversal against it** (`Annotate.check_eq` and six siblings) is one mutual induction
  over the seven sorts. Each case unfolds one arm of the traversal and one arm of
  `Checker.check`. Where a child reads an answer, the case splits on that answer. The checker's
  success projection does not read the path (`effTy_of_check`, `termTy_of_term?`).
- **The statements after a head**: a head other than a `bindYield` binds nothing
  (`Checker.checkStmt_step_binds`). So the checker checks them at the step function's
  environment.

`fold_of` reads the traversal as a fold of the program's family (`Annotate.check.alg`,
`Annotate.check.eq_cata`), as it reads `Checker.check` (`Laws/Program/Folds/Checker.lean`).

## Placement

Concept `initial-algebras-folds` (`docs/core/semantics.md` §2.7), requirement R14.
`annotate_eq_table` is the pointer of the claim proposed as `annotate-table` (role
compatibility). It is the one-traversal implementation of the claim `address-table`, whose
specification is the table. It serves the open part `marking-agrees` of R14, in its clause on
one traversal that answers every address. Its consumers are the typed print's slice P2
(`printTyped` reads each node's entry) and the session's call instances. Each helper below
names the step it is.

What these statements do not establish:

- an entry after a refused read: that subtree is not reached, as in the table;
- a bound on the cost: no theorem counts the checks of the traversal;
- anything at a term, which has no address.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

variable {Op : Type}

fold_of Effect4.Program.Annotate.check

/-! ## The address list, one step down -/

/-- **The address fold from a base path is the fold from a shorter one, under the rest of the
base.** At a program. The address yield's instance of the path fold's naturality
(`foldMapAt_eff_base`, `foldMapAt_eff_hom`, `Laws/Program/Address.lean`). A step of
`annotate-table`. Its consumer is `foldMapAt_eff_paths_cons`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_eff_paths_shift (e : Eff Op) (q r : List Nat) :
    foldMapAt_eff [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_eff [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_eff_base, foldMapAt_eff_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- `foldMapAt_eff_paths_shift` at a statement. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmt_paths_shift (e : Stmt Op) (q r : List Nat) :
    foldMapAt_stmt [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_stmt [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_stmt_base, foldMapAt_stmt_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- `foldMapAt_eff_paths_shift` at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmts_paths_shift (e : Stmts Op) (q r : List Nat) :
    foldMapAt_stmts [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_stmts [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_stmts_base, foldMapAt_stmts_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- `foldMapAt_eff_paths_shift` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_effs_paths_shift (e : Effs Op) (q r : List Nat) :
    foldMapAt_effs [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_effs [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_effs_base, foldMapAt_effs_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- `foldMapAt_eff_paths_shift` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_action_paths_shift (e : ActionTerm Op) (q r : List Nat) :
    foldMapAt_action [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_action [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_action_base, foldMapAt_action_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- `foldMapAt_eff_paths_shift` at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layer_paths_shift (e : LayerTerm Op) (q r : List Nat) :
    foldMapAt_layer [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_layer [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_layer_base, foldMapAt_layer_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- `foldMapAt_eff_paths_shift` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layers_paths_shift (e : LayerTerms Op) (q r : List Nat) :
    foldMapAt_layers [] (· ++ ·) (q ++ r) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_layers [] (· ++ ·) r e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map (q ++ ·) := by
  rw [foldMapAt_layers_base, foldMapAt_layers_hom (List.map (q ++ ·)) (unit' := [])
    (fun a b => List.map_append)]
  rfl

/-- **The address fold from a child's base path is the fold from the root's, under that base.**
At a program. A step of `annotate-table`. Its consumer is `Node.addresses_eq_cons`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_eff_paths_cons (e : Eff Op) (i : Nat) (q : List Nat) :
    foldMapAt_eff [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_eff [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_eff_paths_shift e (i :: q) []

/-- `foldMapAt_eff_paths_cons` at a statement. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmt_paths_cons (e : Stmt Op) (i : Nat) (q : List Nat) :
    foldMapAt_stmt [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_stmt [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_stmt_paths_shift e (i :: q) []

/-- `foldMapAt_eff_paths_cons` at a statement list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_stmts_paths_cons (e : Stmts Op) (i : Nat) (q : List Nat) :
    foldMapAt_stmts [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_stmts [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_stmts_paths_shift e (i :: q) []

/-- `foldMapAt_eff_paths_cons` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_effs_paths_cons (e : Effs Op) (i : Nat) (q : List Nat) :
    foldMapAt_effs [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_effs [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_effs_paths_shift e (i :: q) []

/-- `foldMapAt_eff_paths_cons` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_action_paths_cons (e : ActionTerm Op) (i : Nat) (q : List Nat) :
    foldMapAt_action [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_action [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_action_paths_shift e (i :: q) []

/-- `foldMapAt_eff_paths_cons` at a layer. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layer_paths_cons (e : LayerTerm Op) (i : Nat) (q : List Nat) :
    foldMapAt_layer [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_layer [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_layer_paths_shift e (i :: q) []

/-- `foldMapAt_eff_paths_cons` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem foldMapAt_layers_paths_cons (e : LayerTerms Op) (i : Nat) (q : List Nat) :
    foldMapAt_layers [] (· ++ ·) (i :: q) e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) =
      (foldMapAt_layers [] (· ++ ·) [] e (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])
        (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p]) (fun _ p => [p])).map
        ((i :: q) ++ ·) := by
  simpa only [List.append_nil] using foldMapAt_layers_paths_shift e (i :: q) []

/-- The addresses of a node's child at an index, each below the index; none where the node has
no child there. -/
def Node.childAddresses (n : Node Op) (i : Nat) : List (List Nat) :=
  match n.child i with
  | some c => (Node.addresses c).map (i :: ·)
  | none => []

/-- **The address list, one step down**: the node first, then the addresses of its children at
the indices 0, 1 and 2. No node has a fourth child, so a constructor with one fails this proof.
The children are reduced by evaluation (`whnf`), not by the equations of `Node.child`. A step
of `annotate-table`. Its consumer is `tableAt_eq_cons`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Node.addresses_eq_cons (n : Node Op) :
    Node.addresses n =
      [] :: (n.childAddresses 0 ++ (n.childAddresses 1 ++ n.childAddresses 2)) := by
  rcases n with e | e | e | e | e | e | e <;> cases e <;>
    simp only [Node.addresses, foldMapAt_eff, foldMapAt_stmt, foldMapAt_stmts, foldMapAt_effs,
      foldMapAt_action, foldMapAt_layer, foldMapAt_layers, Node.childAddresses] <;>
    (conv in (occs := *) Node.child _ _ => all_goals whnf) <;>
    simp only [List.nil_append, foldMapAt_eff_paths_cons, foldMapAt_stmt_paths_cons,
      foldMapAt_stmts_paths_cons, foldMapAt_effs_paths_cons, foldMapAt_action_paths_cons,
      foldMapAt_layer_paths_cons, foldMapAt_layers_paths_cons, List.cons_append, List.append_nil]

/-! ## The table at a node -/

/-- The entry at the address `b` below a node that stands at the address `a`, from the node's
environment `ctx`. Its environment and its answer are the table's (`table`). -/
def tableEntryAt (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op) (a b : List Nat) :
    Table.Entry :=
  let env := ctx.bind fun c => n.envAt s c b
  ⟨a ++ b, env, match n.at_ b, env with
    | some (.eff q), some (.env tys) => some (Checker.check s tys (a ++ b) q)
    | _, _ => none⟩

/-- **The table at a node**: one entry for each address of the node's subtree, standing at the
address `a`, from the node's environment `ctx`. The environment `none` is a subtree that is not
reached. -/
def tableAt (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op) (a : List Nat) :
    List Table.Entry :=
  (Node.addresses n).map (tableEntryAt s ctx n a)

/-- The answer that the table holds at a node itself: the checker's at a program in an
environment of variables, and none elsewhere. -/
def nodeAnswer (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op) (a : List Nat) :
    Option (Except TypeRefusal EffTy) :=
  match n, ctx with
  | .eff q, some (.env tys) => some (Checker.check s tys a q)
  | _, _ => none

/-- The table of a node's child at an index, at the child's address, from the environment
that the step function gives the child; empty where the node has no child there. -/
def childTableAt (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op) (a : List Nat)
    (i : Nat) : List Table.Entry :=
  match n.child i with
  | some c => tableAt s (ctx.bind fun x => n.childEnv s x i) c (a ++ [i])
  | none => []

/-- **The address table is the table at the root**, by definition. A step of `annotate-table`.
Its consumer is `annotate_eq_table`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem table_eq_tableAt (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    table s env0 p = tableAt s (some (.env env0)) (.eff p) [] := rfl

/-- The entries below a child are the child's table: the address, the environment and the node
each take one step. A step of `annotate-table`. Its consumer is `tableAt_eq_cons`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem childAddresses_map_tableEntryAt (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op)
    (a : List Nat) (i : Nat) :
    (n.childAddresses i).map (tableEntryAt s ctx n a) = childTableAt s ctx n a i := by
  unfold Node.childAddresses childTableAt
  cases hc : n.child i with
  | none => rfl
  | some c =>
    simp only [List.map_map, tableAt]
    refine List.map_congr_left fun b _ => ?_
    simp only [Function.comp_apply, tableEntryAt, Node.envAt, Node.at_, hc, Option.bind_some,
      Option.bind_assoc, List.append_assoc, List.singleton_append]

/-- The entry at a node itself holds the node's environment and its answer. A step of
`annotate-table`. Its consumer is `tableAt_eq_cons`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableEntryAt_nil (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op)
    (a : List Nat) : tableEntryAt s ctx n a [] = ⟨a, ctx, nodeAnswer s ctx n a⟩ := by
  cases ctx with
  | none => cases n <;> simp only [tableEntryAt, Node.at_, Option.bind_none, List.append_nil,
      nodeAnswer]
  | some c => rcases n with q | q | q | q | q | q | q <;> cases c <;> simp only [tableEntryAt,
      Node.envAt, Node.at_, Option.bind_some, List.append_nil, nodeAnswer]

/-- **The table at a node, one step down**: the node's own entry, then the table of each child
at the child's address, from the environment that the step function gives the child. A step of
`annotate-table`. Its consumers are the cases of `Annotate.check_eq` and its siblings. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_eq_cons (s : Signature Op) (ctx : Option NodeEnv) (n : Node Op) (a : List Nat) :
    tableAt s ctx n a = ⟨a, ctx, nodeAnswer s ctx n a⟩ ::
      (childTableAt s ctx n a 0 ++ (childTableAt s ctx n a 1 ++ childTableAt s ctx n a 2)) := by
  rw [tableAt, Node.addresses_eq_cons, List.map_cons, List.map_append, List.map_append,
    childAddresses_map_tableEntryAt, childAddresses_map_tableEntryAt,
    childAddresses_map_tableEntryAt, tableEntryAt_nil]

/-- **A subtree that is not reached**: its table holds no environment and no answer at any
address, which is the traversal's record of it. A step of `annotate-table`. Its consumers are
the cases of `Annotate.check_eq` and its siblings where a read is refused. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem tableAt_none (s : Signature Op) (n : Node Op) (a : List Nat) :
    tableAt s none n a = Annotate.unreached a n := by
  unfold tableAt Annotate.unreached
  refine List.map_congr_left fun b _ => ?_
  simp only [tableEntryAt, Option.bind_none]
  split
  · rename_i h
    cases h
  · rfl

/-! ## What a read takes from an answer -/

/-- **The checker's answer at any path gives `effTy`'s**: the success projection does not read
the path. A step of `annotate-table`. Its consumers are the cases of `Annotate.check_eq` where
a child reads an earlier sibling's type. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem effTy_of_check {s : Signature Op} {env : TyEnv} {q : List Nat} {e : Eff Op}
    {x : Except TypeRefusal EffTy} (h : Checker.check s env q e = x) :
    effTy s env e = x.toOption := by
  rw [← check_toOption_eq_effTy s env q e, h]

/-- **A term's check at any path gives `termTy`'s answer.** A step of `annotate-table`. Its
consumers are the cases of `select` and `iterate` in `Annotate.check_eq`, whose children read a
term's type. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem termTy_of_term? {s : Signature Op} {env : TyEnv} {q : List Nat} {t : Term}
    {x : Except TypeRefusal Ty} (h : Checker.term? s env q t = x) :
    termTy s env t = x.toOption := by
  rw [← Checker.toOption_term? s env q t, h]

/-- A bind on an answer is the continuation at it. A step of `annotate-table`. Its consumers are
the cases of `select` and of a statement list in `Annotate.check_eq` and its siblings. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
private theorem except_ok_bind {ε α β : Type} (a : α) (f : α → Except ε β) :
    (Except.ok a >>= f) = f a := rfl

/-- A bind on a refusal is the refusal. A step of `annotate-table`. Its consumer is the case of
a statement list in `Annotate.checkStmts_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
private theorem except_error_bind {ε α β : Type} (e : ε) (f : α → Except ε β) :
    (Except.error e >>= f) = .error e := rfl

/-- `pure` is an answer. A step of `annotate-table`. Its consumer is the case of a statement
list in `Annotate.checkStmts_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
private theorem except_pure {ε α : Type} (a : α) : (pure a : Except ε α) = .ok a := rfl

/-- **A statement other than a `bindYield` binds nothing**: where the checker answers it as a
step, the step's bindings are empty. So the statements after it are checked at its own
environment, which is the step function's. A step of `annotate-table`. Its consumer is the
case of a statement list in `Annotate.checkStmts_eq`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Checker.checkStmt_step_binds {s : Signature Op} {env : TyEnv} {inLoop : Bool}
    {q : List Nat} {head : Stmt Op} {g : GenTy} {binds : List Ty}
    (hb : ∀ e, head ≠ .bindYield e)
    (h : Checker.checkStmt s env inLoop q head = .ok (.step g binds)) : binds = [] := by
  cases head <;> aesop (rule_sets := [Effect4.Checker])

/-! ## The traversal against the table -/

set_option maxHeartbeats 400000 in
mutual

/-- **The traversal at a program is the table at it, with the checker's answer.** At every
environment and every path. The cases are the traversal's arms, in its order. A step of
`annotate-table`. Its consumer is `annotate_eq_table`. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.check_eq (s : Signature Op) (e : Eff Op) (env : TyEnv) (p : List Nat) :
    Annotate.check s env p e =
      (tableAt s (some (.env env)) (.eff e) p, Checker.check s env p e) :=
  match e with
  | .succeed _ | .fail _ | .failCause _ | .sync _ | .perform _ _ | .yieldNow _ | .awaitFiber _ _
  | .service _ => by
    rw [tableAt_eq_cons]
    rfl
  | .suspend body | .uninterruptible body | .interruptible body | .exit body | .scoped body
  | .provideService _ _ body | .restore _ body => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, Annotate.check_eq s body, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl
  | .gen body => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, Annotate.checkStmts_eq s body, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl
  | .withFiber action => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, Annotate.checkAction_eq s action, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl
  -- a definition block: the checker refuses at the node, and no child is reached
  | .defs decls bodies main => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, tableAt_none, List.append_nil]
    rfl
  | .provideLayer layer _ body => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, Annotate.checkLayer_eq s layer, Annotate.check_eq s body,
      nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl
  -- the second child reads the first child's type
  | .bind body next | .catchCause body next | .onExit body next | .acquireRelease body next
  | .catchIf _ body next => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, Annotate.check_eq s body, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil, Checker.check]
    cases h : Checker.check s env (p ++ [0]) body with
    | ok bt =>
      simp only [effTy_of_check h, Except.toOption, Option.map_some, Annotate.check_eq s next]
      rfl
    | error r =>
      simp only [effTy_of_check h, Except.toOption, Option.map_none, tableAt_none]
      rfl
  -- both branches read the body's type
  | .matchCause body onValue onCause => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, Annotate.check_eq s body, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, Checker.check]
    cases h : Checker.check s env (p ++ [0]) body with
    | ok bt =>
      simp only [effTy_of_check h, Except.toOption, Option.map_some, Annotate.check_eq s onValue,
        Annotate.check_eq s onCause]
      rfl
    | error r =>
      simp only [effTy_of_check h, Except.toOption, Option.map_none, tableAt_none]
      rfl
  -- both arms read the scrutinee's type and what the decision binds from it
  | .select scrutinee d a0 a1 => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil, Checker.check]
    cases h : Checker.term? s env p scrutinee with
    | ok t =>
      simp only [termTy_of_term? h, Except.toOption, Option.bind_some, except_ok_bind]
      cases ha : d.arms t with
      | some arms =>
        simp only [Option.map_some, Annotate.check_eq s a0, Annotate.check_eq s a1]
        rfl
      | none =>
        simp only [Option.map_none, tableAt_none]
        rfl
    | error r =>
      simp only [termTy_of_term? h, Except.toOption, Option.bind_none, Option.map_none,
        tableAt_none]
      rfl
  -- the body reads the initial term's type
  | .iterate _ initial _ _ _ body => by
    rw [tableAt_eq_cons]
    simp only [Annotate.check, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil, Checker.check]
    cases h : Checker.term? s env p initial with
    | ok c0 =>
      simp only [termTy_of_term? h, Except.toOption, Option.map_some, Annotate.check_eq s body]
      rfl
    | error r =>
      simp only [termTy_of_term? h, Except.toOption, Option.map_none, tableAt_none]
      rfl

/-- `Annotate.check_eq` at a layer, which is typed closed. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.checkLayer_eq (s : Signature Op) (l : LayerTerm Op) (p : List Nat) :
    Annotate.checkLayer s p l =
      (tableAt s (some .closed) (.layer l) p, Checker.checkLayer s p l) :=
  match l with
  | .succeed _ _ | .ref _ => by
    rw [tableAt_eq_cons]
    rfl
  | .effect _ body | .effectDiscard body => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkLayer, Annotate.check_eq s body, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, List.append_nil]
    rfl
  | .provide a b | .provideMerge a b | .merge a b => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkLayer, Annotate.checkLayer_eq s a, Annotate.checkLayer_eq s b,
      nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, List.append_nil]
    rfl
  | .fresh inner | .orDie inner => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkLayer, Annotate.checkLayer_eq s inner, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, List.append_nil]
    rfl
  | .mergeAll layers => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkLayer, Annotate.checkLayers_eq s layers, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, List.append_nil]
    rfl

/-- `Annotate.check_eq` at a layer list. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.checkLayers_eq (s : Signature Op) (ls : LayerTerms Op) (p : List Nat) :
    Annotate.checkLayers s p ls =
      (tableAt s (some .closed) (.layers ls) p, Checker.checkLayers s p ls) :=
  match ls with
  | .nil => by
    rw [tableAt_eq_cons]
    rfl
  | .cons head tail => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkLayers, Annotate.checkLayer_eq s head, Annotate.checkLayers_eq s tail,
      nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, List.append_nil]
    rfl

/-- `Annotate.check_eq` at a statement. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.checkStmt_eq (s : Signature Op) (st : Stmt Op) (env : TyEnv) (inLoop : Bool)
    (p : List Nat) :
    Annotate.checkStmt s env inLoop p st =
      (tableAt s (some (.body env inLoop)) (.stmt st) p, Checker.checkStmt s env inLoop p st) :=
  match st with
  | .ret _ | .breakLoop => by
    rw [tableAt_eq_cons]
    rfl
  | .bindYield effect | .yieldDiscard effect => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkStmt, Annotate.check_eq s effect, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl
  | .ifElse _ thenB elseB => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkStmt, Annotate.checkStmts_eq s thenB, Annotate.checkStmts_eq s elseB,
      nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, NodeEnv.inLoop, List.append_nil]
    rfl
  | .whileTrue body => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkStmt, Annotate.checkStmts_eq s body, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl

/-- `Annotate.check_eq` at a statement list, at every `afterRet`: the entries do not read it.
The statements after a head read its type only after a `bindYield`; after every other head
they stand at the head's environment, whether the checker reaches them or not. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.checkStmts_eq (s : Signature Op) (ss : Stmts Op) (env : TyEnv) (inLoop : Bool)
    (afterRet : Option (List Nat)) (p : List Nat) :
    Annotate.checkStmts s env inLoop afterRet p ss =
      (tableAt s (some (.body env inLoop)) (.stmts ss) p,
        Checker.checkStmts s env inLoop afterRet p ss) :=
  match ss with
  | .nil => by
    rw [tableAt_eq_cons]
    rfl
  | .cons head rest => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkStmts, Annotate.checkStmt_eq s head, nodeAnswer, childTableAt,
      Checker.checkStmts]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, List.append_nil]
    generalize hx : Checker.checkStmt s env inLoop (p ++ [0]) head = x
    cases head with
    | bindYield e =>
      simp only [Node.childEnv, NodeEnv.tyEnv, NodeEnv.inLoop]
      cases hc : Checker.check s env (p ++ [0] ++ [0]) e with
      | ok t =>
        simp only [Checker.checkStmt, hc, except_ok_bind, except_pure] at hx
        subst hx
        simp only [effTy_of_check hc, Except.toOption, Option.map_some, StmtTy.fold,
          Annotate.checkStmts_eq s rest]
        rfl
      | error r =>
        simp only [Checker.checkStmt, hc, except_error_bind] at hx
        subst hx
        simp only [effTy_of_check hc, Except.toOption, Option.map_none, tableAt_none]
        rfl
    | yieldDiscard _ | ret _ | ifElse _ _ _ | whileTrue _ | breakLoop =>
      simp only [Node.childEnv, NodeEnv.tyEnv, NodeEnv.inLoop]
      cases x with
      | ok st =>
        cases st with
        | step g binds =>
          obtain rfl : binds = [] := Checker.checkStmt_step_binds (fun _ h => by cases h) hx
          simp only [StmtTy.fold, except_ok_bind, List.append_nil, Annotate.checkStmts_eq s rest]
          rfl
        | ret a =>
          simp only [StmtTy.fold, Annotate.checkStmts_eq s rest]
          rfl
        | pass =>
          simp only [StmtTy.fold, Annotate.checkStmts_eq s rest]
          rfl
      | error r =>
        simp only [Annotate.checkStmts_eq s rest]
        rfl

/-- `Annotate.check_eq` at a race's entrants. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.checkEffs_eq (s : Signature Op) (es : Effs Op) (env : TyEnv) (p : List Nat) :
    Annotate.checkEffs s env p es =
      (tableAt s (some (.env env)) (.effs es) p, Checker.checkEffs s env p es) :=
  match es with
  | .nil => by
    rw [tableAt_eq_cons]
    rfl
  | .cons head tail => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkEffs, Annotate.check_eq s head, Annotate.checkEffs_eq s tail,
      nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl

/-- `Annotate.check_eq` at a fiber action. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem Annotate.checkAction_eq (s : Signature Op) (a : ActionTerm Op) (env : TyEnv)
    (p : List Nat) :
    Annotate.checkAction s env p a =
      (tableAt s (some (.env env)) (.action a) p, Checker.checkAction s env p a) :=
  match a with
  | .runIn _ _ | .interrupt _ | .interruptScoped _ | .interruptAll _ _ | .awaitAll _
  | .awaitAllFailFast _ | .snapshotChildren | .awaitNewChildren _ | .setContext _ | .getContext
  | .getId | .closeScope _ _ | .getInterruptible => by
    rw [tableAt_eq_cons]
    rfl
  | .fork program _ | .forkIn program _ _ | .forkScoped program _ => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkAction, Annotate.check_eq s program, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl
  | .raceAll entrants => by
    rw [tableAt_eq_cons]
    simp only [Annotate.checkAction, Annotate.checkEffs_eq s entrants, nodeAnswer, childTableAt]
    conv in (occs := *) Node.child _ _ => all_goals whnf
    simp only [Option.bind_some, Node.childEnv, NodeEnv.tyEnv, List.append_nil]
    rfl

end

/-- **The one traversal answers the address table.** `annotate` checks each node once, and its
entries are the table's, in the table's order: the environment and the checker's answer at
every address of a program, and no environment where a step reads a refused sibling. The
pointer of the claim proposed as `annotate-table`; it implements the claim `address-table`,
whose specification is the table. Its consumers are the typed print (slice P2) and the
session's call instances.

It says nothing of the cost, and nothing past a refused read: there, as in the table, the
subtree is not reached. -/
@[semantics "initial-algebras-folds" (requirement := R14)]
theorem annotate_eq_table (s : Signature Op) (env0 : TyEnv) (p : Eff Op) :
    annotate s env0 p = table s env0 p := by
  rw [table_eq_tableAt, annotate, Annotate.check_eq]

end Effect4.Program
