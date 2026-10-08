module

public import Effect4.Program.Typing.Rules
public import Effect4.Program.Checker
public import Effect4.Program.ScopedOp
public import Effect4.Program.Definitions

/-!
# Program.Typing — the checker's answers, as projections of the one check

`Program/Checker.lean`'s `check sig env p e : Except TypeRefusal EffTy` is the checker. This
module names its success at the root, `effTy sig env e`, and the five siblings — the names the
proof graph and the application interface have always used — as definitions, with `typeOf`,
`typeOfProgram` and `WellTyped` over them, and the weakening law: inserting an unused
environment slot changes no success projection (`check_weaken`, at every path; `effTy_weaken`;
`typeOf_weaken`), at a signature that types an operation alike once its own term is weakened
(`Signature.WeakenNatural`). The rules the checker applies are `Typing/Rules.lean`. The hand recursion
that once defined `effTy` here, and the proof graph over it, were deleted on 2026-09-18 once
every consumer reached the fold (`docs/core/traversal-census.md` §7.8).
-/

@[expose] public section

namespace Effect4.Program

open Effect4 (ServiceKey)
open Effect4.Machine.Env (Requirement)
open Checker

variable {Op : Type}

/-! ### The success projections -/

/-- The type of a program under an environment: the check's success at the root. -/
def effTy (sig : Signature Op) (env : TyEnv) (e : Eff Op) : Option EffTy :=
  (check sig env [] e).toOption

/-- The signature of a closed layer term: the check's success at the root. -/
def layerTy (sig : Signature Op) (l : LayerTerm Op) : Option LayerTy :=
  (checkLayer sig [] l).toOption

/-- The signature of a `mergeAll` spine: the layers' signatures under the nonempty merge
(`Layer.ts:1652`, at least one). -/
def layersTy (sig : Signature Op) (ls : LayerTerms Op) : Option LayerTy :=
  (checkLayers sig [] ls).toOption.bind LayerTy.mergeNonempty

/-- A generator body's state, outside or inside a loop, not after a `return`. -/
def stmtsTy (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (b : Stmts Op) : Option GenTy :=
  (checkStmts sig env inLoop none [] b).toOption

/-- Race entrants' joined type. -/
def effsTy (sig : Signature Op) (env : TyEnv) (es : Effs Op) : Option EffTy :=
  (checkEffs sig env [] es).toOption

/-- A fiber action's type. -/
def actionTy (sig : Signature Op) (env : TyEnv) (a : ActionTerm Op) : Option EffTy :=
  (checkAction sig env [] a).toOption

/-- `typeOf` at the empty environment. Structural: a layer reference (`LayerTerm.ref`) types
as nothing here; `typeOfProgram` is the whole program's typing. -/
def typeOf (sig : Signature Op) (program : Eff Op) : Option EffTy := effTy sig [] program

/-- The type of a whole program, its layer references resolved (the host rows slice). The
checker tests one thing: the references are well formed (`Eff.layerRefsWF`, `Program/Refs.lean`:
every target a non-reference layer that precedes its reference). Then it expands the program
(`Eff.expandRefs`) and checks the expansion as a whole module (`Checker.checkModule`,
`Program/Definitions.lean`): a definition block at its root is checked with its bodies, and the
main program at the block's signature (decisions row 328). It answers `none` when the references
are not well formed. The expansion has no reference site (`expanded_refs_nil_of_wf`,
`Laws/Program/ReferenceExpansion.lean`), so the checker does not test for one (decisions row
273). A program with no references and no block is `typeOf` itself. -/
def typeOfProgram (sig : Signature Op) (program : Eff Op) : Option EffTy :=
  if program.layerRefsWF then (Checker.checkModule sig program.expandRefs).toOption else none

/-- A layer is well-typed when `layerTy` answers. -/
def WellTypedLayer (sig : Signature Op) (l : LayerTerm Op) : Prop :=
  (layerTy sig l).isSome = true

instance (sig : Signature Op) (l : LayerTerm Op) : Decidable (WellTypedLayer sig l) := by
  unfold WellTypedLayer; infer_instance

/-- A program is well-typed when `typeOf` answers. -/
def WellTyped (sig : Signature Op) (program : Eff Op) : Prop := (typeOf sig program).isSome

instance (sig : Signature Op) (program : Eff Op) : Decidable (WellTyped sig program) := by
  unfold WellTyped; infer_instance

/-! ### Inserting an environment slot

A refusal names the term it refuses, so what weakening preserves is the success projection:
at every path, the check of the shifted program under the widened environment succeeds exactly
as the check of the program under the original, at the same type. The proof unfolds the check
on both sides and pushes the projection through the connectives (`toOption_bind`, …); the
statement sort is handled by cases on the head, since a statement's type carries its syntax.

Weakening maps an operation's own term too (`ScopedOp.mapTerm`, state plan T3b). So the law
holds at a signature that types an operation alike once its term is weakened
(`Signature.WeakenNatural`): the same domain and the same row columns. -/

/-- A signature types an operation alike once its binder term is weakened: the same domain, the
same row columns (`Row.columns`), and the weakened binder term with the same templates
(`BinderTerm.weaken`). So the row check reads nothing the weakening moved but the term, which
is weakened with its environment. The premise of `check_weaken`. -/
def Signature.WeakenNatural [ScopedOp Op] (sig : Signature Op) : Prop :=
  ∀ cut op, sig.dom (ScopedOp.mapTerm (Term.weaken cut) op) = sig.dom op ∧
    (sig.rowOf (ScopedOp.mapTerm (Term.weaken cut) op)).columns = (sig.rowOf op).columns ∧
    sig.termOf (ScopedOp.mapTerm (Term.weaken cut) op) =
      (sig.termOf op).map (BinderTerm.weaken cut)

/-- An operation's term use survives an inserted slot: the weakened term at the widened
environment types as the term at the original (`termTy_weaken`, at `post ++ [A]`). A step of
`check_weaken`. -/
theorem Signature.termUse_weaken [ScopedOp Op] {sig : Signature Op} (hw : sig.WeakenNatural)
    (pre post : TyEnv) (inserted : Ty) (op : Op) :
    sig.termUse (pre ++ inserted :: post) (ScopedOp.mapTerm (Term.weaken pre.length) op) =
      sig.termUse (pre ++ post) op := by
  obtain ⟨-, -, hterm⟩ := hw pre.length op
  unfold Signature.termUse
  rw [hterm]
  cases sig.termOf op with
  | none => rfl
  | some b =>
    simp only [Option.map_some, BinderTerm.weaken, Option.some.injEq, TermUse.mk.injEq,
      true_and]
    funext A
    simpa only [List.append_assoc, List.cons_append] using
      termTy_weaken sig pre (post ++ [A]) inserted b.term

mutual
  theorem check_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
      (pre post : TyEnv) (inserted : Ty) (p : List Nat) (program : Eff Op) :
      (check sig (pre ++ inserted :: post) p (Eff.weaken pre.length program)).toOption =
        (check sig (pre ++ post) p program).toOption :=
    match program with
    | .awaitFiber _ mode => by
      cases mode <;> simp only [Eff.weaken, check, toOption_bind, toOption_pure, toOption_expect,
        toOption_term?, termTy_weaken]
    | .perform op _ => by
      obtain ⟨hdom, hcols, -⟩ := hw pre.length op
      simp only [Eff.weaken, check, toOption_bind, toOption_term?, termTy_weaken,
        apply_ite Except.toOption, toOption_throw, toOption_rowCheck, hdom, rowTy_columns hcols,
        Signature.termUse_weaken hw]
    | .succeed _ | .fail _ | .failCause _ | .sync _ | .suspend _
    | .bind _ _ | .gen _ | .catchCause _ _ | .catchIf _ _ _ | .matchCause _ _ _
    | .onExit _ _ | .exit _ | .uninterruptible _ | .interruptible _ | .yieldNow _
    | .withFiber _ | .scoped _ | .acquireRelease _ _
    | .provideLayer _ _ _ | .service _ | .provideService _ _ _ | .select _ _ _ _
    | .iterate _ _ _ _ _ _ | .restore _ _ | .defs _ _ _ => by
      simp only [Eff.weaken, check, toOption_bind, toOption_pure, toOption_throw, toOption_expect,
        toOption_term?, toOption_cause?, apply_ite Except.toOption, termTy_weaken, causeTy_weaken,
        catchIfError_weaken, List.append_assoc, List.cons_append, check_weaken sig hw,
        checkStmts_weaken sig hw, checkAction_weaken sig hw]

  theorem checkStmts_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
      (pre post : TyEnv) (inserted : Ty) (inLoop : Bool) (afterRet : Option (List Nat))
      (p : List Nat) (body : Stmts Op) :
      (checkStmts sig (pre ++ inserted :: post) inLoop afterRet p (Stmts.weaken pre.length body)).toOption =
        (checkStmts sig (pre ++ post) inLoop afterRet p body).toOption :=
    match body with
    | .nil => rfl
    | .cons head rest => by
      cases afterRet with
      | some _ => simp only [Stmts.weaken, checkStmts, toOption_throw]
      | none =>
        cases head <;> simp only [Stmts.weaken, Stmt.weaken, checkStmts, checkStmt,
          toOption_bind, toOption_pure, toOption_throw, toOption_term?,
          toOption_fold, StmtTy.fold.eq_1, StmtTy.fold.eq_2, StmtTy.fold.eq_3,
          apply_ite Except.toOption, Option.bind_some, Option.bind_assoc, termTy_weaken,
          List.append_assoc, List.cons_append, check_weaken sig hw, checkStmts_weaken sig hw]

  theorem checkEffs_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
      (pre post : TyEnv) (inserted : Ty) (p : List Nat) (entrants : Effs Op) :
      (checkEffs sig (pre ++ inserted :: post) p (Effs.weaken pre.length entrants)).toOption =
        (checkEffs sig (pre ++ post) p entrants).toOption :=
    match entrants with
    | .nil => rfl
    | .cons _ _ => by
      simp only [Effs.weaken, checkEffs, toOption_bind, toOption_pure, check_weaken sig hw,
        checkEffs_weaken sig hw]

  theorem checkAction_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
      (pre post : TyEnv) (inserted : Ty) (p : List Nat) (action : ActionTerm Op) :
      (checkAction sig (pre ++ inserted :: post) p (ActionTerm.weaken pre.length action)).toOption =
        (checkAction sig (pre ++ post) p action).toOption :=
    match action with
    | .interruptAll _ who => by
      cases who <;> simp only [ActionTerm.weaken, checkAction, Option.map, toOption_bind,
        toOption_pure, toOption_throw, toOption_expect, toOption_term?, apply_ite Except.toOption,
        termTy_weaken]
    | .fork _ _ | .forkIn _ _ _ | .forkScoped _ _ | .runIn _ _ | .interrupt _
    | .interruptScoped _ | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren
    | .awaitNewChildren _ | .raceAll _ | .setContext _ | .getContext | .getId
    | .closeScope _ _ | .getInterruptible => by
      simp only [ActionTerm.weaken, checkAction, toOption_bind, toOption_pure, toOption_throw,
        toOption_expect, toOption_term?, apply_ite Except.toOption, termTy_weaken,
        check_weaken sig hw, checkEffs_weaken sig hw]
end

/-- Inserting one slot preserves the typing result, including refusal. -/
theorem effTy_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
    (pre post : TyEnv) (inserted : Ty) (program : Eff Op) :
    effTy sig (pre ++ inserted :: post) (Eff.weaken pre.length program) =
      effTy sig (pre ++ post) program :=
  check_weaken sig hw pre post inserted [] program

theorem stmtsTy_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
    (pre post : TyEnv) (inserted : Ty) (inLoop : Bool) (body : Stmts Op) :
    stmtsTy sig (pre ++ inserted :: post) inLoop (Stmts.weaken pre.length body) =
      stmtsTy sig (pre ++ post) inLoop body :=
  checkStmts_weaken sig hw pre post inserted inLoop none [] body

theorem effsTy_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
    (pre post : TyEnv) (inserted : Ty) (entrants : Effs Op) :
    effsTy sig (pre ++ inserted :: post) (Effs.weaken pre.length entrants) =
      effsTy sig (pre ++ post) entrants :=
  checkEffs_weaken sig hw pre post inserted [] entrants

theorem actionTy_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
    (pre post : TyEnv) (inserted : Ty) (action : ActionTerm Op) :
    actionTy sig (pre ++ inserted :: post) (ActionTerm.weaken pre.length action) =
      actionTy sig (pre ++ post) action :=
  checkAction_weaken sig hw pre post inserted [] action

/-- A closed program may be placed under a new surrounding binder without changing its type.
The inserted slot is unused by the shifted program. -/
theorem typeOf_weaken [ScopedOp Op] (sig : Signature Op) (hw : sig.WeakenNatural)
    (inserted : Ty) (program : Eff Op) :
    effTy sig [inserted] (Eff.weaken 0 program) = typeOf sig program :=
  effTy_weaken sig hw [] [] inserted program

end Effect4.Program
