import Effect4.Program.Typing.Rules
import Effect4.Program.Checker

/-!
# Program.Typing — the checker's answers, as projections of the one check

`Program/Checker.lean`'s `check sig env p e : Except TypeRefusal EffTy` is the checker. This
module names its success at the root, `effTy sig env e`, and the five siblings — the names the
proof graph and the application interface have always used — as definitions, with `typeOf`,
`typeOfProgram` and `WellTyped` over them, and the weakening law: inserting an unused
environment slot changes no success projection (`check_weaken`, at every path; `effTy_weaken`;
`typeOf_weaken`). The rules the checker applies are `Typing/Rules.lean`. The hand recursion
that once defined `effTy` here, and the proof graph over it, were deleted on 2026-09-18 once
every consumer reached the fold (`docs/core/traversal-census.md` §7.8).
-/

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

/-- The type of a whole program, its layer references resolved (the host rows slice): when
the references are well formed (`Eff.layerRefsWF`, `Program/Refs.lean`: every target a
non-reference layer that precedes its reference) the program is expanded to its
reference-free twin (`Eff.expandRefs`) and typed structurally; otherwise `none`. A program
with no references is `typeOf` itself. -/
def typeOfProgram (sig : Signature Op) (program : Eff Op) : Option EffTy :=
  if program.layerRefsWF && (program.expandRefs.refSites []).isEmpty then
    typeOf sig program.expandRefs
  else none

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
statement sort is handled by cases on the head, since a statement's type carries its syntax. -/

mutual
  theorem check_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (p : List Nat)
      (program : Eff Op) :
      (check sig (pre ++ inserted :: post) p (Eff.weaken pre.length program)).toOption =
        (check sig (pre ++ post) p program).toOption :=
    match program with
    | .awaitFiber _ mode => by
      cases mode <;> simp only [Eff.weaken, check, toOption_bind, toOption_pure, toOption_expect,
        toOption_term?, termTy_weaken]
    | .succeed _ | .fail _ | .failCause _ | .sync _ | .suspend _
    | .perform _ _ | .bind _ _ | .gen _ | .catchCause _ _ | .catchIf _ _ _ | .matchCause _ _ _
    | .onExit _ _ | .exit _ | .uninterruptible _ | .interruptible _ | .yieldNow _
    | .withFiber _ | .scoped _ | .acquireRelease _ _
    | .provideLayer _ _ _ | .service _ | .provideService _ _ _ | .select _ _ _ _
    | .iterate _ _ _ _ _ _ => by
      simp only [Eff.weaken, check, toOption_bind, toOption_pure, toOption_throw, toOption_expect,
        toOption_term?, apply_ite Except.toOption, termTy_weaken, causeTy_weaken,
        catchIfError_weaken, List.append_assoc, List.cons_append, check_weaken,
        checkStmts_weaken, checkAction_weaken]

  theorem checkStmts_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (inLoop : Bool) (afterRet : Option (List Nat)) (p : List Nat) (body : Stmts Op) :
      (checkStmts sig (pre ++ inserted :: post) inLoop afterRet p (Stmts.weaken pre.length body)).toOption =
        (checkStmts sig (pre ++ post) inLoop afterRet p body).toOption :=
    match body with
    | .nil => rfl
    | .cons head rest => by
      cases afterRet with
      | some _ => simp only [Stmts.weaken, checkStmts, toOption_throw]
      | none =>
        cases head <;> simp only [Stmts.weaken, Stmt.weaken, checkStmts, checkStmt,
          toOption_bind, toOption_pure, toOption_throw, toOption_expect, toOption_term?,
          toOption_fold, StmtTy.fold.eq_1, StmtTy.fold.eq_2, StmtTy.fold.eq_3,
          apply_ite Except.toOption, Option.bind_some, Option.bind_assoc, termTy_weaken,
          List.append_assoc, List.cons_append, check_weaken, checkStmts_weaken]

  theorem checkEffs_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (p : List Nat)
      (entrants : Effs Op) :
      (checkEffs sig (pre ++ inserted :: post) p (Effs.weaken pre.length entrants)).toOption =
        (checkEffs sig (pre ++ post) p entrants).toOption :=
    match entrants with
    | .nil => rfl
    | .cons _ _ => by
      simp only [Effs.weaken, checkEffs, toOption_bind, toOption_pure, check_weaken,
        checkEffs_weaken]

  theorem checkAction_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
      (p : List Nat) (action : ActionTerm Op) :
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
    | .closeScope _ _ => by
      simp only [ActionTerm.weaken, checkAction, toOption_bind, toOption_pure, toOption_throw,
        toOption_expect, toOption_term?, apply_ite Except.toOption, termTy_weaken, check_weaken,
        checkEffs_weaken]
end

/-- Inserting one slot preserves the typing result, including refusal. -/
theorem effTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (program : Eff Op) :
    effTy sig (pre ++ inserted :: post) (Eff.weaken pre.length program) =
      effTy sig (pre ++ post) program :=
  check_weaken sig pre post inserted [] program

theorem stmtsTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (inLoop : Bool)
    (body : Stmts Op) :
    stmtsTy sig (pre ++ inserted :: post) inLoop (Stmts.weaken pre.length body) =
      stmtsTy sig (pre ++ post) inLoop body :=
  checkStmts_weaken sig pre post inserted inLoop none [] body

theorem effsTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty) (entrants : Effs Op) :
    effsTy sig (pre ++ inserted :: post) (Effs.weaken pre.length entrants) =
      effsTy sig (pre ++ post) entrants :=
  checkEffs_weaken sig pre post inserted [] entrants

theorem actionTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
    (action : ActionTerm Op) :
    actionTy sig (pre ++ inserted :: post) (ActionTerm.weaken pre.length action) =
      actionTy sig (pre ++ post) action :=
  checkAction_weaken sig pre post inserted [] action

/-- A closed program may be placed under a new surrounding binder without changing its type.
The inserted slot is unused by the shifted program. -/
theorem typeOf_weaken (sig : Signature Op) (inserted : Ty) (program : Eff Op) :
    effTy sig [inserted] (Eff.weaken 0 program) = typeOf sig program :=
  effTy_weaken sig [] [] inserted program

end Effect4.Program
