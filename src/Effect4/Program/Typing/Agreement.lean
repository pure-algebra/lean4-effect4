import Effect4.Program.Checker
import Effect4.Program.Folds.Checker
import Effect4.Program.Typing.Terms
import Effect4.Program.Folds.TermTy

/-!
# Program.Typing.Agreement — the fold checker is the hand checker

`Checker.check sig env p e : Except TypeRefusal EffTy` succeeds exactly as `effTy sig env e`
does, one theorem per sort of the program's family by structural recursion (`check_eq`,
`checkLayer_eq`, …). This is the connector of `Program/Checker.lean`: every property of `effTy`
(`Typing/Sound.lean`, `Typing/Check.lean`) reaches the fold through it, and the callers move
across it. The refusal needs no agreement any more: `explain` *is* the check's refusal
(`Program/Checker.lean`, since the hand blame block was deleted on 2026-09-18), and the law of
the projection (DI-86, `explain_none_iff`) is the shape of `Except`. The file lives in the core
root because `Api.check` is total by that law.

The list sort is stated at its consumer: the layers' signatures under the nonempty merge are
`layersTy`'s result. `checkStmts` agrees under `afterRet := none`; under `some ret` it is the
empty tail a `return` demands (`checkStmts_afterRet`).

The last sections carry the connectors across: `effTy.eq_cata` states the hand checker as the
success of the fold of `check.alg` (`Program/Folds/Checker.lean`), and `termTy.eq_cata` the
term typer as the fold `argTy` (`Typing/Terms.lean`), which is what the census reads.
-/

namespace Effect4.Program

namespace Checker

variable {Op : Type}

open Effect4.Machine.Env (Requirement)

/-! ## The monad's laws, definitionally -/

theorem bind_ok {α β : Type} (a : α) (f : α → Except TypeRefusal β) : (Except.ok a >>= f) = f a := rfl
theorem bind_error {α β : Type} (r : TypeRefusal) (f : α → Except TypeRefusal β) :
    (Except.error r >>= f) = Except.error r := rfl
theorem pure_eq {α : Type} (a : α) : (pure a : Except TypeRefusal α) = Except.ok a := rfl
theorem throw_eq {α : Type} (r : TypeRefusal) : (throw r : Except TypeRefusal α) = Except.error r := rfl
theorem toOption_ok {α : Type} (a : α) : (Except.ok a : Except TypeRefusal α).toOption = some a := rfl
theorem toOption_error {α : Type} (r : TypeRefusal) :
    (Except.error r : Except TypeRefusal α).toOption = none := rfl
theorem refusal_ok {α : Type} (a : α) : refusal (Except.ok a) = none := rfl
theorem refusal_error {α : Type} (r : TypeRefusal) :
    refusal (Except.error r : Except TypeRefusal α) = some r := rfl

/-- The reductions every arm ends in: the monad's laws, the projections, the `Option` laws of
the hand blocks, the total join and merge, path normalisation, and the conditions. -/
local macro "check_step" : tactic => `(tactic| simp only [Checker.expect, Checker.term?, bind_ok, bind_error, pure_eq, throw_eq,
  toOption_ok, toOption_error, refusal_ok, refusal_error, Option.bind_eq_bind, Option.bind_some,
  Option.bind_none, Option.map_eq_map, Option.map_some, Option.map_none, Option.isSome_some,
  Option.isSome_none, GenTy.merge_eq, EffTy.joinAnswer_eq, List.append_assoc, List.cons_append,
  List.nil_append, List.append_nil, eq_self_iff_true, ↓reduceIte, Bool.false_eq_true, and_true,
  true_and])

/-- `check_step`, then both projections by reduction. -/
local macro "check_arm" : tactic => `(tactic| (check_step <;> constructor <;> rfl))

/-! ## The mode flag and the list sort -/

/-- After a `return` the tail must be empty. -/
theorem checkStmts_afterRet (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (ret p : List Nat) :
    (rest : Stmts Op) → checkStmts sig env inLoop (some ret) p rest =
      (match rest with
        | .nil => pure ⟨none, .never, Requirement.empty⟩
        | .cons _ _ => throw ⟨ret, .returnNotLast⟩)
  | .nil => rfl
  | .cons _ _ => rfl

/-- The signatures of a `cons` are a `cons`: never `ok []`. -/
theorem checkLayers_cons_ne_nil (sig : Signature Op) (p : List Nat) (next : LayerTerm Op)
    (tail : LayerTerms Op) : checkLayers sig p (.cons next tail) ≠ .ok [] := by
  rw [checkLayers.eq_2]
  cases checkLayer sig (p ++ [0]) next with
  | error r => exact nofun
  | ok h =>
    cases checkLayers sig (p ++ [1]) tail with
    | error r => exact nofun
    | ok t => exact nofun

/-- The nonempty merge is some. -/
theorem mergeNonempty_cons (l : LayerTy) :
    (ls : List LayerTy) → ∃ m, LayerTy.mergeNonempty (l :: ls) = some m
  | [] => ⟨l, rfl⟩
  | m :: rest =>
    let ⟨x, hx⟩ := mergeNonempty_cons m rest
    ⟨l.merge x, by simp only [LayerTy.mergeNonempty, hx, Option.map_some]⟩

/-! ## The agreement, one theorem per sort -/

mutual
theorem check_eq (sig : Signature Op) (env : TyEnv) (p : List Nat) : (e : Eff Op) →
    (check sig env p e).toOption = Program.effTy sig env e
  | .succeed value => by
    simp only [Checker.check, Program.effTy, term?]
    cases termTy sig env value <;> check_arm
  | .fail error => by
    simp only [Checker.check, Program.effTy, term?]
    cases termTy sig env error with
    | none => check_arm
    | some e => check_step; split <;> check_arm
  | .failCause cause => by
    simp only [Checker.check, Program.effTy]
    cases causeTy sig env cause <;> check_arm
  | .sync thunk => by
    simp only [Checker.check, Program.effTy, term?]
    cases termTy sig env thunk <;> check_arm
  | .suspend body => by
    have ih := check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, ← ih]
  | .perform op request => by
    simp only [Checker.check, Program.effTy, term?]
    cases termTy sig env request with
    | none => check_arm
    | some r =>
      check_step
      cases sig.dom op <;> cases Ty.sub r.normalize (sig.rowOf op).request.normalize <;> check_arm
  | .bind first rest => by
    have hf := check_eq sig env (p ++ [0]) first
    have hr := fun env => check_eq sig env (p ++ [1]) rest
    simp only [Checker.check, Program.effTy, ← hf,
      ← hr]
    cases check sig env (p ++ [0]) first with
    | error r => check_arm
    | ok f =>
      check_step
      cases check sig (env ++ [f.answer]) (p ++ [1]) rest <;> check_arm
  | .gen body => by
    have ih := checkStmts_eq sig env false (p ++ [0]) body
    simp only [Checker.check, Program.effTy, ← ih]
    cases checkStmts sig env false none (p ++ [0]) body <;> check_arm
  | .catchCause body handler => by
    have hb := check_eq sig env (p ++ [0]) body
    have hh := fun env => check_eq sig env (p ++ [1]) handler
    simp only [Checker.check, Program.effTy, ← hb,
      ← hh]
    cases check sig env (p ++ [0]) body with
    | error r => check_arm
    | ok b =>
      check_step
      cases check sig (env ++ [.causeOf b.error]) (p ++ [1]) handler <;> check_arm
  | .catchIf test body handler => by
    have hb := check_eq sig env (p ++ [0]) body
    have hh := fun env => check_eq sig env (p ++ [1]) handler
    simp only [Checker.check, Program.effTy, term?, ← hb,
      ← hh]
    cases check sig env (p ++ [0]) body with
    | error r => check_arm
    | ok b =>
      check_step
      cases termTy sig (env ++ [b.error]) test with
      | none => check_arm
      | some predicate =>
        check_step
        split
        · cases check sig (env ++ [b.error]) (p ++ [1]) handler <;> check_arm
        · check_arm
  | .select s d a0 a1 => by
    have h0 := fun env => check_eq sig env (p ++ [0]) a0
    have h1 := fun env => check_eq sig env (p ++ [1]) a1
    simp only [Checker.check, Program.effTy, term?,
      ← h0, ← h1]
    cases termTy sig env s with
    | none => check_arm
    | some t =>
      check_step
      cases d.arms t with
      | none => check_arm
      | some pair =>
        obtain ⟨e0, e1⟩ := pair
        check_step
        cases check sig (env ++ e0) (p ++ [0]) a0 with
        | error r => check_arm
        | ok t0 =>
          check_step
          cases check sig (env ++ e1) (p ++ [1]) a1 <;> check_arm
  | .matchCause body onValue onCause => by
    have hb := check_eq sig env (p ++ [0]) body
    have hv := fun env => check_eq sig env (p ++ [1]) onValue
    have hc := fun env => check_eq sig env (p ++ [2]) onCause
    simp only [Checker.check, Program.effTy, ← hb,
      ← hv, ← hc]
    cases check sig env (p ++ [0]) body with
    | error r => check_arm
    | ok b =>
      check_step
      cases check sig (env ++ [b.answer]) (p ++ [1]) onValue with
      | error r => check_arm
      | ok v =>
        check_step
        cases check sig (env ++ [.causeOf b.error]) (p ++ [2]) onCause <;> check_arm
  | .onExit body finalizer => by
    have hb := check_eq sig env (p ++ [0]) body
    have hf := fun env => check_eq sig env (p ++ [1]) finalizer
    simp only [Checker.check, Program.effTy, ← hb,
      ← hf]
    cases check sig env (p ++ [0]) body with
    | error r => check_arm
    | ok b =>
      check_step
      cases check sig (env ++ [.exitOf b.answer b.error]) (p ++ [1]) finalizer <;> check_arm
  | .exit body => by
    have ih := check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, ← ih]
    cases check sig env (p ++ [0]) body <;> check_arm
  | .uninterruptible body => by
    have ih := check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, ← ih]
  | .interruptible body => by
    have ih := check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, ← ih]
  | .iterate cursorTy initial test step result body => by
    have hb := fun env => check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, term?,
      ← hb]
    cases termTy sig env initial with
    | none => check_arm
    | some c0 =>
      check_step
      cases termTy sig (env ++ [cursorTy.getD c0]) test with
      | none => check_arm
      | some t =>
        check_step
        cases check sig (env ++ [cursorTy.getD c0]) (p ++ [0]) body with
        | error r => check_arm
        | ok b =>
          check_step
          cases termTy sig (env ++ [cursorTy.getD c0, b.answer]) step with
          | none => check_arm
          | some c1 =>
            check_step
            cases termTy sig (env ++ [cursorTy.getD c0]) result with
            | none => check_arm
            | some d =>
              check_step
              split
              · check_arm
              · split
                · check_arm
                · split <;> check_arm
  | .yieldNow _ => by
    simp only [Checker.check, Program.effTy]
    check_arm
  | .awaitFiber fiber mode => by
    simp only [Checker.check, Program.effTy, term?]
    cases termTy sig env fiber with
    | none => check_arm
    | some t =>
      check_step
      cases fiberTy t with
      | none => check_arm
      | some pair =>
        obtain ⟨value, error⟩ := pair
        cases mode <;> check_arm
  | .withFiber action => by
    have ih := checkAction_eq sig env (p ++ [0]) action
    simp only [Checker.check, Program.effTy, ← ih]
  | .scoped body => by
    have ih := check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, ← ih]
    cases check sig env (p ++ [0]) body <;> check_arm
  | .acquireRelease acquire release => by
    have ha := check_eq sig env (p ++ [0]) acquire
    have hr := fun env => check_eq sig env (p ++ [1]) release
    simp only [Checker.check, Program.effTy, ← ha,
      ← hr]
    cases check sig env (p ++ [0]) acquire with
    | error r => check_arm
    | ok a =>
      check_step
      cases check sig (env ++ [a.answer, .exitOf a.answer a.error]) (p ++ [1]) release <;> check_arm
  | .provideLayer layer _ body => by
    have hl := checkLayer_eq sig (p ++ [0]) layer
    have hb := check_eq sig env (p ++ [1]) body
    simp only [Checker.check, Program.effTy, ← hl, ← hb]
    cases checkLayer sig (p ++ [0]) layer with
    | error r => check_arm
    | ok l =>
      check_step
      cases check sig env (p ++ [1]) body <;> check_arm
  | .service key => by
    simp only [Checker.check, Program.effTy]
    cases sig.serviceTy key <;> check_arm
  | .provideService key value body => by
    have hb := check_eq sig env (p ++ [0]) body
    simp only [Checker.check, Program.effTy, term?, ← hb]
    cases sig.serviceTy key with
    | none => check_arm
    | some ty =>
      check_step
      cases termTy sig env value with
      | none => check_arm
      | some v =>
        check_step
        cases check sig env (p ++ [0]) body with
        | error r => check_arm
        | ok b =>
          check_step
          cases Ty.sub v.normalize ty.normalize <;> check_arm

theorem checkLayer_eq (sig : Signature Op) (p : List Nat) : (l : LayerTerm Op) →
    (checkLayer sig p l).toOption = Program.layerTy sig l
  | .succeed _ value => by
    simp only [Checker.checkLayer, Program.layerTy]
    cases litVal value <;> check_arm
  | .effect _ body => by
    have ih := check_eq sig [] (p ++ [0]) body
    simp only [Checker.checkLayer, Program.layerTy, ← ih]
    cases check sig [] (p ++ [0]) body <;> check_arm
  | .effectDiscard body => by
    have ih := check_eq sig [] (p ++ [0]) body
    simp only [Checker.checkLayer, Program.layerTy, ← ih]
    cases check sig [] (p ++ [0]) body <;> check_arm
  | .provide self that => by
    have hs := checkLayer_eq sig (p ++ [0]) self
    have ht := checkLayer_eq sig (p ++ [1]) that
    simp only [Checker.checkLayer, Program.layerTy, ← hs,
      ← ht]
    cases checkLayer sig (p ++ [0]) self with
    | error r => check_arm
    | ok s =>
      check_step
      cases checkLayer sig (p ++ [1]) that <;> check_arm
  | .provideMerge self that => by
    have hs := checkLayer_eq sig (p ++ [0]) self
    have ht := checkLayer_eq sig (p ++ [1]) that
    simp only [Checker.checkLayer, Program.layerTy, ← hs,
      ← ht]
    cases checkLayer sig (p ++ [0]) self with
    | error r => check_arm
    | ok s =>
      check_step
      cases checkLayer sig (p ++ [1]) that <;> check_arm
  | .merge left right => by
    have hl := checkLayer_eq sig (p ++ [0]) left
    have hr := checkLayer_eq sig (p ++ [1]) right
    simp only [Checker.checkLayer, Program.layerTy, ← hl,
      ← hr]
    cases checkLayer sig (p ++ [0]) left with
    | error r => check_arm
    | ok a =>
      check_step
      cases checkLayer sig (p ++ [1]) right <;> check_arm
  | .fresh inner => by
    have ih := checkLayer_eq sig (p ++ [0]) inner
    simp only [Checker.checkLayer, Program.layerTy, ← ih]
  | .orDie inner => by
    have ih := checkLayer_eq sig (p ++ [0]) inner
    simp only [Checker.checkLayer, Program.layerTy, ← ih]
    cases checkLayer sig (p ++ [0]) inner <;> check_arm
  | .ref _ => by
    simp only [Checker.checkLayer, Program.layerTy]
    check_arm
  | .mergeAll layers => by
    cases layers with
    | nil =>
      simp only [Checker.checkLayer, Checker.checkLayers, Program.layerTy, Program.layersTy]
      check_arm
    | cons next tail =>
      have ih := checkLayers_eq sig (p ++ [0]) (.cons next tail)
      have hne := checkLayers_cons_ne_nil sig (p ++ [0]) next tail
      simp only [Checker.checkLayer, Program.layerTy, ← ih]
      rcases hc : checkLayers sig (p ++ [0]) (.cons next tail) with r | (_ | ⟨t, ts⟩)
      · check_arm
      · exact absurd hc hne
      · obtain ⟨m, hm⟩ := mergeNonempty_cons t ts
        check_step
        simp only [hm]
        check_arm

theorem checkLayers_eq (sig : Signature Op) (p : List Nat) : (ls : LayerTerms Op) →
    (checkLayers sig p ls).toOption.bind LayerTy.mergeNonempty = Program.layersTy sig ls
  | .nil => rfl
  | .cons head .nil => by
    have hh := checkLayer_eq sig (p ++ [0]) head
    simp only [Checker.checkLayers, Program.layersTy, ← hh]
    cases checkLayer sig (p ++ [0]) head <;> check_arm
  | .cons head (.cons next tail) => by
    have hh := checkLayer_eq sig (p ++ [0]) head
    have ht := checkLayers_eq sig (p ++ [1]) (.cons next tail)
    have hne := checkLayers_cons_ne_nil sig (p ++ [1]) next tail
    rw [Checker.checkLayers.eq_2, Program.layersTy.eq_3 sig head (.cons next tail) nofun,
      ← hh, ← ht]
    cases checkLayer sig (p ++ [0]) head with
    | error r => check_arm
    | ok h =>
      check_step
      rcases hc : checkLayers sig (p ++ [1]) (.cons next tail) with r | (_ | ⟨t, ts⟩)
      · check_arm
      · exact absurd hc hne
      · obtain ⟨m, hm⟩ := mergeNonempty_cons t ts
        check_step
        simp only [LayerTy.mergeNonempty, hm]
        check_arm

theorem checkStmts_eq (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (p : List Nat) :
    (b : Stmts Op) →
      (checkStmts sig env inLoop none p b).toOption = Program.stmtsTy sig env inLoop b
  | .nil => rfl
  | .cons (.bindYield effect) rest => by
    have he := check_eq sig env (p ++ [0, 0]) effect
    have hr := fun env => checkStmts_eq sig env inLoop (p ++ [1]) rest
    simp only [Checker.checkStmts, Checker.checkStmt, Program.stmtsTy,
      List.append_assoc, List.cons_append, List.nil_append, ← he,
      ← hr]
    cases check sig env (p ++ [0, 0]) effect with
    | error r => check_arm
    | ok t =>
      check_step
      cases checkStmts sig (env ++ [t.answer]) inLoop none (p ++ [1]) rest <;> check_arm
  | .cons (.yieldDiscard effect) rest => by
    have he := check_eq sig env (p ++ [0, 0]) effect
    have hr := checkStmts_eq sig env inLoop (p ++ [1]) rest
    simp only [Checker.checkStmts, Checker.checkStmt, Program.stmtsTy,
      List.append_assoc, List.cons_append, List.nil_append, ← he, ← hr]
    cases check sig env (p ++ [0, 0]) effect with
    | error r => check_arm
    | ok t =>
      check_step
      cases checkStmts sig env inLoop none (p ++ [1]) rest <;> check_arm
  | .cons (.ret value) rest => by
    simp only [Checker.checkStmts, Checker.checkStmt, Program.stmtsTy,
      term?, checkStmts_afterRet]
    cases rest <;> cases termTy sig env value <;> check_arm
  | .cons (.ifElse test thenB elseB) rest => by
    have ha := checkStmts_eq sig env inLoop (p ++ [0, 0]) thenB
    have hb := checkStmts_eq sig env inLoop (p ++ [0, 1]) elseB
    have hr := checkStmts_eq sig env inLoop (p ++ [1]) rest
    simp only [Checker.checkStmts, Checker.checkStmt, Program.stmtsTy,
      term?, List.append_assoc, List.cons_append, List.nil_append, ← ha, ← hb, ← hr]
    cases termTy sig env test with
    | none => check_arm
    | some t =>
      check_step
      split
      · cases checkStmts sig env inLoop none (p ++ [0, 0]) thenB with
        | error r => check_arm
        | ok a =>
          check_step
          cases checkStmts sig env inLoop none (p ++ [0, 1]) elseB with
          | error r => check_arm
          | ok b =>
            check_step
            cases checkStmts sig env inLoop none (p ++ [1]) rest <;> check_arm
      · check_arm
  | .cons (.whileTrue body) rest => by
    have hb := checkStmts_eq sig env true (p ++ [0, 0]) body
    have hr := checkStmts_eq sig env inLoop (p ++ [1]) rest
    simp only [Checker.checkStmts, Checker.checkStmt, Program.stmtsTy,
      List.append_assoc, List.cons_append, List.nil_append, ← hb, ← hr]
    cases checkStmts sig env true none (p ++ [0, 0]) body with
    | error r => check_arm
    | ok b =>
      check_step
      cases checkStmts sig env inLoop none (p ++ [1]) rest <;> check_arm
  | .cons .breakLoop rest => by
    have hr := checkStmts_eq sig env inLoop (p ++ [1]) rest
    simp only [Checker.checkStmts, Checker.checkStmt, Program.stmtsTy,
      ← hr]
    cases inLoop <;> check_arm

theorem checkEffs_eq (sig : Signature Op) (env : TyEnv) (p : List Nat) : (es : Effs Op) →
    (checkEffs sig env p es).toOption = Program.effsTy sig env es
  | .nil => rfl
  | .cons head tail => by
    have hh := check_eq sig env (p ++ [0]) head
    have ht := checkEffs_eq sig env (p ++ [1]) tail
    simp only [Checker.checkEffs, Program.effsTy, ← hh, ← ht]
    cases check sig env (p ++ [0]) head with
    | error r => check_arm
    | ok h =>
      check_step
      cases checkEffs sig env (p ++ [1]) tail <;> check_arm

theorem checkAction_eq (sig : Signature Op) (env : TyEnv) (p : List Nat) : (a : ActionTerm Op) →
    (checkAction sig env p a).toOption = Program.actionTy sig env a
  | .fork program _ => by
    have ih := check_eq sig env (p ++ [0]) program
    simp only [Checker.checkAction, Program.actionTy, ← ih]
    cases check sig env (p ++ [0]) program <;> check_arm
  | .forkIn program _ scope => by
    have ih := check_eq sig env (p ++ [0]) program
    simp only [Checker.checkAction, Program.actionTy, term?, ← ih]
    cases check sig env (p ++ [0]) program with
    | error r => check_arm
    | ok t =>
      check_step
      cases termTy sig env scope with
      | none => check_arm
      | some s => check_step; split <;> check_arm
  | .forkScoped program _ => by
    have ih := check_eq sig env (p ++ [0]) program
    simp only [Checker.checkAction, Program.actionTy, ← ih]
    cases check sig env (p ++ [0]) program <;> check_arm
  | .runIn target scope => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env target with
    | none => check_arm
    | some t =>
      check_step
      cases fiberTy t with
      | none => check_arm
      | some pair =>
        check_step
        cases termTy sig env scope with
        | none => check_arm
        | some s => check_step; split <;> check_arm
  | .interrupt target => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env target with
    | none => check_arm
    | some t => check_step; cases fiberTy t <;> check_arm
  | .interruptScoped target => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env target with
    | none => check_arm
    | some t => check_step; cases fiberTy t <;> check_arm
  | .interruptAll targets interruptor => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env targets with
    | none => check_arm
    | some ts =>
      check_step
      cases ts with
      | list inner =>
        check_step
        cases fiberTy inner with
        | none => check_arm
        | some pair =>
          check_step
          cases interruptor with
          | none => check_arm
          | some who =>
            check_step
            cases termTy sig env who with
            | none => check_arm
            | some w => check_step; split <;> check_arm
      | _ => check_arm
  | .awaitAll targets => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env targets with
    | none => check_arm
    | some ts =>
      check_step
      cases ts with
      | list inner =>
        check_step
        cases fiberTy inner with
        | none => check_arm
        | some pair => obtain ⟨value, error⟩ := pair; check_arm
      | _ => check_arm
  | .awaitAllFailFast targets => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env targets with
    | none => check_arm
    | some ts =>
      check_step
      cases ts with
      | list inner =>
        check_step
        cases fiberTy inner with
        | none => check_arm
        | some pair => obtain ⟨value, error⟩ := pair; check_arm
      | _ => check_arm
  | .snapshotChildren => by
    simp only [Checker.checkAction, Program.actionTy]
    check_arm
  | .awaitNewChildren snapshot => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env snapshot with
    | none => check_arm
    | some s => check_step; split <;> check_arm
  | .raceAll entrants => by
    have ih := checkEffs_eq sig env (p ++ [0]) entrants
    simp only [Checker.checkAction, Program.actionTy, ← ih]
  | .setContext context => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env context with
    | none => check_arm
    | some c => check_step; split <;> check_arm
  | .getContext => by
    simp only [Checker.checkAction, Program.actionTy]
    check_arm
  | .getId => by
    simp only [Checker.checkAction, Program.actionTy]
    check_arm
  | .closeScope scope exit => by
    simp only [Checker.checkAction, Program.actionTy, term?]
    cases termTy sig env scope with
    | none => check_arm
    | some s =>
      check_step
      cases termTy sig env exit with
      | none => check_arm
      | some e =>
        check_step
        cases e <;> check_step
        split <;> check_arm
end

/-! ## The whole program, and the projection law -/

/-- `typeOf` is the success of the check at the root. -/
theorem typeOf_eq (sig : Signature Op) (program : Eff Op) :
    (check sig [] [] program).toOption = typeOf sig program := check_eq sig [] [] program

/-- `explain` is the refusal of the check at the root, by definition. -/
theorem explain_eq (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    refusal (check sig env [] e) = explain sig env e := rfl

/-- A check is `ok` or it is `error`: its refusal is `none` exactly when its success is
`some`. Every `*_none_iff` below is this, through the agreement. -/
theorem refusal_none_iff {α : Type} (x : Except TypeRefusal α) :
    refusal x = none ↔ x.toOption.isSome := by
  cases x <;> simp only [refusal, Except.toOption, Option.isSome, reduceCtorEq,
    Bool.false_eq_true, iff_self]

end Checker

/-! ## The law of the projection (DI-86)

`explain` answers `none` exactly when `effTy` answers: the located refusal is the check's, by
definition, and a check is `ok` or it is `error`. Once a mutual induction following every arm
of two hand blocks (`Blame.lean`, before 2026-09-18). `Api.check` is total by it. -/

open Checker

/-- The law of the projection: `explain` refuses exactly when the checker does. -/
theorem explain_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    explain sig env e = none ↔ (effTy sig env e).isSome := by
  rw [← check_eq sig env [] e]
  exact refusal_none_iff _

/-- A refusal is where a program fails to type, and a typed program has no refusal. -/
theorem blame_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    blame sig env e = none ↔ (effTy sig env e).isSome := by
  simp [blame, ← explain_none_iff]

namespace Checker

/-! ## The hand checker as the fold -/

/-- `effTy` is the success of the fold of `check.alg`, at any path. -/
theorem _root_.Effect4.Program.effTy.eq_cata (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (e : Eff Op) : Program.effTy sig env e = (cata_eff (check.alg sig) e env p).toOption :=
  (check_eq sig env p e).symm.trans (congrArg Except.toOption (check.eq_cata sig env p e))

theorem _root_.Effect4.Program.layerTy.eq_cata (sig : Signature Op) (p : List Nat) (l : LayerTerm Op) :
    Program.layerTy sig l = (cata_layer (check.alg sig) l p).toOption :=
  (checkLayer_eq sig p l).symm.trans (congrArg Except.toOption (checkLayer.eq_cata sig p l))

/-- `layersTy` is the nonempty merge of the fold's list of signatures. -/
theorem _root_.Effect4.Program.layersTy.eq_cata (sig : Signature Op) (p : List Nat)
    (ls : LayerTerms Op) :
    Program.layersTy sig ls = (cata_layers (check.alg sig) ls p).toOption.bind LayerTy.mergeNonempty :=
  (checkLayers_eq sig p ls).symm.trans
    (congrArg (fun x : Except TypeRefusal (List LayerTy) => x.toOption.bind LayerTy.mergeNonempty)
      (checkLayers.eq_cata sig p ls))

/-- `stmtsTy` is the fold under `afterRet := none`. -/
theorem _root_.Effect4.Program.stmtsTy.eq_cata (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (p : List Nat) (b : Stmts Op) :
    Program.stmtsTy sig env inLoop b = (cata_stmts (check.alg sig) b env inLoop none p).toOption :=
  (checkStmts_eq sig env inLoop p b).symm.trans
    (congrArg Except.toOption (checkStmts.eq_cata sig env inLoop none p b))

theorem _root_.Effect4.Program.effsTy.eq_cata (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (es : Effs Op) : Program.effsTy sig env es = (cata_effs (check.alg sig) es env p).toOption :=
  (checkEffs_eq sig env p es).symm.trans (congrArg Except.toOption (checkEffs.eq_cata sig env p es))

theorem _root_.Effect4.Program.actionTy.eq_cata (sig : Signature Op) (env : TyEnv) (p : List Nat)
    (a : ActionTerm Op) :
    Program.actionTy sig env a = (cata_action (check.alg sig) a env p).toOption :=
  (checkAction_eq sig env p a).symm.trans
    (congrArg Except.toOption (checkAction.eq_cata sig env p a))

end Checker

/-! ## The term typer -/

namespace Checker

mutual
theorem argTy_eq (sig : Signature Op) (env : TyEnv) (const : Bool) :
    (t : Term) → Checker.argTy sig env const t = Program.argTy sig env const t
  | .var _ => rfl
  | .lit _ => rfl
  | .app atom args => by
    simp only [Checker.argTy, Program.argTy, Program.termTy,
      argsTy_eq sig env (sig.constAtom atom) args]

theorem argsTy_eq (sig : Signature Op) (env : TyEnv) (const : Bool) :
    (ts : Terms) → Checker.argsTy sig env const ts = Program.termsTy sig env const ts
  | .nil => rfl
  | .cons head tail => by
    rw [Program.termsTy_cons, Checker.argsTy.eq_2, argTy_eq sig env const head,
      argsTy_eq sig env const tail]
    rfl
end

/-- `termTy` is the fold at `false`: outside a const-generic atom the literal rule is `Lit.ty`. -/
theorem termTy_eq (sig : Signature Op) (env : TyEnv) :
    (t : Term) → Checker.argTy sig env false t = Program.termTy sig env t
  | .var _ => rfl
  | .lit _ => by simp only [Checker.argTy, Program.termTy, litArgTy_false]
  | .app atom args => by
    simp only [Checker.argTy, Program.termTy, argsTy_eq sig env (sig.constAtom atom) args]

theorem _root_.Effect4.Program.termTy.eq_cata (sig : Signature Op) (env : TyEnv) (t : Term) :
    Program.termTy sig env t = cata_term (argTy.alg sig env) t false :=
  (termTy_eq sig env t).symm.trans (argTy.eq_cata sig env false t)

theorem _root_.Effect4.Program.termsTy.eq_cata (sig : Signature Op) (env : TyEnv) (const : Bool)
    (ts : Terms) : Program.termsTy sig env const ts = cata_terms (argTy.alg sig env) ts const :=
  (argsTy_eq sig env const ts).symm.trans (argsTy.eq_cata sig env const ts)

end Checker

end Effect4.Program
