import Effect4.Program.Checker
import Effect4.Program.Folds.Checker
import Aesop

/-!
# Laws.Program.Typing.Checker — the fold checker agrees with the hand checker

`Checker.effTy sig env e = effTy sig env e`, one theorem per sort of the program's family, by
structural recursion over it. This is the connector of `Program/Checker.lean`: every property
of `effTy` (`Typing/Sound.lean`, `Typing/Check.lean`) reaches the fold checker through it, and
the callers move across it.

The list sort is stated at its consumer: the layers' signatures under the nonempty merge are
`layersTy`'s result. `stmtsTy` agrees under `afterRet := false`; under `true` it is the empty
tail a `return` demands (`stmtsTy_afterRet`).

The last section carries the connectors across: `effTy.eq_cata` states the hand checker as the
fold of `Checker.effTy.alg` (`Program/Folds/Checker.lean`), which is what the census reads.
-/

namespace Effect4.Program.Checker

variable {Op : Type}

open Effect4.Machine.Env (Requirement)

/-- After a `return` the tail must be empty. -/
theorem stmtsTy_afterRet (sig : Signature Op) (env : TyEnv) (inLoop : Bool) :
    (rest : Stmts Op) → Checker.stmtsTy sig env inLoop true rest =
      (match rest with | .nil => some ⟨none, .never, Requirement.empty⟩ | .cons _ _ => none)
  | .nil => rfl
  | .cons _ _ => rfl

/-- The signatures of a `cons` are a `cons`: never `some []`. -/
theorem layersTy_cons_ne_nil (sig : Signature Op) (next : LayerTerm Op) (tail : LayerTerms Op) :
    Checker.layersTy sig (.cons next tail) ≠ some [] := by
  rw [Checker.layersTy.eq_2]
  cases Checker.layerTy sig next with
  | none => exact nofun
  | some h =>
    cases Checker.layersTy sig tail with
    | none => exact nofun
    | some t => exact nofun

mutual
theorem effTy_eq (sig : Signature Op) (env : TyEnv) :
    (e : Eff Op) → Checker.effTy sig env e = Program.effTy sig env e
  | .succeed _ => by simp only [Checker.effTy, Program.effTy]
  | .fail _ => by simp only [Checker.effTy, Program.effTy]
  | .failCause _ => by simp only [Checker.effTy, Program.effTy]
  | .sync _ => by simp only [Checker.effTy, Program.effTy]
  | .suspend body => by simp only [Checker.effTy, Program.effTy, effTy_eq sig env body]
  | .perform _ _ => by simp only [Checker.effTy, Program.effTy]
  | .bind first rest => by
    have ih := fun env => effTy_eq sig env rest
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env first, ih]
  | .gen body => by simp only [Checker.effTy, Program.effTy, stmtsTy_eq sig env false body]
  | .catchCause body handler => by
    have ih := fun env => effTy_eq sig env handler
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env body, ih]
  | .catchIf test body handler => by
    have ih := fun env => effTy_eq sig env handler
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env body, ih]
  | .select s d a0 a1 => by
    have ih0 := fun env => effTy_eq sig env a0
    have ih1 := fun env => effTy_eq sig env a1
    simp only [Checker.effTy, Program.effTy, ih0, ih1]
  | .matchCause body onValue onCause => by
    have ihv := fun env => effTy_eq sig env onValue
    have ihc := fun env => effTy_eq sig env onCause
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env body, ihv, ihc]
  | .onExit body finalizer => by
    have ih := fun env => effTy_eq sig env finalizer
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env body, ih]
  | .exit body => by simp only [Checker.effTy, Program.effTy, effTy_eq sig env body]
  | .uninterruptible body => by simp only [Checker.effTy, Program.effTy, effTy_eq sig env body]
  | .interruptible body => by simp only [Checker.effTy, Program.effTy, effTy_eq sig env body]
  | .iterate _ _ _ _ _ body => by
    have ih := fun env => effTy_eq sig env body
    simp only [Checker.effTy, Program.effTy, ih]
  | .yieldNow _ => by simp only [Checker.effTy, Program.effTy]
  | .awaitFiber _ _ => rfl
  | .withFiber action => by simp only [Checker.effTy, Program.effTy, actionTy_eq sig env action]
  | .scoped body => by simp only [Checker.effTy, Program.effTy, effTy_eq sig env body]
  | .acquireRelease acquire release => by
    have ih := fun env => effTy_eq sig env release
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env acquire, ih]
  | .provideLayer layer _ body => by
    simp only [Checker.effTy, Program.effTy, layerTy_eq sig layer, effTy_eq sig env body]
  | .service _ => by simp only [Checker.effTy, Program.effTy]
  | .provideService _ _ body => by
    simp only [Checker.effTy, Program.effTy, effTy_eq sig env body]

theorem layerTy_eq (sig : Signature Op) :
    (l : LayerTerm Op) → Checker.layerTy sig l = Program.layerTy sig l
  | .succeed _ _ => by simp only [Checker.layerTy, Program.layerTy]
  | .effect _ body => by simp only [Checker.layerTy, Program.layerTy, effTy_eq sig [] body]
  | .effectDiscard body => by simp only [Checker.layerTy, Program.layerTy, effTy_eq sig [] body]
  | .provide self that => by
    simp only [Checker.layerTy, Program.layerTy, layerTy_eq sig self, layerTy_eq sig that]
  | .provideMerge self that => by
    simp only [Checker.layerTy, Program.layerTy, layerTy_eq sig self, layerTy_eq sig that]
  | .merge left right => by
    simp only [Checker.layerTy, Program.layerTy, layerTy_eq sig left, layerTy_eq sig right]
  | .fresh inner => by simp only [Checker.layerTy, Program.layerTy, layerTy_eq sig inner]
  | .orDie inner => by simp only [Checker.layerTy, Program.layerTy, layerTy_eq sig inner]
  | .ref _ => by simp only [Checker.layerTy, Program.layerTy]
  | .mergeAll layers => by simp only [Checker.layerTy, Program.layerTy, layersTy_eq sig layers]

/-- The layers' signatures under the nonempty merge are `layersTy`'s result. -/
theorem layersTy_eq (sig : Signature Op) :
    (ls : LayerTerms Op) →
      (Checker.layersTy sig ls).bind LayerTy.mergeNonempty = Program.layersTy sig ls
  | .nil => rfl
  | .cons head .nil => by
    rw [Checker.layersTy.eq_2, Program.layersTy.eq_2, layerTy_eq sig head]
    cases Program.layerTy sig head <;> rfl
  | .cons head (.cons next tail) => by
    have iht := layersTy_eq sig (.cons next tail)
    have hne := layersTy_cons_ne_nil sig next tail
    rw [Checker.layersTy.eq_2, Program.layersTy.eq_3 sig head (.cons next tail) nofun,
      layerTy_eq sig head, ← iht]
    rcases hc : Checker.layersTy sig (.cons next tail) with _ | (_ | ⟨t, ts⟩)
    · cases Program.layerTy sig head <;> rfl
    · exact absurd hc hne
    · cases Program.layerTy sig head with
      | none => rfl
      | some h =>
        simp only [Option.bind_eq_bind, Option.bind_some, LayerTy.mergeNonempty]
        cases LayerTy.mergeNonempty (t :: ts) <;> rfl

theorem stmtsTy_eq (sig : Signature Op) (env : TyEnv) (inLoop : Bool) :
    (b : Stmts Op) → Checker.stmtsTy sig env inLoop false b = Program.stmtsTy sig env inLoop b
  | .nil => by simp only [Checker.stmtsTy, Program.stmtsTy]
  | .cons (.bindYield effect) rest => by
    have ih := fun env => stmtsTy_eq sig env inLoop rest
    simp only [Checker.stmtsTy, Program.stmtsTy, Checker.stmtTy, Option.bind_eq_bind,
      effTy_eq sig env effect, Bool.false_eq_true, ↓reduceIte]
    cases Program.effTy sig env effect with
    | none => rfl
    | some t =>
      simp only [Option.bind_some, ih, GenTy.merge, GenTy.joinAnswer, Option.bind_eq_bind]
  | .cons (.yieldDiscard effect) rest => by
    have ih := stmtsTy_eq sig env inLoop rest
    simp only [Checker.stmtsTy, Program.stmtsTy, Checker.stmtTy, Option.bind_eq_bind,
      effTy_eq sig env effect, Bool.false_eq_true, ↓reduceIte]
    cases Program.effTy sig env effect with
    | none => rfl
    | some t =>
      simp only [Option.bind_some, List.append_nil, ih, GenTy.merge, GenTy.joinAnswer,
        Option.bind_eq_bind]
  | .cons (.ret value) rest => by
    simp only [Checker.stmtsTy, Program.stmtsTy, Checker.stmtTy, Option.bind_eq_bind,
      Option.map_eq_map, stmtsTy_afterRet, Bool.false_eq_true, ↓reduceIte]
    cases rest <;> cases termTy sig env value <;> rfl
  | .cons (.ifElse test thenB elseB) rest => by
    have iha := stmtsTy_eq sig env inLoop thenB
    have ihb := stmtsTy_eq sig env inLoop elseB
    have ihr := stmtsTy_eq sig env inLoop rest
    simp only [Checker.stmtsTy, Program.stmtsTy, Checker.stmtTy, Option.bind_eq_bind, iha, ihb,
      Bool.false_eq_true, ↓reduceIte]
    cases termTy sig env test with
    | none => rfl
    | some t =>
      simp only [Option.bind_some]
      split
      · cases Program.stmtsTy sig env inLoop thenB with
        | none => rfl
        | some a =>
          simp only [Option.bind_some]
          cases Program.stmtsTy sig env inLoop elseB with
          | none => rfl
          | some b =>
            simp only [Option.bind_some]
            cases GenTy.merge a b with
            | none => cases Program.stmtsTy sig env inLoop rest <;> rfl
            | some ab => simp only [Option.bind_some, List.append_nil, ihr]
      · rfl
  | .cons (.whileTrue body) rest => by
    have ihb := stmtsTy_eq sig env true body
    have ihr := stmtsTy_eq sig env inLoop rest
    simp only [Checker.stmtsTy, Program.stmtsTy, Checker.stmtTy, Option.bind_eq_bind, ihb,
      Bool.false_eq_true, ↓reduceIte]
    cases Program.stmtsTy sig env true body with
    | none => rfl
    | some b => simp only [Option.bind_some, List.append_nil, ihr]
  | .cons .breakLoop rest => by
    have ihr := stmtsTy_eq sig env inLoop rest
    cases inLoop <;> simp only [Checker.stmtsTy, Program.stmtsTy, Checker.stmtTy,
      Option.bind_eq_bind, Option.bind_some, Option.bind_none, ihr, Bool.false_eq_true,
      ↓reduceIte]

theorem effsTy_eq (sig : Signature Op) (env : TyEnv) :
    (es : Effs Op) → Checker.effsTy sig env es = Program.effsTy sig env es
  | .nil => by simp only [Checker.effsTy, Program.effsTy]
  | .cons head tail => by
    simp only [Checker.effsTy, Program.effsTy, effTy_eq sig env head, effsTy_eq sig env tail]

theorem actionTy_eq (sig : Signature Op) (env : TyEnv) :
    (a : ActionTerm Op) → Checker.actionTy sig env a = Program.actionTy sig env a
  | .fork program _ => by simp only [Checker.actionTy, Program.actionTy, effTy_eq sig env program]
  | .forkIn program _ _ => by
    simp only [Checker.actionTy, Program.actionTy, effTy_eq sig env program]
  | .forkScoped program _ => by
    simp only [Checker.actionTy, Program.actionTy, effTy_eq sig env program]
  | .runIn _ _ => by simp only [Checker.actionTy, Program.actionTy]
  | .interrupt _ => by simp only [Checker.actionTy, Program.actionTy]
  | .interruptScoped _ => by simp only [Checker.actionTy, Program.actionTy]
  | .interruptAll _ _ => rfl
  | .awaitAll _ => rfl
  | .awaitAllFailFast _ => rfl
  | .snapshotChildren => by simp only [Checker.actionTy, Program.actionTy]
  | .awaitNewChildren _ => by simp only [Checker.actionTy, Program.actionTy]
  | .raceAll entrants => by
    simp only [Checker.actionTy, Program.actionTy, effsTy_eq sig env entrants]
  | .setContext _ => by simp only [Checker.actionTy, Program.actionTy]
  | .getContext => by simp only [Checker.actionTy, Program.actionTy]
  | .getId => by simp only [Checker.actionTy, Program.actionTy]
  | .closeScope _ _ => rfl
end

/-- `typeOf` through the fold checker. -/
theorem typeOf_eq (sig : Signature Op) (program : Eff Op) :
    Checker.effTy sig [] program = typeOf sig program := effTy_eq sig [] program

/-! ## The hand checker as the fold -/

/-- `effTy` is the fold of `Checker.effTy.alg`, through the agreement. -/
theorem _root_.Effect4.Program.effTy.eq_cata (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    Program.effTy sig env e = cata_eff (Checker.effTy.alg sig) e env :=
  (effTy_eq sig env e).symm.trans (Checker.effTy.eq_cata sig env e)

theorem _root_.Effect4.Program.layerTy.eq_cata (sig : Signature Op) (l : LayerTerm Op) :
    Program.layerTy sig l = cata_layer (Checker.effTy.alg sig) l :=
  (layerTy_eq sig l).symm.trans (Checker.layerTy.eq_cata sig l)

/-- `layersTy` is the nonempty merge of the fold's list of signatures. -/
theorem _root_.Effect4.Program.layersTy.eq_cata (sig : Signature Op) (ls : LayerTerms Op) :
    Program.layersTy sig ls = (cata_layers (Checker.effTy.alg sig) ls).bind LayerTy.mergeNonempty :=
  (layersTy_eq sig ls).symm.trans
    (congrArg (·.bind LayerTy.mergeNonempty) (Checker.layersTy.eq_cata sig ls))

/-- `stmtsTy` is the fold under `afterRet := false`. -/
theorem _root_.Effect4.Program.stmtsTy.eq_cata (sig : Signature Op) (env : TyEnv) (inLoop : Bool)
    (b : Stmts Op) :
    Program.stmtsTy sig env inLoop b = cata_stmts (Checker.effTy.alg sig) b env inLoop false :=
  (stmtsTy_eq sig env inLoop b).symm.trans (Checker.stmtsTy.eq_cata sig env inLoop false b)

theorem _root_.Effect4.Program.effsTy.eq_cata (sig : Signature Op) (env : TyEnv) (es : Effs Op) :
    Program.effsTy sig env es = cata_effs (Checker.effTy.alg sig) es env :=
  (effsTy_eq sig env es).symm.trans (Checker.effsTy.eq_cata sig env es)

theorem _root_.Effect4.Program.actionTy.eq_cata (sig : Signature Op) (env : TyEnv)
    (a : ActionTerm Op) :
    Program.actionTy sig env a = cata_action (Checker.effTy.alg sig) a env :=
  (actionTy_eq sig env a).symm.trans (Checker.actionTy.eq_cata sig env a)

end Effect4.Program.Checker
