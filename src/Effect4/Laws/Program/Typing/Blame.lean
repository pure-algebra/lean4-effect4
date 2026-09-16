import Effect4.Program.Typing.Blame

/-!
# Laws.Program.Typing.Blame — the projection is the checker's (DI-86)

`explain` answers `none` exactly when `effTy` answers, at every sort and every environment:
the located refusal is a projection of the one checker, and this law is what keeps it one.
Each arm unfolds both sides, splits every match on the same discriminants the checker
matches on, and closes with the children's laws.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Effect4.Program

variable {Op : Type}

/-- The checker's `do` chains end in `some`: their success is the last bound option's. -/
@[simp] theorem isSome_bind_some {α β : Type} (x : Option α) (f : α → β) :
    (x.bind fun r => some (f r)).isSome = x.isSome := by
  cases x <;> rfl

@[simp] theorem isSome_ite_some_none {α : Type} (c : Prop) [Decidable c] (x : α) :
    (if c then some x else none).isSome = decide c := by
  split <;> simp_all

/-- A bound option whose continuation always succeeds succeeds exactly when it does. -/
@[simp] theorem isSome_bind_of_forall {α β : Type} (x : Option α) (f : α → Option β)
    (h : ∀ a, (f a).isSome = true) : (x.bind f).isSome = x.isSome := by
  cases x <;> simp_all

@[simp] theorem isSome_of_not_none {α : Type} (x : Option α) (h : ¬ x = none) :
    x.isSome = true := by
  cases x <;> simp_all

/-- The generator answer join never refuses (part 4: the least upper bound). -/
@[simp] theorem GenTy.joinAnswer_isSome (a b : Option Ty) : (GenTy.joinAnswer a b).isSome = true := by
  unfold GenTy.joinAnswer
  split <;> simp [EffTy.joinAnswer]

@[simp] theorem GenTy.merge_isSome (a b : GenTy) : (GenTy.merge a b).isSome = true := by
  simp [GenTy.merge]

mutual
  theorem explainEff_none_iff (sig : Signature Op) (e : Eff Op) :
      ∀ env p, explainEff sig env p e = none ↔ (effTy sig env e).isSome := by
    match e with
  | .succeed v =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .fail e =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .failCause c =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .yieldError e =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .sync t =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .suspend b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .perform op r =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .bind a b =>
    intro env pth
    have ih_a := explainEff_none_iff sig a
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .gen ss =>
    intro env pth
    have ih_ss := explainStmts_none_iff sig ss
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .catchCause b h =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_h := explainEff_none_iff sig h
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .catchIf t b h =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_h := explainEff_none_iff sig h
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .matchCause b v c =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_v := explainEff_none_iff sig v
    have ih_c := explainEff_none_iff sig c
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .onExit b f =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    have ih_f := explainEff_none_iff sig f
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .exit b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .uninterruptible b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interruptible b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .branch t a b =>
    intro env pth
    have ih_a := explainEff_none_iff sig a
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .whileLoop i t s b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .yieldNow n =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .callback op r =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitFiber f m =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .withFiber a =>
    intro env pth
    have ih_a := explainAction_none_iff sig a
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .scoped b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .acquireRelease a r =>
    intro env pth
    have ih_a := explainEff_none_iff sig a
    have ih_r := explainEff_none_iff sig r
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provideLayer l i b =>
    intro env pth
    have ih_l := explainLayer_none_iff sig l
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .service k =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provideService k v b =>
    intro env pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural e

  theorem explainStmts_none_iff (sig : Signature Op) (ss : Stmts Op) :
      ∀ env inLoop p, explainStmts sig env inLoop p ss = none ↔ (stmtsTy sig env inLoop ss).isSome := by
    match ss with
    | .nil =>
      intro env inLoop pth
      simp [explainStmts, stmtsTy]
    | .cons (.bindYield effect) rest =>
      intro env inLoop pth
      have ih_effect := explainEff_none_iff sig effect
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons (.yieldDiscard effect) rest =>
      intro env inLoop pth
      have ih_effect := explainEff_none_iff sig effect
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons (.ret value) rest =>
      intro env inLoop pth
      cases rest <;> simp only [explainStmts, stmtsTy, termRefusal] <;> (repeat' split) <;> (try simp_all)
    | .cons (.ifElse test thenB elseB) rest =>
      intro env inLoop pth
      have ih_thenB := fun env => explainStmts_none_iff sig thenB env inLoop
      have ih_elseB := fun env => explainStmts_none_iff sig elseB env inLoop
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons (.whileTrue body) rest =>
      intro env inLoop pth
      have ih_body := fun env => explainStmts_none_iff sig body env true
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons .breakLoop rest =>
      intro env inLoop pth
      have ih_rest := fun env => explainStmts_none_iff sig rest env inLoop
      simp only [explainStmts, stmtsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural ss

  theorem explainEffs_none_iff (sig : Signature Op) (es : Effs Op) :
      ∀ env p, explainEffs sig env p es = none ↔ (effsTy sig env es).isSome := by
    match es with
    | .nil =>
      intro env pth
      simp [explainEffs, effsTy]
    | .cons head tail =>
      intro env pth
      have ih_head := explainEff_none_iff sig head
      have ih_tail := explainEffs_none_iff sig tail
      simp only [explainEffs, effsTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural es

  theorem explainAction_none_iff (sig : Signature Op) (a : ActionTerm Op) :
      ∀ env p, explainAction sig env p a = none ↔ (actionTy sig env a).isSome := by
    match a with
  | .fork p o =>
    intro env pth
    have ih_p := explainEff_none_iff sig p
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .forkIn p o s =>
    intro env pth
    have ih_p := explainEff_none_iff sig p
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .forkScoped p o =>
    intro env pth
    have ih_p := explainEff_none_iff sig p
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .runIn t s =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interrupt t =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interruptScoped t =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .interruptAll ts who =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitAll ts =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitAllFailFast ts =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .snapshotChildren =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .awaitNewChildren s =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .raceAll es =>
    intro env pth
    have ih_es := explainEffs_none_iff sig es
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .setContext c =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .getContext =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .getId =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .closeScope s e =>
    intro env pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural a

  theorem explainLayer_none_iff (sig : Signature Op) (l : LayerTerm Op) :
      ∀ p, explainLayer sig p l = none ↔ (layerTy sig l).isSome := by
    match l with
  | .succeed k v =>
    intro pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .effect k b =>
    intro pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .effectDiscard b =>
    intro pth
    have ih_b := explainEff_none_iff sig b
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provide s t =>
    intro pth
    have ih_s := explainLayer_none_iff sig s
    have ih_t := explainLayer_none_iff sig t
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .provideMerge s t =>
    intro pth
    have ih_s := explainLayer_none_iff sig s
    have ih_t := explainLayer_none_iff sig t
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .merge s t =>
    intro pth
    have ih_s := explainLayer_none_iff sig s
    have ih_t := explainLayer_none_iff sig t
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .fresh i =>
    intro pth
    have ih_i := explainLayer_none_iff sig i
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .orDie i =>
    intro pth
    have ih_i := explainLayer_none_iff sig i
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .ref t =>
    intro pth
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  | .mergeAll ls =>
    intro pth
    have ih_ls := explainLayers_none_iff sig ls
    simp only [explainEff, effTy, termRefusal, explainStmts, stmtsTy, explainEffs, effsTy, explainAction, actionTy, explainLayer, layerTy, explainLayers, layersTy]
    (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural l

  theorem explainLayers_none_iff (sig : Signature Op) (ls : LayerTerms Op) :
      ∀ p, explainLayers sig p ls = none ↔ (layersTy sig ls).isSome := by
    match ls with
    | .nil =>
      intro pth
      simp [explainLayers, layersTy]
    | .cons head .nil =>
      intro pth
      have ih_head := explainLayer_none_iff sig head
      simp only [explainLayers, layersTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
    | .cons head (.cons h2 t2) =>
      intro pth
      have ih_head := explainLayer_none_iff sig head
      have ih_tail := explainLayers_none_iff sig (.cons h2 t2)
      simp only [explainLayers, layersTy]
      (repeat' split) <;> simp_all [EffTy.joinAnswer]
  termination_by structural ls
end

/-- The law of the projection: `explain` refuses exactly when the checker does. -/
theorem explain_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    explain sig env e = none ↔ (effTy sig env e).isSome :=
  explainEff_none_iff sig e env []

/-- A refusal is where a program fails to type, and a typed program has no refusal. -/
theorem blame_none_iff (sig : Signature Op) (env : TyEnv) (e : Eff Op) :
    blame sig env e = none ↔ (effTy sig env e).isSome := by
  simp [blame, ← explain_none_iff]

end Effect4.Program
