import Effect4.Laws.Program.Signature
import Effect4.Laws.Program.ReferenceTyping
import Effect4.Laws.Program.Typing.CheckSound

/-!
# Laws/Program/ExpandFix — an expansion round fixes every typed term

The reference expansion is a fold (`Eff.expandRound`, `Program/Refs.lean`) whose algebra is the
identity at every constructor but `ref`. The typing judgment (`HasTy` and its family,
`Typing/HasTy.lean`) has no rule for a reference, so the term of a derivation holds none, and one
round leaves it as it is (`hasTy_expandRound` and siblings, one recursion over derivations as
`hasTy_ext`'s). Through the checker's soundness and completeness: a checked layer is fixed by a
round (`checkLayer_expandRound`), and the checker's verdict does not read the path, which only
locates refusals (`checkLayer_path`).

Placement (AGENTS.md, Trust): concept initial-algebras-folds (`docs/core/semantics.md` §2.7: the
fold identity on the constructors a term uses) with residual-program-typing's admission; consumer
the layer family's reference hop (`Typed/LayerArm.lean`), which reads the target's check off the
site's.
-/

set_option autoImplicit false

namespace Effect4.Program

open Conform.Effect4.Typing

section ExpandFix

/-- A two-argument constructor over equal arguments. -/
private theorem congrArg₂ {α β γ : Sort _} (f : α → β → γ) {a a' : α} {b b' : β} (ha : a = a')
    (hb : b = b') : f a b = f a' b' :=
  congr (congrArg f ha) hb

variable {Op : Type} {sig : Signature Op} (orig : Node Op)

mutual
/-- **A typed program is fixed by an expansion round.** The round is a fold that is the identity at
every constructor but `ref` (`expandAlgebra`), and the typing judgment has no rule for a reference,
so a derivation's term holds none: each arm is the constructor over its children's fixed points. -/
theorem hasTy_expandRound :
    ∀ {env : TyEnv} {e : Eff Op} {t : EffTy}, HasTy sig env e t → Eff.expandRound orig e = e
  | _, _, _, .succeed _ => rfl
  | _, _, _, .fail _ _ => rfl
  | _, _, _, .failCause _ => rfl
  | _, _, _, .sync _ => rfl
  | _, _, _, .suspend hb => congrArg Eff.suspend (hasTy_expandRound hb)
  | _, _, _, .perform _ _ _ => rfl
  | _, _, _, .bind hf hr => congrArg₂ Eff.bind (hasTy_expandRound hf) (hasTy_expandRound hr)
  | _, _, _, .gen hb => congrArg Eff.gen (stmtsHasTy_expandRound hb)
  | _, _, _, .catchCause hb hh _ =>
    congrArg₂ Eff.catchCause (hasTy_expandRound hb) (hasTy_expandRound hh)
  | _, _, _, .catchIf hb _ _ hh _ =>
    congrArg₂ (Eff.catchIf _) (hasTy_expandRound hb) (hasTy_expandRound hh)
  | _, _, _, .select _ _ h0 h1 _ =>
    congrArg₂ (Eff.select _ _) (hasTy_expandRound h0) (hasTy_expandRound h1)
  | _, _, _, .matchCause hb hv hc _ => by
    show Eff.matchCause (Eff.expandRound orig _) (Eff.expandRound orig _)
      (Eff.expandRound orig _) = _
    rw [hasTy_expandRound hb, hasTy_expandRound hv, hasTy_expandRound hc]
  | _, _, _, .onExit hb hf => congrArg₂ Eff.onExit (hasTy_expandRound hb) (hasTy_expandRound hf)
  | _, _, _, .exit hb => congrArg Eff.exit (hasTy_expandRound hb)
  | _, _, _, .uninterruptible hb => congrArg Eff.uninterruptible (hasTy_expandRound hb)
  | _, _, _, .interruptible hb => congrArg Eff.interruptible (hasTy_expandRound hb)
  | _, _, _, .iterate _ _ _ hb _ _ _ _ =>
    congrArg (Eff.iterate _ _ _ _ _) (hasTy_expandRound hb)
  | _, _, _, .yieldNow _ => rfl
  | _, _, _, .awaitFiber_join _ _ => rfl
  | _, _, _, .awaitFiber_await _ _ => rfl
  | _, _, _, .withFiber ha => congrArg Eff.withFiber (actionHasTy_expandRound ha)
  | _, _, _, .scoped hb => congrArg Eff.scoped (hasTy_expandRound hb)
  | _, _, _, .acquireRelease ha hr _ =>
    congrArg₂ Eff.acquireRelease (hasTy_expandRound ha) (hasTy_expandRound hr)
  | _, _, _, .provideLayer _ hl hb => by
    show Eff.provideLayer (LayerTerm.expandRound orig _) _ (Eff.expandRound orig _) = _
    rw [layerHasTy_expandRound hl, hasTy_expandRound hb]
  | _, _, _, .service _ => rfl
  | _, _, _, .provideService _ _ _ hb =>
    congrArg (Eff.provideService _ _) (hasTy_expandRound hb)
  | _, _, _, .restore _ _ hb => congrArg (Eff.restore _) (hasTy_expandRound hb)

theorem stmtsHasTy_expandRound :
    ∀ {env : TyEnv} {inLoop : Bool} {ss : Stmts Op} {g : GenTy},
      StmtsHasTy sig env inLoop ss g → Stmts.expandRound orig ss = ss
  | _, _, _, _, .nil => rfl
  | _, _, _, _, .bindYield he hr => by
    show Stmts.cons (Stmt.bindYield (Eff.expandRound orig _)) (Stmts.expandRound orig _) = _
    rw [hasTy_expandRound he, stmtsHasTy_expandRound hr]
  | _, _, _, _, .yieldDiscard he hr => by
    show Stmts.cons (Stmt.yieldDiscard (Eff.expandRound orig _)) (Stmts.expandRound orig _) = _
    rw [hasTy_expandRound he, stmtsHasTy_expandRound hr]
  | _, _, _, _, .ret _ => rfl
  | _, _, _, _, .ifElse _ _ ha hb hr _ _ => by
    show Stmts.cons (Stmt.ifElse _ (Stmts.expandRound orig _) (Stmts.expandRound orig _))
      (Stmts.expandRound orig _) = _
    rw [stmtsHasTy_expandRound ha, stmtsHasTy_expandRound hb, stmtsHasTy_expandRound hr]
  | _, _, _, _, .whileTrue hb hr _ => by
    show Stmts.cons (Stmt.whileTrue (Stmts.expandRound orig _)) (Stmts.expandRound orig _) = _
    rw [stmtsHasTy_expandRound hb, stmtsHasTy_expandRound hr]
  | _, _, _, _, .breakLoop hr => by
    show Stmts.cons Stmt.breakLoop (Stmts.expandRound orig _) = _
    rw [stmtsHasTy_expandRound hr]

theorem effsHasTy_expandRound :
    ∀ {env : TyEnv} {es : Effs Op} {t : EffTy}, EffsHasTy sig env es t → Effs.expandRound orig es = es
  | _, _, _, .nil => rfl
  | _, _, _, .cons hh ht _ => congrArg₂ Effs.cons (hasTy_expandRound hh) (effsHasTy_expandRound ht)

theorem actionHasTy_expandRound :
    ∀ {env : TyEnv} {a : ActionTerm Op} {t : EffTy}, ActionHasTy sig env a t →
      ActionTerm.expandRound orig a = a
  | _, _, _, .fork _ hp => by
    show ActionTerm.fork (Eff.expandRound orig _) _ = _
    rw [hasTy_expandRound hp]
  | _, _, _, .forkIn _ hp _ _ => by
    show ActionTerm.forkIn (Eff.expandRound orig _) _ _ = _
    rw [hasTy_expandRound hp]
  | _, _, _, .forkScoped _ hp => by
    show ActionTerm.forkScoped (Eff.expandRound orig _) _ = _
    rw [hasTy_expandRound hp]
  | _, _, _, .runIn _ _ _ _ => rfl
  | _, _, _, .interrupt _ _ => rfl
  | _, _, _, .interruptScoped _ _ => rfl
  | _, _, _, .interruptAll_self _ _ _ => rfl
  | _, _, _, .interruptAll_by _ _ _ _ _ => rfl
  | _, _, _, .awaitAll _ _ _ => rfl
  | _, _, _, .awaitAllFailFast _ _ _ => rfl
  | _, _, _, .snapshotChildren => rfl
  | _, _, _, .awaitNewChildren _ _ => rfl
  | _, _, _, .raceAll he => congrArg ActionTerm.raceAll (effsHasTy_expandRound he)
  | _, _, _, .setContext _ _ => rfl
  | _, _, _, .getContext => rfl
  | _, _, _, .getId => rfl
  | _, _, _, .closeScope _ _ _ _ => rfl
  | _, _, _, .getInterruptible => rfl

theorem layerHasTy_expandRound :
    ∀ {l : LayerTerm Op} {s : LayerTy}, LayerHasTy sig l s → LayerTerm.expandRound orig l = l
  | _, _, .succeed _ _ _ => rfl
  | _, _, .effect hb _ _ => congrArg (LayerTerm.effect _) (hasTy_expandRound hb)
  | _, _, .effectDiscard hb => congrArg LayerTerm.effectDiscard (hasTy_expandRound hb)
  | _, _, .provide ha hb =>
    congrArg₂ LayerTerm.provide (layerHasTy_expandRound ha) (layerHasTy_expandRound hb)
  | _, _, .provideMerge ha hb =>
    congrArg₂ LayerTerm.provideMerge (layerHasTy_expandRound ha) (layerHasTy_expandRound hb)
  | _, _, .merge ha hb =>
    congrArg₂ LayerTerm.merge (layerHasTy_expandRound ha) (layerHasTy_expandRound hb)
  | _, _, .fresh hi => congrArg LayerTerm.fresh (layerHasTy_expandRound hi)
  | _, _, .orDie hi => congrArg LayerTerm.orDie (layerHasTy_expandRound hi)
  | _, _, .mergeAll hl => congrArg LayerTerm.mergeAll (layersHasTy_expandRound hl)

theorem layersHasTy_expandRound :
    ∀ {ls : LayerTerms Op} {l : LayerTy}, LayersHasTy sig ls l → LayerTerms.expandRound orig ls = ls
  | _, _, .one hl => by
    show LayerTerms.cons (LayerTerm.expandRound orig _) LayerTerms.nil = _
    rw [layerHasTy_expandRound hl]
  | _, _, .cons hl hr =>
    congrArg₂ LayerTerms.cons (layerHasTy_expandRound hl) (layersHasTy_expandRound hr)
end

/-- **A checked layer is fixed by an expansion round** (its derivation, `checkLayer_sound`). -/
theorem checkLayer_expandRound {p : List Nat} {l : LayerTerm Op} {lt : LayerTy}
    (h : Checker.checkLayer sig p l = .ok lt) : LayerTerm.expandRound orig l = l :=
  layerHasTy_expandRound orig (checkLayer_sound sig l p lt h)

/-- **The checker's verdict on a layer does not read the path**: the derivation is path-free
(`checkLayer_sound`), and the checker answers it at every path (`checkLayer_complete`). -/
theorem checkLayer_path {p : List Nat} {l : LayerTerm Op} {lt : LayerTy}
    (h : Checker.checkLayer sig p l = .ok lt) (p' : List Nat) : Checker.checkLayer sig p' l = .ok lt :=
  checkLayer_complete sig l lt (checkLayer_sound sig l p lt h) p'

end ExpandFix

/-! ## A layer's expansion commutes with its constructors -/

section LayerRounds

variable {Op : Type} (orig : Node Op)

private abbrev lrounds (xs : List Nat) (l : LayerTerm Op) : LayerTerm Op :=
  xs.foldl (fun acc _ => LayerTerm.expandRound orig acc) l

private abbrev erounds (xs : List Nat) (e : Eff Op) : Eff Op :=
  xs.foldl (fun acc _ => Eff.expandRound orig acc) e

/-- A constructor that commutes with one round commutes with every number of them: the rounds
are a fold, and `C` a homomorphism of the step (`List.foldl_hom`). -/
private theorem lrounds_one : ∀ (C : LayerTerm Op → LayerTerm Op),
    (∀ a, LayerTerm.expandRound orig (C a) = C (LayerTerm.expandRound orig a)) →
    ∀ (xs : List Nat) (a : LayerTerm Op), lrounds orig xs (C a) = C (lrounds orig xs a) :=
  fun C hC _ _ => List.foldl_hom C (fun x _ => hC x)

private theorem lrounds_two : ∀ (C : LayerTerm Op → LayerTerm Op → LayerTerm Op),
    (∀ a b, LayerTerm.expandRound orig (C a b) =
      C (LayerTerm.expandRound orig a) (LayerTerm.expandRound orig b)) →
    ∀ (xs : List Nat) (a b : LayerTerm Op),
      lrounds orig xs (C a b) = C (lrounds orig xs a) (lrounds orig xs b)
  | _, _, [], _, _ => rfl
  | C, hC, _ :: xs, a, b => by
    show lrounds orig xs (LayerTerm.expandRound orig (C a b)) =
      C (lrounds orig xs (LayerTerm.expandRound orig a)) (lrounds orig xs (LayerTerm.expandRound orig b))
    rw [hC]
    exact lrounds_two C hC xs _ _

/-- As `lrounds_one`, for a layer built from a program: the homomorphism crosses the two sorts. -/
private theorem lrounds_body : ∀ (C : Eff Op → LayerTerm Op),
    (∀ e, LayerTerm.expandRound orig (C e) = C (Eff.expandRound orig e)) →
    ∀ (xs : List Nat) (e : Eff Op), lrounds orig xs (C e) = C (erounds orig xs e) :=
  fun C hC _ _ => List.foldl_hom C (fun x _ => hC x)

private theorem erounds_provideLayer : ∀ (xs : List Nat) (l : LayerTerm Op) (i : Bool)
    (b : Eff Op),
    erounds orig xs (.provideLayer l i b) = .provideLayer (lrounds orig xs l) i (erounds orig xs b)
  | [], _, _, _ => rfl
  | _ :: xs, l, i, b => erounds_provideLayer xs (LayerTerm.expandRound orig l) i (Eff.expandRound orig b)

/-- `mergeAll` is a homomorphism from the spine's rounds to the layer's. -/
private theorem lrounds_mergeAll : ∀ (xs : List Nat) (ls : LayerTerms Op),
    lrounds orig xs (.mergeAll ls) =
      .mergeAll (xs.foldl (fun acc _ => LayerTerms.expandRound orig acc) ls) :=
  fun _ _ => List.foldl_hom LayerTerm.mergeAll (fun _ _ => rfl)

/-- A layer one round fixes is fixed by every number of rounds: the constant map out of `Unit`
is a homomorphism of the step exactly when the round fixes the layer (`List.foldl_hom`). -/
private theorem lrounds_fix : ∀ (l : LayerTerm Op), LayerTerm.expandRound orig l = l →
    ∀ (xs : List Nat), lrounds orig xs l = l :=
  fun l hl _ => List.foldl_hom (fun _ : Unit => l) (g₁ := fun _ _ => ()) (init := ()) (fun _ _ => hl)

end LayerRounds

variable {Op : Type} (root : Eff Op)

theorem Eff.expandIn_provideLayer (l : LayerTerm Op) (i : Bool) (b : Eff Op) :
    Eff.expandIn root (.provideLayer l i b) =
      .provideLayer (LayerTerm.expandIn root l) i (Eff.expandIn root b) :=
  erounds_provideLayer _ _ l i b

theorem LayerTerm.expandIn_fresh (inner : LayerTerm Op) :
    LayerTerm.expandIn root (.fresh inner) = .fresh (LayerTerm.expandIn root inner) :=
  lrounds_one _ LayerTerm.fresh (fun _ => rfl) _ inner

theorem LayerTerm.expandIn_orDie (inner : LayerTerm Op) :
    LayerTerm.expandIn root (.orDie inner) = .orDie (LayerTerm.expandIn root inner) :=
  lrounds_one _ LayerTerm.orDie (fun _ => rfl) _ inner

theorem LayerTerm.expandIn_provide (self that : LayerTerm Op) :
    LayerTerm.expandIn root (.provide self that) =
      .provide (LayerTerm.expandIn root self) (LayerTerm.expandIn root that) :=
  lrounds_two _ LayerTerm.provide (fun _ _ => rfl) _ self that

theorem LayerTerm.expandIn_provideMerge (self that : LayerTerm Op) :
    LayerTerm.expandIn root (.provideMerge self that) =
      .provideMerge (LayerTerm.expandIn root self) (LayerTerm.expandIn root that) :=
  lrounds_two _ LayerTerm.provideMerge (fun _ _ => rfl) _ self that

theorem LayerTerm.expandIn_merge (left right : LayerTerm Op) :
    LayerTerm.expandIn root (.merge left right) =
      .merge (LayerTerm.expandIn root left) (LayerTerm.expandIn root right) :=
  lrounds_two _ LayerTerm.merge (fun _ _ => rfl) _ left right

theorem LayerTerm.expandIn_effect (key : ServiceKey) (body : Eff Op) :
    LayerTerm.expandIn root (.effect key body) = .effect key (Eff.expandIn root body) :=
  lrounds_body _ (LayerTerm.effect key) (fun _ => rfl) _ body

theorem LayerTerm.expandIn_effectDiscard (body : Eff Op) :
    LayerTerm.expandIn root (.effectDiscard body) = .effectDiscard (Eff.expandIn root body) :=
  lrounds_body _ LayerTerm.effectDiscard (fun _ => rfl) _ body

/-- The rounds a `mergeAll`'s spine runs. -/
def LayerTerms.expandIn (ls : LayerTerms Op) : LayerTerms Op :=
  (List.range ((root.refSites []).length + 1)).foldl
    (fun acc _ => LayerTerms.expandRound (Node.eff root) acc) ls

private theorem lsrounds_cons : ∀ (xs : List Nat) (h : LayerTerm Op) (t : LayerTerms Op),
    xs.foldl (fun acc _ => LayerTerms.expandRound (Node.eff root) acc) (.cons h t) =
      .cons (xs.foldl (fun acc _ => LayerTerm.expandRound (Node.eff root) acc) h)
        (xs.foldl (fun acc _ => LayerTerms.expandRound (Node.eff root) acc) t)
  | [], _, _ => rfl
  | _ :: xs, h, t => lsrounds_cons xs (LayerTerm.expandRound (Node.eff root) h)
      (LayerTerms.expandRound (Node.eff root) t)

private theorem lsrounds_nil : ∀ (xs : List Nat),
    xs.foldl (fun acc _ => LayerTerms.expandRound (Node.eff root) acc) (.nil : LayerTerms Op) = .nil
  | [] => rfl
  | _ :: xs => lsrounds_nil xs

theorem LayerTerms.expandIn_cons (h : LayerTerm Op) (t : LayerTerms Op) :
    LayerTerms.expandIn root (.cons h t) =
      .cons (LayerTerm.expandIn root h) (LayerTerms.expandIn root t) :=
  lsrounds_cons root _ h t

theorem LayerTerms.expandIn_nil : LayerTerms.expandIn root (.nil : LayerTerms Op) = .nil :=
  lsrounds_nil root _

theorem LayerTerm.expandIn_mergeAll (ls : LayerTerms Op) :
    LayerTerm.expandIn root (.mergeAll ls) = .mergeAll (LayerTerms.expandIn root ls) :=
  lrounds_mergeAll _ _ ls

theorem LayerTerm.expandIn_succeed (key : ServiceKey) (value : Lit) :
    LayerTerm.expandIn root (.succeed key value) = .succeed key value :=
  lrounds_fix _ _ rfl _

end Effect4.Program
