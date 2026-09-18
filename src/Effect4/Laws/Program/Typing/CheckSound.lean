import Effect4.Laws.Program.Typing.HasTy
import Effect4.Laws.Program.Typing.CheckInversion

/-!
# Laws.Program.Typing.CheckSound — the fold checker and the rules agree, at every path

Two mutual blocks of six theorems over the program's family, for the fold checker
`Checker.check` (`Program/Checker.lean`), the shape of `Sound.lean`'s for the hand checker:

* **soundness** — what the checker accepts, the rules derive:
  `check sig env p e = .ok t → HasTy sig env e t`, and the five siblings;
* **completeness** — what the rules derive, the checker accepts, at the same type and **at
  every path**: `HasTy sig env e t → check sig env p e = .ok t`, and the five siblings.

The path is universal on both sides, so the success projection is independent of it
(`check_toOption`): an `ok` at one path derives a judgment, which completeness returns at any
other. That corollary is what lets the hand checker become a projection of the fold at the
empty path without a second structural induction.

The list sort is stated with its nonempty merge: `checkLayers` answers the list of signatures
and `LayersHasTy` their merge.
-/

namespace Conform.Effect4.Typing

open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Program.Checker
open _root_.Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-! ## Soundness: what the checker accepts, the rules derive -/

mutual

theorem check_sound (sig : Signature Op) (e : Eff Op) :
    ∀ (env : TyEnv) (p : List Nat) (t : EffTy), check sig env p e = .ok t → HasTy sig env e t := by
  cases e with
  | succeed value =>
    intro env p t h
    obtain ⟨ty, hty, rfl⟩ := inv_succeed sig env p value t h
    exact .succeed hty
  | select s d a0 a1 =>
    intro env p t h
    obtain ⟨ty, arms, t0, t1, hs, harms, h0, h1, rfl⟩ := inv_select sig env p s d a0 a1 t h
    exact .select hs harms (check_sound sig a0 _ _ t0 h0) (check_sound sig a1 _ _ t1 h1)
      (EffTy.joinAnswer_eq _ _)
  | fail error =>
    intro env p t h
    obtain ⟨ty, hty, herr, rfl⟩ := inv_fail sig env p error t h
    exact .fail hty herr
  | failCause cause =>
    intro env p t h
    obtain ⟨ty, hty, rfl⟩ := inv_failCause sig env p cause t h
    exact .failCause hty
  | sync thunk =>
    intro env p t h
    obtain ⟨ty, hty, rfl⟩ := inv_sync sig env p thunk t h
    exact .sync hty
  | suspend body =>
    intro env p t h
    exact .suspend (check_sound sig body env _ t (inv_suspend sig env p body t h))
  | perform op request =>
    intro env p t h
    obtain ⟨requestTy, hdom, hreq, heq, rfl⟩ := inv_perform sig env p op request t h
    exact .perform hdom hreq heq
  | bind first rest =>
    intro env p t h
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind sig env p first rest t h
    exact .bind (check_sound sig first env _ f hf) (check_sound sig rest _ _ r hr)
  | gen body =>
    intro env p t h
    obtain ⟨g, hg, rfl⟩ := inv_gen sig env p body t h
    exact .gen (checkStmts_sound sig body env false _ g hg)
  | catchCause body handler =>
    intro env p t h
    obtain ⟨b, hh, hb, hhh, rfl⟩ := inv_catchCause sig env p body handler t h
    exact .catchCause (check_sound sig body env _ b hb) (check_sound sig handler _ _ hh hhh)
      (EffTy.joinAnswer_eq _ _)
  | catchIf test body handler =>
    intro env p t h
    obtain ⟨b, hh, hb, ht, hhh, rfl⟩ := inv_catchIf sig env p test body handler t h
    exact .catchIf (check_sound sig body env _ b hb) ht (check_sound sig handler _ _ hh hhh)
      (EffTy.joinAnswer_eq _ _)
  | matchCause body onValue onCause =>
    intro env p t h
    obtain ⟨b, v, c, hb, hv, hc, rfl⟩ := inv_matchCause sig env p body onValue onCause t h
    exact .matchCause (check_sound sig body env _ b hb) (check_sound sig onValue _ _ v hv)
      (check_sound sig onCause _ _ c hc) (EffTy.joinAnswer_eq _ _)
  | onExit body finalizer =>
    intro env p t h
    obtain ⟨b, f, hb, hf, rfl⟩ := inv_onExit sig env p body finalizer t h
    exact .onExit (check_sound sig body env _ b hb) (check_sound sig finalizer _ _ f hf)
  | exit body =>
    intro env p t h
    obtain ⟨b, hb, rfl⟩ := inv_exit sig env p body t h
    exact .exit (check_sound sig body env _ b hb)
  | uninterruptible body =>
    intro env p t h
    exact .uninterruptible (check_sound sig body env _ t (inv_uninterruptible sig env p body t h))
  | interruptible body =>
    intro env p t h
    exact .interruptible (check_sound sig body env _ t (inv_interruptible sig env p body t h))
  | iterate cursor initial test step result body =>
    intro env p t h
    obtain ⟨c0, c1, d, b, hinit, htest, hbody, hstep, hresult, hsub0, hsub1, rfl⟩ :=
      inv_iterate sig env p cursor initial test step result body t h
    exact .iterate hinit htest (check_sound sig body _ _ b hbody) hstep hresult hsub0 hsub1
  | yieldNow priority =>
    intro env p t h
    obtain rfl := inv_yieldNow sig env p priority t h
    exact .yieldNow priority
  | awaitFiber fiber mode =>
    intro env p t h
    cases mode with
    | joinEffect =>
      obtain ⟨handle, pair, hterm, hfib, rfl⟩ := inv_awaitFiber_join sig env p fiber t h
      exact .awaitFiber_join hterm hfib
    | awaitValue =>
      obtain ⟨handle, pair, hterm, hfib, rfl⟩ := inv_awaitFiber_await sig env p fiber t h
      exact .awaitFiber_await hterm hfib
  | withFiber action =>
    intro env p t h
    exact .withFiber (checkAction_sound sig action env _ t (inv_withFiber sig env p action t h))
  | «scoped» body =>
    intro env p t h
    obtain ⟨b, hb, rfl⟩ := inv_scoped sig env p body t h
    exact HasTy.scoped (check_sound sig body env _ b hb)
  | acquireRelease acquire release =>
    intro env p t h
    obtain ⟨a, r, ha, hr, rfl⟩ := inv_acquireRelease sig env p acquire release t h
    exact .acquireRelease (check_sound sig acquire env _ a ha) (check_sound sig release _ _ r hr)
  | provideLayer layer isLocal body =>
    intro env p t h
    obtain ⟨l, b, hl, hb, rfl⟩ := inv_provideLayer sig env p layer isLocal body t h
    exact .provideLayer isLocal (checkLayer_sound sig layer _ l hl) (check_sound sig body env _ b hb)
  | service key =>
    intro env p t h
    obtain ⟨ty, hty, rfl⟩ := inv_service sig env p key t h
    exact .service hty
  | provideService key value body =>
    intro env p t h
    obtain ⟨ty, valueTy, b, hty, hval, heq, hb, rfl⟩ :=
      inv_provideService sig env p key value body t h
    exact .provideService hty hval heq (check_sound sig body env _ b hb)
termination_by structural e

theorem checkStmts_sound (sig : Signature Op) (body : Stmts Op) :
    ∀ (env : TyEnv) (inLoop : Bool) (p : List Nat) (g : GenTy),
      checkStmts sig env inLoop none p body = .ok g → StmtsHasTy sig env inLoop body g := by
  cases body with
  | nil =>
    intro env inLoop p g h
    obtain rfl := inv_stmts_nil sig env inLoop p g h
    exact .nil
  | cons head tail =>
    cases head with
    | bindYield effect =>
      intro env inLoop p g h
      obtain ⟨t, r, ht, hr, rfl⟩ := inv_stmts_bindYield sig env inLoop p effect tail g h
      exact .bindYield (check_sound sig effect env _ t ht) (checkStmts_sound sig tail _ inLoop _ r hr)
    | yieldDiscard effect =>
      intro env inLoop p g h
      obtain ⟨t, r, ht, hr, rfl⟩ := inv_stmts_yieldDiscard sig env inLoop p effect tail g h
      exact .yieldDiscard (check_sound sig effect env _ t ht)
        (checkStmts_sound sig tail env inLoop _ r hr)
    | ret value =>
      cases tail with
      | nil =>
        intro env inLoop p g h
        obtain ⟨ty, hty, rfl⟩ := inv_stmts_ret sig env inLoop p value g h
        exact .ret hty
      | cons next rest =>
        intro env inLoop p g h
        exact (inv_stmts_ret_cons sig env inLoop p value next rest g h).elim
    | ifElse test thenB elseB =>
      intro env inLoop p g h
      obtain ⟨htest, a, b, r, ha, hb, hr, rfl⟩ :=
        inv_stmts_ifElse sig env inLoop p test thenB elseB tail g h
      exact .ifElse htest (checkStmts_sound sig thenB env inLoop _ a ha)
        (checkStmts_sound sig elseB env inLoop _ b hb) (checkStmts_sound sig tail env inLoop _ r hr)
        (GenTy.merge_eq _ _) (GenTy.merge_eq _ _)
    | whileTrue loopBody =>
      intro env inLoop p g h
      obtain ⟨b, r, hb, hr, rfl⟩ := inv_stmts_whileTrue sig env inLoop p loopBody tail g h
      exact .whileTrue (checkStmts_sound sig loopBody env true _ b hb)
        (checkStmts_sound sig tail env inLoop _ r hr) (GenTy.merge_eq _ _)
    | breakLoop =>
      intro env inLoop p g h
      obtain ⟨hflag, hrest⟩ := inv_stmts_breakLoop sig env inLoop p tail g h
      subst hflag
      exact .breakLoop (checkStmts_sound sig tail env true _ g hrest)
termination_by structural body

theorem checkEffs_sound (sig : Signature Op) (entrants : Effs Op) :
    ∀ (env : TyEnv) (p : List Nat) (t : EffTy), checkEffs sig env p entrants = .ok t →
      EffsHasTy sig env entrants t := by
  cases entrants with
  | nil =>
    intro env p t h
    obtain rfl := inv_effs_nil sig env p t h
    exact .nil
  | cons head tail =>
    intro env p t h
    obtain ⟨hh, r, hhd, hr, rfl⟩ := inv_effs_cons sig env p head tail t h
    exact .cons (check_sound sig head env _ hh hhd) (checkEffs_sound sig tail env _ r hr)
      (EffTy.joinAnswer_eq _ _)
termination_by structural entrants

theorem checkAction_sound (sig : Signature Op) (action : ActionTerm Op) :
    ∀ (env : TyEnv) (p : List Nat) (t : EffTy), checkAction sig env p action = .ok t →
      ActionHasTy sig env action t := by
  cases action with
  | fork program options =>
    intro env p t h
    obtain ⟨q, hq, rfl⟩ := inv_action_fork sig env p program options t h
    exact .fork options (check_sound sig program env _ q hq)
  | forkIn program options scope =>
    intro env p t h
    obtain ⟨q, hq, hs, rfl⟩ := inv_action_forkIn sig env p program options scope t h
    exact .forkIn options (check_sound sig program env _ q hq) hs
  | forkScoped program options =>
    intro env p t h
    obtain ⟨q, hq, rfl⟩ := inv_action_forkScoped sig env p program options t h
    exact .forkScoped options (check_sound sig program env _ q hq)
  | runIn target scope =>
    intro env p t h
    obtain ⟨handle, pair, ht, hf, hs, rfl⟩ := inv_action_runIn sig env p target scope t h
    exact .runIn ht hf hs
  | interrupt target =>
    intro env p t h
    obtain ⟨handle, pair, ht, hf, rfl⟩ := inv_action_interrupt sig env p target t h
    exact .interrupt ht hf
  | interruptScoped target =>
    intro env p t h
    obtain ⟨handle, pair, ht, hf, rfl⟩ := inv_action_interruptScoped sig env p target t h
    exact .interruptScoped ht hf
  | interruptAll targets who =>
    intro env p t h
    cases who with
    | none =>
      obtain ⟨inner, pair, ht, hf, rfl⟩ := inv_action_interruptAll_self sig env p targets t h
      exact .interruptAll_self ht hf
    | some w =>
      obtain ⟨inner, pair, ht, hf, hw, rfl⟩ :=
        inv_action_interruptAll_by sig env p targets w t h
      exact .interruptAll_by ht hf hw
  | awaitAll targets =>
    intro env p t h
    obtain ⟨inner, pair, ht, hf, rfl⟩ := inv_action_awaitAll sig env p targets t h
    exact .awaitAll ht hf
  | awaitAllFailFast targets =>
    intro env p t h
    obtain ⟨inner, pair, ht, hf, rfl⟩ := inv_action_awaitAllFailFast sig env p targets t h
    exact .awaitAllFailFast ht hf
  | snapshotChildren =>
    intro env p t h
    obtain rfl := inv_action_snapshotChildren sig env p t h
    exact .snapshotChildren
  | awaitNewChildren snapshot =>
    intro env p t h
    obtain ⟨hs, rfl⟩ := inv_action_awaitNewChildren sig env p snapshot t h
    exact .awaitNewChildren hs
  | raceAll entrants =>
    intro env p t h
    exact .raceAll (checkEffs_sound sig entrants env _ t (inv_action_raceAll sig env p entrants t h))
  | setContext context =>
    intro env p t h
    obtain ⟨hc, rfl⟩ := inv_action_setContext sig env p context t h
    exact .setContext hc
  | getContext =>
    intro env p t h
    obtain rfl := inv_action_getContext sig env p t h
    exact .getContext
  | getId =>
    intro env p t h
    obtain rfl := inv_action_getId sig env p t h
    exact .getId
  | closeScope scope exitTerm =>
    intro env p t h
    obtain ⟨pair, hs, he, rfl⟩ := inv_action_closeScope sig env p scope exitTerm t h
    exact .closeScope hs he
termination_by structural action

theorem checkLayer_sound (sig : Signature Op) (layer : LayerTerm Op) :
    ∀ (p : List Nat) (s : LayerTy), checkLayer sig p layer = .ok s → LayerHasTy sig layer s := by
  cases layer with
  | succeed key value =>
    intro p s h
    obtain ⟨v, hv, rfl⟩ := inv_layer_succeed sig p key value s h
    exact .succeed hv
  | effect key body =>
    intro p s h
    obtain ⟨t, ht, rfl⟩ := inv_layer_effect sig p key body s h
    exact .effect (check_sound sig body [] _ t ht)
  | effectDiscard body =>
    intro p s h
    obtain ⟨t, ht, rfl⟩ := inv_layer_effectDiscard sig p body s h
    exact .effectDiscard (check_sound sig body [] _ t ht)
  | provide self that =>
    intro p s h
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_layer_provide sig p self that s h
    exact .provide (checkLayer_sound sig self _ a ha) (checkLayer_sound sig that _ b hb)
  | provideMerge self that =>
    intro p s h
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_layer_provideMerge sig p self that s h
    exact .provideMerge (checkLayer_sound sig self _ a ha) (checkLayer_sound sig that _ b hb)
  | merge left right =>
    intro p s h
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_layer_merge sig p left right s h
    exact .merge (checkLayer_sound sig left _ a ha) (checkLayer_sound sig right _ b hb)
  | fresh inner =>
    intro p s h
    exact .fresh (checkLayer_sound sig inner _ s (inv_layer_fresh sig p inner s h))
  | orDie inner =>
    intro p s h
    obtain ⟨i, hi, rfl⟩ := inv_layer_orDie sig p inner s h
    exact .orDie (checkLayer_sound sig inner _ i hi)
  | ref target =>
    intro p s h
    exact (inv_layer_ref sig p target s h).elim
  | mergeAll layers =>
    intro p s h
    obtain ⟨ls, hls, hm⟩ := inv_layer_mergeAll sig p layers s h
    exact .mergeAll (checkLayers_sound sig layers _ ls s hls hm)
termination_by structural layer

/-- The list of signatures under its nonempty merge derives the spine's judgment. -/
theorem checkLayers_sound (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ (p : List Nat) (ls : List LayerTy) (m : LayerTy), checkLayers sig p layers = .ok ls →
      LayerTy.mergeNonempty ls = some m → LayersHasTy sig layers m := by
  cases layers with
  | nil =>
    intro p ls m h hm
    obtain rfl := inv_layers_nil sig p ls h
    simp only [LayerTy.mergeNonempty, reduceCtorEq] at hm
  | cons head tail =>
    intro p ls m h hm
    obtain ⟨hd, tl, hh, ht, rfl⟩ := inv_layers_cons sig p head tail ls h
    cases tail with
    | nil =>
      obtain rfl := inv_layers_nil sig (p ++ [1]) tl ht
      simp only [LayerTy.mergeNonempty, Option.some.injEq] at hm
      subst hm
      exact .one (checkLayer_sound sig head _ hd hh)
    | cons next rest =>
      obtain ⟨h', t', hh', ht', rfl⟩ := inv_layers_cons sig (p ++ [1]) next rest tl ht
      simp only [LayerTy.mergeNonempty, Option.map_eq_some_iff] at hm
      obtain ⟨m', hm', rfl⟩ := hm
      exact .cons (checkLayer_sound sig head _ hd hh)
        (checkLayers_sound sig (.cons next rest) (p ++ [1]) (h' :: t') m' ht hm')
termination_by structural layers

end

/-! ## Completeness: what the rules derive, the checker accepts, at every path -/

mutual

theorem check_complete (sig : Signature Op) (e : Eff Op) :
    ∀ (env : TyEnv) (t : EffTy), HasTy sig env e t → ∀ p, check sig env p e = .ok t := by
  cases e with
  | succeed value => intro env t hd p; cases hd; aesop
  | select s d a0 a1 =>
    intro env t hd p; cases hd
    have ih0 := check_complete sig a0 _ _ ‹HasTy sig _ a0 _› (p ++ [0])
    have ih1 := check_complete sig a1 _ _ ‹HasTy sig _ a1 _› (p ++ [1])
    aesop
  | fail error => intro env t hd p; cases hd; aesop
  | failCause cause => intro env t hd p; cases hd; aesop
  | sync thunk => intro env t hd p; cases hd; aesop
  | suspend body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | perform op request => intro env t hd p; cases hd; aesop
  | bind first rest =>
    intro env t hd p; cases hd
    have ihf := check_complete sig first _ _ ‹HasTy sig _ first _› (p ++ [0])
    have ihr := check_complete sig rest _ _ ‹HasTy sig _ rest _› (p ++ [1])
    aesop
  | gen body =>
    intro env t hd p; cases hd
    have ih := checkStmts_complete sig body _ _ _ ‹StmtsHasTy sig _ _ body _› (p ++ [0])
    aesop
  | catchCause body handler =>
    intro env t hd p; cases hd
    have ihb := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    have ihh := check_complete sig handler _ _ ‹HasTy sig _ handler _› (p ++ [1])
    aesop
  | catchIf test body handler =>
    intro env t hd p; cases hd
    have ihb := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    have ihh := check_complete sig handler _ _ ‹HasTy sig _ handler _› (p ++ [1])
    aesop
  | matchCause body onValue onCause =>
    intro env t hd p; cases hd
    have ihb := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    have ihv := check_complete sig onValue _ _ ‹HasTy sig _ onValue _› (p ++ [1])
    have ihc := check_complete sig onCause _ _ ‹HasTy sig _ onCause _› (p ++ [2])
    aesop
  | onExit body finalizer =>
    intro env t hd p; cases hd
    have ihb := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    have ihf := check_complete sig finalizer _ _ ‹HasTy sig _ finalizer _› (p ++ [1])
    aesop
  | exit body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | uninterruptible body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | interruptible body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | iterate cursor initial test step result body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | yieldNow priority => intro env t hd p; cases hd; aesop
  | awaitFiber fiber mode =>
    intro env t hd p
    cases mode with
    | joinEffect => cases hd; aesop
    | awaitValue => cases hd; aesop
  | withFiber action =>
    intro env t hd p; cases hd
    have ih := checkAction_complete sig action _ _ ‹ActionHasTy sig _ action _› (p ++ [0])
    aesop
  | «scoped» body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | acquireRelease acquire release =>
    intro env t hd p; cases hd
    have iha := check_complete sig acquire _ _ ‹HasTy sig _ acquire _› (p ++ [0])
    have ihr := check_complete sig release _ _ ‹HasTy sig _ release _› (p ++ [1])
    aesop
  | provideLayer layer isLocal body =>
    intro env t hd p; cases hd
    have ihl := checkLayer_complete sig layer _ ‹LayerHasTy sig layer _› (p ++ [0])
    have ihb := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [1])
    aesop
  | service key => intro env t hd p; cases hd; aesop
  | provideService key value body =>
    intro env t hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
termination_by structural e

theorem checkStmts_complete (sig : Signature Op) (body : Stmts Op) :
    ∀ (env : TyEnv) (inLoop : Bool) (g : GenTy), StmtsHasTy sig env inLoop body g →
      ∀ p, checkStmts sig env inLoop none p body = .ok g := by
  cases body with
  | nil => intro env inLoop g hd p; cases hd; aesop
  | cons head tail =>
    cases head with
    | bindYield effect =>
      intro env inLoop g hd p; cases hd
      have iht := check_complete sig effect _ _ ‹HasTy sig _ effect _› (p ++ [0, 0])
      have ihr := checkStmts_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _› (p ++ [1])
      aesop
    | yieldDiscard effect =>
      intro env inLoop g hd p; cases hd
      have iht := check_complete sig effect _ _ ‹HasTy sig _ effect _› (p ++ [0, 0])
      have ihr := checkStmts_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _› (p ++ [1])
      aesop
    | ret value =>
      cases tail with
      | nil => intro env inLoop g hd p; cases hd; aesop
      | cons next rest => intro env inLoop g hd p; cases hd
    | ifElse test thenB elseB =>
      intro env inLoop g hd p; cases hd
      have iha := checkStmts_complete sig thenB _ _ _ ‹StmtsHasTy sig _ _ thenB _› (p ++ [0, 0])
      have ihb := checkStmts_complete sig elseB _ _ _ ‹StmtsHasTy sig _ _ elseB _› (p ++ [0, 1])
      have ihr := checkStmts_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _› (p ++ [1])
      aesop
    | whileTrue loopBody =>
      intro env inLoop g hd p; cases hd
      have ihb := checkStmts_complete sig loopBody _ _ _ ‹StmtsHasTy sig _ _ loopBody _› (p ++ [0, 0])
      have ihr := checkStmts_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _› (p ++ [1])
      aesop
    | breakLoop =>
      intro env inLoop g hd p; cases hd
      have ih := checkStmts_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _› (p ++ [1])
      aesop
termination_by structural body

theorem checkEffs_complete (sig : Signature Op) (entrants : Effs Op) :
    ∀ (env : TyEnv) (t : EffTy), EffsHasTy sig env entrants t →
      ∀ p, checkEffs sig env p entrants = .ok t := by
  cases entrants with
  | nil => intro env t hd p; cases hd; aesop
  | cons head tail =>
    intro env t hd p; cases hd
    have ihh := check_complete sig head _ _ ‹HasTy sig _ head _› (p ++ [0])
    have ihr := checkEffs_complete sig tail _ _ ‹EffsHasTy sig _ tail _› (p ++ [1])
    aesop
termination_by structural entrants

theorem checkAction_complete (sig : Signature Op) (action : ActionTerm Op) :
    ∀ (env : TyEnv) (t : EffTy), ActionHasTy sig env action t →
      ∀ p, checkAction sig env p action = .ok t := by
  cases action with
  | fork program options =>
    intro env t hd p; cases hd
    have ih := check_complete sig program _ _ ‹HasTy sig _ program _› (p ++ [0])
    aesop
  | forkIn program options scope =>
    intro env t hd p; cases hd
    have ih := check_complete sig program _ _ ‹HasTy sig _ program _› (p ++ [0])
    aesop
  | forkScoped program options =>
    intro env t hd p; cases hd
    have ih := check_complete sig program _ _ ‹HasTy sig _ program _› (p ++ [0])
    aesop
  | runIn target scope => intro env t hd p; cases hd; aesop
  | interrupt target => intro env t hd p; cases hd; aesop
  | interruptScoped target => intro env t hd p; cases hd; aesop
  | interruptAll targets who =>
    intro env t hd p
    cases who with
    | none => cases hd; aesop
    | some w => cases hd; aesop
  | awaitAll targets => intro env t hd p; cases hd; aesop
  | awaitAllFailFast targets => intro env t hd p; cases hd; aesop
  | snapshotChildren => intro env t hd p; cases hd; aesop
  | awaitNewChildren snapshot => intro env t hd p; cases hd; aesop
  | raceAll entrants =>
    intro env t hd p; cases hd
    have ih := checkEffs_complete sig entrants _ _ ‹EffsHasTy sig _ entrants _› (p ++ [0])
    aesop
  | setContext context => intro env t hd p; cases hd; aesop
  | getContext => intro env t hd p; cases hd; aesop
  | getId => intro env t hd p; cases hd; aesop
  | closeScope scope exitTerm => intro env t hd p; cases hd; aesop
termination_by structural action

theorem checkLayer_complete (sig : Signature Op) (layer : LayerTerm Op) :
    ∀ (s : LayerTy), LayerHasTy sig layer s → ∀ p, checkLayer sig p layer = .ok s := by
  cases layer with
  | succeed key value => intro s hd p; cases hd; aesop
  | effect key body =>
    intro s hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | effectDiscard body =>
    intro s hd p; cases hd
    have ih := check_complete sig body _ _ ‹HasTy sig _ body _› (p ++ [0])
    aesop
  | provide self that =>
    intro s hd p; cases hd
    have iha := checkLayer_complete sig self _ ‹LayerHasTy sig self _› (p ++ [0])
    have ihb := checkLayer_complete sig that _ ‹LayerHasTy sig that _› (p ++ [1])
    aesop
  | provideMerge self that =>
    intro s hd p; cases hd
    have iha := checkLayer_complete sig self _ ‹LayerHasTy sig self _› (p ++ [0])
    have ihb := checkLayer_complete sig that _ ‹LayerHasTy sig that _› (p ++ [1])
    aesop
  | merge left right =>
    intro s hd p; cases hd
    have iha := checkLayer_complete sig left _ ‹LayerHasTy sig left _› (p ++ [0])
    have ihb := checkLayer_complete sig right _ ‹LayerHasTy sig right _› (p ++ [1])
    aesop
  | fresh inner =>
    intro s hd p; cases hd
    have ih := checkLayer_complete sig inner _ ‹LayerHasTy sig inner _› (p ++ [0])
    aesop
  | orDie inner =>
    intro s hd p; cases hd
    have ih := checkLayer_complete sig inner _ ‹LayerHasTy sig inner _› (p ++ [0])
    aesop
  | ref target => intro s hd p; cases hd
  | mergeAll layers =>
    intro s hd p; cases hd
    obtain ⟨ls, hls, hm⟩ :=
      checkLayers_complete sig layers _ ‹LayersHasTy sig layers _› (p ++ [0])
    aesop
termination_by structural layer

/-- The spine's judgment is a list of signatures under its nonempty merge, at every path. -/
theorem checkLayers_complete (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ (m : LayerTy), LayersHasTy sig layers m →
      ∀ p, ∃ ls, checkLayers sig p layers = .ok ls ∧ LayerTy.mergeNonempty ls = some m := by
  cases layers with
  | nil => intro m hd; cases hd
  | cons head tail =>
    cases tail with
    | nil =>
      intro m hd p; cases hd
      have ih := checkLayer_complete sig head _ ‹LayerHasTy sig head _› (p ++ [0])
      exact ⟨[m], by aesop, rfl⟩
    | cons next rest =>
      intro m hd p; cases hd with
      | cons hhead htail =>
        rename_i h t
        have ihh := checkLayer_complete sig head _ hhead (p ++ [0])
        obtain ⟨ls, hls, hm⟩ := checkLayers_complete sig (.cons next rest) _ htail (p ++ [1])
        obtain ⟨l, ls', -, -, rfl⟩ := inv_layers_cons sig (p ++ [1]) next rest ls hls
        refine ⟨h :: l :: ls', by aesop, ?_⟩
        simp only [LayerTy.mergeNonempty, hm, Option.map_some]
termination_by structural layers

end

/-! ## The consequence: the success projection does not depend on the path -/

/-- A check that succeeds at one path succeeds at every path, at the same type; one that
refuses at one path refuses at every path. -/
theorem check_toOption (sig : Signature Op) (env : TyEnv) (p p' : List Nat) (e : Eff Op) :
    (check sig env p e).toOption = (check sig env p' e).toOption := by
  cases h : check sig env p e with
  | ok t => rw [check_complete sig e env t (check_sound sig e env p t h) p']
  | error r =>
    cases h' : check sig env p' e with
    | ok t' => rw [check_complete sig e env t' (check_sound sig e env p' t' h') p] at h; cases h
    | error r' => rfl

end Conform.Effect4.Typing
