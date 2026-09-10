import Effect4.Laws.Program.Typing.HasTy
import Effect4.Laws.Program.Typing.Inversion

/-!
# Conform.Effect4.Typing.Sound — the algorithm and the rules agree, on the whole language

Two mutual blocks of six theorems each, over the seven-type mutual syntax of
`src/Effect4/Program/Eff.lean:261-398`:

* **soundness** — what the checker accepts, the rules derive:
  `effTy sig env e = some t → HasTy sig env e t`, and the five siblings;
* **completeness** — what the rules derive, the checker accepts, *at the same type*:
  `HasTy sig env e t → effTy sig env e = some t`, and the five siblings.

Both recurse **structurally on the syntax** (`termination_by structural`), the style of
`src/Effect4/Laws/Program/Typed.lean:504-550`: `induction` cannot be used, since a mutual
inductive's recursor carries one motive per type of the family. Completeness inverts the
*derivation* with a single `cases` per arm — the derivation's constructors are indexed by the
program, so at a fixed constructor exactly one rule applies (and at `LayerTerm.ref`, at the
empty `mergeAll` spine, and after a `return`, *none* does, which closes those goals with no
case at all).

Each soundness arm is three lines and always the same three: invert, recurse, apply the rule.
Each completeness arm is: invert the derivation, name the premises, recurse, `simp` with the
checker's equation and the premises. Nothing else appears in either block.

The consequences at the end: `WellTyped` is inhabitation of the judgment, the judgment is
deterministic (a program has at most one type), and the weakening theorem of
`Typing.lean:502-514` restated on the relation.
-/

namespace Conform.Effect4.Typing

open _root_.Effect4
open _root_.Effect4.Program
open _root_.Effect4.Machine.Env (Requirement)

variable {Op : Type}

/-! ## Soundness: what the algorithm accepts, the rules derive -/

mutual

/-- `effTy` accepts only what `HasTy` derives (`Typing.lean:178-281`). -/
theorem effTy_sound (sig : Signature Op) (e : Eff Op) :
    ∀ (env : TyEnv) (t : EffTy), effTy sig env e = some t → HasTy sig env e t := by
  cases e with
  | succeed value =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_succeed sig env value t h
    exact .succeed hty
  | fail error =>
    intro env t h
    obtain ⟨ty, hty, herr, rfl⟩ := inv_fail sig env error t h
    exact .fail hty herr
  | failCause cause =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_failCause sig env cause t h
    exact .failCause hty
  | yieldError error =>
    intro env t h
    obtain ⟨ty, hty, herr, rfl⟩ := inv_yieldError sig env error t h
    exact .yieldError hty herr
  | sync thunk =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_sync sig env thunk t h
    exact .sync hty
  | suspend body =>
    intro env t h
    exact .suspend (effTy_sound sig body env t (inv_suspend sig env body t h))
  | perform op request =>
    intro env t h
    obtain ⟨requestTy, hdom, hreq, heq, rfl⟩ := inv_perform sig env op request t h
    exact .perform hdom hreq heq
  | bind first rest =>
    intro env t h
    obtain ⟨f, r, hf, hr, rfl⟩ := inv_bind sig env first rest t h
    exact .bind (effTy_sound sig first env f hf) (effTy_sound sig rest _ r hr)
  | gen body =>
    intro env t h
    obtain ⟨g, hg, rfl⟩ := inv_gen sig env body t h
    exact .gen (stmtsTy_sound sig body env false g hg)
  | catchCause body handler =>
    intro env t h
    obtain ⟨b, hh, answer, hb, hhh, hj, rfl⟩ := inv_catchCause sig env body handler t h
    exact .catchCause (effTy_sound sig body env b hb) (effTy_sound sig handler _ hh hhh) hj
  | catchIf test body handler =>
    intro env t h
    obtain ⟨b, hh, answer, hb, ht, hhh, hj, rfl⟩ := inv_catchIf sig env test body handler t h
    exact .catchIf (effTy_sound sig body env b hb) ht
      (effTy_sound sig handler _ hh hhh) hj
  | matchCause body onValue onCause =>
    intro env t h
    obtain ⟨b, v, c, answer, hb, hv, hc, hj, rfl⟩ :=
      inv_matchCause sig env body onValue onCause t h
    exact .matchCause (effTy_sound sig body env b hb) (effTy_sound sig onValue _ v hv)
      (effTy_sound sig onCause _ c hc) hj
  | onExit body finalizer =>
    intro env t h
    obtain ⟨b, f, hb, hf, rfl⟩ := inv_onExit sig env body finalizer t h
    exact .onExit (effTy_sound sig body env b hb) (effTy_sound sig finalizer _ f hf)
  | exit body =>
    intro env t h
    obtain ⟨b, hb, rfl⟩ := inv_exit sig env body t h
    exact .exit (effTy_sound sig body env b hb)
  | uninterruptible body =>
    intro env t h
    exact .uninterruptible (effTy_sound sig body env t (inv_uninterruptible sig env body t h))
  | interruptible body =>
    intro env t h
    exact .interruptible (effTy_sound sig body env t (inv_interruptible sig env body t h))
  | branch test thenB elseB =>
    intro env t h
    obtain ⟨htest, a, b, answer, ha, hb, hj, rfl⟩ := inv_branch sig env test thenB elseB t h
    exact .branch htest (effTy_sound sig thenB env a ha) (effTy_sound sig elseB env b hb) hj
  | whileLoop initial test step body =>
    intro env t h
    obtain ⟨cursor, b, hinit, htest, hbody, hstep, rfl⟩ :=
      inv_whileLoop sig env initial test step body t h
    exact .whileLoop hinit htest (effTy_sound sig body _ b hbody) hstep
  | yieldNow priority =>
    intro env t h
    obtain rfl := inv_yieldNow sig env priority t h
    exact .yieldNow priority
  | callback register request =>
    intro env t h
    obtain ⟨requestTy, hdom, hkind, hreq, heq, rfl⟩ := inv_callback sig env register request t h
    exact .callback hdom hkind hreq heq
  | awaitFiber fiber mode =>
    intro env t h
    cases mode with
    | joinEffect =>
      obtain ⟨handle, value, error, hterm, hfib, rfl⟩ := inv_awaitFiber_join sig env fiber t h
      exact .awaitFiber_join hterm hfib
    | awaitValue =>
      obtain ⟨handle, value, error, hterm, hfib, rfl⟩ := inv_awaitFiber_await sig env fiber t h
      exact .awaitFiber_await hterm hfib
  | withFiber action =>
    intro env t h
    exact .withFiber (actionTy_sound sig action env t (inv_withFiber sig env action t h))
  | «scoped» body =>
    intro env t h
    obtain ⟨b, hb, rfl⟩ := inv_scoped sig env body t h
    exact HasTy.scoped (effTy_sound sig body env b hb)
  | acquireRelease acquire release =>
    intro env t h
    obtain ⟨a, r, ha, hr, rfl⟩ := inv_acquireRelease sig env acquire release t h
    exact .acquireRelease (effTy_sound sig acquire env a ha) (effTy_sound sig release _ r hr)
  | choose site left right =>
    intro env t h
    obtain ⟨l, r, answer, hl, hr, hj, rfl⟩ := inv_choose sig env site left right t h
    exact .choose site (effTy_sound sig left env l hl) (effTy_sound sig right env r hr) hj
  | provideLayer layer isLocal body =>
    intro env t h
    obtain ⟨l, b, hl, hb, rfl⟩ := inv_provideLayer sig env layer isLocal body t h
    exact .provideLayer isLocal (layerTy_sound sig layer l hl) (effTy_sound sig body env b hb)
  | service key =>
    intro env t h
    obtain ⟨ty, hty, rfl⟩ := inv_service sig env key t h
    exact .service hty
  | provideService key value body =>
    intro env t h
    obtain ⟨ty, valueTy, b, hty, hval, heq, hb, rfl⟩ := inv_provideService sig env key value body t h
    exact .provideService hty hval heq (effTy_sound sig body env b hb)
termination_by structural e

/-- `stmtsTy` accepts only what `StmtsHasTy` derives (`Typing.lean:328-356`). -/
theorem stmtsTy_sound (sig : Signature Op) (body : Stmts Op) :
    ∀ (env : TyEnv) (inLoop : Bool) (g : GenTy),
      stmtsTy sig env inLoop body = some g → StmtsHasTy sig env inLoop body g := by
  cases body with
  | nil =>
    intro env inLoop g h
    obtain rfl := inv_stmts_nil sig env inLoop g h
    exact .nil
  | cons head tail =>
    cases head with
    | bindYield effect =>
      intro env inLoop g h
      obtain ⟨t, r, ht, hr, rfl⟩ := inv_stmts_bindYield sig env inLoop effect tail g h
      exact .bindYield (effTy_sound sig effect env t ht)
        (stmtsTy_sound sig tail _ inLoop r hr)
    | yieldDiscard effect =>
      intro env inLoop g h
      obtain ⟨t, r, ht, hr, rfl⟩ := inv_stmts_yieldDiscard sig env inLoop effect tail g h
      exact .yieldDiscard (effTy_sound sig effect env t ht)
        (stmtsTy_sound sig tail env inLoop r hr)
    | ret value =>
      cases tail with
      | nil =>
        intro env inLoop g h
        obtain ⟨ty, hty, rfl⟩ := inv_stmts_ret sig env inLoop value g h
        exact .ret hty
      | cons next rest =>
        intro env inLoop g h
        exact (inv_stmts_ret_cons sig env inLoop value next rest g h).elim
    | ifElse test thenB elseB =>
      intro env inLoop g h
      obtain ⟨htest, a, b, r, ab, ha, hb, hr, hab, hg⟩ :=
        inv_stmts_ifElse sig env inLoop test thenB elseB tail g h
      exact .ifElse htest (stmtsTy_sound sig thenB env inLoop a ha)
        (stmtsTy_sound sig elseB env inLoop b hb) (stmtsTy_sound sig tail env inLoop r hr) hab hg
    | whileTrue loopBody =>
      intro env inLoop g h
      obtain ⟨b, r, hb, hr, hg⟩ := inv_stmts_whileTrue sig env inLoop loopBody tail g h
      exact .whileTrue (stmtsTy_sound sig loopBody env true b hb)
        (stmtsTy_sound sig tail env inLoop r hr) hg
    | breakLoop =>
      intro env inLoop g h
      obtain ⟨hflag, hrest⟩ := inv_stmts_breakLoop sig env inLoop tail g h
      subst hflag
      exact .breakLoop (stmtsTy_sound sig tail env true g hrest)
termination_by structural body

/-- `effsTy` accepts only what `EffsHasTy` derives (`Typing.lean:359-365`). -/
theorem effsTy_sound (sig : Signature Op) (entrants : Effs Op) :
    ∀ (env : TyEnv) (t : EffTy), effsTy sig env entrants = some t →
      EffsHasTy sig env entrants t := by
  cases entrants with
  | nil =>
    intro env t h
    obtain rfl := inv_effs_nil sig env t h
    exact .nil
  | cons head tail =>
    intro env t h
    obtain ⟨hh, r, answer, hhd, hr, hj, rfl⟩ := inv_effs_cons sig env head tail t h
    exact .cons (effTy_sound sig head env hh hhd) (effsTy_sound sig tail env r hr) hj
termination_by structural entrants

/-- `actionTy` accepts only what `ActionHasTy` derives (`Typing.lean:368-434`). -/
theorem actionTy_sound (sig : Signature Op) (action : ActionTerm Op) :
    ∀ (env : TyEnv) (t : EffTy), actionTy sig env action = some t →
      ActionHasTy sig env action t := by
  cases action with
  | fork program options =>
    intro env t h
    obtain ⟨p, hp, rfl⟩ := inv_action_fork sig env program options t h
    exact .fork options (effTy_sound sig program env p hp)
  | forkIn program options scope =>
    intro env t h
    obtain ⟨p, hp, hs, rfl⟩ := inv_action_forkIn sig env program options scope t h
    exact .forkIn options (effTy_sound sig program env p hp) hs
  | forkScoped program options =>
    intro env t h
    obtain ⟨p, hp, rfl⟩ := inv_action_forkScoped sig env program options t h
    exact .forkScoped options (effTy_sound sig program env p hp)
  | runIn target scope =>
    intro env t h
    obtain ⟨handle, value, error, ht, hf, hs, rfl⟩ := inv_action_runIn sig env target scope t h
    exact .runIn ht hf hs
  | interrupt target =>
    intro env t h
    obtain ⟨handle, value, error, ht, hf, rfl⟩ := inv_action_interrupt sig env target t h
    exact .interrupt ht hf
  | interruptScoped target =>
    intro env t h
    obtain ⟨handle, value, error, ht, hf, rfl⟩ := inv_action_interruptScoped sig env target t h
    exact .interruptScoped ht hf
  | interruptAll targets who =>
    intro env t h
    cases who with
    | none =>
      obtain ⟨inner, value, error, ht, hf, rfl⟩ :=
        inv_action_interruptAll_self sig env targets t h
      exact .interruptAll_self ht hf
    | some w =>
      obtain ⟨inner, value, error, ht, hf, hw, rfl⟩ :=
        inv_action_interruptAll_by sig env targets w t h
      exact .interruptAll_by ht hf hw
  | awaitAll targets =>
    intro env t h
    obtain ⟨inner, value, error, ht, hf, rfl⟩ := inv_action_awaitAll sig env targets t h
    exact .awaitAll ht hf
  | awaitAllFailFast targets =>
    intro env t h
    obtain ⟨inner, value, error, ht, hf, rfl⟩ := inv_action_awaitAllFailFast sig env targets t h
    exact .awaitAllFailFast ht hf
  | snapshotChildren =>
    intro env t h
    obtain rfl := inv_action_snapshotChildren sig env t h
    exact .snapshotChildren
  | awaitNewChildren snapshot =>
    intro env t h
    obtain ⟨hs, rfl⟩ := inv_action_awaitNewChildren sig env snapshot t h
    exact .awaitNewChildren hs
  | raceAll entrants =>
    intro env t h
    exact .raceAll (effsTy_sound sig entrants env t (inv_action_raceAll sig env entrants t h))
  | setContext context =>
    intro env t h
    obtain ⟨hc, rfl⟩ := inv_action_setContext sig env context t h
    exact .setContext hc
  | getContext =>
    intro env t h
    obtain rfl := inv_action_getContext sig env t h
    exact .getContext
  | getId =>
    intro env t h
    obtain rfl := inv_action_getId sig env t h
    exact .getId
  | closeScope scope exitTerm =>
    intro env t h
    obtain ⟨value, error, hs, he, rfl⟩ := inv_action_closeScope sig env scope exitTerm t h
    exact .closeScope hs he
termination_by structural action

/-- `layerTy` accepts only what `LayerHasTy` derives (`Typing.lean:290-314`). -/
theorem layerTy_sound (sig : Signature Op) (layer : LayerTerm Op) :
    ∀ (s : LayerTy), layerTy sig layer = some s → LayerHasTy sig layer s := by
  cases layer with
  | succeed key value =>
    intro s h
    obtain ⟨v, hv, rfl⟩ := inv_layer_succeed sig key value s h
    exact .succeed hv
  | effect key body =>
    intro s h
    obtain ⟨t, ht, rfl⟩ := inv_layer_effect sig key body s h
    exact .effect (effTy_sound sig body [] t ht)
  | effectDiscard body =>
    intro s h
    obtain ⟨t, ht, rfl⟩ := inv_layer_effectDiscard sig body s h
    exact .effectDiscard (effTy_sound sig body [] t ht)
  | provide self that =>
    intro s h
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_layer_provide sig self that s h
    exact .provide (layerTy_sound sig self a ha) (layerTy_sound sig that b hb)
  | provideMerge self that =>
    intro s h
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_layer_provideMerge sig self that s h
    exact .provideMerge (layerTy_sound sig self a ha) (layerTy_sound sig that b hb)
  | merge left right =>
    intro s h
    obtain ⟨a, b, ha, hb, rfl⟩ := inv_layer_merge sig left right s h
    exact .merge (layerTy_sound sig left a ha) (layerTy_sound sig right b hb)
  | fresh inner =>
    intro s h
    exact .fresh (layerTy_sound sig inner s (inv_layer_fresh sig inner s h))
  | orDie inner =>
    intro s h
    obtain ⟨i, hi, rfl⟩ := inv_layer_orDie sig inner s h
    exact .orDie (layerTy_sound sig inner i hi)
  | ref target =>
    intro s h
    exact (inv_layer_ref sig target s h).elim
  | mergeAll layers =>
    intro s h
    exact .mergeAll (layersTy_sound sig layers s (inv_layer_mergeAll sig layers s h))
termination_by structural layer

/-- `layersTy` accepts only what `LayersHasTy` derives (`Typing.lean:318-324`). -/
theorem layersTy_sound (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ (s : LayerTy), layersTy sig layers = some s → LayersHasTy sig layers s := by
  cases layers with
  | nil =>
    intro s h
    exact (inv_layers_nil sig s h).elim
  | cons head tail =>
    cases tail with
    | nil =>
      intro s h
      exact .one (layerTy_sound sig head s (inv_layers_one sig head s h))
    | cons next rest =>
      intro s h
      obtain ⟨a, b, ha, hb, rfl⟩ := inv_layers_cons sig head next rest s h
      exact .cons (layerTy_sound sig head a ha) (layersTy_sound sig (.cons next rest) b hb)
termination_by structural layers

end

/-! ## Completeness: what the rules derive, the algorithm accepts

Every arm is the same four moves, and no arm is anything else:

1. `cases hd` — invert the derivation. At a fixed constructor exactly one rule applies, so this
   is a *decomposition*, not a case analysis; at `LayerTerm.ref`, at the empty `mergeAll`
   spine, and after a `return` **no** rule applies, so `cases hd` closes the goal outright and
   the arm is one line.
2. one `have … := <sibling>_complete … ‹judgment›` per recursive premise — the induction
   hypothesis, fetched by its *type* (`‹HasTy sig _ body _›` is `by assumption`) rather than by
   a name, because `cases` reorders a rule's premises: the leaf equations that the index
   unification consumes are moved in front of the judgments.
3. `simp_all [<checker>]` — the checker's equation for this arm, plus every premise of the
   rule, which `simp_all` takes from the context whether or not it is named.
-/

mutual

/-- Every `HasTy` derivation is an acceptance by `effTy`, at the same type. -/
theorem effTy_complete (sig : Signature Op) (e : Eff Op) :
    ∀ (env : TyEnv) (t : EffTy), HasTy sig env e t → effTy sig env e = some t := by
  cases e with
  | succeed value =>
    intro env t hd; cases hd; simp_all [effTy]
  | fail error =>
    intro env t hd; cases hd; simp_all [effTy]
  | failCause cause =>
    intro env t hd; cases hd; simp_all [effTy]
  | yieldError error =>
    intro env t hd; cases hd; simp_all [effTy]
  | sync thunk =>
    intro env t hd; cases hd; simp_all [effTy]
  | suspend body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | perform op request =>
    intro env t hd; cases hd; simp_all [effTy]
  | bind first rest =>
    intro env t hd; cases hd
    have ihf := effTy_complete sig first _ _ ‹HasTy sig _ first _›
    have ihr := effTy_complete sig rest _ _ ‹HasTy sig _ rest _›
    simp_all [effTy]
  | gen body =>
    intro env t hd; cases hd
    have ih := stmtsTy_complete sig body _ _ _ ‹StmtsHasTy sig _ _ body _›
    simp_all [effTy]
  | catchCause body handler =>
    intro env t hd; cases hd
    have ihb := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    have ihh := effTy_complete sig handler _ _ ‹HasTy sig _ handler _›
    simp_all [effTy]
  | catchIf test body handler =>
    intro env t hd; cases hd
    have ihb := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    have ihh := effTy_complete sig handler _ _ ‹HasTy sig _ handler _›
    simp_all [effTy]
  | matchCause body onValue onCause =>
    intro env t hd; cases hd
    have ihb := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    have ihv := effTy_complete sig onValue _ _ ‹HasTy sig _ onValue _›
    have ihc := effTy_complete sig onCause _ _ ‹HasTy sig _ onCause _›
    simp_all [effTy]
  | onExit body finalizer =>
    intro env t hd; cases hd
    have ihb := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    have ihf := effTy_complete sig finalizer _ _ ‹HasTy sig _ finalizer _›
    simp_all [effTy]
  | exit body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | uninterruptible body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | interruptible body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | branch test thenB elseB =>
    intro env t hd; cases hd
    have iha := effTy_complete sig thenB _ _ ‹HasTy sig _ thenB _›
    have ihb := effTy_complete sig elseB _ _ ‹HasTy sig _ elseB _›
    simp_all [effTy]
  | whileLoop initial test step body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | yieldNow priority =>
    intro env t hd; cases hd; simp_all [effTy]
  | callback register request =>
    intro env t hd; cases hd; simp_all [effTy]
  | awaitFiber fiber mode =>
    intro env t hd
    cases mode with
    | joinEffect => cases hd; simp_all [effTy]
    | awaitValue => cases hd; simp_all [effTy]
  | withFiber action =>
    intro env t hd; cases hd
    have ih := actionTy_complete sig action _ _ ‹ActionHasTy sig _ action _›
    simp_all [effTy]
  | «scoped» body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | acquireRelease acquire release =>
    intro env t hd; cases hd
    have iha := effTy_complete sig acquire _ _ ‹HasTy sig _ acquire _›
    have ihr := effTy_complete sig release _ _ ‹HasTy sig _ release _›
    simp_all [effTy]
  | choose site left right =>
    intro env t hd; cases hd
    have ihl := effTy_complete sig left _ _ ‹HasTy sig _ left _›
    have ihr := effTy_complete sig right _ _ ‹HasTy sig _ right _›
    simp_all [effTy]
  | provideLayer layer isLocal body =>
    intro env t hd; cases hd
    have ihl := layerTy_complete sig layer _ ‹LayerHasTy sig layer _›
    have ihb := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
  | service key =>
    intro env t hd; cases hd; simp_all [effTy]
  | provideService key value body =>
    intro env t hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [effTy]
termination_by structural e

/-- Every `StmtsHasTy` derivation is an acceptance by `stmtsTy`. -/
theorem stmtsTy_complete (sig : Signature Op) (body : Stmts Op) :
    ∀ (env : TyEnv) (inLoop : Bool) (g : GenTy),
      StmtsHasTy sig env inLoop body g → stmtsTy sig env inLoop body = some g := by
  cases body with
  | nil =>
    intro env inLoop g hd; cases hd; simp_all [stmtsTy]
  | cons head tail =>
    cases head with
    | bindYield effect =>
      intro env inLoop g hd; cases hd
      have iht := effTy_complete sig effect _ _ ‹HasTy sig _ effect _›
      have ihr := stmtsTy_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _›
      simp_all [stmtsTy]
    | yieldDiscard effect =>
      intro env inLoop g hd; cases hd
      have iht := effTy_complete sig effect _ _ ‹HasTy sig _ effect _›
      have ihr := stmtsTy_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _›
      simp_all [stmtsTy]
    | ret value =>
      cases tail with
      | nil =>
        intro env inLoop g hd; cases hd; simp_all [stmtsTy]
      | cons next rest =>
        -- no rule applies: a statement after a `return` has no derivation
        intro env inLoop g hd; cases hd
    | ifElse test thenB elseB =>
      intro env inLoop g hd; cases hd
      have iha := stmtsTy_complete sig thenB _ _ _ ‹StmtsHasTy sig _ _ thenB _›
      have ihb := stmtsTy_complete sig elseB _ _ _ ‹StmtsHasTy sig _ _ elseB _›
      have ihr := stmtsTy_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _›
      simp_all [stmtsTy]
    | whileTrue loopBody =>
      intro env inLoop g hd; cases hd
      have ihb := stmtsTy_complete sig loopBody _ _ _ ‹StmtsHasTy sig _ _ loopBody _›
      have ihr := stmtsTy_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _›
      simp_all [stmtsTy]
    | breakLoop =>
      intro env inLoop g hd; cases hd
      have ih := stmtsTy_complete sig tail _ _ _ ‹StmtsHasTy sig _ _ tail _›
      simp_all [stmtsTy]
termination_by structural body

/-- Every `EffsHasTy` derivation is an acceptance by `effsTy`. -/
theorem effsTy_complete (sig : Signature Op) (entrants : Effs Op) :
    ∀ (env : TyEnv) (t : EffTy), EffsHasTy sig env entrants t →
      effsTy sig env entrants = some t := by
  cases entrants with
  | nil =>
    intro env t hd; cases hd; simp_all [effsTy]
  | cons head tail =>
    intro env t hd; cases hd
    have ihh := effTy_complete sig head _ _ ‹HasTy sig _ head _›
    have ihr := effsTy_complete sig tail _ _ ‹EffsHasTy sig _ tail _›
    simp_all [effsTy]
termination_by structural entrants

/-- Every `ActionHasTy` derivation is an acceptance by `actionTy`. -/
theorem actionTy_complete (sig : Signature Op) (action : ActionTerm Op) :
    ∀ (env : TyEnv) (t : EffTy), ActionHasTy sig env action t →
      actionTy sig env action = some t := by
  cases action with
  | fork program options =>
    intro env t hd; cases hd
    have ih := effTy_complete sig program _ _ ‹HasTy sig _ program _›
    simp_all [actionTy]
  | forkIn program options scope =>
    intro env t hd; cases hd
    have ih := effTy_complete sig program _ _ ‹HasTy sig _ program _›
    simp_all [actionTy]
  | forkScoped program options =>
    intro env t hd; cases hd
    have ih := effTy_complete sig program _ _ ‹HasTy sig _ program _›
    simp_all [actionTy]
  | runIn target scope =>
    intro env t hd; cases hd; simp_all [actionTy]
  | interrupt target =>
    intro env t hd; cases hd; simp_all [actionTy]
  | interruptScoped target =>
    intro env t hd; cases hd; simp_all [actionTy]
  | interruptAll targets who =>
    intro env t hd
    cases who with
    | none => cases hd; simp_all [actionTy]
    | some w => cases hd; simp_all [actionTy]
  | awaitAll targets =>
    intro env t hd; cases hd; simp_all [actionTy]
  | awaitAllFailFast targets =>
    intro env t hd; cases hd; simp_all [actionTy]
  | snapshotChildren =>
    intro env t hd; cases hd; simp_all [actionTy]
  | awaitNewChildren snapshot =>
    intro env t hd; cases hd; simp_all [actionTy]
  | raceAll entrants =>
    intro env t hd; cases hd
    have ih := effsTy_complete sig entrants _ _ ‹EffsHasTy sig _ entrants _›
    simp_all [actionTy]
  | setContext context =>
    intro env t hd; cases hd; simp_all [actionTy]
  | getContext =>
    intro env t hd; cases hd; simp_all [actionTy]
  | getId =>
    intro env t hd; cases hd; simp_all [actionTy]
  | closeScope scope exitTerm =>
    intro env t hd; cases hd; simp_all [actionTy]
termination_by structural action

/-- Every `LayerHasTy` derivation is an acceptance by `layerTy`. -/
theorem layerTy_complete (sig : Signature Op) (layer : LayerTerm Op) :
    ∀ (s : LayerTy), LayerHasTy sig layer s → layerTy sig layer = some s := by
  cases layer with
  | succeed key value =>
    intro s hd; cases hd; simp_all [layerTy]
  | effect key body =>
    intro s hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [layerTy]
  | effectDiscard body =>
    intro s hd; cases hd
    have ih := effTy_complete sig body _ _ ‹HasTy sig _ body _›
    simp_all [layerTy]
  | provide self that =>
    intro s hd; cases hd
    have iha := layerTy_complete sig self _ ‹LayerHasTy sig self _›
    have ihb := layerTy_complete sig that _ ‹LayerHasTy sig that _›
    simp_all [layerTy]
  | provideMerge self that =>
    intro s hd; cases hd
    have iha := layerTy_complete sig self _ ‹LayerHasTy sig self _›
    have ihb := layerTy_complete sig that _ ‹LayerHasTy sig that _›
    simp_all [layerTy]
  | merge left right =>
    intro s hd; cases hd
    have iha := layerTy_complete sig left _ ‹LayerHasTy sig left _›
    have ihb := layerTy_complete sig right _ ‹LayerHasTy sig right _›
    simp_all [layerTy]
  | fresh inner =>
    intro s hd; cases hd
    have ih := layerTy_complete sig inner _ ‹LayerHasTy sig inner _›
    simp_all [layerTy]
  | orDie inner =>
    intro s hd; cases hd
    have ih := layerTy_complete sig inner _ ‹LayerHasTy sig inner _›
    simp_all [layerTy]
  | ref target =>
    -- no rule applies: a layer reference has no derivation
    intro s hd; cases hd
  | mergeAll layers =>
    intro s hd; cases hd
    have ih := layersTy_complete sig layers _ ‹LayersHasTy sig layers _›
    simp_all [layerTy]
termination_by structural layer

/-- Every `LayersHasTy` derivation is an acceptance by `layersTy`. -/
theorem layersTy_complete (sig : Signature Op) (layers : LayerTerms Op) :
    ∀ (s : LayerTy), LayersHasTy sig layers s → layersTy sig layers = some s := by
  cases layers with
  | nil =>
    -- no rule applies: `Layer.mergeAll` takes at least one layer
    intro s hd; cases hd
  | cons head tail =>
    cases tail with
    | nil =>
      intro s hd; cases hd
      have ih := layerTy_complete sig head _ ‹LayerHasTy sig head _›
      simp_all [layersTy]
    | cons next rest =>
      intro s hd; cases hd
      have ihh := layerTy_complete sig head _ ‹LayerHasTy sig head _›
      have iht := layersTy_complete sig (.cons next rest) _ ‹LayersHasTy sig (.cons next rest) _›
      simp_all [layersTy]
termination_by structural layers

end

/-! ## The three consequences -/

/-- The algorithm and the rules define the same relation, arm for arm. -/
theorem effTy_eq_hasTy (sig : Signature Op) (env : TyEnv) (e : Eff Op) (t : EffTy) :
    effTy sig env e = some t ↔ HasTy sig env e t :=
  ⟨effTy_sound sig e env t, effTy_complete sig e env t⟩

/-- `WellTyped` — the algorithm answers at the empty environment (`Typing.lean:603`) — is
inhabitation of the judgment. -/
theorem wellTyped_iff (sig : Signature Op) (program : Eff Op) :
    WellTyped sig program ↔ ∃ t, HasTy sig [] program t := by
  constructor
  · intro h
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp h
    exact ⟨t, effTy_sound sig program [] t ht⟩
  · rintro ⟨t, ht⟩
    exact Option.isSome_iff_exists.mpr ⟨t, effTy_complete sig program [] t ht⟩

/-- The judgment is deterministic: a program has at most one type. This is completeness'
first dividend — a declarative system stated without care would not have it. -/
theorem hasTy_unique (sig : Signature Op) (env : TyEnv) (e : Eff Op) {t₁ t₂ : EffTy}
    (h₁ : HasTy sig env e t₁) (h₂ : HasTy sig env e t₂) : t₁ = t₂ :=
  Option.some.inj ((effTy_complete sig e env t₁ h₁).symm.trans (effTy_complete sig e env t₂ h₂))

/-- The four sibling determinisms, by the same argument. -/
theorem stmtsHasTy_unique (sig : Signature Op) (env : TyEnv) (inLoop : Bool) (b : Stmts Op)
    {g₁ g₂ : GenTy} (h₁ : StmtsHasTy sig env inLoop b g₁)
    (h₂ : StmtsHasTy sig env inLoop b g₂) : g₁ = g₂ :=
  Option.some.inj
    ((stmtsTy_complete sig b env inLoop g₁ h₁).symm.trans (stmtsTy_complete sig b env inLoop g₂ h₂))

theorem effsHasTy_unique (sig : Signature Op) (env : TyEnv) (es : Effs Op) {t₁ t₂ : EffTy}
    (h₁ : EffsHasTy sig env es t₁) (h₂ : EffsHasTy sig env es t₂) : t₁ = t₂ :=
  Option.some.inj ((effsTy_complete sig es env t₁ h₁).symm.trans (effsTy_complete sig es env t₂ h₂))

theorem actionHasTy_unique (sig : Signature Op) (env : TyEnv) (a : ActionTerm Op)
    {t₁ t₂ : EffTy} (h₁ : ActionHasTy sig env a t₁) (h₂ : ActionHasTy sig env a t₂) : t₁ = t₂ :=
  Option.some.inj
    ((actionTy_complete sig a env t₁ h₁).symm.trans (actionTy_complete sig a env t₂ h₂))

theorem layerHasTy_unique (sig : Signature Op) (l : LayerTerm Op) {s₁ s₂ : LayerTy}
    (h₁ : LayerHasTy sig l s₁) (h₂ : LayerHasTy sig l s₂) : s₁ = s₂ :=
  Option.some.inj ((layerTy_complete sig l s₁ h₁).symm.trans (layerTy_complete sig l s₂ h₂))

/-- Weakening, restated on the relation: inserting an environment slot the shifted program
does not use changes no derivation (`Typing.lean:502-514`, `effTy_weaken`). -/
theorem hasTy_weaken (sig : Signature Op) (pre post : TyEnv) (inserted : Ty)
    (program : Eff Op) (t : EffTy) :
    HasTy sig (pre ++ inserted :: post) (Eff.weaken pre.length program) t ↔
      HasTy sig (pre ++ post) program t := by
  rw [← effTy_eq_hasTy, ← effTy_eq_hasTy, effTy_weaken]

/-- A closed program may be placed under a new surrounding binder without changing its
derivation (`Typing.lean:553-555`, `typeOf_weaken`). -/
theorem hasTy_weaken_closed (sig : Signature Op) (inserted : Ty) (program : Eff Op)
    (t : EffTy) :
    HasTy sig [inserted] (Eff.weaken 0 program) t ↔ HasTy sig [] program t :=
  hasTy_weaken sig [] [] inserted program t

/-! ## Axioms: the ceiling is `[propext, Quot.sound]` for all twenty-one -/

#print axioms effTy_sound
#print axioms stmtsTy_sound
#print axioms effsTy_sound
#print axioms actionTy_sound
#print axioms layerTy_sound
#print axioms layersTy_sound
#print axioms effTy_complete
#print axioms stmtsTy_complete
#print axioms effsTy_complete
#print axioms actionTy_complete
#print axioms layerTy_complete
#print axioms layersTy_complete
#print axioms effTy_eq_hasTy
#print axioms wellTyped_iff
#print axioms hasTy_unique
#print axioms stmtsHasTy_unique
#print axioms effsHasTy_unique
#print axioms actionHasTy_unique
#print axioms layerHasTy_unique
#print axioms hasTy_weaken
#print axioms hasTy_weaken_closed

end Conform.Effect4.Typing
