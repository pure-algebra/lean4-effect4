(** * BudgetDefs: definitions by budgeted unfolding, so the budget relation covers every program

    [Budget.v] relates Lean's [denoteRowsB] to the tree meaning on the fragment both have arms
    for. Lean's tree has no arm for definitions; the README's proposal 1 asks for them "by
    budgeted unfolding, monotone as loops are". This file gives the budgeted tree every arm of
    [Denote.denote] and proves the relation for every program, with no fragment condition.

    - [denoteW k call]: [Denote.denote]'s arms as a finite tree, with Lean's loop arm
      ([iterB], [loop_stepB], [then_opt]) at budget [k], and each call, invocation and
      parameter's run handed to [call].
    - [denoteD k d]: calls unfolded to depth [d]; a call deeper than that is cut. [denoteBD k],
      the tree at budget [k], is [denoteD k k] at the root.
    - [M]: the meaning of a program under its definitions, [interp_mrec] of [Denote.denote].
      [Denote.meaning] is [M] at the root, by definition ([meaning_is_M]).

    The theorems, each for every program, host and start: monotone in both budgets
    ([denoteD_approx]); below the meaning ([denoteD_below]); every finish and wait of the
    meaning's run is reached at some budget ([adequacyD]); so Lean's three chain outcomes are
    the run's [≈ Ret], frontier node and [≈ ITree.spin] ([finishesD_iff], [waitsD_iff],
    [divergesD_iff]), and with no host the meaning diverges exactly when every budget cuts
    ([meaning_divergesD_iff]). On [Budget.v]'s fragment the tree is Lean's transcription, node
    for node ([denoteBD_same]).

    The call depth is this file's count; Lean has no definition arm whose count it could
    follow. A call's body is no subterm of the program, so [adequacyD] is a strong induction on
    the silent steps before the run's end: each call adds one ([mrec_call]). *)

From Stdlib Require Import List ZArith String Bool Lia Arith.
Import ListNotations.
From ITree Require Import ITree ITreeFacts Basics.Basics Events.State Events.StateFacts
  Interp.RecursionFacts.
From Paco Require Import paco.
Import ITreeNotations Basics.Basics.Monads.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Judgments E4.Budget.

Local Open Scope list_scope.

(** ** The budgeted tree with definitions *)

(** What a call, an invocation or a parameter's run becomes: a program, its environment, the
    parameters' stack and the context, to a finite tree. *)
Definition calls_t : Type :=
  eff native_op -> list val_ -> list frame_args -> val_ -> program E1 (option exitv).

Definition cut_calls : calls_t := fun _ _ _ _ => PRet None.

Section Tree.

Context (bodies : list (eff native_op)).

(** **[Denote.denote]'s arms as a finite tree.** Each arm is [Denote.denote]'s; the sequence and
    the loop are [denoteRowsB]'s ([then_opt], [iterB], [loop_stepB]); a run of a definition or
    a parameter is [call]'s. *)
Fixpoint denoteW (k : nat) (call : calls_t) (e : eff native_op) (env : list val_)
    (ps : list frame_args) (ctx : val_) {struct e} : program E1 (option exitv) :=
  match e with
  | Eff_succeed t => PRet (Some (leaf (option_map Success (eval_term env t))))
  | Eff_fail t => PRet (Some (leaf (option_map fail_exit (eval_term env t))))
  | Eff_sync t => PRet (Some (Success (match eval_term env t with Some v => v | None => Val_unit end)))
  | Eff_suspend b => denoteW k call b env ps ctx
  | Eff_perform op r =>
    match eval_term env r with
    | None => PRet (Some bad_shape)
    | Some v =>
      match op with
      | NativeOp_external i => PVis (inr1 (Row i v)) (fun x => PRet (Some x))
      | NativeOp_refMake => PVis (inl1 (RefMake v)) (fun x => PRet (Some (Success x)))
      | NativeOp_refGet => PVis (inl1 (RefGet v)) (fun x => PRet (Some (Success x)))
      | NativeOp_refSet =>
        match v with
        | Val_list [c; w] => PVis (inl1 (RefSet c w)) (fun x => PRet (Some (Success x)))
        | _ => PRet (Some bad_shape)
        end
      (* a call: definition [n]'s body at the request alone, an empty frame pushed *)
      | NativeOp_call n =>
        match nth_error bodies (Z.to_nat n) with
        | Some body => call body [v] (([], []) :: ps) ctx
        | None => PRet (Some bad_shape)
        end
      (* a parameter: the innermost invocation's program, at its caller's environment *)
      | NativeOp_param i =>
        match ps with
        | (args, fenv) :: below =>
          match nth_error args (Z.to_nat i) with
          | Some a => call a (fenv ++ [v]) below ctx
          | None => PRet (Some bad_shape)
          end
        | [] => PRet (Some bad_shape)
        end
      | _ => PRet (Some outside)
      end
    end
  | Eff_bind a b =>
    then_opt (denoteW k call a env ps ctx) (fun ex =>
      match ex with
      | Success v => denoteW k call b (env ++ [v]) ps ctx
      | Failure _ => PRet (Some ex)
      end)
  | Eff_select t d a b =>
    match option_map (decide d) (eval_term env t) with
    | Some (Some (true, bound)) => denoteW k call a (env ++ bound) ps ctx
    | Some (Some (false, bound)) => denoteW k call b (env ++ bound) ps ctx
    | _ => PRet (Some bad_shape)
    end
  | Eff_provideContext t b =>
    match eval_term env t with Some c => denoteW k call b env ps c | None => PRet (Some bad_shape) end
  | Eff_withFiber (ActionTerm_context _) => PRet (Some (Success ctx))
  | Eff_defs _ _ main _ => denoteW k call main env ps ctx
  (* an invocation: as a call, with its programs pushed at this environment *)
  | Eff_invoke n r args =>
    match eval_term env r, nth_error bodies (Z.to_nat n) with
    | Some v, Some body => call body [v] ((effs_list args, env) :: ps) ctx
    | _, _ => PRet (Some bad_shape)
    end
  | Eff_iterate _ initial test step result body =>
    match eval_term env initial with
    | Some c0 => pmap opt_join (iterB (loop_stepB (fun env' => denoteW k call body env' ps ctx) env test step result) k c0)
    | None => PRet (Some bad_shape)
    end
  | _ => PRet (Some outside)
  end.

(** **Calls unfolded to depth [d]**: at depth zero a call is cut. *)
Fixpoint denoteD (k d : nat) {struct d} : calls_t :=
  denoteW k (match d with O => cut_calls | S d' => denoteD k d' end).

Lemma denoteD_eq k d : denoteD k d = denoteW k (match d with O => cut_calls | S d' => denoteD k d' end).
Proof. destruct d; reflexivity. Qed.

(** ** The meaning under the definitions *)

Definition hdl : RunE ~> itree E0 :=
  fun T r => match r in RunE T return itree E0 T with Run e env ps ctx => denote bodies e env ps ctx end.

(** **The meaning of a program at an environment, a stack and a context**, each run answered by
    the definitions. *)
Definition M (e : eff native_op) (env : list val_) (ps : list frame_args) (ctx : val_) : itree E1 exitv :=
  interp_mrec hdl (denote bodies e env ps ctx).

End Tree.

(** The tree at budget [k] of a program: loops at [k] tests, calls at depth [k], from the root. *)
Definition denoteBD (k : nat) (main : eff native_op) : program E1 (option exitv) :=
  denoteD (bodies_of main) k k main [] [] Val_unit.

(** [Denote.meaning] is [M] at the root, by definition. *)
Lemma meaning_is_M main : meaning main = M (bodies_of main) main [] [] Val_unit.
Proof. reflexivity. Qed.

(** Induction on a program, every constructor's parts named. *)
Ltac eff_ind e :=
  induction e as [t | t | ct | t | b IHb | op r | a IHa b IHb | ss | a IHa b IHb | a IHa b IHb c IHc
                 | a IHa b IHb | a IHa | a IHa | a IHa | yi | t om | act | a IHa | a IHa b IHb
                 | lt bb a IHa | sk | sk t a IHa | t a IHa b IHb | t d a IHa b IHb
                 | ty init test step result body IHbody | t a IHa | ds bs main IHmain ls | ni r args
                 | t a IHa].

(** ** Monotone in both budgets *)

Lemma denoteW_approx bodies (c1 c2 : calls_t) k k'
    (Hc : forall e env ps ctx, approx (c1 e env ps ctx) (c2 e env ps ctx)) (Hk : k <= k') :
  forall e env ps ctx, approx (denoteW bodies k c1 e env ps ctx) (denoteW bodies k' c2 e env ps ctx).
Proof.
  intros e; eff_ind e; intros env ps ctx; cbn [denoteW]; try apply approx_refl.
  - (* suspend *) apply IHb.
  - (* perform *)
    destruct (eval_term env r) as [v |]; [| apply approx_refl].
    destruct op; try apply approx_refl.
    + destruct (nth_error bodies (Z.to_nat i)); [apply Hc | apply approx_refl].
    + destruct ps as [| [args fenv] below]; [apply approx_refl |].
      destruct (nth_error args (Z.to_nat i)); [apply Hc | apply approx_refl].
  - (* bind *) apply approx_then_opt; [apply IHa |].
    intros [v | image]; [apply IHb | apply approx_refl].
  - (* select *)
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |]; auto; apply approx_refl.
  - (* iterate *)
    destruct (eval_term env init) as [c0 |]; [| apply approx_refl].
    apply approx_iter_loop_stepB; [intros env'; apply IHbody | exact Hk].
  - (* defs *) apply IHmain.
  - (* invoke *)
    destruct (eval_term env r) as [v |]; [| apply approx_refl].
    destruct (nth_error bodies (Z.to_nat ni)); [apply Hc | apply approx_refl].
  - (* provideContext *) destruct (eval_term env t) as [c |]; [apply IHa | apply approx_refl].
Qed.

(** **Monotone in the loop budget and the call depth** ([denoteRowsB_approx]'s statement). *)
Theorem denoteD_approx bodies k k' d d' : k <= k' -> d <= d' ->
  forall e env ps ctx, approx (denoteD bodies k d e env ps ctx) (denoteD bodies k' d' e env ps ctx).
Proof.
  intros Hk; revert d'; induction d as [| d IH]; intros d' Hd e env ps ctx.
  - rewrite (denoteD_eq _ k' d'). cbn [denoteD].
    apply denoteW_approx; [intros; constructor | exact Hk].
  - destruct d' as [| d']; [lia |]. cbn [denoteD].
    apply denoteW_approx; [intros; apply IH; lia | exact Hk].
Qed.

Corollary denoteBD_approx k k' main : k <= k' -> approx (denoteBD k main) (denoteBD k' main).
Proof. intros Hk; apply denoteD_approx; exact Hk. Qed.

(** [Denote.denote]'s triggers, with the injection into [E0] written out. *)
Lemma trigger_store {X} (e : StoreE X) : (trigger e : itree E0 X) = ITree.trigger (inr1 (inl1 e)).
Proof. reflexivity. Qed.
Lemma trigger_row {X} (e : RowE X) : (trigger e : itree E0 X) = ITree.trigger (inr1 (inr1 e)).
Proof. reflexivity. Qed.
Lemma trigger_run {X} (e : RunE X) : (trigger e : itree E0 X) = ITree.trigger (inl1 e).
Proof. reflexivity. Qed.

(** ** The meaning's equations, each exact in its silent steps *)

Section Equations.

Context (bodies : list (eff native_op)).
Local Notation hd := (hdl bodies).

Lemma mrec_ret {R} (x : R) : interp_mrec hd (Ret x) ≅ Ret x.
Proof. rewrite unfold_interp_mrec; reflexivity. Qed.

Lemma mrec_tau {R} (t : itree E0 R) : interp_mrec hd (Tau t) ≅ Tau (interp_mrec hd t).
Proof. rewrite unfold_interp_mrec; reflexivity. Qed.

(** A cell or host event: the event, then one silent step. *)
Lemma mrec_event {X} (e : E1 X) : interp_mrec hd (ITree.trigger (@inr1 RunE E1 X e)) ≅ Vis e (fun x => Tau (Ret x)).
Proof.
  rewrite unfold_interp_mrec; cbn. apply eqit_Vis; intros x. rewrite mrec_ret. reflexivity.
Qed.

(** **A call is one silent step, then the body's meaning.** *)
Lemma mrec_call body env ps ctx :
  interp_mrec hd (ITree.trigger (@inl1 RunE E1 _ (Run body env ps ctx))) ≅ Tau (M bodies body env ps ctx).
Proof. rewrite unfold_interp_mrec; cbn. rewrite bind_ret_r. reflexivity. Qed.

Lemma mrec_iter {I R} (f : I -> itree E0 (I + R)) (g : I -> itree E1 (I + R))
    (Hfg : forall i, interp_mrec hd (f i) ≅ g i) :
  forall i, interp_mrec hd (ITree.iter f i) ≅ ITree.iter g i.
Proof.
  ginit. gcofix CIH. intros i.
  rewrite 2 unfold_iter. rewrite interp_mrec_bind.
  guclo eqit_clo_bind. econstructor; [apply Hfg |].
  intros [i' | y] _ []; cbn.
  - rewrite mrec_tau. gstep; constructor. gbase. apply CIH.
  - rewrite mrec_ret. gstep; constructor; auto.
Qed.

Lemma mrec_loop_step (bodyT : list val_ -> itree E0 exitv) env test step result c :
  interp_mrec hd (loop_step bodyT env test step result c) ≅
    loop_stepF (fun env' => interp_mrec hd (bodyT env')) env test step result c.
Proof.
  unfold loop_step, loop_stepF.
  destruct (eval_term (env ++ [c]) test) as [[] |]; try apply mrec_ret.
  match goal with bb : bool |- _ => destruct bb end; [| apply mrec_ret].
  rewrite interp_mrec_bind. apply eq_itree_clo_bind with (UU := eq); [reflexivity |]. intros x ? <-.
  destruct x as [a | image]; [destruct (eval_term (env ++ [c; a]) step) |]; apply mrec_ret.
Qed.

(** **A loop's meaning is [ITree.iter] over its body's meaning.** *)
Lemma M_iterate ty init test step result body env ps ctx c0 :
  eval_term env init = Some c0 ->
  M bodies (Eff_iterate ty init test step result body) env ps ctx ≅
    ITree.iter (loop_stepF (fun env' => M bodies body env' ps ctx) env test step result) c0.
Proof.
  intros Hc. unfold M at 1. cbn [denote]. rewrite Hc.
  apply mrec_iter; intros c. apply mrec_loop_step.
Qed.

Lemma M_bind a b env ps ctx :
  M bodies (Eff_bind a b) env ps ctx ≅
    ITree.bind (M bodies a env ps ctx)
      (fun x => match x with Success v => M bodies b (env ++ [v]) ps ctx | Failure _ => Ret x end).
Proof.
  unfold M at 1. cbn [denote]. unfold seq. rewrite interp_mrec_bind.
  apply eq_itree_clo_bind with (UU := eq); [reflexivity |]. intros x ? <-.
  destruct x; [reflexivity | apply mrec_ret].
Qed.

End Equations.

(** ** Below the meaning *)

Ltac below_ret := constructor; rewrite mrec_ret; reflexivity.
Ltac norm_trigger := rewrite ?trigger_store, ?trigger_row, ?trigger_run.

(** A call's run below the call's meaning makes the whole tree below the meaning. *)
Lemma denoteW_below bodies k (call : calls_t)
    (Hc : forall e env ps ctx, below (call e env ps ctx) (M bodies e env ps ctx)) :
  forall e env ps ctx, below (denoteW bodies k call e env ps ctx) (M bodies e env ps ctx).
Proof.
  intros e; eff_ind e; intros env ps ctx; cbn [denoteW]; unfold M; cbn [denote]; unfold ret_val;
    try below_ret.
  - (* succeed *) destruct (eval_term env t); below_ret.
  - (* fail *) destruct (eval_term env t); below_ret.
  - (* suspend *) apply IHb.
  - (* perform *)
    destruct (eval_term env r) as [v |]; [| below_ret].
    destruct op; try below_ret.
    1-2: norm_trigger; econstructor; [unfold ITree.map; rewrite interp_mrec_bind, mrec_event, bind_vis; reflexivity |];
      intros x; constructor; rewrite bind_tau, bind_ret_l, mrec_ret, tau_eutt; reflexivity.
    + destruct v; try below_ret.
      destruct l as [| c' [| w [| ? ?]]]; try below_ret.
      norm_trigger; econstructor; [unfold ITree.map; rewrite interp_mrec_bind, mrec_event, bind_vis; reflexivity |];
        intros x; constructor; rewrite bind_tau, bind_ret_l, mrec_ret, tau_eutt; reflexivity.
    + norm_trigger; econstructor; [rewrite mrec_event; reflexivity |]. intros x; constructor; rewrite tau_eutt; reflexivity.
    + destruct (nth_error bodies (Z.to_nat i)) as [body |]; [| below_ret].
      norm_trigger; eapply below_eutt; [apply Hc |]. rewrite mrec_call, tau_eutt. reflexivity.
    + destruct ps as [| [args fenv] below]; [below_ret |].
      destruct (nth_error args (Z.to_nat i)) as [a |]; [| below_ret].
      norm_trigger; eapply below_eutt; [apply Hc |]. rewrite mrec_call, tau_eutt. reflexivity.
  - (* bind *)
    unfold seq. rewrite interp_mrec_bind. apply below_bind; [apply IHa | reflexivity |].
    intros [v | image]; cbn; [apply IHb | below_ret].
  - (* withFiber *) destruct act; below_ret.
  - (* select *)
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |]; try below_ret;
      [apply IHa | apply IHb].
  - (* iterate *)
    destruct (eval_term env init) as [c0 |]; [| below_ret].
    eapply below_eutt; [apply below_loop with (bodyF := fun env' => M bodies body env' ps ctx); intros env'; apply IHbody |].
    symmetry. apply eq_sub_eutt, mrec_iter. intros c'. apply mrec_loop_step.
  - (* defs *) apply IHmain.
  - (* invoke *)
    destruct (eval_term env r) as [v |]; [| below_ret].
    destruct (nth_error bodies (Z.to_nat ni)) as [body |]; [| below_ret].
    norm_trigger; eapply below_eutt; [apply Hc |]. rewrite mrec_call, tau_eutt. reflexivity.
  - (* provideContext *) destruct (eval_term env t) as [c' |]; [apply IHa | below_ret].
Qed.

(** **The tree at every budget and depth is below the meaning**: where it is not cut it is the
    meaning, node for node, up to silent steps. *)
Theorem denoteD_below bodies k : forall d e env ps ctx,
  below (denoteD bodies k d e env ps ctx) (M bodies e env ps ctx).
Proof.
  induction d as [| d IH]; intros e env ps ctx; cbn [denoteD]; apply denoteW_below; intros.
  - constructor.
  - apply IH.
Qed.

Corollary denoteBD_below k main : below (denoteBD k main) (meaning main).
Proof. apply denoteD_below. Qed.

(** ** Every end of the meaning is reached at some budget *)

#[global] Instance ends_eq_itree_proper {F A} n : Proper (eq_itree eq ==> eq ==> iff) (@ends F A n).
Proof. intros t t' Ht o o' <-; split; intros H; eapply ends_eq_itree; eauto; symmetry; exact Ht. Qed.

Lemma crun_outcome_monoD {St} (h : host E1 St) bodies k k' d d' e env ps ctx s o :
  k <= k' -> d <= d' -> crun h (denoteD bodies k d e env ps ctx) s = outcome_of o ->
  crun h (denoteD bodies k' d' e env ps ctx) s = outcome_of o.
Proof. intros Hk Hd; apply crun_outcome_approx, denoteD_approx; assumption. Qed.

Lemma mrec_trigger_eutt bodies {X} (e : E1 X) (f : X -> exitv) :
  interp_mrec (hdl bodies) (ITree.map f (ITree.trigger (@inr1 RunE E1 X e))) ≈ ITree.map f (ITree.trigger e).
Proof.
  unfold ITree.map. rewrite interp_mrec_bind, mrec_event. unfold ITree.trigger. rewrite !bind_vis.
  apply eqit_Vis; intros x. rewrite bind_tau, !bind_ret_l, mrec_ret, tau_eutt. reflexivity.
Qed.

Lemma mrec_row_eutt bodies (e : E1 exitv) :
  interp_mrec (hdl bodies) (ITree.trigger (@inr1 RunE E1 exitv e)) ≈ ITree.trigger e.
Proof.
  rewrite mrec_event. unfold ITree.trigger. apply eqit_Vis; intros x. rewrite tau_eutt. reflexivity.
Qed.

Lemma ends_event_adequacy {St} (h : host E1 St) bodies {X} (e : E1 X) (f : X -> exitv) m s o :
  ends m (run_tree h (interp_mrec (hdl bodies) (ITree.map f (ITree.trigger (@inr1 RunE E1 X e)))) s) o ->
  crun h (PVis e (fun x => PRet (Some (f x)))) s = outcome_of o.
Proof.
  intros H. apply adequacy_trigger. eapply Ends_eutt; [exists m; exact H |].
  apply run_tree_eutt; [apply mrec_trigger_eutt | reflexivity].
Qed.

Lemma ends_row_adequacy {St} (h : host E1 St) bodies (e : E1 exitv) m s o :
  ends m (run_tree h (interp_mrec (hdl bodies) (ITree.trigger (@inr1 RunE E1 exitv e))) s) o ->
  crun h (PVis e (fun x => PRet (Some x))) s = outcome_of o.
Proof.
  intros H. apply adequacy_row. eapply Ends_eutt; [exists m; exact H |].
  apply run_tree_eutt; [apply mrec_row_eutt | reflexivity].
Qed.

(** One step of [denoteD], folded back where the depth is not a constructor. *)
Ltac unfold_D := rewrite denoteD_eq; cbn [denoteW]; repeat rewrite <- denoteD_eq.

Ltac ret_case H := eapply ends_ret_inv in H; [| rewrite mrec_ret; apply run_ret]; subst.

(** **Every finish and every wait of the meaning's run under a host is reached at some
    budget.** A strong induction on the silent steps before the end: a call costs one, so the
    body's end comes sooner; inside, an induction on the program. *)
Theorem adequacyD {St} (h : host E1 St) bodies : forall n e env ps ctx s o,
  ends n (run_tree h (M bodies e env ps ctx) s) o ->
  exists k, crun h (denoteD bodies k k e env ps ctx) s = outcome_of o.
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind.
  enough (G : forall e m, m <= n -> forall env ps ctx s o,
             ends m (run_tree h (M bodies e env ps ctx) s) o ->
             exists k, crun h (denoteD bodies k k e env ps ctx) s = outcome_of o)
    by (intros e env ps ctx s o H; exact (G e n (le_n n) env ps ctx s o H)).
  intros e; eff_ind e; intros m Hm env ps ctx s o H;
    unfold M in H; cbn [denote] in H; unfold ret_val in H;
    try (ret_case H; exists 0; reflexivity).
  - (* succeed *) destruct (eval_term env t) eqn:He; ret_case H; exists 0; cbn; rewrite He; reflexivity.
  - (* fail *) destruct (eval_term env t) eqn:He; ret_case H; exists 0; cbn; rewrite He; reflexivity.
  - (* suspend *)
    destruct (IHb m Hm env ps ctx s o H) as [k Hk]. exists k. unfold_D. exact Hk.
  - (* perform *)
    destruct (eval_term env r) as [v |] eqn:Hev;
      [| ret_case H; exists 0; cbn; rewrite Hev; reflexivity].
    destruct op; try (ret_case H; exists 0; cbn; rewrite Hev; reflexivity).
    1-2: rewrite trigger_store in H; exists 0; cbn; rewrite Hev;
      exact (ends_event_adequacy h bodies _ Success m s o H).
    + destruct v; try (ret_case H; exists 0; cbn; rewrite Hev; reflexivity).
      destruct l as [| c' [| w [| ? ?]]]; try (ret_case H; exists 0; cbn; rewrite Hev; reflexivity).
      rewrite trigger_store in H; exists 0; cbn; rewrite Hev.
      exact (ends_event_adequacy h bodies _ Success m s o H).
    + rewrite trigger_row in H; exists 0; cbn; rewrite Hev.
      exact (ends_row_adequacy h bodies _ m s o H).
    + (* call *)
      destruct (nth_error bodies (Z.to_nat i)) as [body |] eqn:Hn;
        [| ret_case H; exists 0; cbn; rewrite Hev, Hn; reflexivity].
      rewrite trigger_run, mrec_call, run_tau in H.
      destruct (ends_tau_inv m _ _ o H (reflexivity _)) as [m' [-> Hm']].
      destruct (IHn m' ltac:(lia) body _ _ ctx s o Hm') as [k1 Hk1].
      exists (S k1). cbn [denoteD denoteW]. rewrite Hev. cbn [denoteW]. rewrite Hn.
      apply (crun_outcome_monoD h bodies k1 (S k1) k1 k1); [lia | lia | exact Hk1].
    + (* param *)
      destruct ps as [| [args fenv] below]; [ret_case H; exists 0; cbn; rewrite Hev; reflexivity |].
      destruct (nth_error args (Z.to_nat i)) as [a |] eqn:Hn;
        [| ret_case H; exists 0; cbn; rewrite Hev, Hn; reflexivity].
      rewrite trigger_run, mrec_call, run_tau in H.
      destruct (ends_tau_inv m _ _ o H (reflexivity _)) as [m' [-> Hm']].
      destruct (IHn m' ltac:(lia) a _ _ ctx s o Hm') as [k1 Hk1].
      exists (S k1). cbn [denoteD denoteW]. rewrite Hev. cbn [denoteW]. rewrite Hn.
      apply (crun_outcome_monoD h bodies k1 (S k1) k1 k1); [lia | lia | exact Hk1].
  - (* bind *)
    unfold seq in H. rewrite interp_mrec_bind, run_bind in H.
    destruct (ends_bind_inv m _ o H _ _ (reflexivity _)) as [[-> Hw] | ([s1 x] & m1 & m2 & H1 & H2 & ->)].
    + destruct (IHa m Hm env ps ctx s None Hw) as [ka Hka]. exists ka.
      unfold_D. unfold then_opt. rewrite crun_bind, Hka. reflexivity.
    + destruct (IHa m1 ltac:(lia) env ps ctx s (Some (s1, x)) H1) as [ka Hka].
      destruct x as [v | image]; cbn in H2.
      * destruct (IHb m2 ltac:(lia) (env ++ [v]) ps ctx s1 o H2) as [kb Hkb].
        exists (Nat.max ka kb). unfold_D. unfold then_opt. rewrite crun_bind.
        rewrite (crun_outcome_monoD h bodies ka (Nat.max ka kb) ka (Nat.max ka kb) a env ps ctx s (Some (s1, Success v)) ltac:(lia) ltac:(lia) Hka).
        cbn. apply (crun_outcome_monoD h bodies kb _ kb); [lia | lia | exact Hkb].
      * ret_case H2. exists ka. unfold_D. unfold then_opt. rewrite crun_bind, Hka. reflexivity.
  - (* withFiber *) destruct act; ret_case H; exists 0; reflexivity.
  - (* select *)
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |] eqn:Hsel;
      try (ret_case H; exists 0; cbn; rewrite Hsel; reflexivity).
    + destruct (IHa m Hm _ ps ctx s o H) as [k Hk]. exists k. unfold_D. rewrite Hsel. exact Hk.
    + destruct (IHb m Hm _ ps ctx s o H) as [k Hk]. exists k. unfold_D. rewrite Hsel. exact Hk.
  - (* iterate *)
    destruct (eval_term env init) as [c0 |] eqn:Hc0; [| ret_case H; exists 0; cbn; rewrite Hc0; reflexivity].
    rewrite (mrec_iter bodies _ (loop_stepF (fun env' => M bodies body env' ps ctx) env test step result)
               (fun c => mrec_loop_step bodies _ env test step result c)) in H.
    destruct (adequacy_loop_upto h n (fun env' => M bodies body env' ps ctx)
                (fun k env' => denoteD bodies k k body env' ps ctx)
                (fun k k' env' Hk => denoteD_approx bodies k k' k k' Hk Hk body env' ps ctx)
                (fun m' env' s' o' Hm' H' => IHbody m' Hm' env' ps ctx s' o' H')
                env test step result m c0 s o Hm H) as [k Hk].
    exists k. unfold_D. rewrite Hc0. exact Hk.
  - (* defs *)
    destruct (IHmain m Hm env ps ctx s o H) as [k Hk]. exists k. unfold_D. exact Hk.
  - (* invoke *)
    destruct (eval_term env r) as [v |] eqn:Hev; [| ret_case H; exists 0; cbn; rewrite Hev; reflexivity].
    destruct (nth_error bodies (Z.to_nat ni)) as [body |] eqn:Hn;
      [| ret_case H; exists 0; cbn; rewrite Hev, Hn; reflexivity].
    rewrite trigger_run, mrec_call, run_tau in H.
    destruct (ends_tau_inv m _ _ o H (reflexivity _)) as [m' [-> Hm']].
    destruct (IHn m' ltac:(lia) body _ _ ctx s o Hm') as [k1 Hk1].
    exists (S k1). cbn [denoteD denoteW]. rewrite Hev, Hn.
    apply (crun_outcome_monoD h bodies k1 (S k1) k1 k1); [lia | lia | exact Hk1].
  - (* provideContext *)
    destruct (eval_term env t) as [c' |] eqn:Hc; [| ret_case H; exists 0; cbn; rewrite Hc; reflexivity].
    destruct (IHa m Hm env ps c' s o H) as [k Hk]. exists k. unfold_D. rewrite Hc. exact Hk.
Qed.

Corollary adequacyBD {St} (h : host E1 St) main s o :
  Ends (run_tree h (meaning main) s) o -> exists k, crun h (denoteBD k main) s = outcome_of o.
Proof. intros [n Hn]. exact (adequacyD h (bodies_of main) n main [] [] Val_unit s o Hn). Qed.

(** ** The three outcomes are one, for every program *)

Definition FinishesD {St} (h : host E1 St) main s (r : exitv) s' : Prop :=
  exists k, crun h (denoteBD k main) s = Some (Some r, s').
Definition WaitsD {St} (h : host E1 St) main s : Prop :=
  exists k, crun h (denoteBD k main) s = None.
Definition ChainDivergesD {St} (h : host E1 St) main s : Prop :=
  forall k, exists s', crun h (denoteBD k main) s = Some (None, s').

Theorem finishesD_iff {St} (h : host E1 St) main s r s' :
  FinishesD h main s r s' <-> run_tree h (meaning main) s ≈ Ret (s', r).
Proof.
  split.
  - intros [k Hk]. destruct (below_run h _ _ (denoteBD_below k main) s (Some (s', r)) Hk) as [n Hn].
    eapply ends_some_eutt; exact Hn.
  - intros Hr. apply (adequacyBD h main s (Some (s', r))). apply eutt_ret_ends; exact Hr.
Qed.

Theorem waitsD_iff {St} (h : host E1 St) main s :
  WaitsD h main s <-> exists X (ev : StuckE E1 X) k, run_tree h (meaning main) s ≈ Vis ev k.
Proof.
  split.
  - intros [k Hk]. destruct (below_run h _ _ (denoteBD_below k main) s None Hk) as [n Hn].
    eapply ends_none_eutt; exact Hn.
  - intros (X & ev & kk & Hv). apply (adequacyBD h main s None). eapply eutt_vis_ends; exact Hv.
Qed.

(** **Divergence is one statement, for every program**: a cut at every budget exactly when the
    meaning's run is [≈ ITree.spin]. *)
Theorem divergesD_iff {St} (h : host E1 St) main s :
  ChainDivergesD h main s <-> Diverges (run_tree h (meaning main) s).
Proof.
  unfold Diverges; split.
  - intros Hd. apply no_ends_spin. intros n o Hn.
    destruct (adequacyBD h main s o (ex_intro _ n Hn)) as [k Hk].
    destruct (Hd k) as [s' Hs']. rewrite Hk in Hs'. destruct o as [[? ?] |]; discriminate.
  - intros Hsp k. destruct (crun h (denoteBD k main) s) as [[[r |] s'] |] eqn:Hk.
    + exfalso. assert (Hf : FinishesD h main s r s') by (exists k; exact Hk).
      apply finishesD_iff in Hf. rewrite Hf in Hsp. exact (eutt_Ret_spin_abs _ Hsp).
    + exists s'; reflexivity.
    + exfalso. assert (Hw : WaitsD h main s) by (exists k; exact Hk).
      apply waitsD_iff in Hw as (X & ev & kk & Hv). rewrite Hv in Hsp. exact (eutt_Vis_spin_abs _ _ Hsp).
Qed.

(** **With no host, for every program**: the meaning diverges exactly when every budget cuts. *)
Theorem meaning_divergesD_iff main :
  Diverges (meaning main) <-> forall k, denoteBD k main = PRet None.
Proof.
  unfold Diverges. split.
  - intros Hsp k. eapply below_spin; [apply denoteBD_below | exact Hsp].
  - intros Hcut. apply no_ends_spin. intros n o Hn.
    pose proof (ends_run_nobody n _ o tt Hn) as Hr.
    destruct (adequacyBD (St := unit) nobody main tt _ Hr) as [k Hk].
    rewrite Hcut in Hk. destruct o; discriminate.
Qed.

(** ** On [Budget.v]'s fragment the tree is Lean's transcription *)

(** Two finite trees with the same nodes, every continuation pointwise. *)
Inductive same {E R} : program E R -> program E R -> Prop :=
| same_ret r : same (PRet r) (PRet r)
| same_vis X (e : E X) k k' : (forall x, same (k x) (k' x)) -> same (PVis e k) (PVis e k').

Lemma same_refl {E R} (p : program E R) : same p p.
Proof. induction p; constructor; auto. Qed.

Lemma same_pbind {E A B} (p q : program E A) (F G : A -> program E B) :
  same p q -> (forall a, same (F a) (G a)) -> same (pbind p F) (pbind q G).
Proof. intros H HFG; induction H; cbn; [apply HFG | constructor; auto]. Qed.

(** Same trees, same run under every host. *)
Lemma same_crun {E R S} (h : host E S) (p q : program E R) s : same p q -> crun h p s = crun h q s.
Proof.
  intros H; revert s; induction H as [r | X e k k' _ IH]; intros s; cbn; [reflexivity |].
  destruct (h X e s) as [[x s'] |]; [apply IH | reflexivity].
Qed.

Lemma same_iterB {E X Y} (f g : X -> program E (Y + X)) (Hfg : forall x, same (f x) (g x)) :
  forall j x, same (iterB f j x) (iterB g j x).
Proof.
  induction j as [| j IH]; intros x; cbn; [constructor |].
  apply same_pbind; [apply Hfg |]. intros [y | x']; cbn; [constructor | apply IH].
Qed.

Lemma same_loop_stepB (b1 b2 : list val_ -> program E1 (option exitv)) (Hb : forall env, same (b1 env) (b2 env))
    env test step result c :
  same (loop_stepB b1 env test step result c) (loop_stepB b2 env test step result c).
Proof.
  unfold loop_stepB. destruct (eval_term (env ++ [c]) test) as [[] |]; try constructor.
  match goal with bb : bool |- _ => destruct bb end; [| constructor].
  apply same_pbind; [apply Hb |]. intros o; apply same_refl.
Qed.

(** **Where [denoteRowsB] has an arm, the tree with definitions is Lean's tree**, node for node,
    whatever the calls and the depth. *)
Theorem denoteW_same bodies k call : forall e env ps ctx, in_fragment e = true ->
  same (denoteW bodies k call e env ps ctx) (denoteB k e env).
Proof.
  intros e; eff_ind e; intros env ps ctx Hin; cbn in Hin; try discriminate; cbn [denoteW denoteB];
    try apply same_refl.
  - apply IHb; exact Hin.
  - destruct (eval_term env r) as [v |]; [| apply same_refl].
    destruct op; try discriminate; apply same_refl.
  - apply andb_prop in Hin as [Ha Hb].
    apply same_pbind; [apply IHa; exact Ha |]. intros [[v | image] |]; [apply IHb; exact Hb | apply same_refl | apply same_refl].
  - apply andb_prop in Hin as [Ha Hb].
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |];
      try apply same_refl; [apply IHa | apply IHb]; assumption.
  - destruct (eval_term env init) as [c0 |]; [| apply same_refl].
    apply same_pbind; [| intros; apply same_refl].
    apply same_iterB. intros c. apply same_loop_stepB. intros env'. apply IHbody; exact Hin.
Qed.

Corollary denoteBD_same k main : in_fragment main = true -> same (denoteBD k main) (denoteB k main []).
Proof. intros Hin. unfold denoteBD. rewrite denoteD_eq. apply denoteW_same; exact Hin. Qed.
