(* The comparison lane's development (rocq/README.md), moved unchanged from the study of
   2026-10-16:
   git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-16-itrees/rocq/Judgments.v.
   The study's README and its other files stay there. *)

(** * Judgments: trace, divergence, frontier and equivalence for the tree meaning

    DB-03 ([docs/DESIGN-BASIS.md]) asks that a relation to an interaction-tree model come with
    explicit trace, divergence and equivalence judgments. Over [Denote.meaning] they are:

    - **equivalence**: [eutt eq], written [≈]: equal up to finitely many silent steps;
    - **trace**: ITree's [is_trace] ([ITree.Interp.Traces]), the finite traces of visible events
      with their answers, ending in a result or cut. Two trees have the same traces exactly when
      they are equivalent ([traces_iff_equivalent], the library's [trace_eq_iff_eutt]);
    - **divergence**: [≈ ITree.spin], an endless run of silent steps; the witness is the
      infinite tree itself, never a budget;
    - **frontier**: a node [Vis (Waits i v) k]: a call no answer exists for ([Run.WaitE]).

    And the facts that keep them apart: an exit is no divergence ([exit_not_divergence]), a
    frontier is no divergence ([frontier_not_divergence]), and a reply tape cannot tell two
    equivalent meanings apart ([tape_respects_equivalence]). [loop_diverges] proves an Eff loop
    whose test is always true divergent, as a theorem about its meaning, at no budget.

    What Lean has instead (reading): [denoteRowsB k] cuts loops at a budget, and its runs at
    growing budgets form a chain ([denoteRowsB_approx], [src/Effect4/Laws/Program/DenoteRowsB.lean]);
    "telling divergence from a frontier at every budget is not yet a statement" (DB-03). The
    proposals of the README state the Lean side of this relation. *)

From Stdlib Require Import List ZArith String.
Import ListNotations.
From ITree Require Import ITree ITreeFacts Interp.Traces Interp.RecursionFacts Basics.Basics
  Events.State Events.StateFacts.
From Paco Require Import paco.
Import ITreeNotations Basics.Basics.Monads.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run.

Local Open Scope Z_scope.

(** ** The judgments *)

Definition Equivalent {E R} (t1 t2 : itree E R) : Prop := t1 ≈ t2.
Definition Diverges {E R} (t : itree E R) : Prop := t ≈ ITree.spin.

(** **Traces are the observation of equivalence**: equal sets of finite traces, exactly when
    equivalent (ITree's [trace_eq_iff_eutt]). *)
Theorem traces_iff_equivalent {E R} (t1 t2 : itree E R) :
  trace_eq t1 t2 <-> Equivalent t1 t2.
Proof. unfold Equivalent. split; intros H; apply trace_eq_iff_eutt; exact H. Qed.

(** ** Exits, frontiers and divergence are three outcomes *)

Theorem exit_not_divergence {E R} (r : R) : ~ Diverges (Ret r : itree E R).
Proof. unfold Diverges. intros H. exact (eutt_Ret_spin_abs _ H). Qed.

Theorem frontier_not_divergence {R} (i : int) (v : val_) (k : void -> itree WaitE R) :
  ~ Diverges (Vis (Waits i v) k).
Proof. unfold Diverges. intros H. exact (eutt_Vis_spin_abs _ _ H). Qed.

(** **A reply tape cannot tell equivalent meanings apart**: any stateful host, the tape among
    them, runs equivalent trees to equivalent runs. *)
Theorem tape_respects_equivalence {E F S R} (h : E ~> stateT S (itree F)) (t1 t2 : itree E R) (s : S) :
  Equivalent t1 t2 -> Equivalent (interp_state h t1 s) (interp_state h t2 s).
Proof. intros H. exact (eutt_interp_state_eq h R t1 t2 H s s eq_refl). Qed.

(** ** A divergent program *)

(** [iterate] at cursor [0]: the test is [true], the body succeeds with [unit], the step keeps
    the cursor. It never ends and calls nothing. *)
Definition loop_forever : eff native_op :=
  Eff_iterate None (Term_lit (Lit_nat 0)) (Term_lit (Lit_bool true)) (Term_var 0)
    (Term_lit Lit_unit) (Eff_succeed (Term_lit Lit_unit)).

Lemma iter_continue_diverges {E A B} (f : A -> itree E (A + B)) :
  (forall a, f a ≅ Ret (inl a)) -> forall a, ITree.iter f a ≈ ITree.spin.
Proof.
  intros Hf. ginit. gcofix CIH. intros a.
  rewrite unfold_iter, Hf, bind_ret_l. cbn.
  rewrite (itree_eta ITree.spin). cbn.
  gstep. constructor. gfinal. left. apply CIH.
Qed.

Lemma interp_spin {E F R} (h : E ~> itree F) : interp h (ITree.spin : itree E R) ≈ ITree.spin.
Proof.
  ginit. gcofix CIH.
  rewrite (itree_eta (ITree.spin : itree E R)). cbn.
  rewrite interp_tau.
  rewrite (itree_eta (ITree.spin : itree F R)). cbn.
  gstep. constructor. gfinal. left. apply CIH.
Qed.

(** The loop's tree before its runs are answered diverges. *)
Lemma loop_denote_diverges ps ctx :
  Diverges (denote (bodies_of loop_forever) loop_forever [] ps ctx).
Proof.
  unfold Diverges. cbn.
  apply iter_continue_diverges. intros c.
  unfold loop_step, ret_val; cbn.
  rewrite bind_ret_l. reflexivity.
Qed.

(** **The loop's meaning diverges**: a theorem about its tree, at no budget. *)
Theorem loop_diverges : Diverges (meaning loop_forever).
Proof.
  unfold Diverges, meaning.
  rewrite mrec_as_interp.
  pose proof (loop_denote_diverges [] Val_unit) as H. unfold Diverges in H.
  match goal with
  | |- interp ?h _ ≈ _ =>
    change (interp h (denote (bodies_of loop_forever) loop_forever [] [] Val_unit) ≈ ITree.spin)
  end.
  rewrite H. apply interp_spin.
Qed.
