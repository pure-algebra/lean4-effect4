(** * SkeletonApprox: a larger budget only extends Lean's call tree

    The theorem is about [Skeleton.v], which is generated from Lean's [Effect4.Run.Tree] (its
    base-phase LCNF, by [src/OCaml5/Tools/GallinaGen.lean]). It holds for every evaluator: the
    functor [Approx] takes any [Eval], so no fact of a term's value, a cell step or a context is
    read. It holds for every program: every arm of [level] and [statements] is covered. *)

From Stdlib Require Import List ZArith String Lia.
Import ListNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Skeleton.

Scheme eff_mut := Induction for eff Sort Prop
  with stmt_mut := Induction for stmt Sort Prop
  with stmts_mut := Induction for stmts Sort Prop.

Module Approx (E : Eval).

Module Import S := Skeleton E.
Import E.

(** [t ⊑ t']: [t'] is [t] with some cuts grown into more tree ([Approx] in
    [src/Effect4/Laws/Run/Tree.lean]). *)
Inductive approx : tree -> tree -> Prop :=
| approx_cut t : approx Tree_cut t
| approx_done ex : approx (Tree_done ex) (Tree_done ex)
| approx_call i v r r' : (forall a, approx (r a) (r' a)) -> approx (Tree_call i v r) (Tree_call i v r')
| approx_cell o r r' : (forall a, approx (r a) (r' a)) -> approx (Tree_cell o r) (Tree_cell o r').

Lemma approx_refl t : approx t t.
Proof. induction t; constructor; auto. Qed.

Lemma bind_mono t t' f f' :
  approx t t' -> (forall x, approx (f x) (f' x)) -> approx (bind t f) (bind t' f').
Proof.
  intros H Hf; induction H; cbn [bind].
  - constructor.
  - apply Hf.
  - constructor; intro a; auto.
  - constructor; intro a; auto.
Qed.

Lemma andThen_mono t t' f f' :
  approx t t' -> (forall v, approx (f v) (f' v)) -> approx (andThen t f) (andThen t' f').
Proof.
  intros H Hf; unfold andThen; apply bind_mono; [exact H |].
  intros [v | c]; [apply Hf | apply approx_refl].
Qed.

Lemma loop_mono body body' env test step result :
  (forall e, approx (body e) (body' e)) ->
  forall n n' c, n <= n' ->
  approx (loop body env test step result n c) (loop body' env test step result n' c).
Proof.
  intros Hb n; induction n as [| n IH]; intros n' c Hn; [constructor |].
  destruct n' as [| n']; [lia |]; cbn [loop].
  destruct (eval_test (eval_push env c) test) as [[|] |]; [| apply approx_refl | apply approx_refl].
  apply bind_mono; [apply Hb |].
  intros [v | cause]; [| apply approx_refl].
  destruct (eval_term (eval_push (eval_push env c) v) step); [apply IH; lia | apply approx_refl].
Qed.

Lemma whileRounds_mono r r' :
  (forall a a', (forall u, approx (a u) (a' u)) -> forall u, approx (r a u) (r' a' u)) ->
  forall n n' u, n <= n' -> approx (whileRounds r n u) (whileRounds r' n' u).
Proof.
  intros Hr n; induction n as [| n IH]; intros n' u Hn; [constructor |].
  destruct n' as [| n']; [lia |]; cbn [whileRounds].
  apply Hr; intro; apply IH; lia.
Qed.

(** Two ways to unfold a definition, the second above the first at every call. *)
Definition urel (u u' : eff native_op -> list val_ -> list frame -> ctx -> tree) : Prop :=
  forall e env fr c, approx (u e env fr c) (u' e env fr c).

(** Two continuations of a loop's [break], the second above the first. *)
Inductive orel : option (unit -> tree) -> option (unit -> tree) -> Prop :=
| orel_none : orel None None
| orel_some f f' : (forall u, approx (f u) (f' u)) -> orel (Some f) (Some f').

Definition P_eff (e : eff native_op) : Prop :=
  forall table bodies k k' u u' env fr c, k <= k' -> urel u u' ->
  approx (level table bodies k u e env fr c) (level table bodies k' u' e env fr c).

Definition P_stmts (ss : stmts native_op) : Prop :=
  forall table bodies k k' u u' env fr c x5 x5' x6 x6', k <= k' -> urel u u' ->
  (forall t, approx (x5 t) (x5' t)) -> orel x6 x6' ->
  approx (statements table bodies k u ss env fr c x5 x6)
         (statements table bodies k' u' ss env fr c x5' x6').

Definition P_stmt (s : stmt native_op) : Prop :=
  match s with
  | Stmt_bindYield e | Stmt_yieldDiscard e => P_eff e
  | Stmt_ifElse _ a b => P_stmts a /\ P_stmts b
  | Stmt_whileTrue b => P_stmts b
  | _ => True
  end.

(** Both sides read the same scrutinee: split it on both at once, then close what is equal, what
    a lemma above relates, and what the hypotheses relate. *)
Ltac mono :=
  repeat match goal with
  | |- approx ?t ?t => apply approx_refl
  | |- approx (match ?x with _ => _ end) (match ?x with _ => _ end) => destruct x
  | Ho : orel ?x ?x' |- approx (match ?x with _ => _ end) (match ?x' with _ => _ end) => destruct Ho
  | |- approx (bind _ _) (bind _ _) => apply bind_mono; [| intro]
  | |- approx (andThen _ _) (andThen _ _) => apply andThen_mono; [| intro]
  | Hu : urel ?u ?u' |- approx (?u _ _ _ _) (?u' _ _ _ _) => apply Hu
  | Hf : forall _, approx (?f _) (?f' _) |- approx (?f _) (?f' _) => apply Hf
  | IH : P_eff ?e, Hk : ?k <= ?k', Hu : urel ?u ?u' |-
      approx (level _ _ ?k ?u ?e _ _ _) (level _ _ ?k' ?u' ?e _ _ _) => apply IH; [exact Hk | exact Hu]
  | IH : P_stmts ?ss, Hk : ?k <= ?k', Hu : urel ?u ?u' |-
      approx (statements _ _ ?k ?u ?ss _ _ _ _ _) (statements _ _ ?k' ?u' ?ss _ _ _ _ _) =>
      apply IH; [exact Hk | exact Hu | intro; cbv beta |]
  | Ho : orel ?x ?x' |- orel ?x ?x' => exact Ho
  | |- orel None None => constructor
  | |- orel (Some _) (Some _) => constructor; intro; cbv beta
  | |- approx (loop _ _ _ _ _ _ _) (loop _ _ _ _ _ _ _) => apply loop_mono; [intro; cbv beta | assumption]
  | |- approx (whileRounds _ _ _) (whileRounds _ _ _) =>
      apply whileRounds_mono; [let Ha := fresh "Ha" in intros ? ? Ha ?; cbv beta | assumption]
  end.

Theorem level_mono : forall e, P_eff e.
Proof.
  apply (eff_mut native_op P_eff P_stmt P_stmts); intros;
    match goal with
    | |- P_eff _ => unfold P_eff; intros; cbn [level]; mono
    | |- P_stmt _ => cbn [P_stmt]; (split; assumption) || assumption || exact I
    | |- P_stmts Stmts_nil => unfold P_stmts; intros; cbn [statements]; mono
    | |- P_stmts (Stmts_cons ?s _) =>
        unfold P_stmts; intros; cbn [statements];
        destruct s; cbn [P_stmt] in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; mono
    end.
Qed.

Lemma unfolded_mono table bodies k k' : k <= k' ->
  forall d d', d <= d' -> urel (unfolded table bodies k d) (unfolded table bodies k' d').
Proof.
  intros Hk d; induction d as [| d IH]; intros d' Hd e env fr c; [constructor |].
  destruct d' as [| d']; [lia |]; cbn [unfolded].
  apply level_mono; [exact Hk |]. apply IH; lia.
Qed.

(** **A larger budget only extends the tree**: Lean's [Tree.ofProgram_approx]
    ([src/Effect4/Laws/Run/Tree.lean]), for every program and every evaluator. *)
Theorem ofProgram_approx table k k' main : k <= k' ->
  approx (ofProgram table k main) (ofProgram table k' main).
Proof.
  intros Hk; unfold ofProgram.
  apply level_mono; [exact Hk |]. apply unfolded_mono; exact Hk.
Qed.

End Approx.
