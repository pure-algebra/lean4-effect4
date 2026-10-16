(** Proofs about the native to-do host [todo_core.ml], over its rocq-of-ocaml translation
    [Todo_core.v]. Each statement names the property of [todo_core.ml]'s header it proves.
    Totality (C1) is Rocq's own check: every [Fixpoint] of [Todo_core.v] is accepted as
    structurally recursive. *)

From Stdlib Require Import List ZArith Lia Sorting.Sorted Bool.
Import ListNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import RocqOfOCaml.Settings.
(* Last, so that the translation's [find] and [remove] shadow [List]'s. *)
Require Import Todo.Todo_core.
Open Scope Z_scope.
Open Scope list_scope.

(** The library of the translation shadows [map] and [filter]; these are the standard ones. *)
Notation lmap := Stdlib.Lists.List.map.
Notation lfilter := Stdlib.Lists.List.filter.

(** OCaml's [=] on [int] is [equiv_decb] at [Z]'s decidable equality. *)
Lemma eqb_spec (a b : int) : reflect (a = b) (equiv_decb a b).
Proof.
  unfold equiv_decb. destruct (equiv_dec a b) as [E | N]; constructor; [exact E | exact N].
Qed.

(** The ids of the stored to-dos, in order. *)
Definition ids (items : list todo) : list Z := lmap (fun x => x.(todo.id)) items.

(** C3's invariant: the ids ascend strictly and stay below [next]. *)
Definition ordered (s : t) : Prop :=
  StronglySorted Z.lt (ids s.(t.items)) /\ Forall (fun i => i < s.(t.next)) (ids s.(t.items)).

(** * C2: [insert] answers the id [next], and the next state's [next] is one more. *)
Theorem insert_id (title : string) (s : t) :
  fst (insert title s) =
    inl {| todo.id := s.(t.next); todo.title := title; todo.done_ := false |} /\
  (snd (insert title s)).(t.next) = s.(t.next) + 1.
Proof. split; reflexivity. Qed.

(** * The ids under each list function *)

Lemma ids_snoc (items : list todo) (x : todo) : ids (snoc items x) = ids items ++ [x.(todo.id)].
Proof. unfold ids. induction items as [| y rest IH]; simpl; [reflexivity | now rewrite IH]. Qed.

Lemma ids_mark (id : int) (d : bool) (items : list todo) : ids (mark id d items) = ids items.
Proof.
  unfold ids. induction items as [| y rest IH]; simpl; [reflexivity |].
  destruct (equiv_decb y.(todo.id) id); simpl; now rewrite IH.
Qed.

Lemma ids_remove (id : int) (items : list todo) :
  ids (remove id items) = lfilter (fun i => negb (equiv_decb i id)) (ids items).
Proof.
  unfold ids. induction items as [| y rest IH]; cbn [remove lmap]; [reflexivity |].
  cbn [lfilter]. destruct (equiv_decb y.(todo.id) id); cbn [negb lmap]; now rewrite IH.
Qed.

(** * Sortedness facts over [Z.lt] *)

Lemma sorted_snoc (l : list Z) (n : Z) :
  StronglySorted Z.lt l -> Forall (fun i => i < n) l -> StronglySorted Z.lt (l ++ [n]).
Proof.
  induction l as [| a rest IH]; intros Hs Hb; simpl.
  - constructor; constructor.
  - inversion Hs as [| ? ? Hrest Hhead]; subst. inversion Hb as [| ? ? Han Hrestb]; subst.
    constructor; [now apply IH |].
    apply Forall_app; split; [exact Hhead | constructor; [exact Han | constructor]].
Qed.

Lemma forall_filter (P : Z -> Prop) (f : Z -> bool) (l : list Z) :
  Forall P l -> Forall P (lfilter f l).
Proof.
  intro H. apply Forall_forall. intros x Hx. apply filter_In in Hx as [Hin _].
  exact (proj1 (Forall_forall P l) H x Hin).
Qed.

Lemma sorted_filter (f : Z -> bool) (l : list Z) :
  StronglySorted Z.lt l -> StronglySorted Z.lt (lfilter f l).
Proof.
  induction l as [| a rest IH]; intro Hs; simpl; [constructor |].
  inversion Hs as [| ? ? Hrest Hhead]; subst.
  destruct (f a); [constructor; [now apply IH | now apply forall_filter] | now apply IH].
Qed.

(** * C3: every method keeps the invariant *)

Theorem insert_keeps_ordered (title : string) (s : t) :
  ordered s -> ordered (snd (insert title s)).
Proof.
  intros [Hs Hb]. unfold ordered; simpl. rewrite ids_snoc; simpl. split.
  - now apply sorted_snoc.
  - apply Forall_app; split.
    + eapply Forall_impl; [| exact Hb]. simpl. intros i Hi. lia.
    + constructor; [lia | constructor].
Qed.

Theorem all_keeps_ordered (s : t) : ordered s -> ordered (snd (all tt s)).
Proof. trivial. Qed.

Theorem set_done_keeps_ordered (request : int * bool) (s : t) :
  ordered s -> ordered (snd (set_done request s)).
Proof.
  destruct request as [id d]. intro H. unfold set_done; simpl.
  destruct (find id s.(t.items)); [| exact H].
  unfold ordered in *; simpl. now rewrite ids_mark.
Qed.

Theorem delete_keeps_ordered (id : int) (s : t) :
  ordered s -> ordered (snd (delete id s)).
Proof.
  intros [Hs Hb]. unfold ordered; simpl. rewrite ids_remove.
  split; [now apply sorted_filter | now apply forall_filter].
Qed.

(** C3, whole: under any of the four methods, a state that holds the invariant leads to one
    that holds it. *)
Theorem step_keeps_ordered (s : t) :
  ordered s ->
  (forall title, ordered (snd (insert title s))) /\
  ordered (snd (all tt s)) /\
  (forall request, ordered (snd (set_done request s))) /\
  (forall id, ordered (snd (delete id s))).
Proof.
  intro H. repeat split; intros;
    first [ now apply insert_keeps_ordered | now apply all_keeps_ordered
          | now apply set_done_keeps_ordered | now apply delete_keeps_ordered
          | apply insert_keeps_ordered; exact H | apply set_done_keeps_ordered; exact H
          | apply delete_keeps_ordered; exact H ].
Qed.

(** C3's reading: an ordered state stores each id at most once. *)
Theorem ordered_ids_unique (s : t) : ordered s -> NoDup (ids s.(t.items)).
Proof.
  intros [Hs _]. induction Hs as [| a rest Hrest IH Hhead]; constructor; [| exact IH].
  intro Hin. pose proof (proj1 (Forall_forall _ _) Hhead a Hin). lia.
Qed.

(** * C4: an absent id changes nothing *)

Lemma find_absent (id : int) (items : list todo) : mem id items = false -> find id items = None.
Proof.
  induction items as [| y rest IH]; simpl; [reflexivity |].
  intro H. apply orb_false_iff in H as [Hy Hrest]. rewrite Hy. now apply IH.
Qed.

Lemma remove_absent (id : int) (items : list todo) : mem id items = false -> remove id items = items.
Proof.
  induction items as [| y rest IH]; simpl; [reflexivity |].
  intro H. apply orb_false_iff in H as [Hy Hrest]. rewrite Hy. now rewrite IH.
Qed.

Theorem absent_set_done (id : int) (d : bool) (s : t) :
  mem id s.(t.items) = false -> set_done (id, d) s = (inl None, s).
Proof. intro H. unfold set_done; simpl. now rewrite find_absent. Qed.

Theorem absent_delete (id : int) (s : t) :
  mem id s.(t.items) = false -> delete id s = (inl false, s).
Proof.
  intro H. unfold delete. rewrite H, remove_absent by exact H. now destruct s.
Qed.

(** After [delete id], [set_done] at [id] finds nothing. *)
Lemma find_remove (id : int) (items : list todo) : find id (remove id items) = None.
Proof.
  induction items as [| y rest IH]; simpl; [reflexivity |].
  destruct (equiv_decb y.(todo.id) id) eqn:E; [exact IH | simpl; now rewrite E].
Qed.

Theorem delete_then_set_done (id : int) (d : bool) (s : t) :
  fst (set_done (id, d) (snd (delete id s))) = inl None.
Proof. unfold set_done, delete; simpl. now rewrite find_remove. Qed.
