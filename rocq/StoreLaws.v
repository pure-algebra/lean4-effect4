(** * The content-addressed store's laws, over Lean's own code

    Every definition this file reads about the store is `StoreCode.v`, printed from the base-phase
    LCNF of `Effect4.Store` (`make gen-rocq`). The hash and the byte codecs are parameters of
    [Prim]: no theorem here assumes anything of the hash. What a proof needs of a parameter is a
    field of [PrimLaws] below, each the statement Lean's compiler erased from the constant it
    names (a `DecidableEq` instance decides equality). A theorem that needs a fact of the codecs
    takes it as a premise named after the Lean theorem that proves it
    (`Effect4.Store.Node.decode_exact`, `Effect4.Store.length_be64`).

    The statement vocabulary ([Resolves], [Closed], [Sound], [Ranked]) restates the Lean `Prop`s of
    `src/Effect4/Store/Domain/Store.lean` and `Word.lean` field for field; LCNF carries no `Prop`,
    so these are written by hand and named beside their Lean originals. *)

From Stdlib Require Import List ZArith Bool Lia.
Import ListNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.StoreCode.

Open Scope Z_scope.

(** RocqOfOCaml's `length` is OCaml's (Z); a rank is a list position, `nat`. *)
Notation len := Stdlib.Lists.List.length.

(** What the proofs take of the parameters: what each erased proof said. *)
Module Type PrimLaws (Import E : Prim).
  (** `Digest.instDecidableEq`, `instDecidableEqKind`, `instDecidableEqNode` decide equality. *)
  Axiom digest_eqb_spec : forall a b, Digest_instDecidableEq a b = true <-> a = b.
  Axiom kind_eqb_spec : forall a b, instDecidableEqKind a b = true <-> a = b.
  Axiom node_eqb_spec : forall a b, instDecidableEqNode a b = true <-> a = b.
End PrimLaws.

Module Laws (E : Prim) (L : PrimLaws E).
Module C := Code E.
Import E L C.

(** ** The vocabulary, as `Store.lean` and `Word.lean` state it *)

Definition find (s : store) (d : digest) : option node := Store_find s d.

(** `Store.Resolves`: the edge's digest is filed, at its kind. *)
Definition Resolves (s : store) (e : any_ref) : Prop :=
  exists m, find s (anyref_digest e) = Some m /\ node_kind m = anyref_kind e.

(** `Closed`: every resident node's checked edges resolve. *)
Definition Closed (s : store) : Prop :=
  forall d n, find s d = Some n -> forall e, In e (Node_checkedEdges n) -> Resolves s e.

(** `Store.Sound.addressed`: every resident sits at the hash of its bytes. *)
Definition Addressed (s : store) : Prop := forall d n, find s d = Some n -> d = sha256 (Node_encode n).

(** `Store.Sound`, field for field. *)
Record Sound (s : store) : Prop := {
  sound_version : forall d n, find s d = Some n -> node_version n = 0;
  sound_wf : forall d n, find s d = Some n -> Val_wf (node_payload n) = true;
  sound_refs : forall d n, find s d = Some n -> Node_malformedRef n = false;
  sound_handles : forall d n, find s d = Some n -> Node_handleInContent n = false;
  sound_addressed : Addressed s;
  sound_closed : Closed s }.

(** `Store.sub`: every node of [a] is a node of [b], at the same digest. *)
Definition Sub (a b : store) : Prop := forall d n, find a d = Some n -> find b d = Some n.

(** ** The find *)

Lemma digest_eqb_refl : forall d, Digest_instDecidableEq d d = true.
Proof. intro d. apply digest_eqb_spec. reflexivity. Qed.

Lemma digest_eqb_neq : forall a b, a <> b -> Digest_instDecidableEq a b = false.
Proof.
  intros a b h. destruct (Digest_instDecidableEq a b) eqn:e; [|reflexivity].
  exfalso. apply h. apply digest_eqb_spec. exact e.
Qed.

Lemma findIn_cons : forall d' n l d,
  findIn ((d', n) :: l) d = if Digest_instDecidableEq d' d then Some n else findIn l d.
Proof. intros. simpl. destruct (Digest_instDecidableEq d' d); reflexivity. Qed.

Lemma findIn_app_some : forall l1 l2 d n, findIn l1 d = Some n -> findIn (l1 ++ l2) d = Some n.
Proof.
  induction l1 as [|[d' m] rest IH]; intros l2 d n h; [discriminate|].
  simpl app. rewrite findIn_cons in *.
  destruct (Digest_instDecidableEq d' d); [exact h|]. apply IH. exact h.
Qed.

Lemma findIn_app_none : forall l1 l2 d, findIn l1 d = None -> findIn (l1 ++ l2) d = findIn l2 d.
Proof.
  induction l1 as [|[d' m] rest IH]; intros l2 d h; [reflexivity|].
  simpl app. rewrite findIn_cons in *.
  destruct (Digest_instDecidableEq d' d); [discriminate|]. apply IH. exact h.
Qed.

Lemma findIn_single : forall d n d', findIn [(d, n)] d' = if Digest_instDecidableEq d d' then Some n else None.
Proof. intros. rewrite findIn_cons. reflexivity. Qed.

Lemma findIn_mem : forall l d n, findIn l d = Some n -> In (d, n) l.
Proof.
  induction l as [|[d' m] rest IH]; intros d n h; [discriminate|].
  rewrite findIn_cons in h. destruct (Digest_instDecidableEq d' d) eqn:e.
  - apply digest_eqb_spec in e. subst. injection h as ->. left. reflexivity.
  - right. apply IH. exact h.
Qed.

(** A find in a list with one binding appended: the old answer, or the new binding. *)
Lemma findIn_append_single : forall l d n d' m,
  findIn (l ++ [(d, n)]) d' = Some m ->
  findIn l d' = Some m \/ (findIn l d' = None /\ d' = d /\ m = n).
Proof.
  intros l d n d' m h. destruct (findIn l d') as [k|] eqn:e.
  - left. rewrite (findIn_app_some _ _ _ _ e) in h. exact h.
  - right. rewrite (findIn_app_none _ _ _ e), findIn_single in h.
    destruct (Digest_instDecidableEq d d') eqn:e2; [|discriminate].
    apply digest_eqb_spec in e2. injection h as ->. auto.
Qed.

(** ** Property 1: the hash is injective on a sound store's residents

    No hypothesis about the hash. `find` is a function and a resident sits at its own address, so
    two residents whose bytes hash alike sit at one digest and are one node. *)

Theorem residents_hash_injective : forall s, Addressed s ->
  forall d1 d2 n1 n2, find s d1 = Some n1 -> find s d2 = Some n2 ->
  sha256 (Node_encode n1) = sha256 (Node_encode n2) -> n1 = n2.
Proof.
  intros s ha d1 d2 n1 n2 h1 h2 hh.
  rewrite (ha _ _ h1), hh, <- (ha _ _ h2) in h1. rewrite h1 in h2. injection h2 as ->. reflexivity.
Qed.

(** The same, as injectivity on the residents' bytes (`InjOn sha256 (Node.encode '' residents)`). *)
Corollary residents_bytes_injective : forall s, Addressed s ->
  forall d1 d2 n1 n2, find s d1 = Some n1 -> find s d2 = Some n2 ->
  sha256 (Node_encode n1) = sha256 (Node_encode n2) -> Node_encode n1 = Node_encode n2.
Proof. intros. f_equal. eapply residents_hash_injective; eauto. Qed.

(** The replacement of `address_inj`: two nodes each resident at its own address, with equal
    addresses, are one node. It needs nothing of the store but the find. *)
Theorem address_inj_resident : forall s n m,
  find s (sha256 (Node_encode n)) = Some n -> find s (sha256 (Node_encode m)) = Some m ->
  sha256 (Node_encode n) = sha256 (Node_encode m) -> n = m.
Proof. intros s n m hn hm h. rewrite h, hm in hn. injection hn as ->. reflexivity. Qed.

(** ** Property 2: domain separation

    A node's bytes begin with its version byte, and a value's bytes with its tag, 1 to 14. So a
    version-0 node's bytes are never a value's bytes: an address (the hash of node bytes) equal to
    a content id (the hash of a payload's value bytes, amendment M6) is an exhibited collision. *)

Lemma framed_head : forall t p, hd_error (framed t p) = Some t.
Proof. reflexivity. Qed.

Theorem version_byte_separates : forall n, hd_error (Node_encode n) = Some (node_version n).
Proof. intro n. destruct n. reflexivity. Qed.

Theorem val_tag_range : forall v, exists t, hd_error (Val_encode v) = Some t /\ 1 <= t <= 14.
Proof.
  intro v. destruct v; simpl; [| destruct b | .. ]; eexists; split; try reflexivity; lia.
Qed.

Theorem domain_separation : forall n v, node_version n = 0 -> Node_encode n <> Val_encode v.
Proof.
  intros n v h e. destruct (val_tag_range v) as [t [ht hr]].
  rewrite <- e, version_byte_separates, h in ht. injection ht as <-. lia.
Qed.

Corollary address_cid_collision : forall n v, node_version n = 0 ->
  sha256 (Node_encode n) = sha256 (Val_encode v) ->
  Node_encode n <> Val_encode v /\ sha256 (Node_encode n) = sha256 (Val_encode v).
Proof. intros n v h e. split; [apply domain_separation; exact h | exact e]. Qed.

Lemma Kind_byte_injective : forall a b, Kind_byte a = Kind_byte b -> a = b.
Proof. intros a b h. destruct a, b; first [reflexivity | discriminate h]. Qed.

(** Equal node bytes are nodes of one kind: the second byte is the kind byte. *)
Theorem kind_separation : forall n m, Node_encode n = Node_encode m -> node_kind n = node_kind m.
Proof.
  intros [v k s p] [v' k' s' p'] e. simpl in *. injection e as _ hk _.
  apply Kind_byte_injective. exact hk.
Qed.

(** ** The put, characterized once

    `Store.putNode_ok`'s statement over the printed `Store_putNode`: what admission established,
    the address, and the outcome with the store it leaves. Every put law below is a corollary. *)

Lemma decWF_eq : forall v, Val_decWF v = Val_wf v.
Proof. intro v. unfold Val_decWF. destruct (Val_wf v); reflexivity. Qed.

Lemma checkEdge_ok : forall s e u, Store_checkEdge s e = Except_ok u -> Resolves s e.
Proof.
  intros s e u h. unfold Store_checkEdge in h. cbv beta zeta in h.
  destruct (Store_find s (anyref_digest e)) as [m|] eqn:hf; [|discriminate].
  destruct (instDecidableEqKind (node_kind m) (anyref_kind e)) eqn:hk; [|discriminate].
  exists m. split; [exact hf|]. apply kind_eqb_spec. exact hk.
Qed.

Lemma checkAll_ok : forall s es u, Store_checkAll s es = Except_ok u -> forall e, In e es -> Resolves s e.
Proof.
  intros s es. induction es as [|e0 es IH]; intros u h e he; [destruct he|].
  simpl in h. destruct (Store_checkEdge s e0) as [a|u0] eqn:hc; [discriminate|].
  destruct he as [<-|he]; [eapply checkEdge_ok; exact hc | eapply IH; eauto].
Qed.

Definition Fresh (s : store) (d : digest) (n : node) (s' : store) : Prop :=
  find s d = None /\ s' = Store_mk (store_nodes s ++ [(d, n)]) (store_roots s).

Theorem putNode_accepted_new_to_old : forall s n o d s',
  Store_putNode s n = Except_ok (o, (d, s')) ->
  Val_wf (node_payload n) = true /\ node_version n = 0 /\ Node_malformedRef n = false /\
  (forall e, In e (Node_checkedEdges n) -> Resolves s e) /\ d = sha256 (Node_encode n) /\
  ((o = Outcome_fresh /\ Fresh s d n s') \/
   (o = Outcome_duplicate /\ find s d = Some n /\ s' = s) \/
   (exists m, o = Outcome_conflict m /\ find s d = Some m /\ m <> n /\ s' = s)).
Proof.
  intros s n o d s' h. unfold Store_putNode in h. cbv beta zeta in h. rewrite decWF_eq in h.
  destruct (Val_wf (node_payload n)) eqn:hwf; [|discriminate].
  destruct (Z.eqb (node_version n) 0) eqn:hv; [|discriminate]. apply Z.eqb_eq in hv.
  destruct (Node_malformedRef n) eqn:hm; [discriminate|].
  destruct (Node_handleInContent n) eqn:hm2; [discriminate|].
  destruct (Store_checkEdges s n) as [a|u] eqn:hce; [discriminate|].
  assert (hres : forall e, In e (Node_checkedEdges n) -> Resolves s e)
    by (intros e he; eapply checkAll_ok; [exact hce | exact he]).
  destruct (resultFault (store_nodes s) n) as [[|q f]|] eqn:hr; [discriminate|discriminate|].
  do 4 (split; [first [assumption | reflexivity]|]).
  destruct (Store_find s (sha256 (Node_encode n))) as [m|] eqn:hf.
  - destruct (instDecidableEqNode m n) eqn:he; injection h as <- <- <-.
    + apply node_eqb_spec in he. subst m. split; [reflexivity|]. right. left. auto.
    + split; [reflexivity|]. right. right. exists m. repeat split; auto.
      intro e. subst m. rewrite (proj2 (node_eqb_spec n n) eq_refl) in he. discriminate.
  - injection h as <- <- <-. split; [reflexivity|]. left. split; [reflexivity|]. split; auto.
Qed.

Theorem putNode_ok : forall s n o d s',
  Store_putNode s n = Except_ok (o, (d, s')) ->
  Val_wf (node_payload n) = true /\ node_version n = 0 /\ Node_malformedRef n = false /\
  (forall e, In e (Node_checkedEdges n) -> Resolves s e) /\ d = sha256 (Node_encode n) /\
  ((o = Outcome_fresh /\ Fresh s d n s') \/
   (o = Outcome_duplicate /\ find s d = Some n /\ s' = s) \/
   (exists m, o = Outcome_conflict m /\ find s d = Some m /\ m <> n /\ s' = s)).
Proof. exact putNode_accepted_new_to_old. Qed.

(** `putNode_ok_handleFree`: successful admission passes M2 before edges or resident lookup. *)
Theorem putNode_ok_handleFree : forall s n o d s',
  Store_putNode s n = Except_ok (o, (d, s')) -> Node_handleInContent n = false.
Proof.
  intros s n o d s' h. unfold Store_putNode in h. cbv beta zeta in h. rewrite decWF_eq in h.
  destruct (Val_wf (node_payload n)); [|discriminate].
  destruct (Z.eqb (node_version n) 0); [|discriminate].
  destruct (Node_malformedRef n); [discriminate|].
  destruct (Node_handleInContent n) eqn:hm2; [discriminate|reflexivity].
Qed.

(** ** Property 4: the store as a growing map from digest to bytes

    [bytes_at] reads the store as the map from a digest to the node bytes filed there. A put that
    is not a conflict files the node's bytes at the node's address; nothing filed ever changes; a
    conflict changes nothing and is either a collision of the address or a store that is not
    addressed, which a re-hash of the occupant tells apart. *)

Definition bytes_at (s : store) (d : digest) : option (list int) := option_map Node_encode (find s d).

Lemma addressed_bytes : forall s, Addressed s <-> forall d b, bytes_at s d = Some b -> d = sha256 b.
Proof.
  intro s. unfold bytes_at. split.
  - intros h d b e. destruct (find s d) as [n|] eqn:hf; [|discriminate]. injection e as <-. eapply h. exact hf.
  - intros h d n hf. apply h. rewrite hf. reflexivity.
Qed.

Theorem put_grows : forall s n o d s', Store_putNode s n = Except_ok (o, (d, s')) -> Sub s s'.
Proof.
  intros s n o d s' h. destruct (putNode_ok _ _ _ _ _ h) as (_ & _ & _ & _ & _ & hc).
  intros d' m hm. destruct hc as [(_ & _ & ->) | [(_ & _ & ->) | (k & _ & _ & _ & ->)]]; [|exact hm|exact hm].
  unfold find, Store_find in *. simpl. apply findIn_app_some. exact hm.
Qed.

Corollary put_bytes_never_change : forall s n o d s' d' b,
  Store_putNode s n = Except_ok (o, (d, s')) -> bytes_at s d' = Some b -> bytes_at s' d' = Some b.
Proof.
  intros s n o d s' d' b h e. unfold bytes_at in *.
  destruct (find s d') as [m|] eqn:hf; [|discriminate]. rewrite (put_grows _ _ _ _ _ h _ _ hf). exact e.
Qed.

Theorem put_get : forall s n o d s', Store_putNode s n = Except_ok (o, (d, s')) ->
  (forall m, o <> Outcome_conflict m) -> find s' d = Some n /\ bytes_at s' d = Some (Node_encode n).
Proof.
  intros s n o d s' h ho. destruct (putNode_ok _ _ _ _ _ h) as (_ & _ & _ & _ & _ & hc).
  assert (hf : find s' d = Some n).
  { destruct hc as [(_ & hf & ->) | [(_ & hf & ->) | (k & hk & _ & _ & _)]].
    - unfold find, Store_find in *. simpl. rewrite findIn_app_none by exact hf.
      rewrite findIn_single, digest_eqb_refl. reflexivity.
    - exact hf.
    - exfalso. exact (ho k hk). }
  split; [exact hf|]. unfold bytes_at. rewrite hf. reflexivity.
Qed.

(** A conflict: nothing changes, another node sits at the address, and that occupant either
    hashes to the address (two different nodes with one address: a collision, exhibited) or does
    not (the store is not addressed: corruption). *)
Theorem put_conflict : forall s n m d s', Store_putNode s n = Except_ok (Outcome_conflict m, (d, s')) ->
  s' = s /\ find s d = Some m /\ m <> n /\ d = sha256 (Node_encode n) /\
  ((sha256 (Node_encode m) = sha256 (Node_encode n)) \/ (sha256 (Node_encode m) <> d /\ ~ Addressed s)).
Proof.
  intros s n m d s' h. destruct (putNode_ok _ _ _ _ _ h) as (_ & _ & _ & _ & hd & hc).
  destruct hc as [(ho & _) | [(ho & _) | (k & hk & hf & hne & ->)]]; try discriminate.
  injection hk as <-. repeat split; auto.
  destruct (Digest_instDecidableEq (sha256 (Node_encode m)) d) eqn:e.
  - left. apply digest_eqb_spec in e. rewrite e. exact hd.
  - right. split.
    + intro x. rewrite x, digest_eqb_refl in e. discriminate.
    + intro ha. rewrite <- (ha _ _ hf), digest_eqb_refl in e. discriminate.
Qed.

(** In an addressed store a conflict is a collision of the address: two nodes, one address. *)
Corollary put_conflict_collision : forall s n m d s', Addressed s ->
  Store_putNode s n = Except_ok (Outcome_conflict m, (d, s')) ->
  m <> n /\ sha256 (Node_encode m) = sha256 (Node_encode n).
Proof.
  intros s n m d s' ha h. destruct (put_conflict _ _ _ _ _ h) as (_ & _ & hne & _ & [e | [_ hna]]).
  - auto.
  - contradiction.
Qed.

(** `Word.apply` grows the store too: replay never overwrites. *)
Theorem apply_grows : forall w s s', Word_apply w s = Except_ok s' -> Sub s s'.
Proof.
  induction w as [|b rest IH]; intros s s' h.
  - injection h as <-. intros d n e. exact e.
  - simpl in h. destruct (Store_putNode s (binding_node b)) as [a|[o [d s1]]] eqn:hp; [discriminate|].
    destruct o; try discriminate; intros d' n e; apply (IH s1 s' h); eapply put_grows; eauto.
Qed.

(** ** Property 3: a built store is ranked by insertion order

    `closure_closed` (`Word.lean`) takes a rank that descends along every edge, `Store.Ranked`, a
    premise it says the model cannot discharge without one about the hash. For a store built from
    empty by puts it needs none: the rank of a digest is the position of its first binding, and a
    fresh node's edges resolved, at admission, among the bindings already there. *)

(** The position of the first binding at [d], or the length when there is none. *)
Fixpoint rank_of (l : list (digest * node)) (d : digest) : nat :=
  match l with
  | [] => O
  | (d', _) :: rest => if Digest_instDecidableEq d' d then O else S (rank_of rest d)
  end.

(** `Store.Ranked`. *)
Definition Ranked (s : store) (rank : digest -> nat) : Prop :=
  forall d n, find s d = Some n -> forall e, In e (Node_checkedEdges n) ->
  (rank (anyref_digest e) < rank d)%nat.

Lemma rank_of_found : forall l d, findIn l d <> None <-> (rank_of l d < len l)%nat.
Proof.
  induction l as [|[d' m] rest IH]; intro d; simpl.
  - split; [intro h; exfalso; apply h; reflexivity | intro h; lia].
  - destruct (Digest_instDecidableEq d' d); [split; [lia | discriminate] |].
    rewrite IH. lia.
Qed.

Lemma rank_of_app_found : forall l1 l2 d, findIn l1 d <> None -> rank_of (l1 ++ l2) d = rank_of l1 d.
Proof.
  induction l1 as [|[d' m] rest IH]; intros l2 d h; [exfalso; apply h; reflexivity|].
  simpl in *. destruct (Digest_instDecidableEq d' d); [reflexivity|]. f_equal. apply IH. exact h.
Qed.

Lemma rank_of_app_none : forall l1 l2 d, findIn l1 d = None -> rank_of (l1 ++ l2) d = (len l1 + rank_of l2 d)%nat.
Proof.
  induction l1 as [|[d' m] rest IH]; intros l2 d h; [reflexivity|].
  simpl in *. destruct (Digest_instDecidableEq d' d); [discriminate|]. f_equal. apply IH. exact h.
Qed.

Lemma resolves_found : forall s e, Resolves s e -> findIn (store_nodes s) (anyref_digest e) <> None.
Proof. intros s e [m [h _]]. unfold find, Store_find in h. simpl in h. rewrite h. discriminate. Qed.

Theorem put_ranked : forall s n o d s', Ranked s (rank_of (store_nodes s)) ->
  Store_putNode s n = Except_ok (o, (d, s')) -> Ranked s' (rank_of (store_nodes s')).
Proof.
  intros s n o d s' hr h. destruct (putNode_ok _ _ _ _ _ h) as (_ & _ & _ & hres & _ & hc).
  destruct hc as [(_ & hf & ->) | [(_ & _ & ->) | (k & _ & _ & _ & ->)]]; [|exact hr|exact hr].
  unfold Ranked, find, Store_find in *. simpl. intros d' m hm e he.
  destruct (findIn_append_single _ _ _ _ _ hm) as [hold | (hnone & -> & ->)].
  - (* a resident before the put: both ranks are the old ones *)
    pose proof (hr _ _ hold e he) as lt.
    assert (hd' : findIn (store_nodes s) d' <> None) by (rewrite hold; discriminate).
    assert (he' : findIn (store_nodes s) (anyref_digest e) <> None).
    { apply rank_of_found. apply rank_of_found in hd'. lia. }
    rewrite !rank_of_app_found by assumption. exact lt.
  - (* the fresh node: its edges resolved before it, below the old length *)
    pose proof (resolves_found _ _ (hres e he)) as he'.
    rewrite rank_of_app_found by exact he'. rewrite rank_of_app_none by exact hnone.
    apply rank_of_found in he'. simpl. rewrite digest_eqb_refl. lia.
Qed.

(** How a store is made: from empty, by puts, with any roots. *)
Inductive Built : store -> Prop :=
  | built_empty : forall r, Built (Store_mk [] r)
  | built_put : forall s n o d s', Built s -> Store_putNode s n = Except_ok (o, (d, s')) -> Built s'
  | built_roots : forall s r, Built s -> Built (Store_mk (store_nodes s) r).

Theorem apply_built : forall w s s', Built s -> Word_apply w s = Except_ok s' -> Built s'.
Proof.
  induction w as [|b rest IH]; intros s s' hb h.
  - injection h as <-. exact hb.
  - simpl in h. destruct (Store_putNode s (binding_node b)) as [a|[o [d s1]]] eqn:hp; [discriminate|].
    destruct o; try discriminate; apply (IH s1); [eapply built_put; eauto | exact h | eapply built_put; eauto | exact h].
Qed.

Theorem built_ranked : forall s, Built s -> Ranked s (rank_of (store_nodes s)).
Proof.
  intros s hb. induction hb as [r | s n o d s' hb IH hp | s r hb IH].
  - intros d n h. discriminate.
  - eapply put_ranked; eauto.
  - exact IH.
Qed.

(** `closure_closed`'s bound: a resident's rank is below the number of nodes. *)
Theorem rank_below_length : forall s d n, find s d = Some n -> (rank_of (store_nodes s) d < len (store_nodes s))%nat.
Proof. intros s d n h. apply rank_of_found. unfold find, Store_find in h. rewrite h. discriminate. Qed.

(** `putNode_sound`, over the printed put: a built store is sound. *)
Theorem put_sound : forall s n o d s', Sound s -> Store_putNode s n = Except_ok (o, (d, s')) -> Sound s'.
Proof.
  intros s n o d s' hs h. pose proof (put_grows _ _ _ _ _ h) as hsub.
  pose proof (putNode_ok_handleFree _ _ _ _ _ h) as hm2.
  destruct (putNode_ok _ _ _ _ _ h) as (hwf & hv & hmr & hres & hd & hc).
  destruct hc as [(_ & hf & ->) | [(_ & _ & ->) | (k & _ & _ & _ & ->)]]; [|exact hs|exact hs].
  assert (hcase : forall d' m, find (Store_mk (store_nodes s ++ [(d, n)]) (store_roots s)) d' = Some m ->
            find s d' = Some m \/ (d' = d /\ m = n)).
  { intros d' m hm. unfold find, Store_find in *. simpl in hm.
    destruct (findIn_append_single _ _ _ _ _ hm) as [x | (_ & x & y)]; [left; exact x | right; auto]. }
  assert (mono : forall e, Resolves s e -> Resolves (Store_mk (store_nodes s ++ [(d, n)]) (store_roots s)) e).
  { intros e [m [hm hk]]. exists m. split; [apply hsub; exact hm | exact hk]. }
  constructor.
  - intros d' m hm. destruct (hcase _ _ hm) as [x | (_ & ->)]; [eapply sound_version; eauto | exact hv].
  - intros d' m hm. destruct (hcase _ _ hm) as [x | (_ & ->)]; [eapply sound_wf; eauto | exact hwf].
  - intros d' m hm. destruct (hcase _ _ hm) as [x | (_ & ->)]; [eapply sound_refs; eauto | exact hmr].
  - intros d' m hm. destruct (hcase _ _ hm) as [x | (_ & ->)]; [eapply sound_handles; eauto | exact hm2].
  - intros d' m hm. destruct (hcase _ _ hm) as [x | (-> & ->)]; [eapply sound_addressed; eauto | exact hd].
  - intros d' m hm e he. apply mono. destruct (hcase _ _ hm) as [x | (_ & ->)];
      [eapply sound_closed; eauto | apply hres; exact he].
Qed.

Theorem built_sound : forall s, Built s -> Sound s.
Proof.
  intros s hb. induction hb as [r | s n o d s' hb IH hp | s r hb IH].
  - constructor; intros d n h; discriminate.
  - eapply put_sound; eauto.
  - destruct IH as [h1 h2 h3 h4 h5 h6]. constructor; try exact h1; try exact h2; try exact h3; try exact h4; try exact h5.
    intros d n hn e he. destruct (h6 d n hn e he) as [m hm]. exists m. exact hm.
Qed.

(** Everything `closure_closed` takes of a store, for a built one, with no premise about the hash. *)
Corollary built_closure_premises : forall s, Built s ->
  Sound s /\ Ranked s (rank_of (store_nodes s)) /\
  (forall d n, find s d = Some n -> (rank_of (store_nodes s) d < len (store_nodes s))%nat).
Proof. intros s hb. split; [apply built_sound | split; [apply built_ranked | apply rank_below_length]]; exact hb. Qed.

(** ** `verify` is sound

    A store that verifies is [Sound], given that `Node.decode` is exact
    (`Effect4.Store.Node.decode_exact`, taken as a premise). *)

Definition DecodeExact : Prop := forall b n, Node_decode b = Some n ->
  b = Node_encode n /\ Val_wf (node_payload n) = true /\ node_version n = 0.

Lemma verifyEdges_ok : forall s at_ es u, verifyEdges s at_ es = Except_ok u -> forall e, In e es -> Resolves s e.
Proof.
  intros s at_ es. induction es as [|e0 es IH]; intros u h e he; [destruct he|].
  simpl in h. destruct (Store_find s (anyref_digest e0)) as [m|] eqn:hf; [|discriminate].
  destruct (instDecidableEqKind (node_kind m) (anyref_kind e0)) eqn:hk; [|discriminate].
  destruct he as [<-|he]; [exists m; split; [exact hf | apply kind_eqb_spec; exact hk] | eapply IH; eauto].
Qed.

Lemma option_eqb_some : forall x n, option_eqb instDecidableEqNode x (Some n) = true -> x = Some n.
Proof.
  intros [m|] n h; [|discriminate]. simpl in h. apply node_eqb_spec in h. subst. reflexivity.
Qed.

Lemma verifyNode_ok : forall s d n u, Store_verifyNode s d n = Except_ok u ->
  sha256 (Node_encode n) = d /\ Node_decode (Node_encode n) = Some n /\ Node_malformedRef n = false /\
  forall e, In e (Node_checkedEdges n) -> Resolves s e.
Proof.
  intros s d n u h. unfold Store_verifyNode in h. cbv beta zeta in h.
  destruct (Digest_instDecidableEq (sha256 (Node_encode n)) d) eqn:hd; [|discriminate].
  destruct (option_eqb instDecidableEqNode (Node_decode (Node_encode n)) (Some n)) eqn:hdec; [|discriminate].
  destruct (Node_malformedRef n) eqn:hm; [discriminate|].
  destruct (Node_handleInContent n) eqn:hm2; [discriminate|].
  destruct (verifyEdges s d (Node_checkedEdges n)) as [a|u'] eqn:hv; [discriminate|].
  repeat split.
  - apply digest_eqb_spec. exact hd.
  - apply option_eqb_some. exact hdec.
  - intros e he. eapply verifyEdges_ok; eauto.
Qed.

(** `verifyNode_handleFree`: every verified resident passes M2. *)
Lemma verifyNode_handleFree : forall s d n u, Store_verifyNode s d n = Except_ok u ->
  Node_handleInContent n = false.
Proof.
  intros s d n u h. unfold Store_verifyNode in h. cbv beta zeta in h.
  destruct (Digest_instDecidableEq (sha256 (Node_encode n)) d); [|discriminate].
  destruct (option_eqb instDecidableEqNode (Node_decode (Node_encode n)) (Some n)); [|discriminate].
  destruct (Node_malformedRef n); [discriminate|].
  destruct (Node_handleInContent n) eqn:hm2; [discriminate|reflexivity].
Qed.

Lemma verifyNodes_ok : forall s l u, verifyNodes s l = Except_ok u ->
  forall d n, In (d, n) l -> exists u', Store_verifyNode s d n = Except_ok u'.
Proof.
  intros s l. induction l as [|[d0 n0] rest IH]; intros u h d n hin; [destruct hin|].
  simpl in h. destruct (Store_verifyNode s d0 n0) as [a|u0] eqn:hv; [discriminate|].
  destruct hin as [e|hin]; [injection e as <- <-; exists u0; exact hv | eapply IH; eauto].
Qed.

Theorem verify_sound : DecodeExact -> forall s u, Store_verify s = Except_ok u -> Sound s.
Proof.
  intros hdec s u h. unfold Store_verify in h. cbv beta zeta in h.
  destruct (verifyNodes s (store_nodes s)) as [a|u0] eqn:hn; [discriminate|].
  assert (each : forall d n, find s d = Some n ->
    sha256 (Node_encode n) = d /\ Node_decode (Node_encode n) = Some n /\ Node_malformedRef n = false /\
    forall e, In e (Node_checkedEdges n) -> Resolves s e).
  { intros d n hf. apply findIn_mem in hf. destruct (verifyNodes_ok _ _ _ hn _ _ hf) as [u' hv].
    eapply verifyNode_ok; eauto. }
  constructor.
  - intros d n hf. destruct (each _ _ hf) as (_ & hd & _). apply hdec in hd. tauto.
  - intros d n hf. destruct (each _ _ hf) as (_ & hd & _). apply hdec in hd. tauto.
  - intros d n hf. apply each in hf. tauto.
  - intros d n hf. apply findIn_mem in hf.
    destruct (verifyNodes_ok _ _ _ hn _ _ hf) as [u' hv].
    eapply verifyNode_handleFree. exact hv.
  - intros d n hf. symmetry. apply each in hf. tauto.
  - intros d n hf. apply each in hf. tauto.
Qed.

End Laws.
