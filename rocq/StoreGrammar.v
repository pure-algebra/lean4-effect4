(** * One byte language: the value codec is prefix-free, so it is injective

    Over the printed `Val_encode` (`StoreCode.v`): a well-formed value's bytes, followed by any
    rest, determine the value and the rest. So the grammar of value frames is unambiguous, node
    bytes are injective on admissible nodes, and a put's conflict in an addressed store is a
    collision of bytes, not only of nodes.

    The codec laws are premises ([CodecLaws]), each a Lean theorem: `Effect4.Store.length_be64`,
    `Effect4.Store.natOfDigits_be64`, `Effect4.Store.natOfDigits_natBytes` and
    `Effect4.Store.decodeString_toUTF8`. [InRange] says what the Rocq model's `int` fields hold in
    Lean: a natural is at least 0, and a float's bits are below 2^64. *)

From Stdlib Require Import List ZArith Bool Lia.
Import ListNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.StoreCode E4.StoreLaws.

Open Scope Z_scope.
Notation len := Stdlib.Lists.List.length.
(** 2^64, the bound a length prefix carries. *)
Notation B64 := 18446744073709551616%Z.

Module Grammar (E : Prim) (L : PrimLaws E).
Module S := Laws E L.
Import E L S S.C.

(** The codec laws, each a Lean theorem. *)
Record CodecLaws : Prop := {
  be64_length : forall n, len (be64 n) = 8%nat;
  be64_injective : forall a b, 0 <= a < B64 -> 0 <= b < B64 -> be64 a = be64 b -> a = b;
  natBytes_injective : forall a b, 0 <= a -> 0 <= b -> natBytes a = natBytes b -> a = b;
  utf8_injective : forall s t, String_toUTF8 s = String_toUTF8 t -> s = t }.

(** What Lean's values are in the model: naturals at least 0, a float's bits below 2^64. *)
Fixpoint InRange (v : val_) : Prop :=
  match v with
  | Val_nat n | Val_negInt n => 0 <= n
  | Val_handle _ n => 0 <= n
  | Val_float b => 0 <= b < B64
  | Val_list xs => (fix go (l : list val_) : Prop :=
      match l with [] => True | x :: t => InRange x /\ go t end) xs
  | Val_pair a b => InRange a /\ InRange b
  | Val_some a => InRange a
  | Val_ctor i xs => 0 <= i /\ (fix go (l : list val_) : Prop :=
      match l with [] => True | x :: t => InRange x /\ go t end) xs
  | _ => True
  end.

Fixpoint InRangeList (l : list val_) : Prop :=
  match l with [] => True | x :: t => InRange x /\ InRangeList t end.

Lemma inrange_list : forall xs, InRange (Val_list xs) = InRangeList xs.
Proof. induction xs as [|x xs IH]; [reflexivity|]. simpl in *. rewrite IH. reflexivity. Qed.

Lemma inrange_ctor : forall i xs, InRange (Val_ctor i xs) = (0 <= i /\ InRangeList xs).
Proof. intros i xs. rewrite <- inrange_list. reflexivity. Qed.

Section WithLaws.
Variable laws : CodecLaws.

(** ** Frames *)

Lemma encode_framed : forall v, Val_encode v = framed (Val_tag v) (Val_payload v).
Proof. intro v. destruct v; try match goal with b : bool |- _ => destruct b end; reflexivity. Qed.

Lemma lengthZ_nonneg : forall {A} (l : list A), 0 <= lengthZ l.
Proof. intros. unfold lengthZ. lia. Qed.

Lemma len_framed : forall t p, len (framed t p) = (len p + 9)%nat.
Proof.
  intros t p. unfold framed. cbv beta zeta. simpl. rewrite length_app, (be64_length laws). lia.
Qed.

Lemma app_same_length : forall {A} (a b c d : list A), len a = len c -> a ++ b = c ++ d -> a = c /\ b = d.
Proof.
  intros A a. induction a as [|x a IH]; intros b c d hl e; destruct c as [|y c]; simpl in *; try discriminate.
  - auto.
  - injection e as -> e. destruct (IH b c d ltac:(lia) e) as [-> ->]. auto.
Qed.

(** One frame, in front of any rest, determines its tag, its payload and the rest. *)
Lemma framed_prefix_free : forall t1 p1 r1 t2 p2 r2,
  lengthZ p1 < B64 -> lengthZ p2 < B64 ->
  framed t1 p1 ++ r1 = framed t2 p2 ++ r2 -> t1 = t2 /\ p1 = p2 /\ r1 = r2.
Proof.
  intros t1 p1 r1 t2 p2 r2 h1 h2 e. unfold framed in e. cbv beta zeta in e. simpl in e.
  injection e as <- e. rewrite <- !app_assoc in e.
  destruct (app_same_length _ _ _ _ (eq_trans (be64_length laws _) (eq_sym (be64_length laws _))) e) as [hb e'].
  apply (be64_injective laws) in hb; [| pose proof (lengthZ_nonneg p1); lia | pose proof (lengthZ_nonneg p2); lia].
  unfold lengthZ in hb. apply Nat2Z.inj in hb.
  destruct (app_same_length _ _ _ _ hb e') as [-> ->]. auto.
Qed.

(** ** Well-formedness, read by case: the printed check as equations *)

Lemma wfList_nil : Val_wfList [] = true.
Proof. reflexivity. Qed.
Lemma wfList_cons : forall x xs, Val_wfList (x :: xs) = (Val_wf x && Val_wfList xs)%bool.
Proof. intros. simpl. destruct (Val_wf x); reflexivity. Qed.
Lemma wf_nat : forall n, Val_wf (Val_nat n) = Z.ltb (lengthZ (natBytes n)) B64.
Proof. reflexivity. Qed.
Lemma wf_negInt : forall n, Val_wf (Val_negInt n) = Z.ltb (lengthZ (natBytes n)) B64.
Proof. reflexivity. Qed.
Lemma wf_str : forall t, Val_wf (Val_str t) = Z.ltb (lengthZ (String_toUTF8 t)) B64.
Proof. reflexivity. Qed.
Lemma wf_bytes : forall bs, Val_wf (Val_bytes bs) = Z.ltb (lengthZ bs) B64.
Proof. reflexivity. Qed.
Lemma wf_ref : forall k d, Val_wf (Val_ref k d) = Z.ltb (lengthZ (k :: d)) B64.
Proof. reflexivity. Qed.
Lemma wf_handle : forall k n, Val_wf (Val_handle k n) = Z.ltb (lengthZ (k :: natBytes n)) B64.
Proof. reflexivity. Qed.
Lemma wf_float : forall b, Val_wf (Val_float b) = Val_floatFrame b.
Proof. reflexivity. Qed.
Lemma wf_list : forall xs, Val_wf (Val_list xs) = (Z.ltb (lengthZ (Val_encodeList xs)) B64 && Val_wfList xs)%bool.
Proof. intros. simpl. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma wf_pair : forall a b,
  Val_wf (Val_pair a b) = (Z.ltb (lengthZ (Val_encode a ++ Val_encode b)) B64 && Val_wf a && Val_wf b)%bool.
Proof. intros. simpl. destruct (Z.ltb _ _); [destruct (Val_wf a)|]; reflexivity. Qed.
Lemma wf_some : forall a, Val_wf (Val_some a) = (Z.ltb (lengthZ (Val_encode a)) B64 && Val_wf a)%bool.
Proof. intros. simpl. destruct (Z.ltb _ _); reflexivity. Qed.
Lemma wf_ctor : forall i xs, Val_wf (Val_ctor i xs) =
  (Z.ltb (lengthZ (natBytes i)) B64 && Z.ltb (lengthZ (framed 2 (natBytes i) ++ Val_encodeList xs)) B64 &&
   Val_wfList xs)%bool.
Proof. intros. simpl. destruct (Z.ltb (lengthZ (natBytes i)) _); [destruct (Z.ltb _ _)|]; reflexivity. Qed.

Lemma and2 : forall a b, (a && b)%bool = true -> a = true /\ b = true.
Proof. intros a b h. apply andb_prop. exact h. Qed.
Lemma and3 : forall a b c, (a && b && c)%bool = true -> a = true /\ b = true /\ c = true.
Proof. intros a b c h. apply andb_prop in h as [h h3]. apply andb_prop in h as [h1 h2]. auto. Qed.

Lemma payload_bound : forall v, Val_wf v = true -> lengthZ (Val_payload v) < B64.
Proof.
  intros v h. pose proof (wf_nat 0) as _.
  destruct v as [| b | n | t | bs | xs | a b | | a | i xs | k d | k n | n | b].
  - reflexivity.
  - destruct b; reflexivity.
  - rewrite wf_nat in h. apply Z.ltb_lt in h. exact h.
  - rewrite wf_str in h. apply Z.ltb_lt in h. exact h.
  - rewrite wf_bytes in h. apply Z.ltb_lt in h. exact h.
  - rewrite wf_list in h. apply and2 in h as [h _]. apply Z.ltb_lt in h. exact h.
  - rewrite wf_pair in h. apply and3 in h as [h _]. apply Z.ltb_lt in h. exact h.
  - reflexivity.
  - rewrite wf_some in h. apply and2 in h as [h _]. apply Z.ltb_lt in h. exact h.
  - rewrite wf_ctor in h. apply and3 in h as [_ [h _]]. apply Z.ltb_lt in h. exact h.
  - rewrite wf_ref in h. apply Z.ltb_lt in h. exact h.
  - rewrite wf_handle in h. apply Z.ltb_lt in h. exact h.
  - rewrite wf_negInt in h. apply Z.ltb_lt in h. exact h.
  - unfold lengthZ. simpl. rewrite (be64_length laws). reflexivity.
Qed.

(** ** One parse per byte string *)

Lemma encode_cons : forall v, exists t rest, Val_encode v = t :: rest.
Proof. intro v. rewrite encode_framed. unfold framed. cbv beta zeta. eauto. Qed.

Lemma encodeList_cons : forall x xs, Val_encodeList (x :: xs) = Val_encode x ++ Val_encodeList xs.
Proof. reflexivity. Qed.

Lemma len_encode : forall v, len (Val_encode v) = (len (Val_payload v) + 9)%nat.
Proof. intro v. rewrite encode_framed. apply len_framed. Qed.

Lemma len_in_encodeList : forall xs x, In x xs -> (len (Val_encode x) <= len (Val_encodeList xs))%nat.
Proof.
  induction xs as [|y xs IH]; intros x hx; [destruct hx|]. rewrite encodeList_cons, length_app.
  destruct hx as [<-|hx]; [lia | specialize (IH x hx); lia].
Qed.

Lemma wfList_mem : forall xs x, Val_wfList xs = true -> In x xs -> Val_wf x = true.
Proof.
  induction xs as [|y xs IH]; intros x h hx; [destruct hx|]. rewrite wfList_cons in h. apply and2 in h as [h1 h2].
  destruct hx as [<-|hx]; [exact h1 | apply IH; assumption].
Qed.

Lemma inrangeList_mem : forall xs x, InRangeList xs -> In x xs -> InRange x.
Proof.
  induction xs as [|y xs IH]; intros x h hx; [destruct hx|]. destruct h as [h1 h2].
  destruct hx as [<-|hx]; [exact h1 | apply IH; assumption].
Qed.

Definition PrefixFree (v : val_) : Prop := forall w r1 r2, Val_wf v = true -> Val_wf w = true ->
  InRange v -> InRange w -> Val_encode v ++ r1 = Val_encode w ++ r2 -> v = w /\ r1 = r2.

Lemma encodeList_injective : forall xs ys, (forall x, In x xs -> PrefixFree x) ->
  Val_wfList xs = true -> Val_wfList ys = true -> InRangeList xs -> InRangeList ys ->
  Val_encodeList xs = Val_encodeList ys -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros ys hp hx hy rx ry e; destruct ys as [|y ys]; try reflexivity.
  - rewrite encodeList_cons in e. destruct (encode_cons y) as (t & r & ht). rewrite ht in e. discriminate.
  - rewrite encodeList_cons in e. destruct (encode_cons x) as (t & r & ht). rewrite ht in e. discriminate.
  - rewrite !encodeList_cons in e. rewrite wfList_cons in hx, hy. apply and2 in hx as [hx hx0]. apply and2 in hy as [hy hy0].
    destruct rx as [rx1 rx2]. destruct ry as [ry1 ry2].
    destruct (hp x (or_introl eq_refl) y _ _ hx hy rx1 ry1 e) as [-> e'].
    f_equal. apply IH; auto. intros z hz. apply hp. right. exact hz.
Qed.

Theorem encode_prefix_free : forall v, PrefixFree v.
Proof.
  enough (H : forall N v, (len (Val_encode v) <= N)%nat -> PrefixFree v)
    by (intro v; exact (H _ v (le_n _))).
  induction N as [|N IH]; intros v hN w r1 r2 hv hw rv rw e.
  { rewrite len_encode in hN. lia. }
  (* every child of [v] is shorter, so the hypothesis covers it *)
  assert (child : forall c, (len (Val_encode c) < len (Val_encode v))%nat -> PrefixFree c)
    by (intros c hc; apply IH; lia).
  rewrite !encode_framed in e.
  destruct (framed_prefix_free _ _ _ _ _ _ (payload_bound _ hv) (payload_bound _ hw) e) as (ht & hp & hr).
  split; [|exact hr]. clear e hr r1 r2.
  pose proof (len_encode v) as hl.
  destruct v as [| b | n | t | bs | xs | a b | | a | i xs | k d | k n | n | b];
  destruct w as [| b' | n' | t' | bs' | ys | a' b' | | a' | i' ys | k' d' | k' n' | n' | b'];
    simpl in ht; try discriminate ht; clear ht.
  - reflexivity.
  - destruct b, b'; simpl in hp; try discriminate hp; reflexivity.
  - simpl in hp. f_equal. apply (natBytes_injective laws); auto.
  - simpl in hp. f_equal. apply (utf8_injective laws). exact hp.
  - simpl in hp. f_equal. exact hp.
  - (* list *) change (Val_encodeList xs = Val_encodeList ys) in hp.
    change (len (Val_encode (Val_list xs)) = (len (Val_encodeList xs) + 9)%nat) in hl. f_equal. rewrite wf_list in hv, hw. apply and2 in hv as [_ hv]. apply and2 in hw as [_ hw].
    rewrite inrange_list in rv, rw.
    apply encodeList_injective; auto.
    intros x hx. apply child. rewrite hl. pose proof (len_in_encodeList _ _ hx). lia.
  - (* pair *) change (Val_encode a ++ Val_encode b = Val_encode a' ++ Val_encode b') in hp.
    change (len (Val_encode (Val_pair a b)) = (len (Val_encode a ++ Val_encode b) + 9)%nat) in hl.
    rewrite length_app in hl. rewrite wf_pair in hv, hw.
    apply and3 in hv as [_ [hv0 hv1]]. apply and3 in hw as [_ [hw0 hw1]].
    destruct rv as [ra rb]. destruct rw as [ra' rb'].
    destruct (child a ltac:(lia) a' _ _ hv0 hw0 ra ra' hp) as [-> hb].
    rewrite <- (app_nil_r (Val_encode b)), <- (app_nil_r (Val_encode b')) in hb.
    destruct (child b ltac:(lia) b' _ _ hv1 hw1 rb rb' hb) as [-> _]. reflexivity.
  - reflexivity.
  - (* some *) change (Val_encode a = Val_encode a') in hp.
    change (len (Val_encode (Val_some a)) = (len (Val_encode a) + 9)%nat) in hl. rewrite wf_some in hv, hw. apply and2 in hv as [_ hv0]. apply and2 in hw as [_ hw0].
    rewrite <- (app_nil_r (Val_encode a)), <- (app_nil_r (Val_encode a')) in hp.
    destruct (child a ltac:(lia) a' _ _ hv0 hw0 rv rw hp) as [-> _]. reflexivity.
  - (* ctor *) change (framed 2 (natBytes i) ++ Val_encodeList xs = framed 2 (natBytes i') ++ Val_encodeList ys) in hp.
    change (len (Val_encode (Val_ctor i xs)) = (len (framed 2%Z (natBytes i) ++ Val_encodeList xs) + 9)%nat) in hl. rewrite wf_ctor in hv, hw.
    apply and3 in hv as [hv [_ hv2]]. apply and3 in hw as [hw [_ hw2]].
    rewrite inrange_ctor in rv, rw. destruct rv as [ri rxs]. destruct rw as [ri' rys].
    apply Z.ltb_lt in hv. apply Z.ltb_lt in hw.
    destruct (framed_prefix_free _ _ _ _ _ _ hv hw hp) as (_ & hi & hl').
    f_equal; [apply (natBytes_injective laws); auto|].
    rewrite length_app in hl.
    apply encodeList_injective; auto.
    intros x hx. apply child. rewrite hl. pose proof (len_in_encodeList _ _ hx). lia.
  - simpl in hp. injection hp as -> ->. reflexivity.
  - simpl in hp. injection hp as -> hp. f_equal. apply (natBytes_injective laws); auto.
  - simpl in hp. f_equal. apply (natBytes_injective laws); auto.
  - simpl in hp. f_equal. apply (be64_injective laws); auto.
Qed.

(** The value codec is injective on well-formed values: the grammar is unambiguous. *)
Theorem encode_injective : forall v w, Val_wf v = true -> Val_wf w = true -> InRange v -> InRange w ->
  Val_encode v = Val_encode w -> v = w.
Proof.
  intros v w hv hw rv rw e. rewrite <- (app_nil_r (Val_encode v)), <- (app_nil_r (Val_encode w)) in e.
  exact (proj1 (encode_prefix_free v w [] [] hv hw rv rw e)).
Qed.

(** What a node is in Lean, which the model erased: a thirty-two byte spec (`Digest.length_eq`)
    and an in-range payload. *)
Definition NodeInRange (n : node) : Prop :=
  len (digest_bytes (node_spec n)) = 32%nat /\ InRange (node_payload n).

(** `Node.encode_injective`, over the printed encoder. *)
Theorem node_encode_injective : forall n m, node_version n = 0 -> node_version m = 0 ->
  Val_wf (node_payload n) = true -> Val_wf (node_payload m) = true -> NodeInRange n -> NodeInRange m ->
  Node_encode n = Node_encode m -> n = m.
Proof.
  intros [v k [sp] p] [v' k' [sp'] p'] hv hv' hw hw' [hs rp] [hs' rp'] e. simpl in *. subst v v'.
  injection e as hk e. apply Kind_byte_injective in hk. subst k'.
  destruct (app_same_length _ _ _ _ (eq_trans hs (eq_sym hs')) e) as [-> e'].
  rewrite (encode_injective _ _ hw hw' rp rp' e'). reflexivity.
Qed.

(** In a sound store a conflict is a collision of bytes: two different node byte strings with one
    hash. *)
Corollary put_conflict_bytes : forall s n m d s', Sound s ->
  NodeInRange n -> NodeInRange m ->
  Store_putNode s n = Except_ok (Outcome_conflict m, (d, s')) ->
  Node_encode m <> Node_encode n /\ sha256 (Node_encode m) = sha256 (Node_encode n).
Proof.
  intros s n m d s' hs rn rm h.
  destruct (putNode_ok _ _ _ _ _ h) as (hwn & hvn & _ & _ & _ & _).
  destruct (put_conflict _ _ _ _ _ h) as (_ & hf & hne & _ & _).
  destruct (put_conflict_collision _ _ _ _ _ (sound_addressed _ hs) h) as [_ hh].
  split; [|exact hh]. intro e. apply hne.
  apply node_encode_injective; auto; [eapply sound_version | eapply sound_wf]; eauto.
Qed.

End WithLaws.

End Grammar.
