(** * Budget: Lean's budgeted call tree is the budget-[k] truncation of the tree meaning

    Lean reads a loop as a chain of finite call trees: [denoteRowsB table k e env]
    ([src/Effect4/Laws/Program/DenoteRowsB.lean]) cuts each loop invocation after [k] tests and
    answers [none] there. Its divergence is a cut at every budget ([Chain.Diverges],
    [src/Effect4/Laws/Program/CallChain.lean] on [claude/math-d3]). The Rocq meaning
    ([Denote.meaning]) has no budget: a loop is [ITree.iter], and divergence is [≈ ITree.spin]
    ([Judgments.Diverges]). This file joins the two readings.

    - [program], [pbind], [crun], [approx]: Lean's finite trees ([Effects.Program]), a host's run
      of one ([Effects.Comodel.run]) and the approximation order ([Effects.Program.Approx]).
    - [iterB], [then_opt], [loop_stepB], [denoteB]: Lean's [iter]
      ([src/Effect4/Laws/Program/Iter.lean]), [thenOpt], [loopStep] and [denoteRowsB],
      transcribed arm by arm over the events of [Denote.v].
    - [denoteF]: the tree meaning on the fragment the two share, over the cell and host events
      alone. On the fragment it is [Denote.meaning] ([meaning_fragment]).
    - [iter_upto], [denoteT]: the truncation of the meaning at budget [k]: each [ITree.iter] of a
      loop cut after [k] tests. It is Lean's tree ([truncation_is_denoteB]).
    - [below]: a finite tree with cuts is below an interaction tree when the two agree, up to
      silent steps, everywhere the finite tree is not cut. Lean's tree at every budget is below
      the meaning ([denoteB_below]).
    - [run_tree]: the meaning run under a host, with a call the host does not answer as a
      frontier node ([Stuck], as [Run.Waits]). Lean's three outcomes and the tree's are one:
      [finishes_iff], [waits_iff], [diverges_iff]; and with no host, [meaning_diverges_iff].

    The fragment is what [Denote.v] and [denoteRowsB] both give an arm: [succeed], [fail],
    [sync], [suspend], [bind], [select], the host rows, the three cell rows and [iterate]
    ([in_fragment]). Lean's arms for [exit], [catchCause], [catchIf], [matchCause] and
    [onExit] have no arm in [Denote.v]; [Denote.v]'s arms for definitions and the context have
    none in [denoteRowsB]. Both sides answer [outside] there. Two differences of the
    transcription: a host row's position is not checked against a row table (the Rocq meaning
    has none, so it is Lean's at a table long enough), and the leaves are [Denote.v]'s own,
    which transcribe [denoteRows]'s. *)

From Stdlib Require Import List ZArith String Bool Lia Arith.
Import ListNotations.
From ITree Require Import ITree ITreeFacts Basics.Basics Events.State Events.StateFacts
  Interp.RecursionFacts.
From Paco Require Import paco.
Import ITreeNotations Basics.Basics.Monads.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Judgments.

Local Open Scope list_scope.

(** ** Lean's finite trees *)

(** [Effects.Program]: a result, or one event with a continuation for each answer. It is
    inductive, so every tree is finite; a budget cut is a result [None]. *)
Inductive program (E : Type -> Type) (R : Type) : Type :=
| PRet (r : R)
| PVis {X : Type} (e : E X) (k : X -> program E R).
Arguments PRet {E R}.
Arguments PVis {E R X}.

Fixpoint pbind {E A B} (p : program E A) (f : A -> program E B) : program E B :=
  match p with
  | PRet a => f a
  | PVis e k => PVis e (fun x => pbind (k x) f)
  end.

Definition pmap {E A B} (f : A -> B) (p : program E A) : program E B :=
  pbind p (fun a => PRet (f a)).

(** A finite tree read as an interaction tree. *)
Fixpoint embed {E R} (p : program E R) : itree E R :=
  match p with
  | PRet r => Ret r
  | PVis e k => Vis e (fun x => embed (k x))
  end.

(** **A host** ([Effects.Comodel]): from a state, an answer to an event and the next state, or
    [None] where it does not answer. *)
Definition host (E : Type -> Type) (S : Type) : Type := forall X, E X -> S -> option (X * S).

(** [Effects.Comodel.run]: the result and the final state, or [None] where the host does not
    answer a call. *)
Fixpoint crun {E R S} (h : host E S) (p : program E R) (s : S) : option (R * S) :=
  match p with
  | PRet r => Some (r, s)
  | PVis e k =>
    match h _ e s with
    | Some (x, s') => crun h (k x) s'
    | None => None
    end
  end.

Lemma crun_bind {E A B S} (h : host E S) (p : program E A) (f : A -> program E B) (s : S) :
  crun h (pbind p f) s =
    match crun h p s with Some (a, s') => crun h (f a) s' | None => None end.
Proof.
  revert s; induction p as [r | X e k IH]; intros s; cbn; [reflexivity |].
  destruct (h X e s) as [[x s'] |]; [apply IH | reflexivity].
Qed.

(** ** The approximation order ([Effects.Program.Approx], [Effects/Coalgebra/System.lean]) *)

(** A cut is below every tree; otherwise both end with one result, or both raise one event and
    are ordered at every answer. *)
Inductive approx {E R} : program E (option R) -> program E (option R) -> Prop :=
| approx_cut q : approx (PRet None) q
| approx_done r : approx (PRet (Some r)) (PRet (Some r))
| approx_vis X (e : E X) k k' : (forall x, approx (k x) (k' x)) -> approx (PVis e k) (PVis e k').

Lemma approx_refl {E R} (p : program E (option R)) : approx p p.
Proof.
  induction p as [[r |] | X e k IH]; constructor; auto.
Qed.

(** [Effects.Comodel.run_approx] and the math seat's [run_approx_none]: a finish and a wait of a
    tree are the same finish and wait of every tree above it. *)
Lemma crun_approx {E R S} (h : host E S) (p q : program E (option R)) (s : S) :
  approx p q ->
  (forall r s', crun h p s = Some (Some r, s') -> crun h q s = Some (Some r, s')) /\
  (crun h p s = None -> crun h q s = None).
Proof.
  intros H; revert s; induction H as [q | r | X e k k' _ IH]; intros s; cbn.
  - split; [intros r s' E'; discriminate | intros E'; discriminate].
  - split; auto.
  - destruct (h X e s) as [[x s1] |]; [apply IH | split; auto].
Qed.

(** ** Lean's loop operator and the budgeted meaning, transcribed *)

(** What a round's answer does ([iterNext]): stop with it, or go on at the next cursor. *)
Definition iter_next {E X Y} (next : X -> program E (option Y)) (r : Y + X) : program E (option Y) :=
  match r with
  | inl y => PRet (Some y)
  | inr x' => next x'
  end.

(** [iter] ([src/Effect4/Laws/Program/Iter.lean]): run the round [f] at most [k] times;
    [inl] stops, [inr] goes on; [None] is the budget ended first. *)
Fixpoint iterB {E X Y} (f : X -> program E (Y + X)) (k : nat) (x : X) : program E (option Y) :=
  match k with
  | O => PRet None
  | S k' => pbind (f x) (iter_next (iterB f k'))
  end.

(** The events of the fragment: the cell rows and the host rows. *)
Notation E1 := (StoreE +' RowE).

(** [thenOpt]: a cut first program cuts the whole. *)
Definition then_opt (p : program E1 (option exitv)) (rest : exitv -> program E1 (option exitv))
    : program E1 (option exitv) :=
  pbind p (fun o => match o with None => PRet None | Some ex => rest ex end).

(** [loopStep]: one round at the cursor [c], in [iter]'s shape. A cut body stops the loop cut. *)
Definition loop_stepB (body : list val_ -> program E1 (option exitv)) (env : list val_)
    (test step result : term) (c : val_) : program E1 (option exitv + val_) :=
  match eval_term (env ++ [c]) test with
  | Some (Val_bool true) =>
    pbind (body (env ++ [c])) (fun o =>
      match o with
      | None => PRet (inl None)
      | Some (Failure image) => PRet (inl (Some (Failure image)))
      | Some (Success a) =>
        match eval_term (env ++ [c; a]) step with
        | Some c' => PRet (inr c')
        | None => PRet (inl (Some bad_shape))
        end
      end)
  | Some (Val_bool false) =>
    PRet (inl (Some (match eval_term (env ++ [c]) result with
                     | Some v => Success v
                     | None => bad_shape
                     end)))
  | _ => PRet (inl (Some bad_shape))
  end.

Definition opt_join {A} (o : option (option A)) : option A :=
  match o with Some x => x | None => None end.

(** A leaf of the fragment, as [Denote.denote] answers it: an exit. *)
Definition leaf (o : option exitv) : exitv := match o with Some x => x | None => bad_shape end.

(** **[denoteRowsB table k]**, at the events of [Denote.v]. Each arm names Lean's. A program
    outside the fragment answers [outside], where Lean's [denoteRows] answers [outsideExit]. *)
Fixpoint denoteB (k : nat) (e : eff native_op) (env : list val_) {struct e}
    : program E1 (option exitv) :=
  match e with
  (* the leaves: [some <$> denoteRows table e env], [denoteRows]'s arms as [Denote.denote] *)
  | Eff_succeed t => PRet (Some (leaf (option_map Success (eval_term env t))))
  | Eff_fail t => PRet (Some (leaf (option_map fail_exit (eval_term env t))))
  | Eff_sync t =>
    PRet (Some (Success (match eval_term env t with Some v => v | None => Val_unit end)))
  | Eff_perform op r =>
    match eval_term env r with
    | None => PRet (Some bad_shape)
    | Some v =>
      match op with
      (* [rowCall]: one node, whose answer is the continuation's exit *)
      | NativeOp_external i => PVis (inr1 (Row i v)) (fun x => PRet (Some x))
      | NativeOp_refMake => PVis (inl1 (RefMake v)) (fun x => PRet (Some (Success x)))
      | NativeOp_refGet => PVis (inl1 (RefGet v)) (fun x => PRet (Some (Success x)))
      | NativeOp_refSet =>
        match v with
        | Val_list [c; w] => PVis (inl1 (RefSet c w)) (fun x => PRet (Some (Success x)))
        | _ => PRet (Some bad_shape)
        end
      | _ => PRet (Some outside)
      end
    end
  (* [.suspend b] *)
  | Eff_suspend b => denoteB k b env
  (* [.bind a b]: [thenOpt], a failure ends the sequence *)
  | Eff_bind a b =>
    then_opt (denoteB k a env) (fun ex =>
      match ex with
      | Success v => denoteB k b (env ++ [v])
      | Failure _ => PRet (Some ex)
      end)
  (* [.select t d a b] *)
  | Eff_select t d a b =>
    match option_map (decide d) (eval_term env t) with
    | Some (Some (true, bound)) => denoteB k a (env ++ bound)
    | Some (Some (false, bound)) => denoteB k b (env ++ bound)
    | _ => PRet (Some bad_shape)
    end
  (* [.iterate]: [Option.join <$> iter (loopStep (denoteRowsB table k body) ..) k c₀] *)
  | Eff_iterate _ initial test step result body =>
    match eval_term env initial with
    | Some c0 => pmap opt_join (iterB (loop_stepB (fun env' => denoteB k body env') env test step result) k c0)
    | None => PRet (Some bad_shape)
    end
  | _ => PRet (Some outside)
  end.

(** The fragment both meanings give an arm. *)
Fixpoint in_fragment (e : eff native_op) : bool :=
  match e with
  | Eff_succeed _ | Eff_fail _ | Eff_sync _ => true
  | Eff_perform op _ =>
    match op with
    | NativeOp_external _ | NativeOp_refMake | NativeOp_refGet | NativeOp_refSet => true
    | _ => false
    end
  | Eff_suspend b => in_fragment b
  | Eff_bind a b => in_fragment a && in_fragment b
  | Eff_select _ _ a b => in_fragment a && in_fragment b
  | Eff_iterate _ _ _ _ _ body => in_fragment body
  | _ => false
  end.

(** ** Monotone in the budget ([denoteRowsB_approx]) *)

Lemma approx_bind {A B} (p q : program E1 (option A)) (F G : option A -> program E1 (option B)) :
  approx p q -> F None = PRet None -> (forall a, approx (F (Some a)) (G (Some a))) ->
  approx (pbind p F) (pbind q G).
Proof.
  intros H Hcut Hk; induction H as [q | r | X e k k' _ IH]; cbn.
  - rewrite Hcut; constructor.
  - apply Hk.
  - constructor; exact IH.
Qed.

Lemma approx_then_opt (p q : program E1 (option exitv)) (f g : exitv -> program E1 (option exitv)) :
  approx p q -> (forall ex, approx (f ex) (g ex)) -> approx (then_opt p f) (then_opt q g).
Proof. intros H Hk; apply approx_bind; auto. Qed.

(** [approx_iter_loopStep]: a loop at a budget is below the same loop at a larger budget over a
    larger body. *)
Lemma approx_iter_loop_stepB (body body' : list val_ -> program E1 (option exitv))
    (hb : forall env, approx (body env) (body' env)) env test step result :
  forall k k', k <= k' -> forall c,
    approx (pmap opt_join (iterB (loop_stepB body env test step result) k c))
           (pmap opt_join (iterB (loop_stepB body' env test step result) k' c)).
Proof.
  induction k as [| k IH]; intros k' Hk c; [constructor |].
  destruct k' as [| k']; [lia |].
  cbn [iterB]. unfold pmap, loop_stepB.
  destruct (eval_term (env ++ [c]) test) as [[] | ]; cbn; try apply approx_refl.
  destruct b; cbn; [| apply approx_refl].
  (* the body's tree, then the round's answer *)
  assert (Hpb : forall (p q : program E1 (option exitv)), approx p q ->
    approx (pbind (pbind (pbind p (fun o => match o with
      | None => PRet (inl None)
      | Some (Failure image) => PRet (inl (Some (Failure image)))
      | Some (Success a) => match eval_term (env ++ [c; a]) step with
                            | Some c' => PRet (inr c') | None => PRet (inl (Some bad_shape)) end
      end)) (iter_next (iterB (loop_stepB body env test step result) k))) (fun a => PRet (opt_join a)))
      (pbind (pbind (pbind q (fun o => match o with
      | None => PRet (inl None)
      | Some (Failure image) => PRet (inl (Some (Failure image)))
      | Some (Success a) => match eval_term (env ++ [c; a]) step with
                            | Some c' => PRet (inr c') | None => PRet (inl (Some bad_shape)) end
      end)) (iter_next (iterB (loop_stepB body' env test step result) k'))) (fun a => PRet (opt_join a)))).
  { intros p q H; induction H as [q | r | X e kk kk' _ IHv]; cbn.
    - constructor.
    - destruct r as [a | image]; cbn; [| constructor].
      destruct (eval_term (env ++ [c; a]) step) as [c' |]; cbn; [| constructor].
      apply IH; lia.
    - constructor; exact IHv. }
  apply Hpb, hb.
Qed.

Theorem denoteB_approx k k' : k <= k' ->
  forall e env, approx (denoteB k e env) (denoteB k' e env).
Proof.
  intros Hk e; induction e; intros env; cbn [denoteB]; try apply approx_refl.
  - (* suspend *) apply IHe.
  - (* bind *) apply approx_then_opt; [apply IHe1 |].
    intros [v | image]; [apply IHe2 | apply approx_refl].
  - (* select *)
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |]; auto; apply approx_refl.
  - (* iterate *)
    destruct (eval_term env t) as [c0 |]; [| apply approx_refl].
    apply approx_iter_loop_stepB; [exact IHe | lia].
Qed.

(** ** The tree meaning on the fragment *)

(** [Denote.seq] and [Denote.loop_step] over the cell and host events alone. *)
Definition seqF (t : itree E1 exitv) (k : val_ -> itree E1 exitv) : itree E1 exitv :=
  ITree.bind t (fun x => match x with Success v => k v | Failure _ => Ret x end).

Definition loop_stepF (body : list val_ -> itree E1 exitv) (env : list val_) (test step result : term)
    (c : val_) : itree E1 (val_ + exitv) :=
  match eval_term (env ++ [c]) test with
  | Some (Val_bool true) =>
    ITree.bind (body (env ++ [c])) (fun x =>
      match x with
      | Failure _ => Ret (inr x)
      | Success a =>
        match eval_term (env ++ [c; a]) step with
        | Some c' => Ret (inl c')
        | None => Ret (inr bad_shape)
        end
      end)
  | Some (Val_bool false) =>
    Ret (inr (match eval_term (env ++ [c]) result with Some v => Success v | None => bad_shape end))
  | _ => Ret (inr bad_shape)
  end.

(** [Denote.denote]'s arms on the fragment, with no definitions and no context. *)
Fixpoint denoteF (e : eff native_op) (env : list val_) {struct e} : itree E1 exitv :=
  match e with
  | Eff_succeed t => Ret (leaf (option_map Success (eval_term env t)))
  | Eff_fail t => Ret (leaf (option_map fail_exit (eval_term env t)))
  | Eff_sync t => Ret (Success (match eval_term env t with Some v => v | None => Val_unit end))
  | Eff_suspend b => denoteF b env
  | Eff_perform op r =>
    match eval_term env r with
    | None => Ret bad_shape
    | Some v =>
      match op with
      | NativeOp_external i => ITree.trigger (inr1 (Row i v))
      | NativeOp_refMake => ITree.map Success (ITree.trigger (inl1 (RefMake v)))
      | NativeOp_refGet => ITree.map Success (ITree.trigger (inl1 (RefGet v)))
      | NativeOp_refSet =>
        match v with
        | Val_list [c; w] => ITree.map Success (ITree.trigger (inl1 (RefSet c w)))
        | _ => Ret bad_shape
        end
      | _ => Ret outside
      end
    end
  | Eff_bind a b => seqF (denoteF a env) (fun v => denoteF b (env ++ [v]))
  | Eff_select t d a b =>
    match option_map (decide d) (eval_term env t) with
    | Some (Some (true, bound)) => denoteF a (env ++ bound)
    | Some (Some (false, bound)) => denoteF b (env ++ bound)
    | _ => Ret bad_shape
    end
  | Eff_iterate _ initial test step result body =>
    match eval_term env initial with
    | Some c0 => ITree.iter (loop_stepF (fun env' => denoteF body env') env test step result) c0
    | None => Ret bad_shape
    end
  | _ => Ret outside
  end.

(** On the fragment, [Denote.denote] raises no [Run]: answered by any recursion, it is
    [denoteF]. *)
Lemma denote_fragment (f : RunE ~> itree (RunE +' E1)) bodies :
  forall e env ps ctx, in_fragment e = true ->
    interp (mrecursive f) (denote bodies e env ps ctx) ≈ denoteF e env.
Proof.
  intros e; induction e; intros env ps ctx Hin; cbn in Hin |- *; try discriminate.
  - unfold ret_val; destruct (eval_term env t); rewrite interp_ret; reflexivity.
  - destruct (eval_term env t); rewrite interp_ret; reflexivity.
  - rewrite interp_ret; reflexivity.
  - apply IHe; exact Hin.
  - destruct (eval_term env t) as [v |]; [| rewrite interp_ret; reflexivity].
    destruct o; try discriminate; cbn.
    + unfold ITree.map; rewrite interp_bind, interp_trigger; cbn.
      apply eutt_clo_bind with (UU := eq); [reflexivity |]; intros ? ? <-.
      rewrite interp_ret; reflexivity.
    + unfold ITree.map; rewrite interp_bind, interp_trigger; cbn.
      apply eutt_clo_bind with (UU := eq); [reflexivity |]; intros ? ? <-.
      rewrite interp_ret; reflexivity.
    + destruct v; try (rewrite interp_ret; reflexivity).
      destruct l as [| c [| w [| ? ?]]]; try (rewrite interp_ret; reflexivity).
      unfold ITree.map; rewrite interp_bind, interp_trigger; cbn.
      apply eutt_clo_bind with (UU := eq); [reflexivity |]; intros ? ? <-.
      rewrite interp_ret; reflexivity.
    + rewrite interp_trigger; cbn; reflexivity.
  - apply andb_prop in Hin as [Ha Hb].
    unfold seq, seqF; rewrite interp_bind.
    apply eutt_clo_bind with (UU := eq); [apply IHe1; exact Ha |]; intros x ? <-.
    destruct x; [apply IHe2; exact Hb | rewrite interp_ret; reflexivity].
  - apply andb_prop in Hin as [Ha Hb].
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |];
      try (rewrite interp_ret; reflexivity); [apply IHe1 | apply IHe2]; assumption.
  - destruct (eval_term env t) as [c0 |]; [| rewrite interp_ret; reflexivity].
    apply interp_iter'_eutt; intros c.
    unfold loop_step, loop_stepF.
    destruct (eval_term (env ++ [c]) t0) as [[] |]; try (rewrite interp_ret; reflexivity).
    destruct b; [| rewrite interp_ret; reflexivity].
    rewrite interp_bind.
    apply eutt_clo_bind with (UU := eq); [apply IHe; exact Hin |]; intros x ? <-.
    destruct x; [destruct (eval_term (env ++ [c; v]) t1) |]; rewrite interp_ret; reflexivity.
Qed.

(** **On the fragment the meaning is [denoteF]**, up to silent steps. *)
Theorem meaning_fragment e : in_fragment e = true -> meaning e ≈ denoteF e [].
Proof.
  intros Hin. unfold meaning. rewrite mrec_as_interp. apply denote_fragment; exact Hin.
Qed.

(** ** The truncation of the meaning at a budget *)

(** **The truncation of a loop**: [ITree.iter f] run for at most [k] tests, then cut ([None]).
    The truncation must see the loop: in the meaning a test is a silent step like any other. So it
    is an operator on the meaning's loop, [ITree.iter], applied at each loop. *)
Fixpoint iter_upto {E X Y} (f : X -> itree E (X + Y)) (k : nat) (x : X) : itree E (option Y) :=
  match k with
  | O => Ret None
  | S k' => ITree.bind (f x) (fun r => match r with inl x' => Tau (iter_upto f k' x') | inr y => Ret (Some y) end)
  end.

Definition seqT (t : itree E1 (option exitv)) (k : val_ -> itree E1 (option exitv))
    : itree E1 (option exitv) :=
  ITree.bind t (fun o => match o with
                         | None => Ret None
                         | Some (Success v) => k v
                         | Some (Failure _ as x) => Ret (Some x)
                         end).

Definition loop_stepT (body : list val_ -> itree E1 (option exitv)) (env : list val_)
    (test step result : term) (c : val_) : itree E1 (val_ + option exitv) :=
  match eval_term (env ++ [c]) test with
  | Some (Val_bool true) =>
    ITree.bind (body (env ++ [c])) (fun o =>
      match o with
      | None => Ret (inr None)
      | Some (Failure _ as x) => Ret (inr (Some x))
      | Some (Success a) =>
        match eval_term (env ++ [c; a]) step with
        | Some c' => Ret (inl c')
        | None => Ret (inr (Some bad_shape))
        end
      end)
  | Some (Val_bool false) =>
    Ret (inr (Some (match eval_term (env ++ [c]) result with Some v => Success v | None => bad_shape end)))
  | _ => Ret (inr (Some bad_shape))
  end.

(** **The meaning truncated at [k]**: [denoteF] with each loop truncated, and a cut carried out of
    every sequence. *)
Fixpoint denoteT (k : nat) (e : eff native_op) (env : list val_) {struct e} : itree E1 (option exitv) :=
  match e with
  | Eff_suspend b => denoteT k b env
  | Eff_bind a b => seqT (denoteT k a env) (fun v => denoteT k b (env ++ [v]))
  | Eff_select t d a b =>
    match option_map (decide d) (eval_term env t) with
    | Some (Some (true, bound)) => denoteT k a (env ++ bound)
    | Some (Some (false, bound)) => denoteT k b (env ++ bound)
    | _ => Ret (Some bad_shape)
    end
  | Eff_iterate _ initial test step result body =>
    match eval_term env initial with
    | Some c0 => ITree.map opt_join (iter_upto (loop_stepT (fun env' => denoteT k body env') env test step result) k c0)
    | None => Ret (Some bad_shape)
    end
  | e => ITree.map Some (denoteF e env)
  end.

Lemma embed_bind {E A B} (p : program E A) (f : A -> program E B) :
  embed (pbind p f) ≅ ITree.bind (embed p) (fun a => embed (f a)).
Proof.
  induction p as [r | X e k IH]; cbn.
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_vis. apply eqit_Vis; intros x; apply IH.
Qed.

(** The loop: a truncated [ITree.iter] is Lean's [iter] at the same budget. *)
Lemma truncation_loop (bodyT : list val_ -> itree E1 (option exitv))
    (bodyB : list val_ -> program E1 (option exitv)) (hb : forall env, bodyT env ≈ embed (bodyB env))
    env test step result :
  forall j c, iter_upto (loop_stepT bodyT env test step result) j c
              ≈ embed (iterB (loop_stepB bodyB env test step result) j c).
Proof.
  induction j as [| j IH]; intros c; cbn; [reflexivity |].
  rewrite embed_bind.
  unfold loop_stepT, loop_stepB.
  destruct (eval_term (env ++ [c]) test) as [[] |]; cbn; rewrite ?bind_ret_l; try reflexivity.
  destruct b; cbn; rewrite ?bind_ret_l; [| reflexivity].
  rewrite bind_bind, embed_bind, bind_bind.
  apply eutt_clo_bind with (UU := eq); [apply hb |]; intros o ? <-.
  destruct o as [[a | image] |]; cbn; rewrite ?bind_ret_l; try reflexivity.
  destruct (eval_term (env ++ [c; a]) step); cbn; rewrite ?bind_ret_l; [| reflexivity].
  rewrite tau_eutt; apply IH.
Qed.

(** **Lean's tree is the truncation of the meaning**: at every budget and on the fragment, the
    meaning truncated at [k] is [denoteRowsB k], up to silent steps. *)
Theorem truncation_is_denoteB k : forall e env, in_fragment e = true ->
  denoteT k e env ≈ embed (denoteB k e env).
Proof.
  intros e; induction e; intros env Hin; cbn in Hin |- *; try discriminate.
  - destruct (eval_term env t); cbn; rewrite map_ret; reflexivity.
  - destruct (eval_term env t); cbn; rewrite map_ret; reflexivity.
  - rewrite map_ret; reflexivity.
  - apply IHe; exact Hin.
  - destruct (eval_term env t) as [v |]; [| cbn; rewrite map_ret; reflexivity].
    destruct o; try discriminate; cbn.
    1-2: unfold ITree.map, ITree.trigger; rewrite !bind_vis;
      apply eqit_Vis; intros x; rewrite !bind_ret_l; reflexivity.
    + destruct v; try (cbn; rewrite map_ret; reflexivity).
      destruct l as [| c [| w [| ? ?]]]; try (cbn; rewrite map_ret; reflexivity).
      unfold ITree.map, ITree.trigger; rewrite !bind_vis;
        apply eqit_Vis; intros x; rewrite !bind_ret_l; reflexivity.
    + unfold ITree.map, ITree.trigger; rewrite bind_vis;
        apply eqit_Vis; intros x; rewrite !bind_ret_l; reflexivity.
  - apply andb_prop in Hin as [Ha Hb].
    unfold seqT, then_opt; rewrite embed_bind.
    apply eutt_clo_bind with (UU := eq); [apply IHe1; exact Ha |]; intros o ? <-.
    destruct o as [[v | image] |]; cbn; [apply IHe2; exact Hb | reflexivity | reflexivity].
  - apply andb_prop in Hin as [Ha Hb].
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |];
      try reflexivity; [apply IHe1 | apply IHe2]; assumption.
  - destruct (eval_term env t) as [c0 |]; [| reflexivity].
    unfold pmap. rewrite embed_bind. unfold ITree.map.
    apply eutt_clo_bind with (UU := eq); [| intros ? ? <-; reflexivity].
    apply truncation_loop; intros env'; apply IHe; exact Hin.
Qed.

(** ** Lean's tree is below the meaning *)

(** **A finite tree with cuts below an interaction tree**: a cut is below every tree; a result is
    below a tree equivalent to that result; an event is below a tree equivalent to the same event,
    each continuation below the other's. The order of [Effects.Program.Approx], with the larger
    side an interaction tree read up to silent steps. *)
Inductive below {E R} : program E (option R) -> itree E R -> Prop :=
| below_cut t : below (PRet None) t
| below_ret r t : t ≈ Ret r -> below (PRet (Some r)) t
| below_vis X (e : E X) k t k' : t ≈ Vis e k' -> (forall x, below (k x) (k' x)) -> below (PVis e k) t.

Lemma below_eutt {E R} (p : program E (option R)) (t t' : itree E R) :
  below p t -> t ≈ t' -> below p t'.
Proof.
  intros H; revert t'; induction H as [t | r t Ht | X e k t k' Ht Hk _]; intros t' Htt'.
  - constructor.
  - constructor; rewrite <- Htt'; exact Ht.
  - econstructor; [rewrite <- Htt'; exact Ht | exact Hk].
Qed.

#[global] Instance below_eutt_proper {E R} (p : program E (option R)) :
  Proper (eutt eq ==> iff) (below p).
Proof.
  intros t t' Htt'; split; intros H; eapply below_eutt; eauto; symmetry; exact Htt'.
Qed.

#[global] Instance below_eq_itree_proper {E R} (p : program E (option R)) :
  Proper (eq_itree eq ==> iff) (below p).
Proof. intros t t' Htt'; apply below_eutt_proper, eq_sub_eutt, Htt'. Qed.

Lemma below_bind {E A B} (p : program E (option A)) (t : itree E A)
    (F : option A -> program E (option B)) (G : A -> itree E B) :
  below p t -> F None = PRet None -> (forall a, below (F (Some a)) (G a)) ->
  below (pbind p F) (ITree.bind t G).
Proof.
  intros H Hcut Hk; induction H as [t | r t Ht | X e k t k' Ht _ IH]; cbn.
  - rewrite Hcut; constructor.
  - eapply below_eutt; [apply Hk |]. rewrite Ht, bind_ret_l; reflexivity.
  - econstructor; [rewrite Ht, bind_vis; reflexivity | exact IH].
Qed.

(** The loop: Lean's [iter] at every budget is below [ITree.iter]. *)
Lemma below_loop (bodyB : list val_ -> program E1 (option exitv)) (bodyF : list val_ -> itree E1 exitv)
    (hb : forall env, below (bodyB env) (bodyF env)) env test step result :
  forall j c, below (pmap opt_join (iterB (loop_stepB bodyB env test step result) j c))
                    (ITree.iter (loop_stepF bodyF env test step result) c).
Proof.
  induction j as [| j IH]; intros c; [constructor |].
  eapply below_eutt; [| symmetry; apply eq_sub_eutt, unfold_iter].
  cbn [iterB]; unfold pmap, loop_stepB, loop_stepF.
  destruct (eval_term (env ++ [c]) test) as [[] |];
    cbn; try (constructor; rewrite bind_ret_l; reflexivity).
  destruct b; cbn; [| constructor; rewrite bind_ret_l; reflexivity].
  rewrite bind_bind.
  specialize (hb (env ++ [c])).
  induction hb as [t | r t Ht | X e k t k' Ht _ IHv]; cbn.
  - constructor.
  - destruct r as [a | image]; cbn.
    + destruct (eval_term (env ++ [c; a]) step) as [c' |] eqn:Hstep; cbn.
      * eapply below_eutt; [apply IH |].
        rewrite Ht, bind_ret_l; cbv beta iota; rewrite Hstep, bind_ret_l, tau_eutt; reflexivity.
      * constructor; rewrite Ht, bind_ret_l; cbv beta iota; rewrite Hstep, bind_ret_l; reflexivity.
    + constructor; rewrite Ht, bind_ret_l; cbv beta iota; rewrite bind_ret_l; reflexivity.
  - econstructor; [rewrite Ht, bind_vis; reflexivity |].
    exact IHv.
Qed.

(** **Lean's tree at every budget is below the meaning** on the fragment: where [denoteRowsB k]
    is not cut it is the meaning, node for node, up to silent steps. *)
Theorem denoteB_below k : forall e env, in_fragment e = true -> below (denoteB k e env) (denoteF e env).
Proof.
  intros e; induction e; intros env Hin; cbn in Hin |- *; try discriminate.
  - destruct (eval_term env t); constructor; reflexivity.
  - destruct (eval_term env t); constructor; reflexivity.
  - constructor; reflexivity.
  - apply IHe; exact Hin.
  - destruct (eval_term env t) as [v |]; [| constructor; reflexivity].
    destruct o; try discriminate; cbn.
    1-2: econstructor; [unfold ITree.map, ITree.trigger; rewrite bind_vis; reflexivity |];
      intros x; constructor; rewrite bind_ret_l; reflexivity.
    + destruct v; try (constructor; reflexivity).
      destruct l as [| c [| w [| ? ?]]]; try (constructor; reflexivity).
      econstructor; [unfold ITree.map, ITree.trigger; rewrite bind_vis; reflexivity |];
        intros x; constructor; rewrite bind_ret_l; reflexivity.
    + econstructor; [unfold ITree.trigger; reflexivity |]; intros x; constructor; reflexivity.
  - apply andb_prop in Hin as [Ha Hb].
    apply below_bind; [apply IHe1; exact Ha | reflexivity |].
    intros [v | image]; [apply IHe2; exact Hb | constructor; reflexivity].
  - apply andb_prop in Hin as [Ha Hb].
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |];
      try (constructor; reflexivity); [apply IHe1 | apply IHe2]; assumption.
  - destruct (eval_term env t) as [c0 |]; [| constructor; reflexivity].
    apply below_loop; intros env'; apply IHe; exact Hin.
Qed.

(** And so below [Denote.meaning], at the root. *)
Corollary denoteB_below_meaning k e : in_fragment e = true -> below (denoteB k e []) (meaning e).
Proof.
  intros Hin. eapply below_eutt; [apply denoteB_below; exact Hin |].
  symmetry; apply meaning_fragment; exact Hin.
Qed.

(** ** Runs under a host, and how a run ends *)

(** A call the host does not answer: a frontier node, whose answer type is empty ([Run.Waits]
    for every event). *)
Variant StuckE (E : Type -> Type) : Type -> Type :=
| Stuck {X : Type} (e : E X) : StuckE E void.
Arguments Stuck {E X}.

Definition h_run {E S} (h : host E S) : E ~> stateT S (itree (StuckE E)) :=
  fun X e s =>
    match h X e s with
    | Some (x, s') => Ret (s', x)
    | None => Vis (Stuck e) (fun v : void => match v with end)
    end.

(** **The meaning run under a host**: the events answered, a refused call a frontier. *)
Definition run_tree {E S R} (h : host E S) (t : itree E R) (s : S) : itree (StuckE E) (S * R) :=
  interp_state (h_run h) t s.

(** How a tree ends after [n] silent steps: with a result, or at an event. A run under a host
    raises only frontiers, so there an event is a wait. *)
Inductive ends {F A} : nat -> itree F A -> option A -> Prop :=
| ends_ret t a : observe t = RetF a -> ends 0 t (Some a)
| ends_vis t X (e : F X) k : observe t = VisF e k -> ends 0 t None
| ends_tau n t u o : observe t = TauF u -> ends n u o -> ends (S n) t o.

Definition Ends {F A} (t : itree F A) (o : option A) : Prop := exists n, ends n t o.

Lemma ends_eq_itree {F A} n (t t' : itree F A) o : ends n t o -> t ≅ t' -> ends n t' o.
Proof.
  intros H; revert t'; induction H as [t a Ht | t X e k Ht | n t u o Ht _ IH]; intros t' Htt'.
  - constructor. apply eqitree_inv_Ret_r. rewrite <- Htt', (itree_eta t), Ht; reflexivity.
  - destruct (eqitree_inv_Vis_r t' e k) as [k' [Hk' _]].
    { rewrite <- Htt', (itree_eta t), Ht; reflexivity. }
    econstructor; exact Hk'.
  - destruct (eqitree_inv_Tau_r t' u) as [u' [Hu' Huu']].
    { rewrite <- Htt', (itree_eta t), Ht; reflexivity. }
    econstructor; [exact Hu' | apply IH; symmetry; exact Huu'].
Qed.

Lemma ends_some_eutt {F A} n (t : itree F A) a : ends n t (Some a) -> t ≈ Ret a.
Proof.
  intros H; remember (Some a) as o eqn:Ho; induction H as [t a' Ht | | n t u o Ht _ IH].
  - inversion Ho; subst. rewrite (itree_eta t), Ht; reflexivity.
  - discriminate.
  - rewrite (itree_eta t), Ht, tau_eutt; apply IH; exact Ho.
Qed.

Lemma ends_none_eutt {F A} n (t : itree F A) :
  ends n t None -> exists X (e : F X) k, t ≈ Vis e k.
Proof.
  intros H; remember None as o eqn:Ho; induction H as [| t X e k Ht | n t u o Ht _ IH].
  - discriminate.
  - exists X, e, k. rewrite (itree_eta t), Ht; reflexivity.
  - destruct (IH Ho) as (X & e & k & Hu). exists X, e, k.
    rewrite (itree_eta t), Ht, tau_eutt; exact Hu.
Qed.

Lemma eutt_ret_ends {F A} (t : itree F A) a : t ≈ Ret a -> Ends t (Some a).
Proof.
  intros H. punfold H. red in H. cbn in H.
  remember (observe t) as ot eqn:Hot. remember (@RetF F A (itree F A) a) as oa eqn:Hoa.
  revert t Hot. induction H; intros t0 Hot; try discriminate.
  - inversion Hoa; subst. exists 0. constructor. symmetry; exact Hot.
  - destruct (IHeqitF Hoa t1 eq_refl) as [n Hn]. exists (S n). econstructor; [symmetry; exact Hot | exact Hn].
Qed.

Lemma eutt_vis_ends {F A X} (t : itree F A) (e : F X) k : t ≈ Vis e k -> Ends t None.
Proof.
  intros H. punfold H. red in H. cbn in H.
  remember (observe t) as ot eqn:Hot. remember (VisF e k) as ov eqn:Hov.
  revert t Hot. induction H; intros t0 Hot; try discriminate.
  - exists 0. econstructor. symmetry; exact Hot.
  - destruct (IHeqitF Hov t1 eq_refl) as [n Hn]. exists (S n). econstructor; [symmetry; exact Hot | exact Hn].
Qed.

Lemma Ends_eutt {F A} (t t' : itree F A) o : Ends t o -> t ≈ t' -> Ends t' o.
Proof.
  intros [n H] Htt'. destruct o as [a |].
  - apply eutt_ret_ends. rewrite <- Htt'. eapply ends_some_eutt; exact H.
  - destruct (ends_none_eutt n t H) as (X & e & k & Hv).
    eapply eutt_vis_ends. rewrite <- Htt'. exact Hv.
Qed.

#[global] Instance Ends_proper {F A} : Proper (eutt eq ==> eq ==> iff) (@Ends F A).
Proof.
  intros t t' Htt' o o' <-; split; intros H; eapply Ends_eutt; eauto; symmetry; exact Htt'.
Qed.

Lemma Ends_ret_inv {F A} (a : A) o : Ends (Ret a : itree F A) o -> o = Some a.
Proof. intros [n H]; inversion H; cbn in *; congruence. Qed.

Lemma Ends_vis {F A X} (e : F X) (k : X -> itree F A) : Ends (Vis e k) None.
Proof. exists 0; econstructor; reflexivity. Qed.

Lemma Ends_vis_inv {F A X} (e : F X) (k : X -> itree F A) o : Ends (Vis e k) o -> o = None.
Proof. intros [n H]; inversion H; cbn in *; congruence. Qed.

(** A sequence ends where its first part waits, or where the rest ends after the first part's
    result; the silent steps add. *)
Lemma ends_bind_inv {F A B} n (u : itree F B) o : ends n u o ->
  forall (t : itree F A) (k : A -> itree F B), u ≅ ITree.bind t k ->
  (o = None /\ ends n t None) \/
  (exists a n1 n2, ends n1 t (Some a) /\ ends n2 (k a) o /\ n = n1 + n2).
Proof.
  intros H; induction H as [u b Hu | u X e kk Hu | n u u' o Hu Hu' IH]; intros t k Hut;
    destruct (observe t) as [r | t1 | Y e' ke] eqn:Ht.
  - right. exists r, 0, 0. split; [constructor; exact Ht |]. split; [| reflexivity].
    apply ends_eq_itree with (t := u); [constructor; exact Hu |].
    rewrite Hut, (itree_eta t), Ht, bind_ret_l; reflexivity.
  - exfalso. assert (Hx : u ≅ Tau (ITree.bind t1 k)) by (rewrite Hut, (itree_eta t), Ht, bind_tau; reflexivity).
    destruct (eqitree_inv_Tau_r _ _ Hx) as [? [Hx' _]]. congruence.
  - exfalso. assert (Hx : u ≅ Vis e' (fun x => ITree.bind (ke x) k)) by (rewrite Hut, (itree_eta t), Ht, bind_vis; reflexivity).
    destruct (eqitree_inv_Vis_r _ _ _ Hx) as [? [Hx' _]]. congruence.
  - right. exists r, 0, 0. split; [constructor; exact Ht |]. split; [| reflexivity].
    apply ends_eq_itree with (t := u); [econstructor; exact Hu |].
    rewrite Hut, (itree_eta t), Ht, bind_ret_l; reflexivity.
  - exfalso. assert (Hx : u ≅ Tau (ITree.bind t1 k)) by (rewrite Hut, (itree_eta t), Ht, bind_tau; reflexivity).
    destruct (eqitree_inv_Tau_r _ _ Hx) as [? [Hx' _]]. congruence.
  - left. split; [reflexivity | econstructor; exact Ht].
  - right. exists r, 0, (S n). split; [constructor; exact Ht |]. split; [| reflexivity].
    apply ends_eq_itree with (t := u); [econstructor; [exact Hu | exact Hu'] |].
    rewrite Hut, (itree_eta t), Ht, bind_ret_l; reflexivity.
  - assert (Hx : u ≅ Tau (ITree.bind t1 k)) by (rewrite Hut, (itree_eta t), Ht, bind_tau; reflexivity).
    destruct (eqitree_inv_Tau_r _ _ Hx) as [u1 [Hx' Hu1]]. rewrite Hu in Hx'. inversion Hx'; subst u1.
    destruct (IH t1 k Hu1) as [[-> H1] | (a & n1 & n2 & H1 & H2 & ->)].
    + left. split; [reflexivity | econstructor; [exact Ht | exact H1]].
    + right. exists a, (S n1), n2. split; [econstructor; [exact Ht | exact H1] |]. split; [exact H2 | reflexivity].
  - exfalso. assert (Hx : u ≅ Vis e' (fun x => ITree.bind (ke x) k)) by (rewrite Hut, (itree_eta t), Ht, bind_vis; reflexivity).
    destruct (eqitree_inv_Vis_r _ _ _ Hx) as [? [Hx' _]]. congruence.
Qed.

Lemma Ends_bind_inv {F A B} (t : itree F A) (k : A -> itree F B) o :
  Ends (ITree.bind t k) o -> (o = None /\ Ends t None) \/ (exists a, Ends t (Some a) /\ Ends (k a) o).
Proof.
  intros [n H]. destruct (ends_bind_inv n _ o H t k (reflexivity _)) as [[-> H1] | (a & n1 & n2 & H1 & H2 & _)].
  - left; split; [reflexivity | exists n; exact H1].
  - right; exists a; split; [exists n1 | exists n2]; assumption.
Qed.

(** The run's equations, each an [eq_itree]. *)
Lemma run_ret {E S R} (h : host E S) (r : R) s : run_tree h (Ret r) s ≅ Ret (s, r).
Proof. apply interp_state_ret. Qed.

Lemma run_tau {E S R} (h : host E S) (t : itree E R) s : run_tree h (Tau t) s ≅ Tau (run_tree h t s).
Proof. apply interp_state_tau. Qed.

Lemma run_bind {E S A B} (h : host E S) (t : itree E A) (k : A -> itree E B) s :
  run_tree h (ITree.bind t k) s ≅ ITree.bind (run_tree h t s) (fun st => run_tree h (k (snd st)) (fst st)).
Proof. apply interp_state_bind. Qed.

Lemma run_vis {E S R X} (h : host E S) (e : E X) (k : X -> itree E R) s :
  run_tree h (Vis e k) s ≅
    match h X e s with
    | Some (x, s') => Tau (run_tree h (k x) s')
    | None => Vis (Stuck e) (fun v : void => match v with end)
    end.
Proof.
  unfold run_tree. rewrite interp_state_vis. unfold h_run.
  destruct (h X e s) as [[x s'] |].
  - rewrite bind_ret_l; reflexivity.
  - rewrite bind_vis. apply eqit_Vis; intros [].
Qed.

#[global] Instance run_tree_eutt {E S R} (h : host E S) :
  Proper (eutt eq ==> eq ==> eutt eq) (@run_tree E S R h).
Proof. intros t t' Ht s s' <-. unfold run_tree. rewrite Ht. reflexivity. Qed.

#[global] Instance run_tree_eq_itree {E S R} (h : host E S) :
  Proper (eq_itree eq ==> eq ==> eq_itree eq) (@run_tree E S R h).
Proof. intros t t' Ht s s' <-. unfold run_tree. rewrite Ht. reflexivity. Qed.

(** What a finite run reports, in [crun]'s shape: a finish, or a wait ([None]). A cut is never
    the end of a run of the meaning. *)
Definition outcome_of {S R} (o : option (S * R)) : option (option R * S) :=
  match o with Some (s', r) => Some (Some r, s') | None => None end.

Lemma crun_outcome_approx {E R S} (h : host E S) (p q : program E (option R)) s o :
  approx p q -> crun h p s = outcome_of o -> crun h q s = outcome_of o.
Proof.
  intros Hpq Hp. destruct (crun_approx h p q s Hpq) as [Hf Hw].
  destruct o as [[s' r] |]; cbn in *; [apply Hf | apply Hw]; exact Hp.
Qed.

(** ** A finish or a wait of Lean's tree is one of the meaning *)

Lemma below_run {E S R} (h : host E S) (p : program E (option R)) (t : itree E R) :
  below p t -> forall s o, crun h p s = outcome_of o -> Ends (run_tree h t s) o.
Proof.
  intros H; induction H as [t | r t Ht | X e k t k' Ht _ IH]; intros s o Hrun; cbn in Hrun.
  - destruct o as [[? ?] |]; discriminate.
  - destruct o as [[s' r'] |]; inversion Hrun; subst.
    rewrite Ht, run_ret. exists 0; constructor; reflexivity.
  - rewrite Ht, run_vis. destruct (h X e s) as [[x s1] |].
    + rewrite tau_eutt. apply IH; exact Hrun.
    + destruct o as [[? ?] |]; [discriminate |]. apply Ends_vis.
Qed.

(** ** Every end of the meaning is reached at some budget *)

Lemma crun_outcome_mono {St} (h : host E1 St) k k' e env s o : k <= k' ->
  crun h (denoteB k e env) s = outcome_of o -> crun h (denoteB k' e env) s = outcome_of o.
Proof. intros Hk; apply crun_outcome_approx, denoteB_approx; exact Hk. Qed.

(** One round of a budgeted loop, read by a host. *)
Lemma crun_round {St} (h : host E1 St) body env test step result k c s :
  crun h (pmap opt_join (iterB (loop_stepB body env test step result) (S k) c)) s =
    match crun h (loop_stepB body env test step result c) s with
    | Some (inl y, s') => Some (y, s')
    | Some (inr c', s') => crun h (pmap opt_join (iterB (loop_stepB body env test step result) k c')) s'
    | None => None
    end.
Proof.
  unfold pmap; cbn [iterB]. rewrite !crun_bind.
  destruct (crun h (loop_stepB body env test step result c) s) as [[[y | c'] s'] |]; cbn;
    [reflexivity | rewrite crun_bind; reflexivity | reflexivity].
Qed.

Lemma ends_ret_inv {F A} n (t : itree F A) a o : ends n t o -> t ≅ Ret a -> o = Some a.
Proof.
  intros H Ht. apply (@Ends_ret_inv F A a o). eapply Ends_eutt; [exists n; exact H |].
  apply eq_sub_eutt; exact Ht.
Qed.

Lemma ends_tau_inv {F A} n (t u : itree F A) o : ends n t o -> t ≅ Tau u -> exists m, n = S m /\ ends m u o.
Proof.
  intros H Ht. destruct (eqitree_inv_Tau_r _ _ Ht) as [u' [Hu' Huu']].
  inversion H; subst; cbn in *; try congruence.
  rewrite Hu' in H0; inversion H0; subst u0.
  exists n0; split; [reflexivity | eapply ends_eq_itree; [exact H1 | exact Huu']].
Qed.

Lemma adequacy_loop {St} (h : host E1 St) (bodyF : list val_ -> itree E1 exitv)
    (bodyB : nat -> list val_ -> program E1 (option exitv))
    (Hmono : forall k k' env, k <= k' -> approx (bodyB k env) (bodyB k' env))
    (Hadq : forall env s o, Ends (run_tree h (bodyF env) s) o ->
              exists k, crun h (bodyB k env) s = outcome_of o)
    env test step result :
  forall n c s o, ends n (run_tree h (ITree.iter (loop_stepF bodyF env test step result) c) s) o ->
    exists k, crun h (pmap opt_join (iterB (loop_stepB (bodyB k) env test step result) k c)) s = outcome_of o.
Proof.
  intros n; induction n as [n IHn] using lt_wf_ind; intros c s o H.
  set (g := loop_stepF bodyF env test step result) in *.
  set (K := fun lr : val_ + exitv => match lr with inl c' => Tau (ITree.iter g c') | inr r => Ret r end).
  assert (Hu : run_tree h (ITree.iter g c) s ≅
                 ITree.bind (run_tree h (g c) s) (fun st => run_tree h (K (snd st)) (fst st))).
  { rewrite unfold_iter. apply run_bind. }
  destruct (ends_bind_inv n _ o H _ _ Hu) as [[-> Hw] | ([s1 lr] & n1 & n2 & H1 & H2 & ->)].
  - (* the round waits: inside the body *)
    unfold g, loop_stepF in Hw.
    destruct (eval_term (env ++ [c]) test) as [[] | ] eqn:Htest;
      try (exfalso; eapply ends_ret_inv in Hw; [discriminate | apply run_ret]).
    match goal with bb : bool |- _ => destruct bb end;
      [| exfalso; eapply ends_ret_inv in Hw; [discriminate | apply run_ret]].
    destruct (ends_bind_inv n _ None Hw _ _ (run_bind h _ _ s)) as [[_ Hb] | ([s2 x] & n3 & n4 & H3 & H4 & _)].
    + destruct (Hadq (env ++ [c]) s None (ex_intro _ n Hb)) as [kb Hkb].
      exists (S kb). rewrite crun_round. unfold loop_stepB. rewrite Htest, crun_bind.
      rewrite (crun_outcome_approx h _ _ s None (Hmono kb (S kb) _ (le_S _ _ (le_n _))) Hkb). reflexivity.
    + exfalso. destruct x as [a | image]; cbn in H4;
        [destruct (eval_term (env ++ [c; a]) step) |];
        eapply ends_ret_inv in H4; try apply run_ret; discriminate.
  - (* the round ends *)
    unfold g, loop_stepF in H1.
    (* a round that is a result: the test fails, or does not evaluate to a Boolean *)
    assert (Hret : forall r : exitv,
              run_tree h (Ret (@inr val_ exitv r) : itree E1 _) s ≅ Ret (s, @inr val_ exitv r) ->
              ends n1 (run_tree h (Ret (@inr val_ exitv r) : itree E1 _) s) (Some (s1, lr)) ->
              crun h (loop_stepB (bodyB 1) env test step result c) s = Some (inl (Some r), s) ->
              exists k, crun h (pmap opt_join (iterB (loop_stepB (bodyB k) env test step result) k c)) s = outcome_of o).
    { intros r Hr H1' Hstep1. eapply ends_ret_inv in H1'; [| exact Hr]. inversion H1'; subst s1 lr.
      cbn in H2. eapply ends_ret_inv in H2; [| apply run_ret]. subst o.
      exists 1. rewrite crun_round, Hstep1. reflexivity. }
    destruct (eval_term (env ++ [c]) test) as [v |] eqn:Htest.
    2: { eapply Hret; [apply run_ret | exact H1 | unfold loop_stepB; rewrite Htest; reflexivity]. }
    destruct v; try (eapply Hret; [apply run_ret | exact H1 | unfold loop_stepB; rewrite Htest; reflexivity]).
    match goal with bb : bool |- _ => destruct bb end.
    2: { eapply Hret; [apply run_ret | exact H1 | unfold loop_stepB; rewrite Htest; reflexivity]. }
    (* the test holds: the body ran *)
    destruct (ends_bind_inv n1 _ _ H1 _ _ (run_bind h _ _ s)) as [[Hc _] | ([s2 x] & n3 & n4 & H3 & H4 & _)];
      [discriminate |].
    destruct (Hadq (env ++ [c]) s (Some (s2, x)) (ex_intro _ n3 H3)) as [kb Hkb].
    assert (Hb : forall k, kb <= k -> crun h (bodyB k (env ++ [c])) s = Some (Some x, s2)).
    { intros k Hk. apply (crun_outcome_approx h _ _ s (Some (s2, x)) (Hmono kb k _ Hk) Hkb). }
    destruct x as [a | image]; cbn in H4.
    + destruct (eval_term (env ++ [c; a]) step) as [c' |] eqn:Hstep.
      * eapply ends_ret_inv in H4; [| apply run_ret]. inversion H4; subst s2 lr.
        cbn in H2. destruct (ends_tau_inv n2 _ _ o H2 (run_tau h _ s1)) as [m [-> Hm]].
        destruct (IHn m ltac:(lia) c' s1 o Hm) as [k1 Hk1].
        exists (S (Nat.max kb k1)). rewrite crun_round. unfold loop_stepB at 1. rewrite Htest, crun_bind.
        rewrite (Hb (S (Nat.max kb k1)) ltac:(lia)). cbn. rewrite Hstep. cbn.
        eapply crun_outcome_approx; [| exact Hk1].
        apply approx_iter_loop_stepB; [intros env'; apply Hmono |]; lia.
      * eapply ends_ret_inv in H4; [| apply run_ret]. inversion H4; subst s2 lr.
        cbn in H2. eapply ends_ret_inv in H2; [| apply run_ret]. subst o.
        exists (S kb). rewrite crun_round. unfold loop_stepB at 1. rewrite Htest, crun_bind.
        rewrite (Hb (S kb) ltac:(lia)). cbn. rewrite Hstep. reflexivity.
    + eapply ends_ret_inv in H4; [| apply run_ret]. inversion H4; subst s2 lr.
      cbn in H2. eapply ends_ret_inv in H2; [| apply run_ret]. subst o.
      exists (S kb). rewrite crun_round. unfold loop_stepB at 1. rewrite Htest, crun_bind.
      rewrite (Hb (S kb) ltac:(lia)). reflexivity.
Qed.

#[global] Instance Ends_eq_itree_proper {F A} : Proper (eq_itree eq ==> eq ==> iff) (@Ends F A).
Proof. intros t t' Htt' o o' <-. apply Ends_proper; [apply eq_sub_eutt; exact Htt' | reflexivity]. Qed.

Lemma adequacy_trigger {St X} (h : host E1 St) (ev : E1 X) (f : X -> exitv) s o :
  Ends (run_tree h (ITree.map f (ITree.trigger ev)) s) o ->
  crun h (PVis ev (fun x => PRet (Some (f x)))) s = outcome_of o.
Proof.
  intros Hend. unfold ITree.map, ITree.trigger in Hend. rewrite bind_vis, run_vis in Hend. cbn.
  destruct (h X ev s) as [[x s1] |].
  - rewrite tau_eutt, bind_ret_l, run_ret in Hend. apply Ends_ret_inv in Hend. subst o. reflexivity.
  - apply Ends_vis_inv in Hend. subst o. reflexivity.
Qed.

Lemma adequacy_row {St} (h : host E1 St) (ev : E1 exitv) s o :
  Ends (run_tree h (ITree.trigger ev) s) o -> crun h (PVis ev (fun x => PRet (Some x))) s = outcome_of o.
Proof.
  intros Hend. unfold ITree.trigger in Hend. rewrite run_vis in Hend. cbn.
  destruct (h exitv ev s) as [[x s1] |].
  - rewrite tau_eutt, run_ret in Hend. apply Ends_ret_inv in Hend. subst o. reflexivity.
  - apply Ends_vis_inv in Hend. subst o. reflexivity.
Qed.

(** **Every end of the meaning is reached at some budget**: under every host, a finish or a wait
    of the meaning's run is one of [denoteRowsB k]'s for some [k]. *)
Theorem adequacy {St} (h : host E1 St) : forall e env, in_fragment e = true -> forall s out,
  Ends (run_tree h (denoteF e env) s) out -> exists k, crun h (denoteB k e env) s = outcome_of out.
Proof.
  intros e env Hin s out Hend; induction e in env, Hin, s, out, Hend |- *; cbn in Hin |- *; try discriminate;
    try (cbn in Hend; rewrite run_ret in Hend; apply Ends_ret_inv in Hend; subst out; exists 0; reflexivity).
  - (* suspend *) apply IHe; assumption.
  - (* perform *)
    cbn in Hend. destruct (eval_term env t) as [v |];
      [| rewrite run_ret in Hend; apply Ends_ret_inv in Hend; subst out; exists 0; reflexivity].
    destruct o; try discriminate; exists 0.
    1-2: apply adequacy_trigger; exact Hend.
    + destruct v; try (rewrite run_ret in Hend; apply Ends_ret_inv in Hend; subst out; reflexivity).
      destruct l as [| c [| w [| ? ?]]];
        try (rewrite run_ret in Hend; apply Ends_ret_inv in Hend; subst out; reflexivity).
      apply adequacy_trigger; exact Hend.
    + apply adequacy_row; exact Hend.
  - (* bind *)
    apply andb_prop in Hin as [Ha Hb]. cbn in Hend.
    unfold seqF in Hend. rewrite run_bind in Hend.
    apply Ends_bind_inv in Hend as [[-> Hw] | ([s1 x] & H1 & H2)].
    + destruct (IHe1 env Ha s None Hw) as [ka Hka]. exists ka.
      unfold then_opt. rewrite crun_bind, Hka. reflexivity.
    + destruct (IHe1 env Ha s (Some (s1, x)) H1) as [ka Hka]. destruct x as [v | image]; cbn in H2.
      * destruct (IHe2 (env ++ [v]) Hb s1 out H2) as [kb Hkb]. exists (Nat.max ka kb).
        unfold then_opt. rewrite crun_bind.
        rewrite (crun_outcome_mono h ka (Nat.max ka kb) e1 env s (Some (s1, Success v)) ltac:(lia) Hka). cbn.
        apply (crun_outcome_mono h kb); [lia | exact Hkb].
      * rewrite run_ret in H2. apply Ends_ret_inv in H2. subst out. exists ka.
        unfold then_opt. rewrite crun_bind, Hka. reflexivity.
  - (* select *)
    apply andb_prop in Hin as [Ha Hb]. cbn in Hend.
    destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |];
      try (rewrite run_ret in Hend; apply Ends_ret_inv in Hend; subst out; exists 0; reflexivity);
      [apply IHe1 | apply IHe2]; assumption.
  - (* iterate *)
    cbn in Hend. destruct (eval_term env t) as [c0 |];
      [| rewrite run_ret in Hend; apply Ends_ret_inv in Hend; subst out; exists 0; reflexivity].
    destruct Hend as [n Hn].
    apply (adequacy_loop h (fun env' => denoteF e env') (fun k env' => denoteB k e env')) with (n := n);
      [intros k k' env' Hk; apply denoteB_approx; exact Hk | intros env' s' o' H'; apply IHe; assumption | exact Hn].
Qed.

(** ** The three outcomes are one *)

(** Lean's three outcomes of the chain [denoteRowsB k] under a host ([Chain.Finishes],
    [Chain.Waits], [Chain.Diverges], [src/Effect4/Laws/Program/CallChain.lean]). *)
Definition Finishes {St} (h : host E1 St) e env s (r : exitv) s' : Prop :=
  exists k, crun h (denoteB k e env) s = Some (Some r, s').
Definition Waits {St} (h : host E1 St) e env s : Prop :=
  exists k, crun h (denoteB k e env) s = None.
Definition ChainDiverges {St} (h : host E1 St) e env s : Prop :=
  forall k, exists s', crun h (denoteB k e env) s = Some (None, s').

(** A tree with no end diverges. *)
Lemma no_ends_spin {F A} : forall (t : itree F A), (forall n o, ~ ends n t o) -> t ≈ ITree.spin.
Proof.
  ginit. gcofix CIH. intros t Hno.
  rewrite (itree_eta t). rewrite (itree_eta ITree.spin). cbn.
  destruct (observe t) as [a | u | X e k] eqn:Ht.
  - exfalso. apply (Hno 0 (Some a)). constructor. exact Ht.
  - gstep. constructor. gfinal. left. apply CIH. intros n o Hu.
    apply (Hno (S n) o). econstructor; [exact Ht | exact Hu].
  - exfalso. apply (Hno 0 None). econstructor. exact Ht.
Qed.

Theorem finishes_iff {St} (h : host E1 St) e env s r s' : in_fragment e = true ->
  Finishes h e env s r s' <-> run_tree h (denoteF e env) s ≈ Ret (s', r).
Proof.
  intros Hin; split.
  - intros [k Hk]. destruct (below_run h _ _ (denoteB_below k e env Hin) s (Some (s', r)) Hk) as [n Hn].
    eapply ends_some_eutt; exact Hn.
  - intros Hr. apply (adequacy h e env Hin s (Some (s', r))). apply eutt_ret_ends; exact Hr.
Qed.

(** A wait is a frontier node of the run, after finitely many silent steps. *)
Theorem waits_iff {St} (h : host E1 St) e env s : in_fragment e = true ->
  Waits h e env s <-> exists X (ev : StuckE E1 X) k, run_tree h (denoteF e env) s ≈ Vis ev k.
Proof.
  intros Hin; split.
  - intros [k Hk]. destruct (below_run h _ _ (denoteB_below k e env Hin) s None Hk) as [n Hn].
    eapply ends_none_eutt; exact Hn.
  - intros (X & ev & kk & Hv). apply (adequacy h e env Hin s None). eapply eutt_vis_ends; exact Hv.
Qed.

(** **Divergence is one statement**: a cut at every budget, Lean's [Chain.Diverges], exactly when
    the meaning's run is [≈ ITree.spin], [Judgments.Diverges]. Every host, every start. *)
Theorem diverges_iff {St} (h : host E1 St) e env s : in_fragment e = true ->
  ChainDiverges h e env s <-> Diverges (run_tree h (denoteF e env) s).
Proof.
  intros Hin; unfold Diverges; split.
  - intros Hd. apply no_ends_spin. intros n o Hn.
    destruct (adequacy h e env Hin s o (ex_intro _ n Hn)) as [k Hk].
    destruct (Hd k) as [s' Hs']. rewrite Hk in Hs'. destruct o as [[? ?] |]; discriminate.
  - intros Hsp k. destruct (crun h (denoteB k e env) s) as [[[r |] s'] |] eqn:Hk.
    + exfalso. assert (Hf : Finishes h e env s r s') by (exists k; exact Hk).
      apply finishes_iff in Hf; [| exact Hin]. rewrite Hf in Hsp. exact (eutt_Ret_spin_abs _ Hsp).
    + exists s'; reflexivity.
    + exfalso. assert (Hw : Waits h e env s) by (exists k; exact Hk).
      apply waits_iff in Hw as (X & ev & kk & Hv); [| exact Hin].
      rewrite Hv in Hsp. exact (eutt_Vis_spin_abs _ _ Hsp).
Qed.

(** The same three, at the root of [Denote.meaning]. *)
Corollary meaning_finishes_iff {St} (h : host E1 St) e s r s' : in_fragment e = true ->
  Finishes h e [] s r s' <-> run_tree h (meaning e) s ≈ Ret (s', r).
Proof. intros Hin. rewrite (meaning_fragment e Hin). apply finishes_iff; exact Hin. Qed.

Corollary meaning_waits_iff {St} (h : host E1 St) e s : in_fragment e = true ->
  Waits h e [] s <-> exists X (ev : StuckE E1 X) k, run_tree h (meaning e) s ≈ Vis ev k.
Proof.
  intros Hin. rewrite (waits_iff h e [] s Hin).
  split; intros (X & ev & kk & Hv); exists X, ev, kk; rewrite <- Hv;
    [symmetry |]; rewrite (meaning_fragment e Hin); reflexivity.
Qed.

Corollary meaning_diverges_under_iff {St} (h : host E1 St) e s : in_fragment e = true ->
  ChainDiverges h e [] s <-> Diverges (run_tree h (meaning e) s).
Proof.
  intros Hin. unfold Diverges. rewrite (meaning_fragment e Hin). apply diverges_iff; exact Hin.
Qed.

(** ** With no host: the meaning itself *)

(** The host that answers nothing: every event is a frontier. *)
Definition nobody {E S} : host E S := fun _ _ _ => None.

Lemma ends_run_nobody {E A S} n (t : itree E A) o (s : S) :
  ends n t o -> Ends (run_tree nobody t s) (option_map (fun a => (s, a)) o).
Proof.
  intros H; induction H as [t a Ht | t X e k Ht | n t u o Ht _ IH].
  - rewrite (itree_eta t), Ht, run_ret. exists 0; constructor; reflexivity.
  - rewrite (itree_eta t), Ht, run_vis. apply Ends_vis.
  - rewrite (itree_eta t), Ht, run_tau, tau_eutt. exact IH.
Qed.

Lemma below_spin {E R} (p : program E (option R)) (t : itree E R) :
  below p t -> t ≈ ITree.spin -> p = PRet None.
Proof.
  intros H Hsp. destruct H as [t | r t Ht | X e k t k' Ht _].
  - reflexivity.
  - exfalso. rewrite Ht in Hsp. exact (eutt_Ret_spin_abs _ Hsp).
  - exfalso. rewrite Ht in Hsp. exact (eutt_Vis_spin_abs _ _ Hsp).
Qed.

(** **The meaning diverges exactly when every budget cuts**: [Judgments.Diverges (meaning e)]
    exactly when [denoteRowsB k] is the cut at every [k]. A program that calls a host or a cell
    at all has a node at a large enough budget and is no divergence on either side. *)
Theorem meaning_diverges_iff e : in_fragment e = true ->
  Diverges (meaning e) <-> forall k, denoteB k e [] = PRet None.
Proof.
  intros Hin. unfold Diverges. rewrite (meaning_fragment e Hin). split.
  - intros Hsp k. eapply below_spin; [apply denoteB_below; exact Hin | exact Hsp].
  - intros Hcut. apply no_ends_spin. intros n o Hn.
    pose proof (ends_run_nobody n _ o tt Hn) as Hr.
    destruct (adequacy (St := unit) nobody e [] Hin tt _ Hr) as [k Hk].
    rewrite Hcut in Hk. destruct o; discriminate.
Qed.
