(* The comparison lane's development (rocq/README.md), moved unchanged from the study of
   2026-10-16:
   git:98a29895b800556365a2edc9924f3ed12787b820:docs/research/2026-10-16-itrees/rocq/Api.v.
   The study's README and its other files stay there. *)

(** * Api: write, run, view and edit Eff programs at a budget, with the theorems behind each

    [Budget.v] proves that Lean's budgeted call tree is the budget-[k] truncation of the tree
    meaning; [BudgetDefs.v] extends the tree to definitions, for every program. This file makes
    that a working surface. Every theorem below holds for every program.

    - **Writing** ([Author]): first-order constructors, definitions and calls among them, and a
      scope check for the positional variables.
    - **Running**: hosts as data (the cells, a reply tape, a host function, two routed side by
      side), [run_at k] (the run of the tree at budget [k], with every answered call; Lean's
      tree where [denoteRowsB] has an arm, [run_at_lean]), and
      [settle] (the least budget at which the run is no longer cut). A finish or a wait it reports
      is the meaning's ([run_at_finished], [run_at_waits], [settle_finished]); it reports a
      finish at some limit exactly when the meaning finishes ([settle_complete]); and the
      meaning diverges exactly when no limit settles ([diverges_iff_never_settles]). A limit
      that has not settled is a finite probe and never a divergence.
    - **Viewing**: a run's steps, and [frames n], the runs at budgets [0 .. n]: an animation of
      the chain growing toward the meaning. A frame never takes back a step of the frame before
      it, and a frame that is no longer cut stays as it is ([frames_grow]).
    - **Editing**: one-hole contexts as data, [plug], and [EffEq], equal meanings at every
      environment. Plugging equal programs gives equal programs ([edit_congruence]); Lean's three
      outcomes do not change under such an edit ([edit_keeps_outcomes]). Four laws to edit by. *)

From Stdlib Require Import List ZArith String Bool Lia Arith.
Import ListNotations.
From ITree Require Import ITree ITreeFacts.
From Paco Require Import paco.
Import ITreeNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Judgments E4.Budget E4.BudgetDefs.

Local Open Scope list_scope.

(** ** Writing *)

Module Author.

(** A variable is a position of the environment, counted from its start: a sequence's second
    program sees the first's value at the next position; a loop's test, result and body see the
    cursor there, and its step sees the cursor and then the body's value. *)
Definition var (i : nat) : term := Term_var (Z.of_nat i).
Definition num (n : Z) : term := Term_lit (Lit_nat n).
Definition bool_ (b : bool) : term := Term_lit (Lit_bool b).
Definition text (s : string) : term := Term_lit (Lit_str s).
Definition unit_ : term := Term_lit Lit_unit.

Fixpoint terms_of (ts : list term) : terms :=
  match ts with [] => Terms_nil | t :: rest => Terms_cons t (terms_of rest) end.

(** The atoms [Denote.atom] answers. *)
Definition app (f : string) (ts : list term) : term := Term_app f (terms_of ts).
Definition pair_ (a b : term) : term := app "pair" [a; b].
Definition fst_ (a : term) : term := app "fst" [a].
Definition snd_ (a : term) : term := app "snd" [a].
Definition eq_ (a b : term) : term := app "eq" [a; b].
Definition lt_ (a b : term) : term := app "lt" [a; b].
Definition mul_ (a b : term) : term := app "mul" [a; b].
Definition not_ (a : term) : term := app "not" [a].
Definition and_ (a b : term) : term := app "and" [a; b].

Definition ret (t : term) : eff native_op := Eff_succeed t.
Definition fail (t : term) : eff native_op := Eff_fail t.
Definition sync (t : term) : eff native_op := Eff_sync t.
Definition suspend (b : eff native_op) : eff native_op := Eff_suspend b.
(** [seq a b]: [b] runs with [a]'s value at the next position; a failure of [a] ends both. *)
Definition seq (a b : eff native_op) : eff native_op := Eff_bind a b.
(** [when t a b]: [a] where [t] is [true], [b] where it is [false]. *)
Definition when (t : term) (a b : eff native_op) : eff native_op := Eff_select t Decision_bool a b.
(** [on_option t none some]: [none] at [none]; [some] at [some x], with [x] at the next
    position. *)
Definition on_option (t : term) (none some : eff native_op) : eff native_op :=
  Eff_select t Decision_option none some.
(** [loop init test step result body]: from the cursor [init], while [test] holds run [body]
    and move the cursor to [step]; at a false test end with [result]. *)
Definition loop (init test step result : term) (body : eff native_op) : eff native_op :=
  Eff_iterate None init test step result body.
(** A call of host row [i]. *)
Definition row (i : Z) (request : term) : eff native_op := Eff_perform (NativeOp_external i) request.
Definition cell_new (t : term) : eff native_op := Eff_perform NativeOp_refMake t.
Definition cell_get (c : term) : eff native_op := Eff_perform NativeOp_refGet c.
Definition cell_set (c v : term) : eff native_op := Eff_perform NativeOp_refSet (pair_ c v).

Fixpoint effs_of (es : list (eff native_op)) : effs native_op :=
  match es with [] => Effs_nil | e :: rest => Effs_cons e (effs_of rest) end.

(** [define bodies main]: [main] with the definitions [bodies]; definition [n] is [bodies]'s
    [n]th, and its body sees the request alone, at position 0. *)
Definition define (bodies : list (eff native_op)) (main : eff native_op) : eff native_op :=
  Eff_defs [] (effs_of bodies) main LayerTerms_nil.
(** A call of definition [n] with a request. *)
Definition call (n : Z) (request : term) : eff native_op := Eff_perform (NativeOp_call n) request.
(** An invocation of definition [n], passing programs; each runs at this environment and its
    request, when the body runs [param i]. *)
Definition invoke (n : Z) (request : term) (args : list (eff native_op)) : eff native_op :=
  Eff_invoke n request (effs_of args).
Definition param (i : Z) (request : term) : eff native_op := Eff_perform (NativeOp_param i) request.
(** The context: set it for a program, and read it. *)
Definition with_context (t : term) (b : eff native_op) : eff native_op := Eff_provideContext t b.
Definition context : eff native_op := Eff_withFiber (ActionTerm_context []).

(** **The scope check**: every variable stands below the environment's length where it is read.
    A program that passes reads no variable past its environment. *)
Fixpoint term_scoped (n : nat) (t : term) : bool :=
  match t with
  | Term_var i => (0 <=? i)%Z && (i <? Z.of_nat n)%Z
  | Term_lit _ => true
  | Term_app _ args => terms_scoped n args
  | Term_record _ _ args => terms_scoped n args
  | Term_field _ target _ => term_scoped n target
  | _ => false
  end
with terms_scoped (n : nat) (ts : terms) : bool :=
  match ts with
  | Terms_nil => true
  | Terms_cons t rest => term_scoped n t && terms_scoped n rest
  end.

Fixpoint scoped (n : nat) (e : eff native_op) : bool :=
  match e with
  | Eff_succeed t | Eff_fail t | Eff_sync t => term_scoped n t
  | Eff_perform _ r => term_scoped n r
  | Eff_suspend b => scoped n b
  | Eff_provideContext t b => term_scoped n t && scoped n b
  | Eff_withFiber (ActionTerm_context _) => true
  | Eff_defs _ _ main _ => scoped n main
  (* a passed program runs at this environment and its request *)
  | Eff_invoke _ r args =>
    term_scoped n r && (fix all (es : effs native_op) : bool :=
                          match es with Effs_nil => true | Effs_cons a rest => scoped (S n) a && all rest end) args
  | Eff_bind a b => scoped n a && scoped (S n) b
  | Eff_select t Decision_option a b => term_scoped n t && scoped n a && scoped (S n) b
  | Eff_select t _ a b => term_scoped n t && scoped n a && scoped n b
  | Eff_iterate _ i test step result body =>
    term_scoped n i && term_scoped (S n) test && term_scoped (S (S n)) step &&
    term_scoped (S n) result && scoped (S n) body
  | _ => false
  end.

(** A program in scope: its root at the empty environment, each definition at its request. *)
Definition ready (e : eff native_op) : bool :=
  scoped 0 e && forallb (scoped 1) (bodies_of e).

End Author.

(** ** Hosts as data *)

(** The cells as a host ([Run.h_store]'s answers): always answers. *)
Definition cells_host : host StoreE cells :=
  fun X e s =>
    match e in StoreE X return option (X * cells) with
    | RefMake v => Some (Val_handle 2%Z (Z.of_nat (Stdlib.Lists.List.length s)), s ++ [v])
    | RefGet c =>
      Some (match cell_index c with
            | Some k => match nth_error s k with Some v => v | None => Val_unit end
            | None => Val_unit
            end, s)
    | RefSet c w => Some (Val_unit, match cell_index c with Some k => set_nth s k w | None => s end)
    end.

(** Two hosts side by side, the cells on the left and the rows on the right ([rowsHost]). *)
Definition route {S T} (cs : host StoreE S) (rows : host RowE T) : host E1 (S * T) :=
  fun X e st =>
    match e with
    | inl1 c => match cs X c (fst st) with Some (x, s') => Some (x, (s', snd st)) | None => None end
    | inr1 r => match rows X r (snd st) with Some (x, t') => Some (x, (fst st, t')) | None => None end
    end.

(** A reply tape ([tapeHandler]): each call takes the next exit; an empty tape leaves it
    waiting. *)
Definition tape : host RowE (list exitv) :=
  fun X e t =>
    match e in RowE X return option (X * list exitv) with
    | Row _ _ => match t with a :: rest => Some (a, rest) | [] => None end
    end.

(** A host function, in [Extract.host]'s shape. *)
Definition fn_host {S} (f : int -> val_ -> S -> option (exitv * S)) : host RowE S :=
  fun X e s => match e in RowE X return option (X * S) with Row i v => f i v s end.

(** The cells, and the rows by a tape: the host of the recorded runs. *)
Definition tape_run : host E1 (cells * list exitv) := route cells_host tape.

(** ** Running and viewing *)

(** One answered event of a run. *)
Inductive step : Set :=
| Called (row : int) (request : val_) (answer : exitv)
| Celled (op : string) (arg : val_) (answer : val_).

(** How a run stops: finished, cut by the budget, waiting on a row, or a cell event refused. *)
Inductive stop : Set :=
| Finished (ex : exitv)
| Cut
| Waiting (row : int) (request : val_)
| Refused (op : string) (arg : val_).

Definition step_of {X} (e : E1 X) : X -> step :=
  match e with
  | inl1 c =>
    match c in StoreE X return X -> step with
    | RefMake v => fun x => Celled "make" v x
    | RefGet c => fun x => Celled "get" c x
    | RefSet c w => fun x => Celled "set" (Val_list [c; w]) x
    end
  | inr1 r => match r in RowE X return X -> step with Row i v => fun x => Called i v x end
  end.

Definition stop_of {X} (e : E1 X) : stop :=
  match e with
  | inl1 c =>
    match c with
    | RefMake v => Refused "make" v
    | RefGet c => Refused "get" c
    | RefSet c w => Refused "set" (Val_list [c; w])
    end
  | inr1 r => match r with Row i v => Waiting i v end
  end.

(** **The run of a finite tree, with its steps** ([observeRows], [runRowsO]). *)
Fixpoint trace {St} (h : host E1 St) (p : program E1 (option exitv)) (s : St)
    : list step * stop * St :=
  match p with
  | PRet None => ([], Cut, s)
  | PRet (Some ex) => ([], Finished ex, s)
  | PVis e k =>
    match h _ e s with
    | Some (x, s') =>
      match trace h (k x) s' with (steps, st, s'') => (step_of e x :: steps, st, s'') end
    | None => ([], stop_of e, s)
    end
  end.

Definition steps_of {St} (r : list step * stop * St) : list step := fst (fst r).
Definition stop_at {St} (r : list step * stop * St) : stop := snd (fst r).

(** What [crun] sees of a run: a wait forgets where it waits ([observeRows_project]). *)
Definition project {St} (r : list step * stop * St) : option (option exitv * St) :=
  match r with
  | (_, Finished ex, s) => Some (Some ex, s)
  | (_, Cut, s) => Some (None, s)
  | (_, Waiting _ _, _) | (_, Refused _ _, _) => None
  end.

Lemma trace_project {St} (h : host E1 St) p s : project (trace h p s) = crun h p s.
Proof.
  revert s; induction p as [[ex |] | X e k IH]; intros s; cbn; [reflexivity | reflexivity |].
  destruct (h X e s) as [[x s'] |].
  - rewrite <- IH. destruct (trace h (k x) s') as [[steps st] s'']. destruct st; reflexivity.
  - destruct e as [c | r]; [destruct c | destruct r]; reflexivity.
Qed.

(** **The run at budget [k]**: Lean's tree [denoteRowsB k] under the host. *)
Definition run_at {St} (k : nat) (h : host E1 St) (e : eff native_op) (s : St) : list step * stop * St :=
  trace h (denoteBD k e) s.

Definition is_wait (st : stop) : bool :=
  match st with Waiting _ _ | Refused _ _ => true | _ => false end.

(** **A reported finish is the meaning's.** *)
Theorem run_at_finished {St} (h : host E1 St) k e s steps ex s' :
  run_at k h e s = (steps, Finished ex, s') -> run_tree h (meaning e) s ≈ Ret (s', ex).
Proof.
  intros Hr. apply finishesD_iff. exists k.
  rewrite <- trace_project. unfold run_at in Hr. rewrite Hr. reflexivity.
Qed.

(** **A reported wait is a frontier of the meaning's run.** *)
Theorem run_at_waits {St} (h : host E1 St) k e s steps st s' :
  run_at k h e s = (steps, st, s') -> is_wait st = true ->
  exists X (ev : StuckE E1 X) kk, run_tree h (meaning e) s ≈ Vis ev kk.
Proof.
  intros Hr Hw. apply waitsD_iff. exists k.
  rewrite <- trace_project. unfold run_at in Hr. rewrite Hr. destruct st; try discriminate; reflexivity.
Qed.

(** A run of a tree below another is cut where they differ, after a prefix of the other's
    steps; elsewhere it is the other's run. *)
Lemma trace_approx {St} (h : host E1 St) (p q : program E1 (option exitv)) s :
  approx p q ->
  trace h p s = trace h q s \/
  exists steps s1, trace h p s = (steps, Cut, s1) /\ exists rest, steps_of (trace h q s) = steps ++ rest.
Proof.
  intros H; revert s; induction H as [q | r | X e k k' _ IH]; intros s.
  - right. exists [], s. split; [reflexivity | exists (steps_of (trace h q s)); reflexivity].
  - left; reflexivity.
  - cbn. destruct (h X e s) as [[x s'] |]; [| left; reflexivity].
    destruct (IH x s') as [Heq | (steps & s1 & Hp & rest & Hq)].
    + left. rewrite Heq. reflexivity.
    + right. rewrite Hp. exists (step_of e x :: steps), s1. split; [reflexivity |].
      exists rest. unfold steps_of in *. destruct (trace h (k' x) s') as [[sq stq] sq']. cbn in *.
      rewrite Hq. reflexivity.
Qed.

(** **A larger budget takes back no step**: the run at [k] is cut after a prefix of the run at
    [k'], or is the run at [k']. *)
Theorem run_at_grows {St} (h : host E1 St) k k' e s : k <= k' ->
  run_at k h e s = run_at k' h e s \/
  exists steps s1, run_at k h e s = (steps, Cut, s1) /\
                   exists rest, steps_of (run_at k' h e s) = steps ++ rest.
Proof. intros Hk. apply trace_approx, denoteBD_approx; exact Hk. Qed.

(** Same trees, same run with the same steps. *)
Lemma same_trace {St} (h : host E1 St) (p q : program E1 (option exitv)) s : same p q -> trace h p s = trace h q s.
Proof.
  intros H; revert s; induction H as [r | X e k k' _ IH]; intros s; cbn; [reflexivity |].
  destruct (h X e s) as [[x s'] |]; [rewrite IH; reflexivity | reflexivity].
Qed.

(** **Where [denoteRowsB] has an arm, the run is the run of Lean's tree**, step for step. *)
Theorem run_at_lean {St} (h : host E1 St) k e s : in_fragment e = true ->
  run_at k h e s = trace h (denoteB k e []) s.
Proof. intros Hin. apply same_trace, denoteBD_same; exact Hin. Qed.

(** **[settle limit]**: the least budget up to [limit] whose run is not cut, and that run. *)
Fixpoint settle {St} (limit : nat) (h : host E1 St) (e : eff native_op) (s : St)
    : option (nat * (list step * stop * St)) :=
  match limit with
  | O => match stop_at (run_at 0 h e s) with Cut => None | _ => Some (0, run_at 0 h e s) end
  | S l =>
    match settle l h e s with
    | Some r => Some r
    | None => match stop_at (run_at (S l) h e s) with Cut => None | _ => Some (S l, run_at (S l) h e s) end
    end
  end.

Lemma settle_some {St} (h : host E1 St) e s : forall limit k r,
  settle limit h e s = Some (k, r) -> k <= limit /\ r = run_at k h e s /\ stop_at r <> Cut.
Proof.
  induction limit as [| l IH]; intros k r Hs; cbn [settle] in Hs.
  - destruct (stop_at (run_at 0 h e s)) eqn:Hst; inversion Hs; subst;
      (split; [lia | split; [reflexivity | rewrite Hst; discriminate]]).
  - destruct (settle l h e s) as [[k0 r0] |] eqn:Hl.
    + inversion Hs; subst. destruct (IH k r eq_refl) as (Hk & Hr & Hc). split; [lia | auto].
    + destruct (stop_at (run_at (S l) h e s)) eqn:Hst; inversion Hs; subst;
        (split; [lia | split; [reflexivity | rewrite Hst; discriminate]]).
Qed.

Lemma settle_none {St} (h : host E1 St) e s : forall limit,
  settle limit h e s = None <-> forall k, k <= limit -> stop_at (run_at k h e s) = Cut.
Proof.
  induction limit as [| l IH]; cbn [settle].
  - split.
    + intros Hs k Hk. assert (k = 0) by lia; subst.
      destruct (stop_at (run_at 0 h e s)); congruence.
    + intros Hall. rewrite (Hall 0 (le_n 0)). reflexivity.
  - split.
    + intros Hs k Hk. destruct (settle l h e s) eqn:Hl; [discriminate |].
      destruct (Nat.eq_dec k (S l)) as [-> | Hne].
      * destruct (stop_at (run_at (S l) h e s)); congruence.
      * apply IH; [reflexivity | lia].
    + intros Hall. rewrite (proj2 IH (fun k Hk => Hall k ltac:(lia))).
      rewrite (Hall (S l) (le_n _)). reflexivity.
Qed.

(** **A settled finish is the meaning's.** *)
Theorem settle_finished {St} (h : host E1 St) limit e s k steps ex s' :
  settle limit h e s = Some (k, (steps, Finished ex, s')) -> run_tree h (meaning e) s ≈ Ret (s', ex).
Proof.
  intros Hs. destruct (settle_some h e s limit k _ Hs) as (_ & Hr & _).
  apply (run_at_finished h k e s steps); symmetry; exact Hr.
Qed.

(** **Complete for finishes**: where the meaning finishes, some limit settles on that finish. *)
Theorem settle_complete {St} (h : host E1 St) e s ex s' :
  run_tree h (meaning e) s ≈ Ret (s', ex) ->
  exists limit k steps, settle limit h e s = Some (k, (steps, Finished ex, s')).
Proof.
  intros Hm. apply finishesD_iff in Hm as [k Hk].
  exists k. destruct (settle k h e s) as [[k0 r] |] eqn:Hs.
  - destruct (settle_some h e s k k0 r Hs) as (Hk0 & Hr & Hc). subst r.
    (* the first budget that is not cut is a finish, the same finish *)
    destruct (run_at_grows h k0 k e s Hk0) as [Heq | (steps & s1 & Hcut & _)];
      [| unfold stop_at in Hc; rewrite Hcut in Hc; contradiction].
    assert (Hp : project (run_at k h e s) = Some (Some ex, s')) by (unfold run_at; rewrite trace_project; exact Hk).
    rewrite <- Heq in Hp. exists k0. destruct (run_at k0 h e s) as [[steps st] s2].
    destruct st; inversion Hp; subst. exists steps. reflexivity.
  - exfalso. apply settle_none with (k := k) in Hs; [| lia].
    assert (Hp : project (run_at k h e s) = Some (Some ex, s')) by (unfold run_at; rewrite trace_project; exact Hk).
    unfold stop_at in Hs. destruct (run_at k h e s) as [[steps st] s2]. cbn in Hs. subst st. discriminate.
Qed.

(** **Divergence is never settling**: the meaning's run diverges exactly when no limit settles.
    One limit that has not settled shows nothing of divergence. *)
Theorem diverges_iff_never_settles {St} (h : host E1 St) e s :
  Diverges (run_tree h (meaning e) s) <-> forall limit, settle limit h e s = None.
Proof.
  rewrite <- divergesD_iff. unfold ChainDivergesD. split.
  - intros Hd limit. apply settle_none. intros k _. destruct (Hd k) as [s' Hs'].
    rewrite <- trace_project in Hs'. unfold stop_at, run_at.
    destruct (trace h (denoteBD k e) s) as [[steps st] s2]. destruct st; inversion Hs'; reflexivity.
  - intros Hn k. pose proof (proj1 (settle_none h e s k) (Hn k) k (le_n _)) as Hc.
    exists (snd (run_at k h e s)). rewrite <- trace_project. unfold stop_at, run_at in *.
    destruct (trace h (denoteBD k e) s) as [[steps st] s2]. cbn in Hc. subst st. reflexivity.
Qed.

(** **Frames**: the runs at budgets [0 .. n], each with its budget. *)
Definition frames {St} (n : nat) (h : host E1 St) (e : eff native_op) (s : St)
    : list (nat * (list step * stop * St)) :=
  map (fun k => (k, run_at k h e s)) (List.seq 0 (S n)).

(** **An animation never takes a step back**: each frame is the next one, or is cut after a prefix
    of the next one's steps. *)
Theorem frames_grow {St} (h : host E1 St) n e s k :
  k < n ->
  run_at k h e s = run_at (S k) h e s \/
  exists steps s1, run_at k h e s = (steps, Cut, s1) /\
                   exists rest, steps_of (run_at (S k) h e s) = steps ++ rest.
Proof. intros _. apply run_at_grows; lia. Qed.

(** ** Editing *)

(** One-hole contexts of the fragment, as data. *)
Inductive hole : Set :=
| Here
| InSuspend (h : hole)
| InSeqFirst (h : hole) (b : eff native_op)
| InSeqRest (a : eff native_op) (h : hole)
| InWhenTrue (t : term) (d : decision) (h : hole) (b : eff native_op)
| InWhenFalse (t : term) (d : decision) (a : eff native_op) (h : hole)
| InLoopBody (c : option ty) (init test step result : term) (h : hole).

Fixpoint plug (h : hole) (x : eff native_op) : eff native_op :=
  match h with
  | Here => x
  | InSuspend h => Eff_suspend (plug h x)
  | InSeqFirst h b => Eff_bind (plug h x) b
  | InSeqRest a h => Eff_bind a (plug h x)
  | InWhenTrue t d h b => Eff_select t d (plug h x) b
  | InWhenFalse t d a h => Eff_select t d a (plug h x)
  | InLoopBody c i t s r h => Eff_iterate c i t s r (plug h x)
  end.

(** The subprogram at a hole's place, if the program has that shape there. *)
Fixpoint at_hole (h : hole) (e : eff native_op) : option (eff native_op) :=
  match h, e with
  | Here, _ => Some e
  | InSuspend h, Eff_suspend b => at_hole h b
  | InSeqFirst h _, Eff_bind a _ => at_hole h a
  | InSeqRest _ h, Eff_bind _ b => at_hole h b
  | InWhenTrue _ _ h _, Eff_select _ _ a _ => at_hole h a
  | InWhenFalse _ _ _ h, Eff_select _ _ _ b => at_hole h b
  | InLoopBody _ _ _ _ _ h, Eff_iterate _ _ _ _ _ body => at_hole h body
  | _, _ => None
  end.

(** **Equal meanings at every environment.** *)
Definition EffEq (a b : eff native_op) : Prop := forall env, denoteF a env ≈ denoteF b env.

Lemma eutt_iter_loop (f g : list val_ -> itree E1 exitv) (hfg : forall env, f env ≈ g env) env test step result c :
  ITree.iter (loop_stepF f env test step result) c ≈ ITree.iter (loop_stepF g env test step result) c.
Proof.
  apply (eutt_iter' eq eq); [| reflexivity].
  intros c' ? <-. unfold loop_stepF.
  destruct (eval_term (env ++ [c']) test) as [[] |]; try (apply eqit_Ret; constructor; reflexivity).
  destruct b; [| apply eqit_Ret; constructor; reflexivity].
  apply eutt_clo_bind with (UU := eq); [apply hfg |]; intros x ? <-.
  destruct x; [destruct (eval_term (env ++ [c'; v]) step) |]; apply eqit_Ret; constructor; reflexivity.
Qed.

(** **An edit by equal programs gives equal programs.** *)
Theorem edit_congruence (h : hole) a b : EffEq a b -> EffEq (plug h a) (plug h b).
Proof.
  intros Hab; induction h; intros env; cbn; auto.
  - unfold seqF. apply eutt_clo_bind with (UU := eq); [apply IHh |]; intros x ? <-. reflexivity.
  - unfold seqF. apply eutt_clo_bind with (UU := eq); [reflexivity |]; intros x ? <-.
    destruct x; [apply IHh | reflexivity].
  - destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |]; try reflexivity; apply IHh.
  - destruct (option_map (decide d) (eval_term env t)) as [[[[] bound] |] |]; try reflexivity; apply IHh.
  - destruct (eval_term env init) as [c0 |]; [| reflexivity]. apply eutt_iter_loop; exact IHh.
Qed.

(** **An edit by equal programs keeps Lean's three outcomes**, under every host. *)
Theorem edit_keeps_outcomes {St} (hst : host E1 St) a b env s : in_fragment a = true -> in_fragment b = true ->
  EffEq a b ->
  (forall r s', Finishes hst a env s r s' <-> Finishes hst b env s r s') /\
  (Waits hst a env s <-> Waits hst b env s) /\
  (ChainDiverges hst a env s <-> ChainDiverges hst b env s).
Proof.
  intros Ha Hb Hab. assert (Hr : run_tree hst (denoteF a env) s ≈ run_tree hst (denoteF b env) s)
    by (rewrite (Hab env); reflexivity).
  split; [| split].
  - intros r s'. rewrite (finishes_iff hst a env s r s' Ha), (finishes_iff hst b env s r s' Hb), Hr. reflexivity.
  - rewrite (waits_iff hst a env s Ha), (waits_iff hst b env s Hb).
    split; intros (X & ev & kk & Hv); exists X, ev, kk; [rewrite <- Hr | rewrite Hr]; exact Hv.
  - rewrite (diverges_iff hst a env s Ha), (diverges_iff hst b env s Hb). unfold Diverges. rewrite Hr. reflexivity.
Qed.

(** *** Laws to edit by *)

Lemma suspend_law a : EffEq (Eff_suspend a) a.
Proof. intros env; reflexivity. Qed.

Lemma when_true_law a b : EffEq (Author.when (Author.bool_ true) a b) a.
Proof. intros env; cbn. rewrite app_nil_r. reflexivity. Qed.

Lemma when_false_law a b : EffEq (Author.when (Author.bool_ false) a b) b.
Proof. intros env; cbn. rewrite app_nil_r. reflexivity. Qed.

(** A failure ends a sequence: the rest never runs. *)
Lemma seq_fail_law t b : EffEq (Author.seq (Author.fail t) b) (Author.fail t).
Proof.
  intros env; cbn. unfold seqF. rewrite bind_ret_l.
  destruct (eval_term env t); reflexivity.
Qed.
