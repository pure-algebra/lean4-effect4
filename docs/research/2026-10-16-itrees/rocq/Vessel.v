(** * Vessel: the vessel workflow as an interaction tree over typed services

    [assess] is [Workflow.lean]'s [assess] over the typed events of [VesselTypes]: one call to the
    STEP service, the capacity check, one call to the FMI service, the two level checks. Its
    study checks are gone, because each reply's type is for the request's study.

    Two theorems, each for every host:
    - [assess_sound_every_host] and [assess_sound_every_stateful_host]: under any host, an
      accepted verdict holds up its duty ([required ≤ usable]) and keeps its sampled maximum
      within the working limit, and its evidence is for its study by type. A replay checks this
      of recorded runs; this states it of every run of every host, at the model.
    - [study_checks_never_fire]: the untyped workflow, with its run-time study checks
      ([assess_raw], as [Workflow.lean] writes it), under any host that is the erasure of a typed
      host, is up to [eutt] the typed workflow's verdict erased. So for such a host the checks
      never fire. They still refuse a foreign host's reply for another study ([raw_refuses]).

    What this does not establish: that the Eff program [Workflow.body] is this tree. That link is
    finite: [VesselCheck.v] runs the Eff program's meaning on six saved native runs. *)

(* An event family's index universe stays above Set, as [interp] needs. *)
Unset Universe Minimization ToSet.

From Coq Require Import NArith String Bool Lia.
From ITree Require Import ITree ITreeFacts Props.Leaf Basics.Basics Events.State.
Import ITreeNotations LeafNotations Basics.Basics.Monads.
Require Import E4.VesselTypes.

Local Open Scope string_scope.
Local Open Scope itree_scope.

(** The two services, as one signature. *)
Notation VE := (GeometryE +' SimulationE).

(** ** The typed workflow *)

Definition assess (s : study) (r : request s) : itree VE (verdict s) :=
  g <- trigger (Exchange s r) ;;
  match g with
  | ToolFailure msg => Ret (Failed msg)
  | Answered g =>
    if negb (holds_up r g) then Ret (Refused BelowHoldUp)
    else
      m <- trigger (Simulate s r) ;;
      match m with
      | ToolFailure msg => Ret (Failed msg)
      | Answered m => Ret (judge r g m)
      end
  end.

(** What an accepted verdict must satisfy. Its evidence is for [s] by its type. *)
Definition sound_verdict {s} (r : request s) (v : verdict s) : Prop :=
  match v with
  | Accepted a =>
    required a = inventory (flow r) (hold_up r) /\
    (magnitude (required a) <= magnitude (usable a))%N /\
    (level_mm (maximum_seen a) <= level_mm (maximum_level r))%N
  | _ => True
  end.

Lemma judge_sound {s} (r : request s) g m :
  holds_up r g = true -> sound_verdict r (judge r g m).
Proof.
  unfold judge, holds_up, above_minimum, below_maximum, sound_verdict, assessment_of; cbn.
  intros Hcap.
  destruct (N.ltb (level_mm (minimum_observed m)) (level_mm (minimum_level r))) eqn:Hmin;
    cbn; [exact I |].
  destruct (N.ltb (level_mm (maximum_level r)) (level_mm (maximum_observed m))) eqn:Hmax;
    cbn; [exact I |].
  apply Bool.negb_true_iff, N.ltb_ge in Hcap.
  apply N.ltb_ge in Hmax.
  repeat split; auto.
Qed.

(** Every value the workflow can end with satisfies [sound_verdict], whatever the replies. *)
Lemma assess_leaves (s : study) (r : request s) (v : verdict s) :
  v ∈ assess s r -> sound_verdict r v.
Proof.
  unfold assess. intros Hv.
  apply Leaf_bind_inv in Hv as [g [_ Hg]].
  destruct g as [g | msg].
  - destruct (negb (holds_up r g)) eqn:Hcap.
    + apply Leaf_Ret_inv in Hg. subst. exact I.
    + apply Leaf_bind_inv in Hg as [m [_ Hm]].
      destruct m as [m | msg].
      * apply Leaf_Ret_inv in Hm. subst.
        apply judge_sound. now apply Bool.negb_false_iff.
      * apply Leaf_Ret_inv in Hm. subst. exact I.
  - apply Leaf_Ret_inv in Hg. subst. exact I.
Qed.

(** **Every host**: whatever answers the two services, every verdict the run can end with is
    sound. *)
Theorem assess_sound_every_host {F} (h : VE ~> itree F) (s : study) (r : request s) v :
  v ∈ interp h (assess s r) -> sound_verdict r v.
Proof. intros Hv. apply assess_leaves. exact (Leaf_interp_inv h _ _ Hv). Qed.

(** The same for a host with a state of its own: a mock, a cache, a recording host. *)
Theorem assess_sound_every_stateful_host {F S} (h : VE ~> stateT S (itree F))
    (s : study) (r : request s) (st : S) x :
  x ∈ interp_state h (assess s r) st -> sound_verdict r (snd x).
Proof. intros Hx. apply assess_leaves. exact (Leaf_interp_state_inv h _ st x Hx). Qed.

(** ** The untyped workflow, with its run-time study checks *)

(** A reply as the Eff workflow sees it: a record whose study fields are data. *)
Record raw_geometry : Set := RawGeometry {
  g_vessel : string; g_revision : positive; g_digest : string;
  g_capacity : N; g_artifact : string; g_passed : bool }.

Record raw_simulation : Set := RawSimulation {
  m_vessel : string; m_revision : positive; m_digest : string;
  m_minimum : N; m_maximum : N; m_artifact : string; m_passed : bool }.

(** The untyped services: the request still names its study, the reply only claims one. *)
Variant RawE : Type -> Type :=
| RawExchange (s : study) (r : request s) : RawE (tool_result raw_geometry)
| RawSimulate (s : study) (r : request s) : RawE (tool_result raw_simulation).

Inductive raw_verdict : Set :=
| RawAccepted (required usable maximum : N) (step_artifact simulation_artifact : string)
| RawRefused (message : string)
| RawFailed (message : string).

(** [sameStudy] of [Workflow.lean]: vessel, revision and input digest. *)
Definition same_geometry (s : study) (g : raw_geometry) : bool :=
  String.eqb (vessel_id (design_of s)) (g_vessel g) &&
  Pos.eqb (revision (design_of s)) (g_revision g) && String.eqb (input_digest s) (g_digest g).

Definition same_simulation (s : study) (m : raw_simulation) : bool :=
  String.eqb (vessel_id (design_of s)) (m_vessel m) &&
  Pos.eqb (revision (design_of s)) (m_revision m) && String.eqb (input_digest s) (m_digest m).

(** [Workflow.lean]'s [assess], with each [require] in order and its message. *)
Definition assess_raw (s : study) (r : request s) : itree RawE raw_verdict :=
  g <- trigger (RawExchange s r) ;;
  match g with
  | ToolFailure msg => Ret (RawFailed msg)
  | Answered g =>
    if negb (same_geometry s g) then Ret (RawRefused "geometry belongs to another study")
    else if negb (g_passed g) then Ret (RawRefused "STEP observations do not agree")
    else if N.ltb (g_capacity g) (magnitude (inventory (flow r) (hold_up r))) then
      Ret (RawRefused "usable capacity is below the hold-up requirement")
    else
      m <- trigger (RawSimulate s r) ;;
      match m with
      | ToolFailure msg => Ret (RawFailed msg)
      | Answered m =>
        if negb (same_simulation s m) then Ret (RawRefused "simulation belongs to another study")
        else if negb (m_passed m) then Ret (RawRefused "simulation did not finish successfully")
        else if N.ltb (m_minimum m) (level_mm (minimum_level r)) then
          Ret (RawRefused "sampled level falls below the working limit")
        else if N.ltb (level_mm (maximum_level r)) (m_maximum m) then
          Ret (RawRefused "sampled level exceeds the working limit")
        else
          Ret (RawAccepted (magnitude (inventory (flow r) (hold_up r))) (g_capacity g)
                 (m_maximum m) (g_artifact g) (m_artifact m))
      end
  end.

(** ** Erasure: a typed host seen by the untyped workflow *)

Definition erase_geometry (s : study) (g : geometry_reply s) : raw_geometry :=
  RawGeometry (vessel_id (design_of s)) (revision (design_of s)) (input_digest s)
    (magnitude (capacity g)) (artifact (step_evidence g)) true.

Definition erase_simulation (s : study) (m : simulation_reply s) : raw_simulation :=
  RawSimulation (vessel_id (design_of s)) (revision (design_of s)) (input_digest s)
    (level_mm (minimum_observed m)) (level_mm (maximum_observed m))
    (artifact (simulation_evidence m)) true.

Definition erase_result {A B : Set} (f : A -> B) (x : tool_result A) : tool_result B :=
  match x with Answered a => Answered (f a) | ToolFailure m => ToolFailure m end.

(** **A typed host's erasure**: it answers the untyped services through the typed host, and
    writes its own study's fields into each reply. *)
Definition erase_host {F} (h : VE ~> itree F) : RawE ~> itree F :=
  fun T e =>
    match e in RawE T return itree F T with
    | RawExchange s r => ITree.map (erase_result (erase_geometry s)) (h _ (inl1 (Exchange s r)))
    | RawSimulate s r => ITree.map (erase_result (erase_simulation s)) (h _ (inr1 (Simulate s r)))
    end.

Definition erase_verdict {s} (v : verdict s) : raw_verdict :=
  match v with
  | Accepted a =>
    RawAccepted (magnitude (required a)) (magnitude (usable a)) (level_mm (maximum_seen a))
      (artifact (step_of a)) (artifact (simulation_of a))
  | Refused BelowHoldUp => RawRefused "usable capacity is below the hold-up requirement"
  | Refused BelowWorkingLimit => RawRefused "sampled level falls below the working limit"
  | Refused AboveWorkingLimit => RawRefused "sampled level exceeds the working limit"
  | Failed m => RawFailed m
  end.

Lemma same_geometry_erased s g : same_geometry s (erase_geometry s g) = true.
Proof. unfold same_geometry; cbn. now rewrite !String.eqb_refl, Pos.eqb_refl. Qed.

Lemma same_simulation_erased s m : same_simulation s (erase_simulation s m) = true.
Proof. unfold same_simulation; cbn. now rewrite !String.eqb_refl, Pos.eqb_refl. Qed.

(** **The study checks never fire for a typed host**: under the erasure of any typed host, the
    untyped workflow's run is, up to [eutt], the typed workflow's run with its verdict erased. *)
Theorem study_checks_never_fire {F} (h : VE ~> itree F) (s : study) (r : request s) :
  interp (erase_host h) (assess_raw s r) ≈ ITree.map erase_verdict (interp h (assess s r)).
Proof.
  unfold assess_raw, assess.
  rewrite interp_bind, interp_trigger, interp_bind, interp_trigger, map_bind.
  cbn. unfold ITree.map at 1. rewrite bind_bind.
  apply eutt_eq_bind. intros [g | msg]; cbn; rewrite bind_ret_l.
  - rewrite same_geometry_erased; cbn.
    unfold holds_up; cbn.
    destruct (N.ltb (magnitude (capacity g)) (magnitude (flow r) * magnitude (hold_up r))); cbn.
    + rewrite !interp_ret, map_ret. reflexivity.
    + rewrite interp_bind, interp_trigger, interp_bind, interp_trigger, map_bind.
      cbn. unfold ITree.map at 1. rewrite bind_bind.
      apply eutt_eq_bind. intros [m | msg']; cbn; rewrite bind_ret_l.
      * rewrite same_simulation_erased; cbn.
        unfold judge, above_minimum, below_maximum; cbn.
        destruct (N.ltb (level_mm (minimum_observed m)) (level_mm (minimum_level r))); cbn;
          [rewrite !interp_ret, map_ret; reflexivity |].
        destruct (N.ltb (level_mm (maximum_level r)) (level_mm (maximum_observed m))); cbn;
          rewrite !interp_ret, map_ret; reflexivity.
      * rewrite !interp_ret, map_ret. reflexivity.
  - rewrite !interp_ret, map_ret. reflexivity.
Qed.

(** The checks still refuse a foreign host: a geometry reply for another study is refused,
    whatever it carries. *)
Theorem raw_refuses {F} (h : RawE ~> itree F) (s : study) (r : request s) g :
  same_geometry s g = false ->
  h _ (RawExchange s r) ≈ Ret (Answered g) ->
  interp h (assess_raw s r) ≈ Ret (RawRefused "geometry belongs to another study").
Proof.
  intros Hother Hh.
  unfold assess_raw.
  rewrite interp_bind, interp_trigger, Hh, bind_ret_l; cbn.
  rewrite Hother; cbn.
  now rewrite interp_ret.
Qed.
