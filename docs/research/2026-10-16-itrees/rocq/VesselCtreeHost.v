(** * VesselCtreeHost: the FMI specification host and a mock host, as choice trees

    The hosts and the one-event refinement of [VesselCtree.v], in a file checked with universe
    checking on. It imports only [CTree] and [Eq], which load consistently. The lift to every
    program ([VesselCtree.mock_refines_spec]) needs [Interp.FoldStateT], which does not load
    with universe checking on (the receipt's control), so it lives in its own file.

    The protocol is small and physical: the sampled minimum and maximum bracket the initial
    level, because the first sample is the initial state ([validate_fmi_reply] checks the initial
    sample, [apps/vessel/fmi/]). The mock computes the final level by a mass balance.

    Built in the opam switch [ctree] (Coq 8.20.1, coq-ctree 2.0, coq-itree 5.2.1). *)

Unset Universe Minimization ToSet.

From Coq Require Import NArith String.
From ITree Require Import Basics.Basics Indexed.Sum.
From CTree Require Import CTree Eq.
Require Import E4.VesselTypes.

Local Open Scope N_scope.

(** An internal choice of any element of a type. *)
Variant chooseB : Type -> Type :=
| Choose (X : Type) : chooseB X.

Notation VE := (GeometryE +' SimulationE).

(** The FMI protocol: the sampled extremes bracket the initial level. *)
Definition sim_protocol {s} (r : request s) (m : simulation_reply s) : Prop :=
  (level_mm (minimum_observed m) <= level_mm (initial_level r) <=
   level_mm (maximum_observed m))%N.

(** A STEP host, deterministic: a function of the study and the request. *)
Definition step_host : Type := forall s, request s -> tool_result (geometry_reply s).

(** **The specification host**: the STEP host answers; the FMI host answers any admissible reply
    for the study, or fails with any message. *)
Definition spec_host (geo : step_host) : VE ~> ctree void1 chooseB :=
  fun T e =>
    match e with
    | inl1 g => match g in GeometryE T return ctree void1 chooseB T with
                | Exchange s r => Ret (geo s r)
                end
    | inr1 m => match m in SimulationE T return ctree void1 chooseB T with
                | Simulate s r =>
                  Br (Choose (string + {x : simulation_reply s | sim_protocol r x}))
                    (fun c => Ret (match c with
                                   | inl message => ToolFailure message
                                   | inr x => Answered (proj1_sig x)
                                   end))
                end
    end.

(** The mock's level: the tank's cross-section by [π/4 ≈ 785/1000], the net flow over the run,
    clamped at the bottom; [1 µL = 1 mm³]. *)
Definition area_mm2 {s} (r : request s) : N :=
  N.max 1 (magnitude (diameter r) * magnitude (diameter r) * 785 / 1000).

Definition final_level {s} (r : request s) : N :=
  let inflow := magnitude (inlet r) * magnitude (duration r) in
  let outflow := magnitude (outlet r) * magnitude (duration r) in
  (level_mm (initial_level r) * area_mm2 r + inflow - outflow) / area_mm2 r.

(** The mock's reply: the extremes of the initial and final levels, with its own evidence. *)
Definition mock_reply {s} (r : request s) : simulation_reply s :=
  SimulationReply
    (Level (N.min (level_mm (initial_level r)) (final_level r)))
    (Level (N.max (level_mm (initial_level r)) (final_level r)))
    (Evidence "mock mass balance" "1" "mock").

Lemma mock_meets {s} (r : request s) : sim_protocol r (mock_reply r).
Proof. unfold sim_protocol, mock_reply; cbn. split; [apply N.le_min_l | apply N.le_max_l]. Qed.

(** **The mock host**: the same STEP host, and the mock's one reply. *)
Definition mock_host (geo : step_host) : VE ~> ctree void1 chooseB :=
  fun T e =>
    match e with
    | inl1 g => match g in GeometryE T return ctree void1 chooseB T with
                | Exchange s r => Ret (geo s r)
                end
    | inr1 m => match m in SimulationE T return ctree void1 chooseB T with
                | Simulate s r => Ret (Answered (mock_reply r))
                end
    end.

(** Event by event, the mock's answer is one of the specification's. *)
Lemma mock_answers_within_spec (geo : step_host) {Z} (e : VE Z) :
  mock_host geo _ e (≲update_val_rel eq (@eq Z)) spec_host geo _ e.
Proof.
  destruct e as [g | m].
  - destruct g as [s r]; cbn. apply ssim_ret. constructor. reflexivity.
  - destruct m as [s r]; cbn.
    apply ssim_br_r with (x := inr (exist _ (mock_reply r) (mock_meets r))).
    apply ssim_ret. constructor. reflexivity.
Qed.

