(** * VesselCheck: the meaning's calls are the saved native runs, on the vessel

    [Vessel_fixture] holds six runs of the vessel's [assess] workflow against the real hosts:
    OCCT for the STEP assembly and an OpenModelica FMU through FMI. They are the six runs that
    Lean's [apps/vessel/check_replay.lean] replays through [Api.replayChecked] (branch
    [codex/vessel-dogfood], [apps/vessel/evidence/replay-check.log]): three accepted, two refused
    by the workflow's own checks, one failed by the FMI host. Each run holds the closed program,
    each reply with the request it answered, and the root's exit. The module is generated from
    the runs' [replay.json] ([gen/vessel_to_ml.py], then rocq-of-ocaml), and its values read back
    exactly ([gen/check_vessel.ml]).

    The check: under the run's replies as a tape, the meaning calls the geometry row (0) and then
    the simulation row (1) with the recorded requests, uses every reply, and ends with the
    recorded exit. The two refused runs end with a failure the program raises ([fail]), so they
    check the failure's encoding ([Denote.fail_exit]) too. Finite checks by [vm_compute]. *)

From Stdlib Require Import List ZArith.
Import ListNotations.
From ITree Require Import ITree.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run.
Require E4.Vessel_fixture.

Module F := E4.Vessel_fixture.

(** A reply or an exit of a saved run, as an exit of the meaning: a tagged failure is
    [Cause.fail (.tagged tag message)], as [check_replay.lean] reads it. *)
Definition exit_of (o : F.outcome) : exitv :=
  match o with
  | F.Succeeded v => Success v
  | F.Failed tag message => fail_exit (Val_list [Val_str tag; Val_str message])
  end.

(** What the meaning shows under a run's replies: each call's row and request, the root's exit
    image, and whether every reply was used. *)
Definition observation (p : eff native_op) (replies : list F.outcome)
    : outcome (list (int * val_) * val_ * bool) :=
  match observe_n 1000000%nat (run_tape p (map exit_of replies)) with
  | Done (st, (_, ex)) =>
    Done (map (fun c => (fst (fst c), snd (fst c))) (snd st),
          exit_image ex,
          match fst st with [] => true | _ => false end)
  | Waiting i v => Waiting i v
  | Unfinished => Unfinished
  end.

(** The rows the workflow calls, in order: the geometry row, then the simulation row. *)
Definition rows_of (requests : list val_) : list (int * val_) :=
  combine (firstn (Stdlib.Lists.List.length requests) [0%Z; 1%Z]) requests.

Definition expected (requests : list val_) (exit_ : F.outcome) :=
  Done (rows_of requests, exit_image (exit_of exit_), true).

Example accepted_0 : observation F.program_0 F.replies_0 = expected F.requests_0 F.exit_0.
Proof. vm_compute. reflexivity. Qed.
Example accepted_1 : observation F.program_1 F.replies_1 = expected F.requests_1 F.exit_1.
Proof. vm_compute. reflexivity. Qed.
Example accepted_2 : observation F.program_2 F.replies_2 = expected F.requests_2 F.exit_2.
Proof. vm_compute. reflexivity. Qed.
Example refused_capacity_3 : observation F.program_3 F.replies_3 = expected F.requests_3 F.exit_3.
Proof. vm_compute. reflexivity. Qed.
Example refused_level_4 : observation F.program_4 F.replies_4 = expected F.requests_4 F.exit_4.
Proof. vm_compute. reflexivity. Qed.
Example fmi_failed_5 : observation F.program_5 F.replies_5 = expected F.requests_5 F.exit_5.
Proof. vm_compute. reflexivity. Qed.

(** Red control: run 0's program under run 4's replies does not show run 0's run. *)
Example control_replies_matter :
  observation F.program_0 F.replies_4 <> expected F.requests_0 F.exit_0.
Proof. vm_compute. discriminate. Qed.
