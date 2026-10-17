(** * TodoCheck: the meaning's calls are the Lean machine's, on the to-do fixture

    [Todo_fixture] holds, for each request of the to-do lane's script, the built program and what
    Lean's run recorded ([Run.runWith], [Test/Dogfood/Scenario/Todo/HostLane.lean]): each host
    call's row, request and answer, and the root's exit image. It is generated from
    [ocaml/engine/test/todo/todo-host.txt] ([gen/fixture_to_ml.py], then rocq-of-ocaml), and its
    values re-encode to the fixture's bytes ([gen/check_fixture.ml]).

    The check is the reading of Lean's H8 ([denoteRows_eq_session],
    [src/Effect4/Laws/Api/SessionMeaning.lean]) at these programs: run the meaning under the run's
    own reply tape. It then issues exactly the recorded calls, in order, consumes the whole tape
    and ends with the recorded exit. Each line is a closed computation that the kernel checks by
    [vm_compute]: a finite check on seven programs and two hosts, not a theorem over programs.
    These programs use definitions, invocations, parameters, cells and the context, which Lean's
    [denoteRows] does not cover. *)

From Stdlib Require Import List ZArith.
Import ListNotations.
From ITree Require Import ITree.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Todo_fixture.

(** The tape a recorded run's calls write: each answer's exit, in call order. *)
Definition tape_of (calls : list (int * val_ * val_)) : list exitv :=
  map (fun c => exit_of_image (snd c)) calls.

(** What the meaning shows under that tape: the calls it made with their answers' images, the
    root's exit image, and whether the tape was read to its end. *)
Definition observation (p : eff native_op) (calls : list (int * val_ * val_))
    : outcome (list (int * val_ * val_) * val_ * bool) :=
  match observe_n 1000000%nat (run_tape p (tape_of calls)) with
  | Done (st, (_, ex)) =>
    Done (map (fun c => (fst (fst c), snd (fst c), exit_image (snd c))) (snd st),
          Val_some (exit_image ex),
          match fst st with [] => true | _ => false end)
  | Waiting i v => Waiting i v
  | Unfinished => Unfinished
  end.

(** The reference host's runs ([result] lines). *)
Example reference_0 : observation program_0 calls_0 = Done (calls_0, exit_0, true). Proof. vm_compute. reflexivity. Qed.
Example reference_1 : observation program_1 calls_1 = Done (calls_1, exit_1, true). Proof. vm_compute. reflexivity. Qed.
Example reference_2 : observation program_2 calls_2 = Done (calls_2, exit_2, true). Proof. vm_compute. reflexivity. Qed.
Example reference_3 : observation program_3 calls_3 = Done (calls_3, exit_3, true). Proof. vm_compute. reflexivity. Qed.
Example reference_4 : observation program_4 calls_4 = Done (calls_4, exit_4, true). Proof. vm_compute. reflexivity. Qed.
Example reference_5 : observation program_5 calls_5 = Done (calls_5, exit_5, true). Proof. vm_compute. reflexivity. Qed.
Example reference_6 : observation program_6 calls_6 = Done (calls_6, exit_6, true). Proof. vm_compute. reflexivity. Qed.

(** The broken host's runs ([broken] lines): insert fails with the rows' error, and the
    failure reaches the root's exit unchanged. *)
Example broken_0 : observation program_0 bcalls_0 = Done (bcalls_0, bexit_0, true). Proof. vm_compute. reflexivity. Qed.
Example broken_1 : observation program_1 bcalls_1 = Done (bcalls_1, bexit_1, true). Proof. vm_compute. reflexivity. Qed.
Example broken_2 : observation program_2 bcalls_2 = Done (bcalls_2, bexit_2, true). Proof. vm_compute. reflexivity. Qed.
Example broken_3 : observation program_3 bcalls_3 = Done (bcalls_3, bexit_3, true). Proof. vm_compute. reflexivity. Qed.
Example broken_4 : observation program_4 bcalls_4 = Done (bcalls_4, bexit_4, true). Proof. vm_compute. reflexivity. Qed.
Example broken_5 : observation program_5 bcalls_5 = Done (bcalls_5, bexit_5, true). Proof. vm_compute. reflexivity. Qed.
Example broken_6 : observation program_6 bcalls_6 = Done (bcalls_6, bexit_6, true). Proof. vm_compute. reflexivity. Qed.

(** Red control: the two hosts' runs differ, so the lines above compare what tells them apart.
    Under the broken tape, request 0 does not show the reference run. *)
Example control_hosts_differ : observation program_0 bcalls_0 <> Done (calls_0, exit_0, true).
Proof. vm_compute. discriminate. Qed.

(** Frontier control: with no reply at all, request 0 waits at its first call, the insert of
    "milk" at row 0, and never exits. *)
Example control_frontier : observation program_0 [] = Waiting 0%Z (Val_str "milk").
Proof. vm_compute. reflexivity. Qed.
