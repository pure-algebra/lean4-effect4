(** * TodoBudgetCheck: the budgeted tree with definitions on the to-do fixture

    The to-do programs use definitions, invocations, parameters, cells and the context, which
    [denoteRowsB] has no arm for. [BudgetDefs.v] gives the budgeted tree those arms. Here each
    request runs at budgets [0], [1], ... under its recorded reply tape, by [Api.settle], until the
    run is no longer cut. It must then make Lean's recorded calls in order, read the whole tape and
    end with Lean's recorded exit, as [TodoCheck.v] checks of the unbudgeted meaning.

    Each line is a closed computation the kernel checks by [vm_compute]: a finite check on seven
    programs and two hosts. By [Api.settle_finished], each finish is also the meaning's. *)

From Stdlib Require Import List ZArith.
Import ListNotations.
From ITree Require Import ITree ITreeFacts.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Budget E4.BudgetDefs E4.Api E4.Examples E4.Todo_fixture E4.TodoCheck.

(** The host calls of a run, with each answer's exit image, as the fixture writes them. *)
Definition calls_of (steps : list step) : list (int * val_ * val_) :=
  flat_map (fun st => match st with Called i v a => [(i, v, exit_image a)] | Celled _ _ _ => [] end) steps.

(** What the settled run shows: its calls, the root's exit image, and whether the tape was read
    to its end; [None] where no budget up to 60 settles on a finish. *)
Definition budget_observation (p : eff native_op) (calls : list (int * val_ * val_))
    : option (list (int * val_ * val_) * val_ * bool) :=
  match settle 60 by_tape p ([], tape_of calls) with
  | Some (_, (steps, Finished ex, (_, rest))) =>
    Some (calls_of steps, Val_some (exit_image ex), match rest with [] => true | _ => false end)
  | _ => None
  end.

(** The budget each request settles at. *)
Definition settled_at (p : eff native_op) (calls : list (int * val_ * val_)) : option nat :=
  option_map fst (settle 60 by_tape p ([], tape_of calls)).

Example settled_budgets :
  map (fun pc => settled_at (fst pc) (snd pc))
    [(program_0, calls_0); (program_1, calls_1); (program_2, calls_2); (program_3, calls_3);
     (program_4, calls_4); (program_5, calls_5); (program_6, calls_6)] =
  [Some 2; Some 2; Some 3; Some 2; Some 3; Some 2; Some 3].
Proof. vm_compute. reflexivity. Qed.

(** The reference host's runs ([result] lines). *)
Example reference_0 : budget_observation program_0 calls_0 = Some (calls_0, exit_0, true). Proof. vm_compute. reflexivity. Qed.
Example reference_1 : budget_observation program_1 calls_1 = Some (calls_1, exit_1, true). Proof. vm_compute. reflexivity. Qed.
Example reference_2 : budget_observation program_2 calls_2 = Some (calls_2, exit_2, true). Proof. vm_compute. reflexivity. Qed.
Example reference_3 : budget_observation program_3 calls_3 = Some (calls_3, exit_3, true). Proof. vm_compute. reflexivity. Qed.
Example reference_4 : budget_observation program_4 calls_4 = Some (calls_4, exit_4, true). Proof. vm_compute. reflexivity. Qed.
Example reference_5 : budget_observation program_5 calls_5 = Some (calls_5, exit_5, true). Proof. vm_compute. reflexivity. Qed.
Example reference_6 : budget_observation program_6 calls_6 = Some (calls_6, exit_6, true). Proof. vm_compute. reflexivity. Qed.

(** The broken host's runs ([broken] lines). *)
Example broken_0 : budget_observation program_0 bcalls_0 = Some (bcalls_0, bexit_0, true). Proof. vm_compute. reflexivity. Qed.
Example broken_1 : budget_observation program_1 bcalls_1 = Some (bcalls_1, bexit_1, true). Proof. vm_compute. reflexivity. Qed.
Example broken_2 : budget_observation program_2 bcalls_2 = Some (bcalls_2, bexit_2, true). Proof. vm_compute. reflexivity. Qed.
Example broken_3 : budget_observation program_3 bcalls_3 = Some (bcalls_3, bexit_3, true). Proof. vm_compute. reflexivity. Qed.
Example broken_4 : budget_observation program_4 bcalls_4 = Some (bcalls_4, bexit_4, true). Proof. vm_compute. reflexivity. Qed.
Example broken_5 : budget_observation program_5 bcalls_5 = Some (bcalls_5, bexit_5, true). Proof. vm_compute. reflexivity. Qed.
Example broken_6 : budget_observation program_6 bcalls_6 = Some (bcalls_6, bexit_6, true). Proof. vm_compute. reflexivity. Qed.

(** Red control: under the broken tape, request 0 does not show the reference run. *)
Example control_hosts_differ : budget_observation program_0 bcalls_0 <> Some (calls_0, exit_0, true).
Proof. vm_compute. discriminate. Qed.

(** Frontier control: with no reply, request 0 settles at once on a wait at its first call, the
    insert of "milk" at row 0. *)
Example control_frontier :
  option_map (fun r => stop_at (snd r)) (settle 60 by_tape program_0 ([], [])) = Some (Waiting 0%Z (Val_str "milk")).
Proof. vm_compute. reflexivity. Qed.
