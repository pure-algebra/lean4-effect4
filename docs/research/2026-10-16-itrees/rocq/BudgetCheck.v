(** * BudgetCheck: the API on the examples, as finite checks and as theorems

    Each [Example] is a closed computation the kernel checks by [vm_compute]: one program, one
    host, one start, one budget or limit. The [Corollary]s are theorems of [Budget.v] and
    [Api.v] at these programs; [forever_cut_everywhere] holds at every budget. *)

From Stdlib Require Import List ZArith String.
Import ListNotations.
From ITree Require Import ITree ITreeFacts.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Judgments E4.Budget E4.Api E4.Examples.

Local Open Scope Z_scope.

Example examples_ready :
  map Author.ready [doubling; forever; ping; cell_counter; before_edit] = [true; true; true; true; true].
Proof. vm_compute. reflexivity. Qed.

(** The doubling loop under a tape of four replies: cut at budget 4 after four calls, finished at
    budget 5 with 16. *)
Example doubling_cut_at_4 :
  stop_at (run_at 4 by_tape doubling ([], units 4)) = Cut /\
  Stdlib.Lists.List.length (steps_of (run_at 4 by_tape doubling ([], units 4))) = 4%nat.
Proof. vm_compute. split; reflexivity. Qed.

Example doubling_settles :
  settle 10 by_tape doubling ([], units 4) =
    Some (5%nat, ([Called 0 (Val_nat 1) (Success Val_unit); Called 0 (Val_nat 2) (Success Val_unit);
                   Called 0 (Val_nat 4) (Success Val_unit); Called 0 (Val_nat 8) (Success Val_unit)],
                  Finished (Success (Val_nat 16)), ([], []))).
Proof. vm_compute. reflexivity. Qed.

(** So the meaning finishes, as a theorem. *)
Corollary doubling_finishes :
  run_tree by_tape (meaning doubling) ([], units 4) ≈ Ret (([], []), Success (Val_nat 16)).
Proof. eapply settle_finished; [reflexivity | exact doubling_settles]. Qed.

(** Under a tape of three replies the fourth call waits. *)
Example doubling_waits_settle :
  settle 10 by_tape doubling ([], units 3) =
    Some (4%nat, ([Called 0 (Val_nat 1) (Success Val_unit); Called 0 (Val_nat 2) (Success Val_unit);
                   Called 0 (Val_nat 4) (Success Val_unit)],
                  Waiting 0 (Val_nat 8), ([], []))).
Proof. vm_compute. reflexivity. Qed.

Corollary doubling_waits :
  exists X (ev : StuckE E1 X) k, run_tree by_tape (meaning doubling) ([], units 3) ≈ Vis ev k.
Proof.
  destruct (settle_some by_tape doubling ([], units 3) 10 4 _ doubling_waits_settle) as (_ & Hr & _).
  eapply (run_at_waits by_tape 4 doubling _ _ (Waiting 0 (Val_nat 8))); [reflexivity | symmetry; exact Hr | reflexivity].
Qed.

(** **The silent loop is cut at every budget**: [Judgments.loop_diverges], the tree theorem,
    read through [meaning_diverges_iff]. A statement at every budget, not a probe. *)
Corollary forever_cut_everywhere : forall k, denoteB k forever [] = PRet None.
Proof. apply meaning_diverges_iff; [reflexivity | exact loop_diverges]. Qed.

Corollary forever_never_settles {St} (h : host E1 St) s limit : settle limit h forever s = None.
Proof.
  apply settle_none. intros k _. unfold run_at. rewrite forever_cut_everywhere. reflexivity.
Qed.

(** The calling loop under a host that always answers: one more call at each budget, always cut
    (a finite probe up to 30). *)
Example ping_probe :
  settle 30 by_unit ping ([], tt) = None /\
  Stdlib.Lists.List.length (steps_of (run_at 30 by_unit ping ([], tt))) = 30%nat.
Proof. vm_compute. split; reflexivity. Qed.

Example cell_counter_settles :
  settle 10 by_tape cell_counter ([], []) =
    Some (4%nat, ([Celled "make" (Val_nat 0) (Val_handle 2 0);
                   Celled "set" (Val_list [Val_handle 2 0; Val_nat 1]) Val_unit;
                   Celled "set" (Val_list [Val_handle 2 0; Val_nat 2]) Val_unit;
                   Celled "set" (Val_list [Val_handle 2 0; Val_nat 4]) Val_unit;
                   Celled "get" (Val_handle 2 0) (Val_nat 4)],
                  Finished (Success (Val_nat 4)), ([Val_nat 4], []))).
Proof. vm_compute. reflexivity. Qed.

(** **The edit**: [before_edit] and [after_edit] are equal programs ([when_true_law]), so Lean's
    three outcomes agree under every host; and here every frame up to 8 is the same. *)
Corollary edit_equal : EffEq before_edit after_edit.
Proof. apply when_true_law. Qed.

Corollary edit_outcomes {St} (h : host E1 St) s :
  (forall r s', Finishes h before_edit [] s r s' <-> Finishes h after_edit [] s r s') /\
  (Waits h before_edit [] s <-> Waits h after_edit [] s) /\
  (ChainDiverges h before_edit [] s <-> ChainDiverges h after_edit [] s).
Proof. apply edit_keeps_outcomes; [reflexivity | reflexivity | exact edit_equal]. Qed.

Example edit_frames :
  map (fun k => run_at k by_tape before_edit ([], units 4)) (List.seq 0 8) =
  map (fun k => run_at k by_tape after_edit ([], units 4)) (List.seq 0 8).
Proof. vm_compute. reflexivity. Qed.
