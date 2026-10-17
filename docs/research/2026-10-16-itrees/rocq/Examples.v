(** * Examples: programs written with [Api.Author], for the checks and the view

    Each is in the fragment and in scope ([Author.ready]). Positions: at the root a loop's cursor
    is [var 0], and its step sees the body's value at [var 1]. *)

From Stdlib Require Import List ZArith String.
Import ListNotations.
Require Import RocqOfOCaml.RocqOfOCaml.
Require Import E4.Eff_types E4.Denote E4.Run E4.Judgments E4.Budget E4.BudgetDefs E4.Api.
Import Author.

Local Open Scope Z_scope.

(** A loop that doubles its cursor from 1 while it is below 16, and calls host row 0 with the
    cursor at each round. It ends with the cursor, 16, after four calls and five tests. *)
Definition doubling : eff native_op :=
  loop (num 1) (lt_ (var 0) (num 16)) (mul_ (var 0) (num 2)) (var 0) (row 0 (var 0)).

(** The silent loop of [Judgments.loop_forever]: its test is always true and it calls nothing. *)
Definition forever : eff native_op := loop_forever.

(** A loop whose test is always true and that calls host row 0 at each round. *)
Definition ping : eff native_op := loop (num 0) (bool_ true) (var 0) unit_ (row 0 (var 0)).

(** A cell written at each round of a doubling loop and read at the end: it holds 4. *)
Definition cell_counter : eff native_op :=
  seq (cell_new (num 0))
      (seq (loop (num 1) (lt_ (var 1) (num 8)) (mul_ (var 1) (num 2)) unit_ (cell_set (var 0) (var 1)))
           (cell_get (var 0))).

(** An edit: a decision on the literal [true], before and after [when_true_law]. *)
Definition before_edit : eff native_op := when (bool_ true) doubling ping.
Definition after_edit : eff native_op := doubling.

(** The doubling loop as a recursive definition: definition 0 calls host row 0 with its request
    and then itself at the double, while the request is below 16. Five calls deep, it ends with
    16. *)
Definition doubling_rec : eff native_op :=
  define [when (lt_ (var 0) (num 16)) (seq (row 0 (var 0)) (call 0 (mul_ (var 0) (num 2)))) (ret (var 0))]
         (call 0 (num 1)).

(** A definition that calls itself at once, forever, and calls nothing else. *)
Definition self_call : eff native_op := define [call 0 (var 0)] (call 0 (num 0)).

(** An invocation: definition 0 runs its passed program twice, at the request 7; the passed
    program calls host row 0 with what it is given. *)
Definition twice : eff native_op :=
  define [seq (param 0 (var 0)) (param 0 (var 0))] (invoke 0 (num 7) [row 0 (var 0)]).

(** Every host call answered with [unit]. *)
Definition answer_unit : host RowE unit := fn_host (fun _ _ s => Some (Success Val_unit, s)).

(** A reply tape of [n] successes with [unit]. *)
Definition units (n : nat) : list exitv := repeat (Success Val_unit) n.

(** The two hosts of the checks, the cells beside the rows. *)
Definition by_tape : host E1 (cells * list exitv) := route cells_host tape.
Definition by_unit : host E1 (cells * unit) := route cells_host answer_unit.
