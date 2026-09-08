(* e4_quiescence.mli — the count of accepted-but-not-yet-applied work, and the wait for zero.

   The design (§1.2.1) says "verbatim + a new .mli" and gives no text for it, so THIS
   INTERFACE IS DERIVED from the module's public face as `ocaml/link/e4_quiescence.ml`
   exposes it at 7d53312 (every top-level value of that file). The laws Q1-Q3 are at the
   head of e4_quiescence.ml. *)

type t
(** The pending-work counter of one host. Mutable and host-level. *)

val create : unit -> t
(** Outstanding zero. *)

val enter : t -> unit
(** One accepted piece of work. Called under the mailbox lock, so a refused push never
    counts. Q1. *)

val leave : t -> unit
(** One applied piece of work; wakes {!wait_zero} on reaching zero. Q1, Q2.
    @raise Invalid_argument if nothing is outstanding — a leave without an enter is a bug,
    not a silent underflow. *)

val outstanding : t -> int
(** enters - leaves. Q1. *)

val totals : t -> int * int
(** [(entered, left)]. *)

val wait_zero : t -> unit
(** Block until nothing is outstanding. Q2. *)

val wait_zero_for : t -> seconds:float -> bool
(** As {!wait_zero} with a HOST deadline: [true] on reaching zero, [false] at the deadline.
    Polls, because `Condition` has no timed wait. The deadline never reaches a decision
    (survey trap #8). Q3. *)
