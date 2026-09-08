(* e4_reply.mli — a one-shot reply cell across domains.

   The design (§1.2.1) says "verbatim + a new .mli" and gives no text for it, so THIS
   INTERFACE IS DERIVED from the module's public face as `ocaml/link/e4_reply.ml` exposes it
   at 7d53312 (every top-level value of that file). The laws P1-P2 are at the head of
   e4_reply.ml.

   Only plain data crosses: ints, strings and records of them — never a Lean value and
   never a machine (THE MEMORY RULE, design §1.2). *)

type 'a t
(** A one-shot cell. Host-level and mutable. *)

val create : unit -> 'a t
(** Empty. *)

val fill : 'a t -> 'a -> unit
(** Fill the cell once and wake every waiter. P1, P2.
    @raise Invalid_argument on a second fill; the first value stays in place. *)

val await : 'a t -> 'a
(** Block until the cell is filled, then return its value, to every waiter, exactly as
    filled. P2. *)

val peek : 'a t -> 'a option
(** The value if the cell is filled; never blocks. *)
