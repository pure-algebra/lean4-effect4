(* e4_ring.mli — the per-domain event ring: seq-tagged rows, single writer, bounded.

   The design (§1.2.1) says "verbatim + a new .mli" and gives no text for it, so THIS
   INTERFACE IS DERIVED from the module's public face as `git:14e6835:ocaml/link/e4_ring.ml` exposes it
   at 7d53312 (every top-level value of that file; `entry` and `read` stay concrete, since
   `link/e4_test.ml` and `e4_host.ml` read their fields). The laws G1-G3 are at the head of
   e4_ring.ml. *)

type entry = {
  domain : int;      (** the writing domain *)
  machine : int;     (** the machine whose step produced the row *)
  seq : int;         (** the global sequence number of the decision *)
  decision : string; (** the decision, on the wire *)
  row : string;      (** the event row, as bytes; strings are how events leave a domain *)
}

type read = {
  entries : entry list; (** G3: index order, from max(cursor, oldest retained) *)
  next : int;           (** G3: the cursor for the next read *)
  gap : bool;           (** G2: entries older than the cursor were dropped *)
}

type t
(** One domain's ring. Host-level and mutable: never reachable from a saved machine. *)

val create : domain:int -> capacity:int -> t
(** @raise Invalid_argument if [capacity < 1]. *)

val domain : t -> int
val capacity : t -> int

val append : t -> entry -> unit
(** Append one row, overwriting the oldest when the ring is full. G1, G2.
    @raise Invalid_argument if a second domain appends (G1). *)

val read : t -> cursor:int -> read
(** Everything written at or after [cursor] that is still retained. G2, G3. *)

val written : t -> int
(** The number of appends ever made: the index the next append will take. *)
