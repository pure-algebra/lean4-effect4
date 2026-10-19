(* Disk_test_support -- the fixtures the owned disk writer's tests share: a small store's nodes
   and roots, the writer's options, readers that render an image or a refusal as one line, and
   a scratch directory.

   What it is: the private library effect4_disk_test_support, for test_disk, test_disk_kill,
   test_disk_stm, test_disk_damage, test_disk_boundary, bench_commit and the model test
   ../../test/stm/stm_disk.ml.  An outside project cannot name it (the install lane's red
   control red_test_library).  Its scratch directory and its removal are the harness's,
   E4_check, so a scratch directory lies under the system's temporary directory (TMPDIR).
   Depends on: Effect4_engine_cas (E4_cas, E4_disk, E4_control, E4_node, E4_kind, E4_addr,
   E4_admission), Effect4_bytes, Eff_frame, E4_check, Zarith.

   Behaviours:
   D1 The nodes are fixed values: a schema node, three exports under it (`a`, `b`, `t`) and a
      fourth (`u`) that refers to `t`; each address is its node's digest.   by construction
   D2 [observation] renders an image's nodes and roots as one line (its durable boundary is
      [image_equal]'s, not the line's); [admission_observation] and [transaction_observation]
      render a refusal or a receipt as one line with every field of its constructor.
                                                                     by construction
   D3 [temp ()] answers a fresh directory, and [remove] takes it away with every sealed entry
      under it, through E4_check (its C3 and C4).                tested (E4_check's test_check)
   D4 [get] and [require] raise Failure on a refusal or a false condition: a fixture that does
      not build is a broken test, not an answer of the writer.    by construction

   What it does not establish: the writer's laws themselves.  The tests above check them as
   finite controls of the actual disk writer, not a universal IO theorem: checked images freeze
   bytes, roots and the durable boundary; preflight refuses without writing; reopened stores
   retain their heads; damage is a fault value. *)

open Effect4_engine_cas

(** [require condition message] raises Failure with [message] when [condition] is false (D4). *)
val require : bool -> string -> unit

(** The value of an [Ok]; raises Failure on an [Error] (D4). *)
val get : ('a, 'b) result -> 'a

(** The writer's options for the tests: small segments and a small index. *)
val opts : E4_cas.open_opts

(** A fresh scratch directory (D3). *)
val temp : unit -> string

(** Removes a scratch directory and everything under it (D3). *)
val remove : string -> unit

(** A string value's frame. *)
val vstr : string -> string

(** A node of version 0 from its kind, its spec and its payload. *)
val node : E4_kind.t -> string -> string -> E4_node.t

(** The fixed nodes and their addresses (D1). *)
val schema : E4_node.t

val s : E4_addr.Addr.t
val a : E4_node.t
val b : E4_node.t
val aa : E4_addr.Addr.t
val ba : E4_addr.Addr.t
val t : E4_node.t
val ta : E4_addr.Addr.t
val u : E4_node.t
val ua : E4_addr.Addr.t

(** An export target at a digest. *)
val target : E4_addr.Addr.t -> E4_control.target

(** A transaction of these nodes and these moves. *)
val transaction : E4_node.t list -> E4_control.move list -> E4_disk.transaction

(** The first transaction of the tests' store. *)
val initial : E4_disk.transaction

(** Two images hold the same nodes, roots and durable boundary. *)
val image_equal : E4_disk.image -> E4_disk.image -> bool

(** The root of that name in an image. *)
val root : E4_disk.image -> string -> E4_control.root option

(** Opens the writer on a directory with {!opts}; raises Failure on a refusal (D4). *)
val open_ : string -> E4_disk.t

(** The writer's image; raises Failure on a refusal (D4). *)
val snapshot : E4_disk.t -> E4_disk.image

(** An image as one line (D2). *)
val observation : E4_disk.image -> string

(** A golden of ../goldens, or of the directory E4_CAS_GOLDENS names; raises Failure when the
    golden is missing. *)
val golden_path : string -> string

(** A refusal of admission as one line (D2). *)
val admission_observation : E4_admission.t -> string

(** A transaction's receipt or refusal as one line (D2). *)
val transaction_observation : (E4_cas.receipt, E4_cas.transaction_error) result -> string
