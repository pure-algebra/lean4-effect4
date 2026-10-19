(** The owned disk writer and frozen checked images.
    Properties: open returns faults as values; every raw node passes byte reading then
    shared admission; images contain ordered bytes and the exact root table/boundary;
    transactions preflight before writing; retained images hold no mutable handles.
    A failed file or directory sync is a failed commit: [commit] answers it as an I/O fault
    and closes the writer (decisions row 417 (3)); tested by test_disk.
    Finite comparison and kill tests establish only their observed command lists. *)
type t

type image

type transaction = E4_cas.transaction =
  { txn_nodes : string list
  ; txn_moves : E4_control.move list
  }

type receipt = E4_cas.receipt
type error = E4_cas.transaction_error

val open_ : dir:string -> E4_cas.open_opts -> (t, E4_admission.t) result
val close : t -> unit
val image : t -> (image, E4_admission.t) result
val nodes : image -> (E4_addr.Addr.t * string) list
val roots : image -> E4_control.root list
val boundary : image -> int * int
val get_bytes : image -> E4_addr.Addr.t -> string option
val read : t -> E4_addr.Addr.t -> (string option, E4_admission.t) result

val commit
  :  ?hook:(E4_cas.commit_point -> unit)
  -> t
  -> transaction
  -> (receipt, error) result
