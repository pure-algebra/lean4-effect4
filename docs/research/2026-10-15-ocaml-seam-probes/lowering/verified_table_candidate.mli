(** Research input for a future Ortac wrapper pilot over E4_table.
    Hand-authored candidate. Gospel and Ortac have not checked this file.
    The implementation would forward these calls to int E4_table.t.
    This interface checks observations. It stores no second table implementation. *)

type t

val bindings : t -> (int * int) list
(*@ bs = bindings t
    pure *)

val mem : int -> t -> bool
(*@ b = mem k t
    pure *)

val find_opt : int -> t -> int option
(*@ value = find_opt k t
    pure *)

val singleton : int -> int -> t
(*@ t = singleton k v
    ensures find_opt k t = Some v *)

val set : int -> int -> t -> t
(*@ result = set k v t
    ensures not (mem k t) -> bindings result = bindings t
    ensures mem k t -> find_opt k result = Some v
    ensures bindings t = old (bindings t) *)
