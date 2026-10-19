(** Control file and root moves.
    Properties: exact root names and stale-first full-head comparison, by construction.
    Policy and kind stay fixed. Duplicate moves retain generation, by construction.
    Version 1 root bytes map Pin to pin and every other plane to swap, tested by test_control.
    Version 2 bytes carry swap, journal, pin. Journal follows designated parents only.
    Version 1 retains its original lowercase ASCII name domain.
    Version 2 accepts exact UTF-8 names through 65535 encoded bytes.
    The wire bounds encoded root generations below 2^62; arithmetic uses Z.t.
    Root bytes: u16 name-byte count; name bytes; u8 policy; u8 target kind;
    32 digest bytes; be64 generation. The fixed payload and checksum stay unchanged.
    CF4: [commit] replaces the file whole through E4_file (tmp, sync, rename, directory
    sync); a crash leaves the old file or the new one, and a failed step raises
    Unix.Unix_error, so the caller's commit fails (decisions row 417 (3)), by construction;
    tested by test_disk. *)
type root_policy = E4_root_policy.t =
  | Swap
  | Journal
  | Pin

type head =
  { digest : E4_addr.Addr.t
  ; generation : Z.t
  }

type target =
  { kind : E4_kind.t
  ; digest : E4_addr.Addr.t
  }

type root =
  { name : string
  ; policy : root_policy
  ; kind : E4_kind.t
  ; head : head
  }

type move =
  | Create of string * root_policy * target
  | Advance of string * head * target

type status =
  | Fresh
  | Gced
  | Imported
  | Reserved of int * string

type payload =
  { pack_end : int * int
  ; index_end : int * int
  ; generation : int
  ; scheme_version : int
  ; ledger_generation : int
  ; roots : root list
  ; status : status
  }

type t = payload

type open_error =
  | Missing
  | Stale_binary of string
  | Corrupt of string
  | Bad_magic
  | Other_scheme of int

type root_error =
  | No_root of string
  | Stale_root of
      { name : string
      ; expected : head option
      ; actual : head option
      }
  | Pinned of string
  | Dangling of E4_addr.Addr.t
  | Wrong_kind of
      { at : E4_addr.Addr.t
      ; expected : E4_kind.t
      ; actual : E4_kind.t
      }
  | Fork of
      { name : string
      ; head : E4_addr.Addr.t
      ; target : E4_addr.Addr.t
      }

val initial : t
val magic : string
val version_string : string
val filename : string
val tmp_filename : string
val max_name_length : int
val fixed_payload_length : int
val control_path : dir:string -> string
val tmp_path : path:string -> string
val encode : payload -> string
val decode : string -> (payload, open_error) result
val read : path:string -> (payload, open_error) result
val commit : path:string -> payload -> unit
val write : path:string -> payload -> unit
val cleanup : dir:string -> unit
val root : payload -> string -> root option
val roots : t -> root list
val pack_end : t -> int * int
val index_end : t -> int * int
val generation : t -> int
val scheme_version : t -> int
val ledger_generation : t -> int
val status : t -> status

val advance_root
  :  payload
  -> resolve:(E4_addr.Addr.t -> E4_kind.t option)
  -> ?parent:(E4_addr.Addr.t -> E4_addr.Addr.t option)
  -> move
  -> (payload, root_error) result

val bump : t -> t
val set_pack_end : t -> int * int -> t
val set_index_end : t -> int * int -> t
val set_ledger_generation : t -> int -> t
val set_status : t -> status -> t
val root_policy_name : root_policy -> string
val root_policy_index : root_policy -> int
val root_policy_of_index : int -> root_policy option
val normalise_name : string -> string
val valid_name : string -> bool
val open_error_word : open_error -> string
val root_error_word : root_error -> string
val head_equal : head -> head -> bool
val root_policy_equal : root_policy -> root_policy -> bool
