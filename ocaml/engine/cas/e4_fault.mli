(** Disk faults remain outside modeled admission.
    Properties: corruption names its address; sealed damage names its position;
    callers receive values; formatting changes no store bytes. *)
type t =
  | Corrupt of E4_addr.Addr.t
  | Sealed_segment of
      { seg : int
      ; off : int
      ; reason : string
      }
  | Record of
      { seg : int
      ; off : int
      ; reason : string
      }
  | Root of
      { name : string
      ; reason : string
      }
  | Pack of string
  | Store of string
  | Io of string
  | Locked of string

val word : t -> string
