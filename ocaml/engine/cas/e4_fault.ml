(* Properties: disk faults are values outside model admission.
   Corruption names its address; sealed damage retains its position and reason.
   No constructor authorizes truncation or changes a resident. *)
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

let word = function
  | Corrupt addr -> "corrupt " ^ E4_addr.Addr.hex addr
  | Sealed_segment { seg; off; reason } ->
    Printf.sprintf "sealedDamage %d:%d %s" seg off reason
  | Record { seg; off; reason } -> Printf.sprintf "record %d:%d %s" seg off reason
  | Root { name; reason } -> "root " ^ name ^ " " ^ reason
  | Pack reason -> "pack " ^ reason
  | Store reason -> "store " ^ reason
  | Io reason -> "io " ^ reason
  | Locked directory -> "locked " ^ directory
;;
