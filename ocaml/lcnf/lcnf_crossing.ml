(* Lcnf_crossing -- see lcnf_crossing.mli. *)

type crossing =
  | Arithmetic
  | Index

type refusal =
  { crossing : crossing
  ; reason : string
  }

exception Refused of refusal

let crossing_name = function
  | Arithmetic -> "arithmetic"
  | Index -> "index"
;;

let refusal_text { crossing; reason } = crossing_name crossing ^ ": " ^ reason

let[@inline never] [@local never] [@specialise never] refuse crossing reason =
  raise (Refused { crossing; reason })
;;
