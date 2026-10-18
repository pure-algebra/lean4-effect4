(* Exact logical milliseconds, corresponding to Effect4.ClockMillis, and the refusal of a value
   at a named crossing.
   Depends on Zarith. Nonnegative values, exact addition/multiplication/comparison and persistence are
   by construction; canonical parsing, refusal before numeric conversion and the crossing each
   refusal names are tested in test_clock.ml. This module performs no clock, timer, or scheduler
   mutation. *)
type t = Z.t

type crossing =
  | Literal
  | Reply
  | Arithmetic
  | Clock
  | Index
  | Panic

type refusal =
  { crossing : crossing
  ; reason : string
  }

exception Profile_refusal of refusal

let crossing_name = function
  | Literal -> "literal"
  | Reply -> "reply"
  | Arithmetic -> "arithmetic"
  | Clock -> "clock"
  | Index -> "index"
  | Panic -> "panic"
;;

let refusal_text { crossing; reason } = crossing_name crossing ^ ": " ^ reason
let refuse crossing reason = raise (Profile_refusal { crossing; reason })
let zero = Z.zero

let natural crossing value =
  if value < 0 then refuse crossing "a negative natural" else Z.of_int value
;;

let of_nat value = natural Clock value
let positive predecessor = Z.succ (of_nat predecessor)
let add = Z.add
let mul = Z.mul
let equal = Z.equal
let le = Z.leq
let lt = Z.lt
let to_decimal = Z.to_string

let of_decimal text =
  let size = String.length text in
  let rec digits index =
    index = size || (text.[index] >= '0' && text.[index] <= '9' && digits (index + 1))
  in
  if size = 0 || (size > 1 && text.[0] = '0') || not (digits 0)
  then None
  else Some (Z.of_string text)
;;

let literal text =
  match of_decimal text with
  | Some value -> value
  | None -> refuse Literal "a noncanonical generated literal"
;;

(* The number-valued rows keep the rc.112 profile. A narrower native int must also be
   able to represent the result. Neither check changes the exact stored clock. *)
let number_bound = Z.of_string "9007199254740991"

let observe crossing what value =
  if Z.sign value < 0 || Z.gt value number_bound || not (Z.fits_int value)
  then refuse crossing (what ^ " outside the program's profile (DI-56)")
  else Z.to_int value
;;

let to_profile_nat value = observe Clock "milliseconds" value

let check_nat crossing value =
  ignore (observe crossing "a natural" (natural crossing value))
;;

let profile_add a b =
  observe Arithmetic "a sum" (Z.add (natural Arithmetic a) (natural Arithmetic b))
;;

let profile_mul a b =
  observe Arithmetic "a product" (Z.mul (natural Arithmetic a) (natural Arithmetic b))
;;
