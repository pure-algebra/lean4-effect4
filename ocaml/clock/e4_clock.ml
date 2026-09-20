(* Exact logical milliseconds, corresponding to Effect4.ClockMillis.
   Depends on Zarith. Nonnegative values, exact addition/comparison and persistence are
   by construction; canonical parsing and refusal before numeric conversion are tested
   in test_clock.ml. This module performs no clock, timer, or scheduler mutation. *)
type t = Z.t

exception Profile_refusal of string

let zero = Z.zero

let of_nat value =
  if value < 0 then raise (Profile_refusal "clock: negative natural")
  else Z.of_int value

let positive predecessor = Z.succ (of_nat predecessor)
let add = Z.add
let equal = Z.equal
let le = Z.leq
let lt = Z.lt
let to_decimal = Z.to_string

let of_decimal text =
  let size = String.length text in
  let rec digits index =
    index = size ||
    (text.[index] >= '0' && text.[index] <= '9' && digits (index + 1))
  in
  if size = 0 || (size > 1 && text.[0] = '0') || not (digits 0) then None
  else Some (Z.of_string text)

let literal text =
  match of_decimal text with
  | Some value -> value
  | None -> raise (Profile_refusal "clock: noncanonical generated literal")

(* The number-valued row keeps the rc.112 profile. A narrower native int must also be
   able to represent the result. Neither check changes the exact stored clock. *)
let number_bound = Z.of_string "9007199254740991"
let to_profile_nat value =
  if Z.sign value < 0 || Z.gt value number_bound || not (Z.fits_int value) then
    raise (Profile_refusal "clockNow: milliseconds outside natural-number profile")
  else Z.to_int value
