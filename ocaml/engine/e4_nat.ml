(* E4_nat — Lean's `Nat` on a 63-bit host.  The property list is in e4_nat.mli. *)

type t = int

let bits = Sys.int_size
let max_nat = max_int

(* D1: 2^62 is max_nat + 1 and is not an OCaml int; the published bound is inclusive. *)
let wire_limit = max_nat

let is_nat (n : int) : bool = n >= 0
let fits_wire (n : t) : bool = n >= 0

let of_lit (n : int) : t = if n < 0 then max_nat else n

let of_lit_decimal (s : string) : t option =
  let n = String.length s in
  if n = 0 then None
  else begin
    let acc = ref 0 in
    let ok = ref true in
    let sat = ref false in
    for i = 0 to n - 1 do
      let c = Char.code (String.unsafe_get s i) in
      if c < 48 || c > 57 then ok := false
      else if not !sat then begin
        let d = c - 48 in
        (* acc * 10 + d > max_nat ? *)
        if !acc > (max_nat - d) / 10 then sat := true else acc := (!acc * 10) + d
      end
    done;
    if not !ok then None else if !sat then Some max_nat else Some !acc
  end

let add (a : t) (b : t) : t =
  let s = a + b in
  if s < 0 then max_nat else s

let sub (a : t) (b : t) : t =
  let d = a - b in
  if d < 0 then 0 else d

let mul (a : t) (b : t) : t =
  if a = 0 || b = 0 then 0
  else if a > max_nat / b then max_nat
  else a * b

let div (a : t) (b : t) : t = if b = 0 then 0 else a / b
let rem (a : t) (b : t) : t = if b = 0 then a else a mod b

let succ (a : t) : t = add a 1
let pred (a : t) : t = if a <= 0 then 0 else a - 1

(* Translate.powClamped's step: `if a = 0 then 0 else if h > max_int / a then max_int
   else h * a`, applied b times to 1.  Applying it past its fixed point cannot change the
   answer, so the loop stops there and `pow 2 (10^9)` terminates. *)
let pow (a : t) (b : t) : t =
  let step r = if a = 0 then 0 else if r > max_nat / a then max_nat else r * a in
  let rec go i r =
    if i >= b then r
    else
      let r' = step r in
      if r' = r then r else go (i + 1) r'
  in
  go 0 1

let rec pow_reference (a : t) (b : t) : t =
  if b <= 0 then 1
  else
    let h = pow_reference a (b - 1) in
    if a = 0 then 0 else if h > max_nat / a then max_nat else h * a

let shift_left (a : t) (b : t) : t = mul a (pow 2 b)
let shift_right (a : t) (b : t) : t = if b >= bits || b < 0 then 0 else a lsr b

let land_ (a : t) (b : t) : t = a land b
let lor_ (a : t) (b : t) : t = a lor b
let lxor_ (a : t) (b : t) : t = a lxor b

let saturates (a : t) (b : t) : bool = a <> 0 && b <> 0 && a > max_nat / b
