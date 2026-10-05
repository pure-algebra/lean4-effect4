let lcnf_utf8_bytes s =
  List.init (String.length s) (fun i -> Char.code (String.get s i))

let lcnf_utf8_length s =
  String.fold_left (fun n c -> if Char.code c land 192 = 128 then n else n + 1) 0 s



(* LCNF mono: CaptureProbe.mulCap (x : Nat) (_mula : Nat) : Nat *)

let capture_probe_mul_cap (x : int) (_mula : int) : int =
  let _mula = x in
  let _mulb = _mula in
  if _mula = 0 then 0 else if _mulb > max_int / _mula then max_int else _mula * _mulb



(* LCNF mono: CaptureProbe.mulOk (x : Nat) (y : Nat) : Nat *)

let capture_probe_mul_ok (x : int) (y : int) : int =
  let _mula = x in
  let _mulb = y in
  if _mula = 0 then 0 else if _mulb > max_int / _mula then max_int else _mula * _mulb



(* LCNF mono: CaptureProbe.shiftCap (_shift_scale : Nat) (b : Nat) : Nat *)

let capture_probe_shift_cap (_shift_scale : int) (b : int) : int =
  let _shift_scale = let rec _pow_clamped _pa _pb = if _pb = 0 then 1 else (let _ph = _pow_clamped _pa (_pb - 1) in
      if _pa = 0 then 0 else if _ph > max_int / _pa then max_int else _ph * _pa) in
  _pow_clamped 2 b in
  if _shift_scale = 0 then 0 else if _shift_scale > max_int / _shift_scale then max_int else _shift_scale * _shift_scale



(* LCNF mono: CaptureProbe.shiftOk (a : Nat) (b : Nat) : Nat *)

let capture_probe_shift_ok (a : int) (b : int) : int =
  let _shift_scale = let rec _pow_clamped _pa _pb = if _pb = 0 then 1 else (let _ph = _pow_clamped _pa (_pb - 1) in
      if _pa = 0 then 0 else if _ph > max_int / _pa then max_int else _ph * _pa) in
  _pow_clamped 2 b in
  if a = 0 then 0 else if _shift_scale > max_int / a then max_int else a * _shift_scale



(* LCNF mono: CaptureProbe.applyTo (f : Nat -> Nat) (x : Nat) : Nat *)

let capture_probe_apply_to (f : int -> int) (x : int) : int =
  f x



(* LCNF mono: CaptureProbe.addCap (_b1 : Nat) (y : Nat) : Nat *)

let capture_probe_add_cap (_b1 : int) (y : int) : int =
  let _x_1 = fun _b1 -> _b1 + _b1 in
  capture_probe_apply_to _x_1 y



(* LCNF mono: CaptureProbe.addOk (a : Nat) (y : Nat) : Nat *)

let capture_probe_add_ok (a : int) (y : int) : int =
  let _x_1 = fun _b1 -> a + _b1 in
  capture_probe_apply_to _x_1 y



(* LCNF mono: List.elem._at_.Effect4.Store.distinctNats.spec_0 (a : Nat) (x.1 : List Nat) : Bool *)

let rec list_elem_at_store_distinct_nats_spec_0 (a : int) (x_1 : int list) : bool =
  match x_1 with
    | [] -> false
    | head_3 :: tail_4 -> (let _x_5 = a = head_3 in
      if _x_5 then _x_5 else list_elem_at_store_distinct_nats_spec_0 a tail_4)



(* LCNF mono: CaptureProbe.containsCap (l : List Nat) (_elem : Nat) : Bool *)

let capture_probe_contains_cap (l : int list) (_elem : int) : bool =
  list_elem_at_store_distinct_nats_spec_0 _elem l



(* LCNF mono: CaptureProbe.containsOk (l : List Nat) (a : Nat) : Bool *)

let capture_probe_contains_ok (l : int list) (a : int) : bool =
  list_elem_at_store_distinct_nats_spec_0 a l





let () =
  List.iter (fun (name, lean, target) ->
      Printf.printf "RESULT\t%s\tlean=%d\tocaml=%d\t%s\n" name lean target
        (if lean = target then "agree" else "DIFFER"))
    [ ("capture_probe_mul_cap 3 5", 15, capture_probe_mul_cap 3 5);
      ("capture_probe_mul_ok 3 5", 15, capture_probe_mul_ok 3 5);
      ("capture_probe_shift_cap 3 2", 12, capture_probe_shift_cap 3 2);
      ("capture_probe_shift_ok 3 2", 12, capture_probe_shift_ok 3 2);
      ("capture_probe_add_cap 3 5", 8, capture_probe_add_cap 3 5);
      ("capture_probe_add_ok 3 5", 8, capture_probe_add_ok 3 5) ]
