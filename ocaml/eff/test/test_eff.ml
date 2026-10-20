(* test_eff — the battery of effect4_eff (hand-written).
   1. The program codec (Eff_codec: Lean's exact embedding, lowered, over the framing kernel):
      a constructor tag no program has, a constructor with a missing or an extra argument, and
      a requirement row out of order are refused at decoding; a negative natural is refused at
      encoding. The codec's agreement with Lean's own bytes is test_lean_wire's, on the goldens
      Lean cuts (ocaml/goldens/eff), and its round trip on random programs is prop_wire's.
   2. The wire kernel: nat digits, the bound, UTF-8, refusals.
   Exit status 1 on any failure; the counts are printed last. *)

open Eff_types

let checks = ref 0
let failures = ref 0

let check (name : string) (ok : bool) : unit =
  incr checks;
  if not ok
  then (
    incr failures;
    Printf.printf "FAIL: %s\n%!" name)
;;

(* ---- 1. the program codec ---- *)

let () =
  let bad_index i =
    Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b i (fun _ -> ())) ()
  in
  check "Eff index 27 is refused" (Eff_codec.decode_program (bad_index 27) = None);
  check
    "Eff index 24 with no payload is refused (provideLayer needs a layer, a flag and a \
     body)"
    (Eff_codec.decode_program (bad_index 24) = None);
  check "Eff index 99 is refused" (Eff_codec.decode_program (bad_index 99) = None);
  check
    "Eff index 17 with no payload is refused (yieldNow needs a nat)"
    (Eff_codec.decode_program (bad_index 17) = None);
  let yield0 =
    Eff_frame.to_string
      (fun b () -> Eff_frame.emit_ctor b 17 (fun b -> Eff_frame.emit_nat b 0))
      ()
  in
  check
    "Eff index 17 with a nat is yieldNow 0"
    (Eff_codec.decode_program yield0 = Some (Eff.YieldNow 0));
  let extra =
    Eff_frame.to_string
      (fun b () ->
         Eff_frame.emit_ctor b 17 (fun b ->
           Eff_frame.emit_nat b 0;
           Eff_frame.emit_nat b 0))
      ()
  in
  check
    "an extra argument inside the frame is refused"
    (Eff_codec.decode_program extra = None);
  (* C3: a requirement row's order is Lean's type's. The OCaml list does not carry it, so a row
     out of order encodes, and its bytes are no program's: the reading refuses them. The control
     is the same program with its row in order, which reads back. *)
  let key n s = { ServiceKey.name = n; service = s } in
  let carrying keys : Eff_codec.program =
    Eff.Bind
      ( Eff.Perform
          (NativeOp.DeferredMakeOf (Ty.ContextOf keys, Ty.Nat), Term.Lit Lit.Unit)
      , Eff.WithFiber (ActionTerm.Context keys) )
  in
  let reads keys =
    Eff_codec.decode_program (Eff_codec.encode_program (carrying keys))
    = Some (carrying keys)
  in
  check "C3 a requirement row in order reads back" (reads [ key 1 2; key 1 3; key 2 0 ]);
  check
    "C3 a requirement row out of order or repeated is refused at decoding"
    ((not (reads [ key 2 0; key 1 3 ]))
     && (not (reads [ key 1 3; key 1 2 ]))
     && not (reads [ key 1 2; key 1 2 ]));
  check
    "C3 a negative natural is refused at encoding"
    (try
       ignore (Eff_codec.encode_program (Eff.Succeed (Term.Lit (Lit.Nat (-1)))));
       false
     with
     | Invalid_argument _ -> true)
;;

(* ---- 2. the wire kernel ---- *)

let () =
  let open Eff_frame in
  check
    "nat digits: 0 is empty, 255 one byte, 256 two"
    (nat_digits 0 = "" && nat_digits 255 = "\255" && nat_digits 256 = "\001\000");
  check "nat digits: max_int is 8 bytes" (String.length (nat_digits max_int) = 8);
  let rt n = exact decode_nat (to_string emit_nat n) = Some n in
  check
    "nat round trip at 0, 1, 255, 256, 65535, 2^32, max_int"
    (rt 0 && rt 1 && rt 255 && rt 256 && rt 65535 && rt (1 lsl 32) && rt max_int);
  check
    "a negative int has no encoding"
    (try
       ignore (nat_digits (-1));
       false
     with
     | Invalid_argument _ -> true);
  let frame tag payload = to_string (fun b () -> emit_frame b tag payload) () in
  check
    "a nat with a leading zero digit is refused"
    (exact decode_nat (frame tag_nat "\000\001") = None);
  check
    "a nat of nine digits is refused"
    (exact decode_nat (frame tag_nat "\001\000\000\000\000\000\000\000\000") = None);
  check
    "a nat of eight digits above max_int is refused"
    (exact decode_nat (frame tag_nat "\064\000\000\000\000\000\000\000") = None);
  check
    "a nat of eight digits at max_int is accepted"
    (exact decode_nat (frame tag_nat "\063\255\255\255\255\255\255\255") = Some max_int);
  check
    "a bool byte other than 0/1 is refused"
    (exact decode_bool (frame tag_bool "\002") = None
     && exact decode_bool (frame tag_bool "\001\000") = None);
  check "unit with a payload is refused" (exact decode_unit (frame tag_unit "\000") = None);
  check
    "the empty string round-trips"
    (exact decode_string (to_string emit_string "") = Some "");
  check
    "UTF-8: multi-byte scalars are accepted"
    (utf8_valid "h\xc3\xa9llo \xe6\x97\xa5\xe6\x9c\xac \xf0\x9f\x98\x80");
  check
    "UTF-8: a stray continuation byte is refused"
    ((not (utf8_valid "\x80")) && exact decode_string (frame tag_string "\xff") = None);
  check
    "UTF-8: overlong and surrogate encodings are refused"
    ((not (utf8_valid "\xc0\x80"))
     && (not (utf8_valid "\xed\xa0\x80"))
     && not (utf8_valid "\xf4\x90\x80\x80"));
  check "UTF-8: a truncated sequence is refused" (not (utf8_valid "\xe6\x97"));
  check
    "emit_string refuses invalid UTF-8"
    (try
       ignore (to_string emit_string "\xff");
       false
     with
     | Invalid_argument _ -> true);
  check
    "a frame shorter than nine bytes is refused"
    (read_frame "\002\000" 0 2 = None && exact decode_nat "" = None);
  check
    "an option's some must fill its payload"
    (exact (decode_option decode_nat) (frame tag_some (nat_digits 1)) = None);
  check
    "a list decodes its elements exactly"
    (exact
       (decode_list decode_nat)
       (to_string (fun b xs -> emit_list b emit_nat xs) [ 1; 2; 3 ])
     = Some [ 1; 2; 3 ]);
  check
    "a pair with a third element is refused"
    (exact
       (decode_pair decode_nat decode_nat)
       (frame
          tag_pair
          (to_string emit_nat 1 ^ to_string emit_nat 2 ^ to_string emit_nat 3))
     = None)
;;

let () =
  Printf.printf "test_eff: %d checks, %d failures\n%!" !checks !failures;
  if !failures > 0 then exit 1
;;
