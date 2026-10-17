(* test_lcnf.ml -- the runtime library's own checks: each property of lcnf_string.mli,
   lcnf_nat.mli and lcnf_list.mli at chosen points, with Lean's answer where the point is inside
   the row's domain, and a red control beside each claim that shows what the claim rules out.
   Finite evaluations; no theorem is restated.

   Depends on: effect4_lcnf.

   Run: cd ocaml && dune test lcnf *)

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let raises_division f = match f () with _ -> false | exception Division_by_zero -> true

(* S1-S3: strings are their UTF-8 bytes. "é" is U+00E9 and "🙂" U+1F642. *)
let strings () =
  let s = "é🙂\n" in
  check "S1 utf8_bytes is Lean's String.toUTF8 on a string outside ASCII"
    (Lcnf_string.utf8_bytes s = [ 195; 169; 240; 159; 153; 130; 10 ]);
  check "S1 utf8_bytes of the empty string is empty" (Lcnf_string.utf8_bytes "" = []);
  check "S2 utf8_length counts scalar values, as Lean's String.length: 2 for \"é🙂\""
    (Lcnf_string.utf8_length "é🙂" = 2 && Lcnf_string.utf8_length "" = 0
    && Lcnf_string.utf8_length "abc" = 3);
  (* red control: the byte count is another answer, so S2 tells the two apart *)
  check "S2 (red control): OCaml's String.length counts 6 bytes in \"é🙂\""
    (String.length "é🙂" = 6);
  check "S3 of_code_points builds the string of its scalar values"
    (Lcnf_string.of_code_points [ 0xE9; 0x1F642; 10 ] = s);
  check "S3 of_utf8_bytes inverts utf8_bytes"
    (Lcnf_string.of_utf8_bytes (Lcnf_string.utf8_bytes s) = s
    && Lcnf_string.utf8_bytes (Lcnf_string.of_utf8_bytes [ 0; 127; 128; 255 ]) = [ 0; 127; 128; 255 ]);
  (* red control: a code point is not a byte; reading the scalar values as bytes is refused by
     Char.chr, so the two inverses are not interchangeable *)
  check "S3 (red control): a code point above 255 is no byte"
    (match Lcnf_string.of_utf8_bytes [ 0x1F642 ] with
     | _ -> false
     | exception Invalid_argument _ -> true)

(* N1-N3: naturals stopped at max_int. Lean's answer is exact; below max_int the helper's is
   the same number. *)
let naturals () =
  let half = max_int / 2 in
  check "N1 mul is the product below max_int: 3 * 5, 0 * max_int, 2 * (max_int / 2)"
    (Lcnf_nat.mul 3 5 = 15 && Lcnf_nat.mul 0 max_int = 0 && Lcnf_nat.mul max_int 0 = 0
    && Lcnf_nat.mul 2 half = max_int - 1);
  check "N1 mul stops at max_int above it: 2 * (max_int / 2 + 1) and max_int * 2"
    (Lcnf_nat.mul 2 (half + 1) = max_int && Lcnf_nat.mul max_int 2 = max_int);
  (* red control: OCaml's raw product wraps to a negative word at the same point *)
  check "N1 (red control): the raw product 2 * (max_int / 2 + 1) wraps below zero"
    (2 * (half + 1) < 0);
  check "N2 pow is the power below max_int: 2^10, 2^61, 3^39, 0^0, 0^5, 1^1000"
    (Lcnf_nat.pow 2 10 = 1024 && Lcnf_nat.pow 2 61 = 2305843009213693952
    && Lcnf_nat.pow 3 39 = 4052555153018976267 && Lcnf_nat.pow 0 0 = 1
    && Lcnf_nat.pow 0 5 = 0 && Lcnf_nat.pow 1 1000 = 1);
  check "N2 pow stops at max_int above it: 2^62, 2^64, 3^40"
    (Lcnf_nat.pow 2 62 = max_int && Lcnf_nat.pow 2 64 = max_int && Lcnf_nat.pow 3 40 = max_int);
  (* red control: a wrapping power reads 2^64 as 0, which would make Val.wf's `< 2 ^ 64` false
     for every value *)
  let rec raw a b = if b = 0 then 1 else a * raw a (b - 1) in
  check "N2 (red control): a wrapping power reads 2^64 as 0" (raw 2 64 = 0);
  check "N3 shift_left is a * 2^b below max_int: 3 lsl 2, 1 lsl 61, 0 lsl 100"
    (Lcnf_nat.shift_left 3 2 = 12 && Lcnf_nat.shift_left 1 61 = 2305843009213693952
    && Lcnf_nat.shift_left 0 100 = 0);
  check "N3 shift_left stops at max_int above it: 1 lsl 62, 3 lsl 61, 3 lsl 62"
    (Lcnf_nat.shift_left 1 62 = max_int && Lcnf_nat.shift_left 3 61 = max_int
    && Lcnf_nat.shift_left 3 62 = max_int);
  (* red control: stopping the power alone still wraps the product *)
  check "N3 (red control): 3 * 2^61 with only the power stopped wraps below zero"
    (3 * Lcnf_nat.pow 2 61 < 0)

(* L1-L2: membership through an asymmetric instance, `a == b` read as `a < b`. *)
let lists () =
  let less a b = a < b in
  check "L1 contains hands the target first: [3].contains 2 under a < b is 2 < 3"
    (Lcnf_list.contains less [ 3 ] 2 && not (Lcnf_list.contains less [ 2 ] 3));
  check "L1 contains answers false at the end of the list" (not (Lcnf_list.contains less [] 2));
  (* red control: the element-first order answers the opposite on the same input *)
  check "L1 (red control): the element-first order answers false where contains answers true"
    (not (List.exists (fun e -> less e 2) [ 3 ]));
  let dividing a b = a / b = 1 in
  check "L2 an exception of the instance passes through"
    (raises_division (fun () -> Lcnf_list.contains dividing [ 0 ] 2));
  check "L2 the scan stops at the first true and never reaches a later zero"
    (Lcnf_list.contains dividing [ 2; 0 ] 2)

let () =
  print_endline "== effect4_lcnf: strings, naturals and membership ==";
  strings ();
  naturals ();
  lists ();
  Printf.printf "== %s: %d failure(s) in %d checks ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures !checks;
  exit (if !failures = 0 then 0 else 1)
