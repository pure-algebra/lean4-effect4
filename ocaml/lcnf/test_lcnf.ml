(* test_lcnf.ml -- the runtime library's own checks: each property of lcnf_string.mli,
   lcnf_nat.mli, lcnf_crossing.mli, lcnf_list.mli and lcnf_array.mli at chosen points, with
   Lean's answer where the point is inside the row's domain, and a red control beside each claim
   that shows what the claim rules out. The chunked vector's checks came here from engine/test/test_log.ml with the vector
   itself. Finite evaluations; no theorem is restated.

   Depends on: effect4_lcnf, Zarith.

   Run: cd ocaml && dune test lcnf *)

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures
;;

let raises_division f =
  match f () with
  | _ -> false
  | exception Division_by_zero -> true
;;

(* S1-S3: strings are their UTF-8 bytes. "é" is U+00E9 and "🙂" U+1F642. *)
let strings () =
  let s = "é🙂\n" in
  check
    "S1 utf8_bytes is Lean's String.toUTF8 on a string outside ASCII"
    (Lcnf_array.to_list (Lcnf_string.utf8_bytes s) = [ 195; 169; 240; 159; 153; 130; 10 ]);
  check
    "S1 utf8_bytes of the empty string is empty"
    (Lcnf_array.is_empty (Lcnf_string.utf8_bytes ""));
  check
    "S2 utf8_length counts scalar values, as Lean's String.length: 2 for \"é🙂\""
    (Lcnf_string.utf8_length "é🙂" = 2
     && Lcnf_string.utf8_length "" = 0
     && Lcnf_string.utf8_length "abc" = 3);
  (* red control: the byte count is another answer, so S2 tells the two apart *)
  check
    "S2 (red control): OCaml's String.length counts 6 bytes in \"é🙂\""
    (String.length "é🙂" = 6);
  check
    "S3 of_code_points builds the string of its scalar values"
    (Lcnf_string.of_code_points [ 0xE9; 0x1F642; 10 ] = s);
  check
    "S3 of_utf8_bytes inverts utf8_bytes"
    (Lcnf_string.of_utf8_bytes (Lcnf_string.utf8_bytes s) = s
     && Lcnf_array.to_list
          (Lcnf_string.utf8_bytes
             (Lcnf_string.of_utf8_bytes (Lcnf_array.of_list [ 0; 127; 128; 255 ])))
        = [ 0; 127; 128; 255 ]);
  (* red control: a code point is not a byte; reading the scalar values as bytes is refused by
     Char.chr, so the two inverses are not interchangeable *)
  check
    "S3 (red control): a code point above 255 is no byte"
    (match Lcnf_string.of_utf8_bytes (Lcnf_array.of_list [ 0x1F642 ]) with
     | _ -> false
     | exception Invalid_argument _ -> true)
;;

(* N1-N5 and X1-X2: naturals are exact (`Z.t`, M4), and a narrowing to the target's `int` refuses
   at its named crossing. Lean's answer is the exact one at every point below. *)
let refused crossing f =
  match f () with
  | _ -> false
  | exception Lcnf_crossing.Refused why -> why.Lcnf_crossing.crossing = crossing
;;

let naturals () =
  let z = Z.of_int in
  let past = Z.succ (z max_int) in
  let huge = Z.pow (z 2) 100 in
  check
    "N1 sub is a - b at or above b, and stops at zero below: 5 - 3, 3 - 5, 2^100 - 1"
    (Z.equal (Lcnf_nat.sub (z 5) (z 3)) (z 2)
     && Z.equal (Lcnf_nat.sub (z 3) (z 5)) Z.zero
     && Z.equal (Lcnf_nat.sub huge Z.one) (Z.pred huge)
     && Z.equal (Lcnf_nat.pred Z.zero) Z.zero
     && Z.equal (Lcnf_nat.pred (z 7)) (z 6));
  (* red control: Zarith's own difference goes below zero, which no natural is *)
  check "N1 (red control): Z.sub 3 5 is negative" (Z.sign (Z.sub (z 3) (z 5)) < 0);
  check
    "N2 div and rem are exact, and 0 and a at a zero divisor: 17 / 5, 17 mod 5, 17 / 0, \
     17 mod 0"
    (Z.equal (Lcnf_nat.div (z 17) (z 5)) (z 3)
     && Z.equal (Lcnf_nat.rem (z 17) (z 5)) (z 2)
     && Z.equal (Lcnf_nat.div (z 17) Z.zero) Z.zero
     && Z.equal (Lcnf_nat.rem (z 17) Z.zero) (z 17)
     && Z.equal (Lcnf_nat.div huge (z 2)) (Z.pow (z 2) 99));
  (* red control: Zarith's own division raises at a zero divisor *)
  check
    "N2 (red control): Z.div 17 0 raises Division_by_zero"
    (raises_division (fun () -> Z.div (z 17) Z.zero));
  check
    "N3 pow and the shifts are exact past max_int: 2^64, 3^40, 1 lsl 100, 2^100 lsr 99, \
     0^0"
    (Z.equal (Lcnf_nat.pow (z 2) (z 64)) (Z.shift_left Z.one 64)
     && Z.equal (Lcnf_nat.pow (z 3) (z 40)) (Z.of_string "12157665459056928801")
     && Z.equal (Lcnf_nat.pow Z.zero Z.zero) Z.one
     && Z.equal (Lcnf_nat.shift_left Z.one (z 100)) huge
     && Z.equal (Lcnf_nat.shift_right huge (z 99)) (z 2));
  (* red control: the target's own int wraps 2^64 to zero, which made `Val.wf`'s `< 2 ^ 64` read
     as `< 0` before M4 *)
  let rec raw a b = if b = 0 then 1 else a * raw a (b - 1) in
  check "N3 (red control): the int power reads 2^64 as 0" (raw 2 64 = 0);
  check
    "N3 an exponent or a shift past max_int is refused at the arithmetic crossing"
    (refused Lcnf_crossing.Arithmetic (fun () -> Lcnf_nat.pow (z 2) past)
     && refused Lcnf_crossing.Arithmetic (fun () -> Lcnf_nat.shift_left Z.one past)
     && refused Lcnf_crossing.Arithmetic (fun () -> Lcnf_nat.shift_right huge past));
  check
    "N4 to_index_exn and to_shift_exn are the natural as an int when it fits"
    (Lcnf_nat.to_index_exn (z 7) = 7
     && Lcnf_nat.to_index_exn (z max_int) = max_int
     && Lcnf_nat.to_shift_exn (z 63) = 63);
  check
    "N4 a natural past max_int is refused, at the index and at the arithmetic crossing"
    (refused Lcnf_crossing.Index (fun () -> Lcnf_nat.to_index_exn past)
     && refused Lcnf_crossing.Arithmetic (fun () -> Lcnf_nat.to_shift_exn past));
  (* red control: Zarith's own conversion raises a different exception, which names no crossing *)
  check
    "N4 (red control): Z.to_int past max_int raises Z.Overflow"
    (match Z.to_int past with
     | _ -> false
     | exception Z.Overflow -> true);
  check
    "N5 index_add and index_sub are the int sum and difference inside the index range"
    (Lcnf_nat.index_add 3 4 = 7
     && Lcnf_nat.index_add (max_int - 1) 1 = max_int
     && Lcnf_nat.index_sub 7 3 = 4
     && Lcnf_nat.index_sub 3 3 = 0);
  check
    "N5 a sum past max_int and a difference below zero are refused at the index crossing"
    (refused Lcnf_crossing.Index (fun () -> Lcnf_nat.index_add max_int 1)
     && refused Lcnf_crossing.Index (fun () -> Lcnf_nat.index_sub 3 4));
  (* red control: the int sum wraps below zero at the same point *)
  check "N5 (red control): max_int + 1 wraps below zero" (max_int + 1 < 0);
  check
    "X1 refuse raises Refused with its crossing and its reason"
    (match Lcnf_crossing.refuse Lcnf_crossing.Index "a reason" with
     | () -> false
     | exception Lcnf_crossing.Refused { crossing = Lcnf_crossing.Index; reason } ->
       String.equal reason "a reason");
  check
    "X2 refusal_text names the crossing as OCaml5.Lcnf.Crossing prints it"
    (String.equal
       (Lcnf_crossing.refusal_text { crossing = Lcnf_crossing.Arithmetic; reason = "r" })
       "arithmetic: r"
     && String.equal (Lcnf_crossing.crossing_name Lcnf_crossing.Index) "index")
;;

(* L1-L2: membership through an asymmetric instance, `a == b` read as `a < b`. *)
let lists () =
  let less a b = a < b in
  check
    "L1 contains hands the target first: [3].contains 2 under a < b is 2 < 3"
    (Lcnf_list.contains less [ 3 ] 2 && not (Lcnf_list.contains less [ 2 ] 3));
  check
    "L1 contains answers false at the end of the list"
    (not (Lcnf_list.contains less [] 2));
  (* red control: the element-first order answers the opposite on the same input *)
  check
    "L1 (red control): the element-first order answers false where contains answers true"
    (not (List.exists (fun e -> less e 2) [ 3 ]));
  let dividing a b = a / b = 1 in
  check
    "L2 an exception of the instance passes through"
    (raises_division (fun () -> Lcnf_list.contains dividing [ 0 ] 2));
  check
    "L2 the scan stops at the first true and never reaches a later zero"
    (Lcnf_list.contains dividing [ 2; 0 ] 2)
;;

(* V1-V6: the chunked vector against the list it stands for. Row i of every vector below is
   distinct, so an order error cannot hide. *)
let row_at i = (7 * i) + 3

let rec push_rows v from upto =
  if from >= upto then v else push_rows (Lcnf_array.push v (row_at from)) (from + 1) upto
;;

(* The reference: the indexed answer, `get_exn` at every index in order. *)
let indexed v = List.init (Lcnf_array.length v) (Lcnf_array.get_exn v)

let raises_invalid f =
  match f () with
  | _ -> false
  | exception Invalid_argument _ -> true
;;

let arrays () =
  let c = Lcnf_array.chunk_size in
  check "chunk_size is the named constant 256" (c = 256);
  (* The boundary lengths of the carrier, and one length of several chunks with a partial tail.
     The two halves a length exercises: frozen chunks below (n / c) * c, the open tail above. *)
  let lengths =
    [ 0, "0"
    ; 1, "1"
    ; c - 1, "chunk_size - 1"
    ; c, "chunk_size"
    ; c + 1, "chunk_size + 1"
    ; 2 * c, "2 * chunk_size"
    ; (5 * c) + 37, "5 * chunk_size + 37"
    ]
  in
  let vec n = push_rows Lcnf_array.empty 0 n in
  List.iter
    (fun (n, label) ->
       let v = vec n in
       check
         (Printf.sprintf "V3 to_list = the indexed answer = push order, length %s" label)
         (Lcnf_array.to_list v = indexed v
          && indexed v = List.init n row_at
          && Lcnf_array.length v = n))
    lengths;
  (* Red controls. Each is a wrong walk built from the same fold, and each must disagree with the
     reference exactly where the claim says it can. Dropping `List.rev` is caught at every length
     of two rows or more. A walk of the frozen chunks alone is caught exactly at the lengths with
     an open tail, and a walk of the tail alone exactly at the lengths with a frozen chunk, so the
     lengths above exercise both halves of the carrier. *)
  let caught_at wrong =
    List.filter_map
      (fun (n, label) ->
         let v = vec n in
         if wrong n v <> indexed v then Some label else None)
      lengths
  in
  let labels ns = List.map (fun n -> List.assoc n lengths) ns in
  let reversed _ v = Lcnf_array.fold v ~init:[] ~f:(fun _ x acc -> x :: acc) in
  let only keep n v =
    let tail_from = n / c * c in
    List.rev
      (Lcnf_array.fold v ~init:[] ~f:(fun i x acc ->
         if keep i tail_from then x :: acc else acc))
  in
  check
    "V3 (red control): the fold without List.rev is caught at every length of 2 rows or \
     more"
    (caught_at reversed = labels [ c - 1; c; c + 1; 2 * c; (5 * c) + 37 ]);
  check
    "V3 (red control): the frozen chunks alone are caught exactly at the lengths with an \
     open tail"
    (caught_at (only (fun i t -> i < t)) = labels [ 1; c - 1; c + 1; (5 * c) + 37 ]);
  check
    "V3 (red control): the open tail alone is caught exactly at the lengths with a \
     frozen chunk"
    (caught_at (only (fun i t -> i >= t)) = labels [ c; c + 1; 2 * c; (5 * c) + 37 ]);
  (* V2 and V5: dense reads, and the proved-index operations refuse outside the range. *)
  let n = (5 * c) + 37 in
  let v = vec n in
  check
    "V2 get is Some on [0, length) and None outside it"
    (List.for_all (fun i -> Lcnf_array.get v i = Some (row_at i)) (List.init n Fun.id)
     && Lcnf_array.get v (-1) = None
     && Lcnf_array.get v n = None
     && Lcnf_array.get Lcnf_array.empty 0 = None);
  check
    "V5 get_exn and set_exn raise Invalid_argument outside [0, length)"
    (raises_invalid (fun () -> Lcnf_array.get_exn v n)
     && raises_invalid (fun () -> Lcnf_array.get_exn v (-1))
     && raises_invalid (fun () -> Lcnf_array.set_exn v n 0)
     && raises_invalid (fun () -> Lcnf_array.set_exn Lcnf_array.empty 0 0));
  (* set_exn at the first and last element of a frozen chunk and inside the open tail: the answer
     is the list with that element replaced, and the argument still answers its own rows. *)
  let replaced i x = List.mapi (fun k r -> if k = i then x else r) (List.init n row_at) in
  List.iter
    (fun (i, label) ->
       let w = Lcnf_array.set_exn v i (-9) in
       check
         (Printf.sprintf
            "V1 set_exn at %s answers the replaced list and leaves its argument"
            label)
         (Lcnf_array.to_list w = replaced i (-9)
          && indexed w = replaced i (-9)
          && Lcnf_array.to_list v = List.init n row_at
          && Lcnf_array.length w = n))
    [ 0, "index 0"
    ; c - 1, "the end of the first chunk"
    ; c, "the start of a chunk"
    ; n - 1, "the open tail's newest element"
    ; 5 * c, "the open tail's oldest element"
    ];
  (* V4, rule 8: two sets on one value at one index each keep their own element, and so does the
     value both came from. The red control reads each sibling against the other's element. *)
  let reads w rows = Lcnf_array.to_list w = rows && indexed w = rows in
  List.iter
    (fun i ->
       let a = Lcnf_array.set_exn v i (-1)
       and b = Lcnf_array.set_exn v i (-2) in
       check
         (Printf.sprintf
            "V4 sibling sets at index %d each keep their element, and the base its row"
            i)
         (reads a (replaced i (-1))
          && reads b (replaced i (-2))
          && reads v (List.init n row_at));
       check
         (Printf.sprintf
            "V4 (red control): each sibling set at index %d read against the other's is \
             caught"
            i)
         ((not (reads a (replaced i (-2)))) && not (reads b (replaced i (-1)))))
    [ 3; n - 2 ];
  (* replicate: n copies at the boundary lengths. Its full chunks share one array, so a set on one
     chunk must leave every other chunk, and the replicated value, unchanged (V4). *)
  List.iter
    (fun (m, label) ->
       check
         (Printf.sprintf "replicate %s copies is the list of them" label)
         (Lcnf_array.to_list (Lcnf_array.replicate m 4) = List.init m (fun _ -> 4)
          && Lcnf_array.length (Lcnf_array.replicate m 4) = m))
    lengths;
  check
    "replicate of a negative count is empty"
    (Lcnf_array.is_empty (Lcnf_array.replicate (-3) 4));
  let r = Lcnf_array.replicate ((3 * c) + 5) 0 in
  let r' = Lcnf_array.set_exn r 10 1 in
  check
    "V4 a set in one replicated chunk leaves the chunks that shared its array, and the \
     original"
    (Lcnf_array.get r' 10 = Some 1
     && Lcnf_array.get r' (c + 10) = Some 0
     && Lcnf_array.get r' ((2 * c) + 10) = Some 0
     && Lcnf_array.get r 10 = Some 0
     && Lcnf_array.to_list r = List.init ((3 * c) + 5) (fun _ -> 0));
  (* V4 by pushes: two pushes onto one shared prefix, and two longer branches that each turn the
     shared tail into a chunk of their own, all made before any is read. *)
  let siblings p =
    let base = vec p in
    let a = Lcnf_array.push base (-1)
    and b = Lcnf_array.push base (-2) in
    base, a, b, push_rows a (p + 1) (p + c + 1), push_rows b (p + 1) (p + c + 1)
  in
  let prefix p = List.init p row_at in
  let branch p = List.init c (fun k -> row_at (p + 1 + k)) in
  List.iter
    (fun (p, label) ->
       let base, a, b, a_long, b_long = siblings p in
       check
         (Printf.sprintf
            "V4 siblings on a shared prefix of length %s each read their own rows"
            label)
         (reads a (prefix p @ [ -1 ])
          && reads b (prefix p @ [ -2 ])
          && reads a_long ((prefix p @ [ -1 ]) @ branch p)
          && reads b_long ((prefix p @ [ -2 ]) @ branch p)
          && reads base (prefix p)))
    lengths;
  check
    "V4 (red control): each pushed sibling read against the other's rows is caught"
    (List.for_all
       (fun (p, _) ->
          let _, a, b, a_long, b_long = siblings p in
          (not (reads a (prefix p @ [ -2 ])))
          && (not (reads b (prefix p @ [ -1 ])))
          && (not (reads a_long ((prefix p @ [ -2 ]) @ branch p)))
          && not (reads b_long ((prefix p @ [ -1 ]) @ branch p)))
       lengths);
  (* The list conversions and the folds. *)
  check
    "of_list and append_list are pushes in list order; with_capacity is empty"
    (Lcnf_array.to_list (Lcnf_array.of_list (List.init n row_at)) = List.init n row_at
     && Lcnf_array.to_list
          (Lcnf_array.append_list (vec c) (List.init 9 (fun k -> row_at (c + k))))
        = List.init (c + 9) row_at
     && Lcnf_array.is_empty (Lcnf_array.with_capacity 64));
  check
    "fold_left is List.fold_left over the elements in order"
    (Lcnf_array.fold_left (fun acc x -> x :: acc) [] v = List.rev (List.init n row_at));
  check
    "slice is the half-open range, clamped"
    (Lcnf_array.slice v ~from:300 ~upto:303 = [ row_at 300; row_at 301; row_at 302 ]
     && Lcnf_array.slice v ~from:(-4) ~upto:2 = [ row_at 0; row_at 1 ]
     && Lcnf_array.slice v ~from:9 ~upto:3 = [])
;;

let () =
  print_endline "== effect4_lcnf: strings, naturals, membership and arrays ==";
  strings ();
  naturals ();
  lists ();
  arrays ();
  Printf.printf
    "== %s: %d failure(s) in %d checks ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures
    !checks;
  exit (if !failures = 0 then 0 else 1)
;;
