(* Independent boundary controls for the exact clock. Depends on effect4_clock only.
   Tests decimal identity, arithmetic/order beyond both JavaScript's exact integer range
   and OCaml max_int, refusal that leaves an already stored clock unchanged, and the crossing
   each refusal names (D9 of the estate review: an addition, a clock reading and an index each
   name their own crossing, not the clock's). A program's literals and a host's reply are no
   crossing of the clock's: Lean's profile support judges them at ingress (M2). *)
let get text =
  match E4_clock.of_decimal text with
  | Some value -> value
  | None -> failwith ("clock fixture rejected: " ^ text)
;;

let check condition message = if not condition then failwith message

let () =
  List.iter
    (fun text -> check (E4_clock.to_decimal (get text) = text) "decimal round trip")
    [ "0"
    ; "9007199254740993"
    ; "4611686018427387904"
    ; "12345678901234567890123456789012345678901234567890"
    ];
  List.iter
    (fun text ->
       check
         (match E4_clock.of_decimal text with
          | None -> true
          | Some _ -> false)
         "noncanonical decimal admitted")
    [ ""; "00"; "01"; "+1"; "-1"; " 1"; "1 "; "1e3"; "0x10"; "1_000" ];
  let a = get "4611686018427387904" in
  let b = E4_clock.add a (E4_clock.of_nat 1) in
  check (E4_clock.to_decimal b = "4611686018427387905") "addition overflow";
  check (E4_clock.lt a b && E4_clock.le a b && not (E4_clock.equal a b)) "order overflow";
  let saved = E4_clock.to_decimal b in
  let refused =
    try
      ignore (E4_clock.to_profile_nat b);
      false
    with
    | E4_clock.Profile_refusal _ -> true
  in
  check refused "out-of-profile observation accepted";
  check (E4_clock.to_decimal b = saved) "refusal changed stored clock";
  check (E4_clock.to_profile_nat (get "17") = 17) "small observation";
  (* On the engine's 64-bit target, pin the exact public-number edge independently
     of the arbitrary-precision storage edge above. *)
  if Sys.word_size = 64
  then (
    check
      (E4_clock.to_profile_nat (get "9007199254740991") = Int64.to_int 9007199254740991L)
      "largest exact public number rejected";
    check
      (try
         ignore (E4_clock.to_profile_nat (get "9007199254740992"));
         false
       with
       | E4_clock.Profile_refusal _ -> true)
      "first overflowing public number admitted");
  print_endline "PASS exact clock: decimal, arithmetic, order and checked observation"
;;

(* The represented multiplication uses exact storage before checked observation. *)
let () =
  let product a b = E4_clock.mul (get a) (get b) in
  check (E4_clock.to_profile_nat (product "0" "9007199254740991") = 0) "zero product";
  check (E4_clock.to_profile_nat (product "6" "7") = 42) "ordinary product";
  check
    (E4_clock.to_decimal (product "134217729" "134217729") = "18014398777917441")
    "product rounded before profile check";
  check
    (E4_clock.to_decimal (product "4611686018427387904" "2") = "9223372036854775808")
    "product saturated before profile check";
  check
    (E4_clock.to_profile_nat (product "9007199254740991" "1")
     = Int64.to_int 9007199254740991L)
    "largest profile product rejected";
  check
    (match E4_clock.to_profile_nat (product "4503599627370496" "2") with
     | _ -> false
     | exception E4_clock.Profile_refusal _ -> true)
    "first product outside the profile admitted";
  print_endline "PASS multiplication: exact product and profile refusal"
;;

(* Each refusal names its crossing (D9), and the program's profile rows answer at their edge. *)
let () =
  let refusal f =
    match f () with
    | _ -> None
    | exception E4_clock.Profile_refusal r -> Some (E4_clock.refusal_text r)
  in
  let refused_at crossing f =
    match f () with
    | _ -> false
    | exception E4_clock.Profile_refusal r -> r.E4_clock.crossing = crossing
  in
  let edge = Int64.to_int 9007199254740991L in
  check (E4_clock.profile_add (edge - 1) 1 = edge) "the largest profile sum refused";
  check (E4_clock.profile_mul 6 7 = 42) "an ordinary profile product refused";
  check
    (refused_at E4_clock.Arithmetic (fun () -> E4_clock.profile_add edge 1))
    "a sum past the profile is not refused at arithmetic";
  check
    (refused_at E4_clock.Arithmetic (fun () -> E4_clock.profile_mul 4503599627370496 2))
    "a product past the profile is not refused at arithmetic";
  check
    (refused_at E4_clock.Clock (fun () ->
       E4_clock.to_profile_nat (get "9007199254740992")))
    "a reading past the profile is not refused at the clock";
  check
    (refused_at E4_clock.Clock (fun () -> E4_clock.of_nat (-1)))
    "a negative clock is not refused at the clock";
  check
    (match E4_clock.literal "01" with
     | _ -> false
     | exception Invalid_argument _ -> true)
    "a noncanonical generated literal is not a programming error";
  check
    (E4_clock.to_decimal (E4_clock.literal "4611686018427387905") = "4611686018427387905")
    "a canonical generated literal is not read exactly";
  check
    (refusal (fun () -> E4_clock.profile_add edge 1)
     = Some "arithmetic: a sum outside the program's profile (DI-56)")
    "the arithmetic refusal's text";
  (* Red control: before D9 the refusals below answered one text, the clock's. *)
  let texts =
    List.filter_map
      refusal
      [ (fun () -> ignore (E4_clock.profile_add edge 1))
      ; (fun () -> ignore (E4_clock.to_profile_nat (get "9007199254740992")))
      ; (fun () -> E4_clock.refuse E4_clock.Index "a length past the target's capacity")
      ]
  in
  check
    (List.length texts = 3 && List.length (List.sort_uniq compare texts) = 3)
    "two crossings answer one refusal text";
  print_endline
    "PASS refusals: each names its crossing, and the profile rows answer at their edge"
;;
