(* Independent boundary controls for the exact clock. Depends on effect4_clock only.
   Tests decimal identity, arithmetic/order beyond both JavaScript's exact integer range
   and OCaml max_int, and refusal that leaves an already stored clock unchanged. *)
let get text =
  match E4_clock.of_decimal text with
  | Some value -> value
  | None -> failwith ("clock fixture rejected: " ^ text)

let check condition message = if not condition then failwith message

let () =
  List.iter
    (fun text -> check (E4_clock.to_decimal (get text) = text) "decimal round trip")
    ["0"; "9007199254740993"; "4611686018427387904";
     "12345678901234567890123456789012345678901234567890"];
  List.iter
    (fun text -> check (match E4_clock.of_decimal text with None -> true | Some _ -> false)
      "noncanonical decimal admitted")
    [""; "00"; "01"; "+1"; "-1"; " 1"; "1 "; "1e3"; "0x10"; "1_000"];
  let a = get "4611686018427387904" in
  let b = E4_clock.add a (E4_clock.of_nat 1) in
  check (E4_clock.to_decimal b = "4611686018427387905") "addition overflow";
  check (E4_clock.lt a b && E4_clock.le a b && not (E4_clock.equal a b)) "order overflow";
  let saved = E4_clock.to_decimal b in
  let refused =
    try ignore (E4_clock.to_profile_nat b); false
    with E4_clock.Profile_refusal _ -> true
  in
  check refused "out-of-profile observation accepted";
  check (E4_clock.to_decimal b = saved) "refusal changed stored clock";
  check (E4_clock.to_profile_nat (get "17") = 17) "small observation";
  (* On the engine's 64-bit target, pin the exact public-number edge independently
     of the arbitrary-precision storage edge above. *)
  if Sys.word_size = 64 then begin
    check (E4_clock.to_profile_nat (get "9007199254740991") = Int64.to_int 9007199254740991L)
      "largest exact public number rejected";
    check
      (try ignore (E4_clock.to_profile_nat (get "9007199254740992")); false
       with E4_clock.Profile_refusal _ -> true)
      "first overflowing public number admitted"
  end;
  print_endline "PASS exact clock: decimal, arithmetic, order and checked observation"

(* The represented multiplication uses exact storage before checked observation. *)
let () =
  let product a b = E4_clock.mul (get a) (get b) in
  check (E4_clock.to_profile_nat (product "0" "9007199254740991") = 0) "zero product";
  check (E4_clock.to_profile_nat (product "6" "7") = 42) "ordinary product";
  check (E4_clock.to_decimal (product "134217729" "134217729") = "18014398777917441")
    "product rounded before profile check";
  check (E4_clock.to_decimal (product "4611686018427387904" "2") = "9223372036854775808")
    "product saturated before profile check";
  check (E4_clock.to_profile_nat (product "9007199254740991" "1") = Int64.to_int 9007199254740991L)
    "largest profile product rejected";
  check (match E4_clock.to_profile_nat (product "4503599627370496" "2") with
    | _ -> false | exception E4_clock.Profile_refusal _ -> true)
    "first product outside the profile admitted";
  print_endline "PASS multiplication: exact product and profile refusal"
