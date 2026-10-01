(* Numbers seat, probe 8: what one natural addition costs under the three OCaml options.

   A measurement, not a gate. Three loops of the same length accumulate a sum:
     raw      `a + b` (today's Nat.add row, Translate.lean:162)
     checked  `if a > bound - b then raise ... else a + b` (DI-56's refusal, checked before)
     zarith   `Z.add a b` (the exact carrier the clock already uses, ocaml/clock/e4_clock.ml)
   Each loop keeps its sum small enough that nothing overflows, so all three do the same
   arithmetic. The median of five runs is printed, in nanoseconds per addition.
   Depends on zarith and unix. Writes nothing. *)

exception Outside_profile

let n = 100_000_000
let bound = max_int

let time f =
  let runs = List.init 5 (fun _ ->
      let t0 = Unix.gettimeofday () in
      let r = f () in
      let t1 = Unix.gettimeofday () in
      ignore (Sys.opaque_identity r);
      (t1 -. t0) *. 1e9 /. float_of_int n) in
  List.nth (List.sort compare runs) 2

let raw () =
  let acc = ref 0 in
  for i = 1 to n do acc := (!acc + (i land 1023)) land 0xFFFFFFF done;
  !acc

let checked_add a b = if a > bound - b then raise Outside_profile else a + b

let checked () =
  let acc = ref 0 in
  for i = 1 to n do acc := (checked_add !acc (i land 1023)) land 0xFFFFFFF done;
  !acc

let zarith () =
  let acc = ref Z.zero in
  let mask = Z.of_int 0xFFFFFFF in
  for i = 1 to n do acc := Z.logand (Z.add !acc (Z.of_int (i land 1023))) mask done;
  Z.to_int !acc

let zarith_no_mask () =
  (* the same additions without the mask, so the only Zarith call per step is Z.add *)
  let acc = ref Z.zero in
  let step = Z.of_int 3 in
  for _ = 1 to n do acc := Z.add !acc step done;
  Z.to_int !acc

let raw_no_mask () =
  let acc = ref 0 in
  for _ = 1 to n do acc := !acc + 3 done;
  !acc

let checked_no_mask () =
  let acc = ref 0 in
  for _ = 1 to n do acc := checked_add !acc 3 done;
  !acc

let () =
  assert (raw () = checked () && raw () = zarith ());
  assert (raw_no_mask () = checked_no_mask () && raw_no_mask () = zarith_no_mask ());
  Printf.printf "additions per loop: %d (median of 5 runs, ns per addition)\n" n;
  Printf.printf "  raw      %.2f   raw, add only      %.2f\n" (time raw) (time raw_no_mask);
  Printf.printf "  checked  %.2f   checked, add only  %.2f\n" (time checked) (time checked_no_mask);
  Printf.printf "  zarith   %.2f   zarith, add only   %.2f\n" (time zarith) (time zarith_no_mask)
