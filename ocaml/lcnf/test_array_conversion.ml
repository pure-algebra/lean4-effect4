(* K0 list conversion controls and allocation observations.
   Depends on Lcnf_array and the OCaml allocation counters.
   Properties, tested in this file:
   - Values match literal lists, including the injected capacity fallback.
   - Retained siblings keep their values after conversion.
   - A known list calibrates the allocation counter before measurements.
   Allocation observations apply only to the tested carriers and sizes. *)

(* Flush pending minor allocations before each reading. *)
let allocated_words () =
  Gc.minor ();
  let minor, promoted, major = Gc.counters () in
  minor +. major -. promoted
;;

let words f =
  Gc.full_major ();
  let before = allocated_words () in
  let value = f () in
  let after = allocated_words () in
  value, after -. before
;;

let check_carrier name equal make n =
  let expected = List.init n make in
  let vector = Lcnf_array.of_list expected in
  let reference () =
    List.rev (Lcnf_array.fold vector ~init:[] ~f:(fun _ x acc -> x :: acc))
  in
  let original, old_words = words reference in
  let normal, normal_words = words (fun () -> Lcnf_array.to_list vector) in
  let fallback, fallback_words =
    words (fun () -> Lcnf_array.to_list_with_capacity ~capacity:3 vector)
  in
  assert (List.equal equal expected original);
  assert (List.equal equal expected normal);
  assert (List.equal equal expected fallback);
  if n > 1 then assert (not (List.equal equal (List.rev expected) normal));
  let sibling = Lcnf_array.push vector (make (n + 1)) in
  ignore (Lcnf_array.to_list sibling);
  assert (List.equal equal expected (Lcnf_array.to_list vector));
  Printf.printf
    "PASS conversion carrier=%s size=%d fold_words=%.0f array_words=%.0f \
     fallback_words=%.0f\n"
    name
    n
    old_words
    normal_words
    fallback_words
;;

let () =
  let calibration, measured = words (fun () -> List.init 10000 Fun.id) in
  assert (List.length calibration = 10000);
  assert (measured >= 30000. && measured < 30100.);
  Printf.printf
    "PASS allocation calibration list_cells=10000 words=%.0f expected_payload_words=30000\n"
    measured;
  List.iter
    (fun n ->
       check_carrier "int" Int.equal (fun x -> x) n;
       check_carrier "float" Float.equal (fun x -> float_of_int x +. 0.25) n)
    [ 0; 1; 3; 4; 255; 256; 257; 10000; 100000 ];
  let original = Lcnf_array.of_list [ 11; 12; 13; 14 ] in
  assert (
    List.equal
      Int.equal
      [ 11; 12; 13; 14 ]
      (Lcnf_array.to_list_with_capacity ~capacity:(-1) original));
  print_endline "PASS capacity fallback, reverse-order red control, retained siblings"
;;
