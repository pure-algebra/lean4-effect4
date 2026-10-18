(* Finite host control. Production files are copied byte-for-byte by run_host_probes.py.
   Measures words allocated, not CPU time. Nothing here replaces production code. *)
let measured f x =
  Gc.full_major ();
  let allocated_words () =
    let minor, promoted, major = Gc.counters () in
    minor +. major -. promoted
  in
  let before = allocated_words () in
  let result = Sys.opaque_identity (f (Sys.opaque_identity x)) in
  Gc.minor ();
  let after = allocated_words () in
  (result, int_of_float (after -. before))

let check label n make =
  let input = List.init n make in
  let vec = Lcnf_array.of_list input in
  let old, old_words = measured Lcnf_array.to_list vec in
  let moved, moved_words = measured E4_trace.to_list vec in
  assert (old = input && moved = input);
  let sibling = Lcnf_array.push vec (make n) in
  assert (Lcnf_array.to_list vec = input);
  assert (E4_trace.to_list sibling = input @ [make n]);
  Printf.printf "{\"kind\":%S,\"n\":%d,\"old_words\":%d,\"trace_words\":%d,\"equal\":true,\"retained_snapshot\":true}\n%!"
    label n old_words moved_words

let () =
  Printf.printf "{\"ocaml_version\":%S,\"word_size\":%d}\n%!" Sys.ocaml_version Sys.word_size;
  List.iter (fun n -> check "int" n Fun.id) [0; 1; 255; 256; 257; 6003; 1_000_000];
  List.iter (fun n -> check "float" n float_of_int) [1; 257; 6003]
