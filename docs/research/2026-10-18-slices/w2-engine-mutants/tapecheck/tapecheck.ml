(* tapecheck -- for every program of test_diff's three corpora and every (fuel, seed, max_len)
   test_diff draws at, the tape `E4_diff.Of (Ref).gen_tape` draws equals the one
   `E4_diff.Of (E4_engine.Make (Api_gen_inst)).gen_tape` draws.  The seeds follow test_diff's
   counters exactly: one counter over the goldens then the truth corpus, one over the Lean
   corpus. *)
open Effect4_engine
module Gen_engine = E4_engine.Make (Api_gen_inst)
module S_gen = E4_diff.Of (Gen_engine)
module S_ref = E4_diff.Of (E4_engine.Ref)

let same = ref 0
let differ = ref 0
let decisions = ref 0

let compare_one (p : Corpora.program) ~fuel ~seed ~max_len =
  let a = S_ref.gen_tape p.Corpora.eff ~fuel ~seed ~max_len
  and b = S_gen.gen_tape p.Corpora.eff ~fuel ~seed ~max_len in
  decisions := !decisions + List.length a;
  if E4_diff.show_tape a = E4_diff.show_tape b
  then incr same
  else (
    incr differ;
    Printf.printf "DIFFER %s fuel=%d seed=%d\n  ref %s\n  gen %s\n" p.Corpora.name fuel seed
      (E4_diff.show_tape a) (E4_diff.show_tape b))

let () =
  let goldens, _ = Corpora.goldens () in
  let truth, _, _ = Corpora.truth () in
  let lean, _ = Corpora.lean_corpus () in
  let bytes_seed = ref 0 in
  List.iter
    (fun p ->
       incr bytes_seed;
       let s = !bytes_seed in
       List.iter
         (fun (fuel, seed, max_len) -> compare_one p ~fuel ~seed ~max_len)
         [ 1000, 31337 + s, 64; 1000, 90210 + (s * 13), 48; 1000, 60613 + (s * 17), 32
         ; 100, 11235 + (s * 5), 24; 10, 4242 + (s * 3), 16 ])
    (goldens @ truth);
  let lean_seed = ref 0 in
  List.iter
    (fun p ->
       incr lean_seed;
       let s = !lean_seed in
       List.iter
         (fun (fuel, seed, max_len) -> compare_one p ~fuel ~seed ~max_len)
         [ 1000, 20260908 + s, 64; 1000, 51000 + (s * 3), 32; 100, 77000 + (s * 7), 16
         ; 10, 99000 + (s * 11), 8 ])
    lean;
  Printf.printf "programs: %d goldens, %d truth, %d lean; tapes compared: %d same, %d differ; %d decisions\n"
    (List.length goldens) (List.length truth) (List.length lean) !same !differ !decisions;
  exit (if !differ = 0 then 0 else 1)
