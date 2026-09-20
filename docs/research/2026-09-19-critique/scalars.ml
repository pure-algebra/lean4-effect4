(* Finite boundary probes, not a whole-machine simulation proof.
   Actual carrier modules are loaded from the audited checkout. Arithmetic expressions
   marked Translate below transcribe src/OCaml5/Lcnf/Translate.lean exactly. *)
#mod_use "e4_nat.ml";;
#mod_use "e4_table.ml";;
#mod_use "e4_memo.ml";;
#mod_use "e4_memo_list.ml";;
#mod_use "e4_log.ml";;
#mod_use "e4_ppath.ml";;
#mod_use "e4_fibers_view.ml";;

let must label condition = if not condition then failwith label
let option_int = function None -> "null" | Some n -> string_of_int n
let list_int xs = "[" ^ String.concat "," (List.map string_of_int xs) ^ "]"

let () =
  must "native 63-bit profile" (Sys.int_size = 63);
  let m = max_int in
  let x = m - 1 in
  let exact_intermediate = Int64.mul (Int64.of_int x) 2L in
  let exact_result = Int64.div exact_intermediate 2L in
  (* Translate Nat.mul, line 161, followed by Nat.div line 168. *)
  let translated_product = if x = 0 then 0 else if 2 > m / x then m else x * 2 in
  let translated_result = translated_product / 2 in
  must "bounded inputs and result, overflowing intermediate" (x < m && exact_result = Int64.of_int x && translated_result <> x);
  let translated_succ = m + 1 in
  let library_succ = E4_nat.succ m in
  must "Nat.succ wrapping versus saturating" (translated_succ < 0 && library_succ = m);
  (* Source m < 2^64 is true. Translate clamps the large literal to max_int. *)
  let translated_bound_guard = m < m in
  must "clamped bound excludes representable endpoint" (not translated_bound_guard);
  Printf.printf "{\"probe\":\"scalar\",\"int_size\":%d,\"max_int\":\"%d\",\"input\":\"%d\",\"exact_intermediate\":\"%Ld\",\"exact_result\":\"%Ld\",\"translated_result\":\"%d\",\"translated_succ_max\":\"%d\",\"library_succ_max\":\"%d\",\"clamped_2pow64_guard_at_max\":%b}\n"
    Sys.int_size m x exact_intermediate exact_result translated_result translated_succ library_succ translated_bound_guard;

  let l0 = E4_memo_list.empty in
  let l1 = E4_memo_list.insert [2] 10 l0 in
  let l2 = E4_memo_list.insert [1] 20 l1 in
  let l3 = E4_memo_list.insert [2] 99 l2 in
  let c0 = E4_memo.empty in
  let c1 = E4_memo.insert [2] 10 c0 in
  let c2 = E4_memo.insert [1] 20 c1 in
  let c3 = E4_memo.insert [2] 99 c2 in
  must "first binding preserved" (E4_memo.find_opt [2] c3 = Some 10 && E4_memo_list.find_opt [2] l3 = Some 10);
  let l4 = E4_memo_list.update [2] (fun n -> n + 1) l3 in
  let c4 = E4_memo.update [2] (fun n -> n + 1) c3 in
  must "pure update congruence" (E4_memo_list.bindings l4 = E4_memo.bindings c4);
  let ld = E4_memo_list.delete [2] l4 in
  let cd = E4_memo.delete [2] c4 in
  must "delete all duplicates" (E4_memo_list.find_opt [2] ld = None && E4_memo.find_opt [2] cd = None);
  let lcalls = ref 0 and ccalls = ref 0 in
  ignore (E4_memo_list.update [2] (fun n -> incr lcalls; n) l3);
  ignore (E4_memo.update [2] (fun n -> incr ccalls; n) c3);
  must "effectful callback invalidates quotient" (!lcalls = 2 && !ccalls = 1);
  Printf.printf "{\"probe\":\"memo\",\"raw_length\":%d,\"map_cardinal\":%d,\"raw_values\":%s,\"map_values\":%s,\"first_binding\":%s,\"after_delete\":%s,\"list_update_callback_calls\":%d,\"map_update_callback_calls\":%d}\n"
    (E4_memo_list.raw_length l3) (E4_memo.cardinal c3)
    (list_int (List.map snd (E4_memo_list.raw l3))) (list_int (List.map snd (E4_memo.bindings c3)))
    (option_int (E4_memo.find_opt [2] c3)) (option_int (E4_memo.find_opt [2] cd)) !lcalls !ccalls;

  let old = E4_table.singleton 0 10 in
  let next = E4_table.set 0 20 old in
  let absent = E4_table.set 99 30 old in
  must "immutable table snapshot" (E4_table.find_opt 0 old = Some 10 && E4_table.find_opt 0 next = Some 20 && absent == old);
  let old_log = E4_log.Vec.of_list (List.init 255 Fun.id) in
  let full_log = E4_log.Vec.append old_log 255 in
  let later_log = E4_log.Vec.append full_log 256 in
  must "frozen chunk snapshots" (E4_log.Vec.length old_log = 255 && E4_log.Vec.get old_log 255 = None && E4_log.Vec.get full_log 255 = Some 255 && E4_log.Vec.get full_log 256 = None && E4_log.Vec.get later_log 256 = Some 256);
  let payload = ref 1 in
  let alias_old = E4_table.singleton 0 payload in
  let alias_next = E4_table.add 1 payload alias_old in
  payload := 2;
  let snapshot_payload = Option.map (!) (E4_table.find_opt 0 alias_old) in
  must "persistent spine does not freeze payload" (snapshot_payload = Some 2 && E4_table.cardinal alias_next = 2);
  Printf.printf "{\"probe\":\"persistence\",\"old_value\":%s,\"new_value\":%s,\"absent_set_same_object\":%b,\"old_log_length\":%d,\"full_log_length\":%d,\"later_log_length\":%d,\"aliased_mutable_payload_in_old_snapshot\":%s}\n"
    (option_int (E4_table.find_opt 0 old)) (option_int (E4_table.find_opt 0 next)) (absent == old)
    (E4_log.Vec.length old_log) (E4_log.Vec.length full_log) (E4_log.Vec.length later_log) (option_int snapshot_payload);

  (* Cached views are indexed by a FIXED resolver/projection, even though their OCaml
     signatures accept that function again at each call. *)
  let child_a n i = Some (n + i) and child_b n i = Some (n + i + 100) in
  let path = E4_ppath.snoc child_a (E4_ppath.make 0) 1 in
  let cached = E4_ppath.node child_b path in
  let recomputed = E4_ppath.walk child_b (E4_ppath.root path) (E4_ppath.to_list path) in
  must "resolver must be fixed" (cached = Some 1 && recomputed = Some 101);
  let view_a v = if v >= 0 then Some v else None in
  let view_b v = Some (-v) in
  let f0 = E4_fibers_view.add ~exit_of:view_a 0 7 E4_fibers_view.empty in
  let f1 = E4_fibers_view.add ~exit_of:view_b 1 9 f0 in
  let mixed = List.map snd (E4_fibers_view.completed f1) in
  let recomputed_view_b = List.map (fun (_, v) -> -v) (E4_fibers_view.bindings f1) in
  must "projection must be fixed" (mixed = [7; -9] && recomputed_view_b = [-7; -9]);
  Printf.printf "{\"probe\":\"fixed-functions\",\"cached_node_after_other_resolver\":%s,\"recomputed_node\":%s,\"mixed_cached_view\":%s,\"recomputed_view\":%s}\n"
    (option_int cached) (option_int recomputed) (list_int mixed) (list_int recomputed_view_b)
