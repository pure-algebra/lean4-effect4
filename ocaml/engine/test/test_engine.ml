(* test_engine.ml -- lane D: the drive loop, the program conversion, the differential
   between the two instances of the generated engine, and the first W1/W2 numbers.

   What it checks (docs/research/2026-09-08-engine-brief.md §2.1; the lane's acceptance):

     1  G0 reproduced on BOTH instances.  `p42` / `pFork` / `pAwait` -- the byte-pinned
        corpus of src/Effect4/Program/Wire.lean:74-106, here written in `Eff_types` and
        converted by `E4_program`, where `ocaml/gen/api_check.ml` writes them directly in
        the generated type -- give `finished ... success 42`, `finished fibers=2 success
        ctor 0 [7]` and `frontier fibers=1`; and `Fast` answers what `Ref` answers.
     2  The differential D1 in miniature: the 37 programs of ocaml/eff/goldens/*.bin,
        decoded by `Eff_wire`, converted by `E4_program`, run at fuel 1000 with no choices
        on both instances.  Outcome, answer, exits, the fiber-table projection, the trace
        rows and the store row must be EQUAL between `Fast` and `Ref` for every one, and
        each instance's drive loop must agree with its own generated `Api.run`.
     3  The ordinal pin (CAS amendment M17): `Eff_types`' alphabet against the engine's,
        against `ocaml/eff/eff_manifest.txt`, plus the per-constructor law
        `ctor_index (of_x v) = Eff_types.ctor_index v` over a sample of EVERY arm of all
        fourteen families, on both instances -- and a mutation check that a transposed
        manifest is refused.
     4  `replay_steps` yields |tape| + 1 machines and its last equals `replay`'s.
     5  The two `failwith` rows of the generated prelude (`sh_dispatcher_mk`,
        `sh_memo_map_mk`, api_engine.ml's PRELUDE) never fire on the corpus: counted.

   And it measures W1 (`Api.run pFork` at fuel 100) and W2 (the chain of `refMake` at
   n = 100 / 300 / 1000) on both instances -- the first numbers of the substitution.  A
   measurement is not a gate: the bench prints a table and fails nothing.

   Run: cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine

module E = Eff_types
module En_fast = E4_engine.Fast
module En_ref = E4_engine.Ref

let failures = ref 0
let checks = ref 0

let check name ok =
  incr checks;
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let fail_note name why =
  incr checks;
  Printf.printf "FAIL %s -- %s\n" name why;
  incr failures

(* The two run-time holes of the seam (lane G receipt N2). *)
let extern_holes = ref 0

let is_hole m =
  let needle = "extern table incomplete" in
  let n = String.length needle and l = String.length m in
  let rec go i = i + n <= l && (String.sub m i n = needle || go (i + 1)) in
  go 0

let guard (f : unit -> 'a) : ('a, string) result =
  match f () with
  | v -> Ok v
  | exception Failure m ->
    if is_hole m then incr extern_holes;
    Error ("Failure: " ^ m)
  | exception e -> Error (Printexc.to_string e)

(* ================================================================ locating the corpus *)

let ancestors d n =
  let rec go d n acc = if n = 0 then List.rev acc else go (Filename.dirname d) (n - 1) (d :: acc) in
  go d n []

let find_path (suffix : string list) (env : string) : string option =
  let rel = List.fold_left Filename.concat (List.hd suffix) (List.tl suffix) in
  let from_env = try [ Sys.getenv env ] with Not_found -> [] in
  let cands =
    from_env
    @ List.concat_map
        (fun a -> [ Filename.concat a rel; Filename.concat a (Filename.concat "ocaml" rel) ])
        (ancestors (Sys.getcwd ()) 9)
  in
  List.find_opt Sys.file_exists cands

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

(* the first occurrence of [needle] in [s] replaced by [by]; [s] unchanged when absent *)
let replace_first needle by s =
  let n = String.length needle and l = String.length s in
  let rec at i = if i + n > l then None else if String.sub s i n = needle then Some i else at (i + 1) in
  match at 0 with
  | None -> s
  | Some i -> String.sub s 0 i ^ by ^ String.sub s (i + n) (l - i - n)

(* ================================================================ the G0 programs *)

let p42 : E.eff = E.Eff_succeed (E.Term_lit (E.Lit_nat 42))

let fork_opts : E.fork_options =
  { E.fork_options_startImmediately = false;
    fork_options_daemon = false;
    fork_options_maskMode = E.Mask_mode_inherit }

let p_fork : E.eff =
  E.Eff_bind
    ( E.Eff_withFiber
        (E.Action_term_fork
           ( E.Eff_bind (E.Eff_yieldNow 0, E.Eff_succeed (E.Term_lit (E.Lit_nat 7))),
             fork_opts )),
      E.Eff_awaitFiber (E.Term_var 0, E.Observer_mode_awaitValue) )

let p_await : E.eff =
  E.Eff_bind
    ( E.Eff_perform (E.Native_op_deferredMake, E.Term_lit E.Lit_unit),
      E.Eff_perform (E.Native_op_deferredAwait, E.Term_var 0) )

(* `chain 0 = succeed unit`, `chain (n+1) = bind (perform refMake (lit (nat n))) (chain n)`
   -- Test/Program/RuntimeRContract.lean's `chain`, the quadratic detector (A1 §6.1 W2). *)
let rec chain n : E.eff =
  if n <= 0 then E.Eff_succeed (E.Term_lit E.Lit_unit)
  else
    E.Eff_bind
      ( E.Eff_perform (E.Native_op_refMake, E.Term_lit (E.Lit_nat (n - 1))),
        chain (n - 1) )

(* ================================================================ one report per run *)

type report = {
  r_outcome : string;
  r_answer : string;
  r_fibers : int;
  r_trace_len : int;
  r_exits : (int * string) list;
  r_rows : (int * string) list;
  r_trace : string list;
  r_store : string;
  r_root : string option;
}

let show_frontier (f : E4_engine.frontier) =
  Printf.sprintf "parked=[%s] armed=[%s] due=%d"
    (String.concat "," (List.map (fun (a, b) -> Printf.sprintf "%d:%d" a b) f.E4_engine.parked))
    (String.concat "," (List.map string_of_int f.E4_engine.armed))
    f.E4_engine.due

let show_answer (a : E4_engine.answer) =
  match a with
  | E4_engine.Finished -> "Finished"
  | E4_engine.Suspended f -> "Suspended " ^ show_frontier f
  | E4_engine.Refused r -> "Refused " ^ r
  | E4_engine.Delay f -> "Delay " ^ show_frontier f

module Rep (En : E4_engine.ENGINE) = struct
  let of_t (t : En.t) : report =
    { r_outcome = En.outcome t;
      r_answer = show_answer (En.answer t);
      r_fibers = En.fiber_count t;
      r_trace_len = En.trace_length t;
      r_exits = En.exits t;
      r_rows = En.fiber_rows t;
      r_trace = En.trace_rows t;
      r_store = En.store_row t;
      r_root = En.root_exit t }

  let report (p : E.eff) ~(fuel : int) : report = of_t (En.run p ~fuel)

  (* The instance's OWN generated `Effect4.Api.run`, so the drive loop is checked against
     the function it is a re-implementation of. *)
  let api_outcome (p : E.eff) ~(fuel : int) : string = En.api_run (En.compile p) ~fuel
end

module RF = Rep (En_fast)
module RR = Rep (En_ref)

let differ (a : report) (b : report) : string list =
  let d = ref [] in
  let cmp label x y = if x <> y then d := label :: !d in
  cmp "outcome" a.r_outcome b.r_outcome;
  cmp "answer" a.r_answer b.r_answer;
  cmp "fibers" (string_of_int a.r_fibers) (string_of_int b.r_fibers);
  cmp "trace_len" (string_of_int a.r_trace_len) (string_of_int b.r_trace_len);
  cmp "exits" (String.concat "|" (List.map snd a.r_exits))
    (String.concat "|" (List.map snd b.r_exits));
  cmp "fiber_rows" (String.concat "|" (List.map snd a.r_rows))
    (String.concat "|" (List.map snd b.r_rows));
  cmp "trace" (String.concat "|" a.r_trace) (String.concat "|" b.r_trace);
  cmp "store" a.r_store b.r_store;
  cmp "root_exit"
    (match a.r_root with None -> "-" | Some s -> s)
    (match b.r_root with None -> "-" | Some s -> s);
  List.rev !d

(* ================================================================ 1. G0 *)

let g0 () =
  print_endline "== 1. G0 on both instances (fuel 1000, no choices) ==";
  let one name (p : E.eff) expect_outcome expect_fibers expect_root =
    match guard (fun () -> (RF.report p ~fuel:1000, RR.report p ~fuel:1000)) with
    | Error e -> fail_note ("G0 " ^ name) e
    | Ok (f, r) ->
      Printf.printf "  %-7s Fast: outcome=%s fibers=%d exit=%s trace=%d\n" name f.r_outcome
        f.r_fibers
        (match f.r_root with None -> "<no exit>" | Some s -> s)
        f.r_trace_len;
      check
        (Printf.sprintf "G0 %s on Fast (%s, fibers=%d, %s)" name expect_outcome
           expect_fibers
           (match expect_root with None -> "no exit" | Some s -> s))
        (f.r_outcome = expect_outcome && f.r_fibers = expect_fibers
        && f.r_root = expect_root);
      check (Printf.sprintf "G0 %s on Ref" name)
        (r.r_outcome = expect_outcome && r.r_fibers = expect_fibers
        && r.r_root = expect_root);
      check (Printf.sprintf "G0 %s: Fast = Ref, whole report" name) (differ f r = []);
      check
        (Printf.sprintf "G0 %s: the drive loop = the generated Api.run (Fast)" name)
        (RF.api_outcome p ~fuel:1000 = f.r_outcome);
      check
        (Printf.sprintf "G0 %s: the drive loop = the generated Api.run (Ref)" name)
        (RR.api_outcome p ~fuel:1000 = r.r_outcome)
  in
  one "p42" p42 "finished" 1 (Some "success 42");
  (* `awaitFiber ... awaitValue` answers the child's REIFIED exit, `ctor 0 [7]`
     (ocaml/gen/api_check.ml:96-97). *)
  one "pFork" p_fork "finished" 2 (Some "success ctor 0 [7]");
  one "pAwait" p_await "frontier" 1 None

(* ================================================================ 2. the 37 goldens *)

let goldens () =
  print_endline "";
  print_endline "== 2. the byte corpus: 37 programs, Fast vs Ref (fuel 1000) ==";
  match find_path [ "eff"; "goldens"; "p42.bin" ] "E4_EFF_GOLDENS" with
  | None -> fail_note "the byte corpus" "ocaml/eff/goldens not found from the cwd"
  | Some marker ->
    let dir = Filename.dirname marker in
    let names =
      List.sort compare
        (List.filter
           (fun f -> Filename.check_suffix f ".bin")
           (Array.to_list (Sys.readdir dir)))
    in
    Printf.printf "  %s: %d programs\n" dir (List.length names);
    let equal = ref 0 and decoded = ref 0 in
    List.iter
      (fun f ->
         let name = Filename.remove_extension f in
         let bytes = read_file (Filename.concat dir f) in
         match Eff_wire.decode_program_exact bytes with
         | None -> Printf.printf "  %-16s DECODE-FAIL (%d bytes)\n" name (String.length bytes)
         | Some p -> (
           incr decoded;
           match guard (fun () -> (RF.report p ~fuel:1000, RR.report p ~fuel:1000)) with
           | Error e -> Printf.printf "  %-16s RAISED %s\n" name e
           | Ok (a, b) ->
             let d = differ a b in
             if d = [] then incr equal;
             Printf.printf "  %-16s %-9s fibers=%-2d trace=%-4d exits=%-2d %s\n" name
               a.r_outcome a.r_fibers a.r_trace_len (List.length a.r_exits)
               (if d = [] then "EQ" else "DIFF: " ^ String.concat "," d);
             if RF.api_outcome p ~fuel:1000 <> a.r_outcome then
               Printf.printf "  %-16s drive loop <> Api.run on Fast\n" name;
             if RR.api_outcome p ~fuel:1000 <> b.r_outcome then
               Printf.printf "  %-16s drive loop <> Api.run on Ref\n" name))
      names;
    let n = List.length names in
    check (Printf.sprintf "every golden decodes (%d/%d)" !decoded n) (!decoded = n);
    check
      (Printf.sprintf "Fast = Ref on every golden: outcome, exits, fibers, trace, store (%d/%d)"
         !equal n)
      (!equal = n)

(* ================================================================ 3. the ordinal pin *)

let sample_lits = [ E.Lit_unit; E.Lit_nat 1; E.Lit_bool true; E.Lit_str "s" ]
let a_term = E.Term_var 0

let sample_terms =
  [ E.Term_var 0; E.Term_lit E.Lit_unit; E.Term_app ("pair", E.Terms_nil) ]

let sample_terms_l = [ E.Terms_nil; E.Terms_cons (a_term, E.Terms_nil) ]

let sample_cause_terms =
  [ E.Cause_term_fail a_term;
    E.Cause_term_die a_term;
    E.Cause_term_interrupt None;
    E.Cause_term_both (E.Cause_term_fail a_term, E.Cause_term_die a_term) ]

let sample_masks =
  [ E.Mask_mode_interruptible; E.Mask_mode_uninterruptible; E.Mask_mode_inherit ]

let sample_obs = [ E.Observer_mode_awaitValue; E.Observer_mode_joinEffect ]
let sample_fins = [ E.Finalizer_strategy_sequential; E.Finalizer_strategy_parallel ]

let sample_fns =
  [ E.Fn_name_incr; E.Fn_name_double; E.Fn_name_zeroWhenPositive; E.Fn_name_noChange;
    E.Fn_name_takeAndBump ]

let sample_ops =
  [ E.Native_op_refMake; E.Native_op_refGet; E.Native_op_refSet; E.Native_op_refGetAndSet;
    E.Native_op_refSetAndGet;
    E.Native_op_refUpdate E.Fn_name_incr;
    E.Native_op_refGetAndUpdate E.Fn_name_incr;
    E.Native_op_refUpdateAndGet E.Fn_name_incr;
    E.Native_op_refUpdateSome E.Fn_name_incr;
    E.Native_op_refGetAndUpdateSome E.Fn_name_incr;
    E.Native_op_refUpdateSomeAndGet E.Fn_name_incr;
    E.Native_op_refModify E.Fn_name_incr;
    E.Native_op_refModifySome E.Fn_name_incr;
    E.Native_op_deferredMake; E.Native_op_deferredIsDone; E.Native_op_deferredPoll;
    E.Native_op_deferredSucceed; E.Native_op_deferredFail; E.Native_op_deferredAwait;
    E.Native_op_scopeMake E.Finalizer_strategy_sequential ]

let u : E.eff = E.Eff_succeed (E.Term_lit E.Lit_unit)

let sample_effs =
  [ E.Eff_succeed a_term;
    E.Eff_fail a_term;
    E.Eff_failCause (E.Cause_term_fail a_term);
    E.Eff_yieldError a_term;
    E.Eff_sync a_term;
    E.Eff_suspend u;
    E.Eff_perform (E.Native_op_refMake, a_term);
    E.Eff_bind (u, u);
    E.Eff_gen E.Stmts_nil;
    E.Eff_catchCause (u, u);
    E.Eff_matchCause (u, u, u);
    E.Eff_onExit (u, u);
    E.Eff_exit u;
    E.Eff_uninterruptible u;
    E.Eff_interruptible u;
    E.Eff_branch (a_term, u, u);
    E.Eff_whileLoop (a_term, a_term, a_term, u);
    E.Eff_yieldNow 0;
    E.Eff_callback (E.Native_op_refMake, a_term);
    E.Eff_awaitFiber (a_term, E.Observer_mode_awaitValue);
    E.Eff_withFiber E.Action_term_getId;
    E.Eff_scoped u;
    E.Eff_acquireRelease (u, u);
    E.Eff_choose (0, u, u) ]

let sample_stmts =
  [ E.Stmt_bindYield u; E.Stmt_yieldDiscard u; E.Stmt_ret a_term;
    E.Stmt_ifElse (a_term, E.Stmts_nil, E.Stmts_nil); E.Stmt_whileTrue E.Stmts_nil;
    E.Stmt_breakLoop ]

let sample_stmtss = [ E.Stmts_nil; E.Stmts_cons (E.Stmt_breakLoop, E.Stmts_nil) ]
let sample_effss = [ E.Effs_nil; E.Effs_cons (u, E.Effs_nil) ]

let sample_actions =
  [ E.Action_term_fork (u, fork_opts);
    E.Action_term_forkIn (u, fork_opts, a_term);
    E.Action_term_forkScoped (u, fork_opts);
    E.Action_term_runIn (a_term, a_term);
    E.Action_term_interrupt a_term;
    E.Action_term_interruptScoped a_term;
    E.Action_term_interruptAll (a_term, None);
    E.Action_term_awaitAll a_term;
    E.Action_term_awaitAllFailFast a_term;
    E.Action_term_snapshotChildren;
    E.Action_term_awaitNewChildren a_term;
    E.Action_term_raceAll E.Effs_nil;
    E.Action_term_setContext a_term;
    E.Action_term_getContext;
    E.Action_term_getId;
    E.Action_term_closeScope (a_term, a_term) ]

module Ord (A : E4_program.PROGRAM_TYPES) = struct
  module P = E4_program.Make (A)

  let bad = ref []
  let n = ref 0

  let one family i src eng =
    incr n;
    if src <> eng then
      bad := Printf.sprintf "%s[%d]: wire %d, engine %d" family i src eng :: !bad

  let go () =
    List.iteri (fun i v -> one "lit" i (E.ctor_index_lit v) (P.ctor_index_lit (P.of_lit v)))
      sample_lits;
    List.iteri (fun i v -> one "term" i (E.ctor_index_term v) (P.ctor_index_term (P.of_term v)))
      sample_terms;
    List.iteri
      (fun i v -> one "terms" i (E.ctor_index_terms v) (P.ctor_index_terms (P.of_terms v)))
      sample_terms_l;
    List.iteri
      (fun i v ->
         one "cause_term" i (E.ctor_index_cause_term v)
           (P.ctor_index_cause_term (P.of_cause_term v)))
      sample_cause_terms;
    List.iteri
      (fun i v ->
         one "mask_mode" i (E.ctor_index_mask_mode v)
           (P.ctor_index_mask_mode (P.of_mask_mode v)))
      sample_masks;
    List.iteri
      (fun i v ->
         one "observer_mode" i (E.ctor_index_observer_mode v)
           (P.ctor_index_observer_mode (P.of_observer_mode v)))
      sample_obs;
    List.iteri
      (fun i v ->
         one "finalizer_strategy" i (E.ctor_index_finalizer_strategy v)
           (P.ctor_index_finalizer_strategy (P.of_finalizer_strategy v)))
      sample_fins;
    List.iteri
      (fun i v -> one "fn_name" i (E.ctor_index_fn_name v) (P.ctor_index_fn_name (P.of_fn_name v)))
      sample_fns;
    List.iteri
      (fun i v ->
         one "native_op" i (E.ctor_index_native_op v)
           (P.ctor_index_native_op (P.of_native_op v)))
      sample_ops;
    List.iteri (fun i v -> one "eff" i (E.ctor_index_eff v) (P.ctor_index_eff (P.of_eff v)))
      sample_effs;
    List.iteri (fun i v -> one "stmt" i (E.ctor_index_stmt v) (P.ctor_index_stmt (P.of_stmt v)))
      sample_stmts;
    List.iteri
      (fun i v -> one "stmts" i (E.ctor_index_stmts v) (P.ctor_index_stmts (P.of_stmts v)))
      sample_stmtss;
    List.iteri (fun i v -> one "effs" i (E.ctor_index_effs v) (P.ctor_index_effs (P.of_effs v)))
      sample_effss;
    List.iteri
      (fun i v ->
         one "action_term" i (E.ctor_index_action_term v)
           (P.ctor_index_action_term (P.of_action_term v)))
      sample_actions;
    (!n, List.rev !bad)
end

module OrdF = Ord (Api_engine_inst)
module OrdR = Ord (Api_engine_ref)

let ordinals () =
  print_endline "";
  print_endline "== 3. the ordinal pin (M17) ==";
  (match E4_program.pin () with
   | Ok () -> check "the wire's alphabet is a PREFIX of the engine's, every family" true
   | Error e -> fail_note "E4_program.pin" e);
  (match find_path [ "eff"; "eff_manifest.txt" ] "E4_EFF_MANIFEST" with
   | None -> fail_note "eff_manifest.txt" "not found from the cwd"
   | Some path -> (
     (match E4_program.parse_manifest path with
      | Error e -> fail_note "eff_manifest.txt parses" e
      | Ok rows ->
        Printf.printf "  %s: %d inductive families\n" path (List.length rows);
        check "eff_manifest.txt parses into inductive families" (List.length rows >= 15));
     match E4_program.check_manifest path with
     | Ok () -> check "eff_manifest.txt = Eff_types = the engine (the content table)" true
     | Error e -> fail_note "E4_program.check_manifest" e));
  (* the mutation: transpose two same-arity arms of `eff` in a copy of the manifest and the
     pin must refuse it.  `fail(term)` and `yieldError(term)` are ordinals 1 and 3, and both
     carry one `term`, so nothing but the ORDER distinguishes them -- this is exactly the
     transposition hole a structural map leaves open (A1 §2.2, U-a's risk). *)
  (match find_path [ "eff"; "eff_manifest.txt" ] "E4_EFF_MANIFEST" with
   | None -> ()
   | Some path ->
     let text = read_file path in
     let swapped =
       replace_first "succeed(term) fail(term) failCause"
         "succeed(term) yieldError(term) failCause" text
     in
     let tmp = Filename.temp_file "e4_manifest" ".txt" in
     let oc = open_out_bin tmp in
     output_string oc swapped;
     close_out oc;
     let verdict = E4_program.check_manifest tmp in
     Sys.remove tmp;
     check "mutation: a transposed `eff` arm in the manifest is REFUSED"
       (swapped <> text && Result.is_error verdict));
  let nf, badf = OrdF.go () in
  let nr, badr = OrdR.go () in
  Printf.printf "  %d + %d constructor ordinals compared\n" nf nr;
  check
    (Printf.sprintf "ctor_index (of_x v) = Eff_types.ctor_index v, %d arms on Fast" nf)
    (badf = []);
  if badf <> [] then List.iter (fun s -> Printf.printf "    %s\n" s) badf;
  check
    (Printf.sprintf "ctor_index (of_x v) = Eff_types.ctor_index v, %d arms on Ref" nr)
    (badr = []);
  if badr <> [] then List.iter (fun s -> Printf.printf "    %s\n" s) badr

(* ================================================================ 4. replay_steps *)

let replay_steps_check () =
  print_endline "";
  print_endline "== 4. replay_steps (EN4) ==";
  let tape =
    [ En_fast.evaluate 0; En_fast.flush; En_fast.flush; En_fast.fire 0;
      En_fast.yield_verdict 0 true ]
  in
  let one name (p : E.eff) fuel =
    let t0 = En_fast.load p ~fuel in
    let steps = List.of_seq (En_fast.replay_steps t0 tape) in
    let last = List.nth steps (List.length steps - 1) in
    let folded = En_fast.replay t0 tape in
    let same a b =
      En_fast.outcome a = En_fast.outcome b
      && En_fast.trace_rows a = En_fast.trace_rows b
      && En_fast.store_row a = En_fast.store_row b
      && En_fast.fiber_rows a = En_fast.fiber_rows b
    in
    (* every prefix: `replay_steps` at position i is `replay` of the first i decisions *)
    let prefix_ok =
      List.for_all
        (fun i ->
           let taken = List.filteri (fun j _ -> j < i) tape in
           same (List.nth steps i) (En_fast.replay t0 taken))
        (List.init (List.length tape + 1) Fun.id)
    in
    check
      (Printf.sprintf "replay_steps %s: |tape|+1 = %d machines" name
         (List.length tape + 1))
      (List.length steps = List.length tape + 1);
    check (Printf.sprintf "replay_steps %s: the last is replay's" name) (same last folded);
    check (Printf.sprintf "replay_steps %s: position i is replay of the first i" name)
      prefix_ok;
    check (Printf.sprintf "snapshot %s is the value" name) (same (En_fast.snapshot t0) t0)
  in
  one "p42" p42 1000;
  one "pFork" p_fork 1000;
  one "pAwait" p_await 1000;
  (* the fuel discriminator: a chain that cannot finish in its fuel answers Delay, not
     Suspended -- the letter `Api.Outcome` does not have (E4_engine header). *)
  let starved = En_fast.run (chain 200) ~fuel:20 in
  Printf.printf "  chain 200 at fuel 20: %s\n" (show_answer (En_fast.answer starved));
  check "a starved run answers Delay (the residue is non-empty), not Suspended"
    (match En_fast.answer starved with E4_engine.Delay _ -> true | _ -> false);
  check "a starved run's outcome is still Api.Outcome.frontier"
    (En_fast.outcome starved = "frontier")

(* ================================================================ the bench *)

let best_of k f =
  let b = ref infinity in
  for _ = 1 to k do
    let t0 = Unix.gettimeofday () in
    f ();
    let dt = Unix.gettimeofday () -. t0 in
    if dt < !b then b := dt
  done;
  !b

let bench () =
  print_endline "";
  print_endline "== W1: the GENERATED Api.run, fuel 100, 20 000 iterations, best of 3 ==";
  print_endline "  program  instance  ms         iterations/s   decisions/s";
  let iters = 20_000 in
  let w1 (prog : string) (name : string) (run : unit -> unit) =
    let ms = best_of 3 run *. 1000.0 in
    Printf.printf "  %-8s %-9s %-10.2f %-14.0f %.0f\n" prog name ms
      (float_of_int iters /. (ms /. 1000.0))
      (2.0 *. float_of_int iters /. (ms /. 1000.0))
  in
  let w1_pair prog (p : E.eff) =
    let pf = En_fast.compile p and pr = En_ref.compile p in
    w1 prog "Fast" (fun () -> for _ = 1 to iters do ignore (En_fast.api_run pf ~fuel:100) done);
    w1 prog "Ref" (fun () -> for _ = 1 to iters do ignore (En_ref.api_run pr ~fuel:100) done)
  in
  w1_pair "p42" p42;
  w1_pair "pAwait" p_await;
  w1_pair "pFork" p_fork;
  print_endline "";
  print_endline "== W2: the chain of refMake, fuel 8n+400, best of 5 ==";
  print_endline
    "  n     instance  steps  refs  load ms   run ms     steps/s      held words   held bytes";
  (* A1-Q8's snapshot measurement: `Gc.full_major (); (Gc.stat ()).live_words` around a
     retained finished machine.  No Obj, no Marshal (ocaml/STANDARDS.md §4). *)
  let held_words f =
    Gc.full_major ();
    let before = (Gc.stat ()).Gc.live_words in
    let v = f () in
    Gc.full_major ();
    let after = (Gc.stat ()).Gc.live_words in
    ignore (Sys.opaque_identity v);
    after - before
  in
  List.iter
    (fun n ->
       let p = chain n in
       let fuel = (8 * n) + 400 in
       let w2 name compile api_run load_program run trace_length refs =
         let prog = compile p in
         let t = run prog ~fuel in
         let steps = trace_length t and nrefs = List.length (refs t) in
         let load_ms = best_of 5 (fun () -> ignore (load_program prog ~fuel)) *. 1000.0 in
         let ms = best_of 5 (fun () -> ignore (api_run prog ~fuel)) *. 1000.0 in
         let words = held_words (fun () -> run (compile p) ~fuel) in
         Printf.printf "  %-5d %-9s %-6d %-5d %-9.3f %-10.3f %-12.0f %-12d %d\n" n name
           steps nrefs load_ms ms
           (float_of_int steps /. (ms /. 1000.0))
           words (words * 8)
       in
       w2 "Fast" En_fast.compile En_fast.api_run En_fast.load_program En_fast.run_program
         En_fast.trace_length En_fast.refs;
       w2 "Ref" En_ref.compile En_ref.api_run En_ref.load_program En_ref.run_program
         En_ref.trace_length En_ref.refs)
    [ 50; 100; 300; 500; 1000 ]

(* ================================================================ main *)

let () =
  print_endline
    "== lane D: the drive loop, the conversion, the two instances of the generated engine ==";
  Printf.printf "  Fast = %s\n  Ref  = %s\n" En_fast.carriers En_ref.carriers;
  print_endline "";
  g0 ();
  goldens ();
  ordinals ();
  replay_steps_check ();
  print_endline "";
  print_endline "== 5. the two failwith rows of the generated prelude ==";
  check
    (Printf.sprintf
       "sh_dispatcher_mk / sh_memo_map_mk never fired on the corpus (%d hits)"
       !extern_holes)
    (!extern_holes = 0);
  bench ();
  print_endline "";
  Printf.printf "== %s: %d failure(s) in %d checks ==\n"
    (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures !checks;
  exit (if !failures = 0 then 0 else 1)
