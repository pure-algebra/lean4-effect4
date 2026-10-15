(* test_engine.ml -- lane D: the drive loop, the differential between the two instances of
   the generated engine, and the first W1/W2 numbers.

   What it checks (docs/research/2026-09-08-engine-brief.md §2.1; the lane's acceptance):

     1  G0 reproduced on BOTH instances.  `p42` / `pFork` / `pAwait` -- the byte-pinned
        corpus of src/Effect4/Program/Wire.lean:74-106, written in `Eff_types`, the one
        program type of the wire and both instances -- give `finished ... success 42`, `finished fibers=2 success
        ctor 0 [7]` and `frontier fibers=1`; and `Fast` answers what `Ref` answers.
        With them, the term rows' environment (the state plan's T3b): a read-modify-write
        row's term reads an outer binder and the cell's value at the node's level
        (`pCapture`, `pLevel@2`), and a `Ref.modify` answers a value of another type than
        the cell's (`pModifyOther`), with two red controls, the term one level down and one
        level up (`pLevel@1`, `pLevel@3`); the values are Lean's
        (Test/Program/CompileContract.lean).
        And the list fold with two binders (decisions row 228): from the head (`pFold`), with
        an outer capture (`pFoldCapture`), inside a fold (`pFoldNested`) and inside an
        operation's term (`pFoldInOp`), with two controls, the empty list and a body that
        refuses (`pFoldEmpty`, `pFoldRefuses`); the values are Lean's
        (Test/Program/FoldContract.lean).
     2  The differential D1 in miniature: the programs of ocaml/eff/goldens/*.bin,
        decoded by `Eff_wire`, run at fuel 1000
        on both instances.  Outcome, answer, exits, the fiber-table projection, the trace
        rows and the store row must be EQUAL between `Fast` and `Ref` for every one, and
        each instance's drive loop must agree with its own generated `Api.run`.
     3  The numeric profile at load: a natural literal outside it is refused, from a value
        and from the wire (EN8). The ordinal pin went with the conversion on 2026-10-15:
        both instances open `Eff_types`, so `ocamlopt` holds the one alphabet.
     4  `replay_steps` yields |tape| + 1 machines and its last equals `replay`'s.
     5  The two `failwith` rows of the generated prelude (`sh_dispatcher_mk`,
        `sh_memo_map_mk`, api_engine.ml's PRELUDE) never fire on the corpus: counted.
     6  E4-PROV-CE-005: a layer body binds its own string, even under an outer number
        binder; both generated-engine carriers must fail with that string.

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
(* ================================================================ the G0 programs *)

let p42 : E.native_op E.eff = E.Eff_succeed (E.Term_lit (E.Lit_nat 42))

let fork_opts : E.fork_options =
  { E.start_immediately = false;
    daemon = false;
    mask_mode = E.MaskMode_inherit }

let p_fork : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_withFiber
        (E.ActionTerm_fork
           ( E.Eff_bind (E.Eff_yieldNow 0, E.Eff_succeed (E.Term_lit (E.Lit_nat 7))),
             fork_opts )),
      E.Eff_awaitFiber (E.Term_var 0, E.ObserverMode_awaitValue) )

let p_await : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_perform (E.NativeOp_deferredMakeOf (E.Ty_nat, E.Ty_nat), E.Term_lit E.Lit_unit),
      E.Eff_perform (E.NativeOp_deferredAwait, E.Term_var 0) )

(* `chain 0 = succeed unit`, `chain (n+1) = bind (perform refMake (lit (nat n))) (chain n)`
   -- Test/Program/RuntimeRContract.lean's `chain`, the quadratic detector (A1 §6.1 W2). *)
let rec chain n : E.native_op E.eff =
  if n <= 0 then E.Eff_succeed (E.Term_lit E.Lit_unit)
  else
    E.Eff_bind
      ( E.Eff_perform (E.NativeOp_refMake, E.Term_lit (E.Lit_nat (n - 1))),
        chain (n - 1) )

(* The term rows' environment (decisions row 43; the state plan's T3b).  A read-modify-write
   row's binder term runs at the node's environment extended by the cell's current value, so it
   reads the current value at the node's level and every outer binder below it.  In the
   generated engine that environment is the point's carrier (`field Effect4.Machine.SyncOp.env
   E.t`, externs.txt) and `sh_ref_step` extends it with `E.snoc`.  The programs and their
   values are Test/Program/CompileContract.lean's `pRefUpdateCapture`, `pRefUpdateLevel` and
   `pRefModifyOther`. *)
let nat_lit n = E.Term_lit (E.Lit_nat n)
let succ_at n = E.Term_app ("succ", E.Terms_cons (E.Term_var n, E.Terms_nil))

(* `Ref.make(5)`, a bound `10`, `Ref.update(ref, a => add(a, x))`, then `Ref.get(ref)`: the
   term captures the outer `x` (`var 1`) and reads the cell's value at the node's level
   (`var 2`). *)
let p_capture : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_perform (E.NativeOp_refMake, nat_lit 5),
      E.Eff_bind
        ( E.Eff_succeed (nat_lit 10),
          E.Eff_bind
            ( E.Eff_perform
                ( E.NativeOp_refUpdateWith
                    (E.Term_app
                       ("add", E.Terms_cons (E.Term_var 2, E.Terms_cons (E.Term_var 1, E.Terms_nil)))),
                  E.Term_var 0 ),
              E.Eff_perform (E.NativeOp_refGet, E.Term_var 0) ) ) )

(* `Ref.make(5)`, then `Ref.modify(ref, a => ["s", a])`: the row answers the string and stores
   the number it read (`pRefModifyOther`).  `B` is the term's, not the cell's. *)
let p_modify_other : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_perform (E.NativeOp_refMake, nat_lit 5),
      E.Eff_perform
        ( E.NativeOp_refModifyWith
            (E.Term_app
               ( "pair",
                 E.Terms_cons
                   (E.Term_lit (E.Lit_str "s"), E.Terms_cons (E.Term_var 1, E.Terms_nil)) )),
          E.Term_var 0 ) )

(* `Ref.make(5)`, a bound `10`, then `Ref.updateAndGet(ref, f)` at a node of level 2. *)
let p_level (f : E.term) : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_perform (E.NativeOp_refMake, nat_lit 5),
      E.Eff_bind
        ( E.Eff_succeed (nat_lit 10),
          E.Eff_perform (E.NativeOp_refUpdateAndGetWith f, E.Term_var 0) ) )

(* The list fold with two binders (decisions row 228).  A fold's body runs at the environment
   extended by the accumulator and the element, so it reads the accumulator at the fold's level
   and the element one above it.  In the generated engine that environment is the point's
   carrier, extended by `E.append` in the evaluator's own loop
   (`list_foldl_m_at_program_eval_term_spec_0`, api_engine.ml).  The programs and their values
   are Test/Program/FoldContract.lean's. *)
let app f args = E.Term_app (f, List.fold_right (fun a t -> E.Terms_cons (a, t)) args E.Terms_nil)
let nil_t = app "nil" []
let nat_list xs = List.fold_right (fun x acc -> app "cons" [ nat_lit x; acc ]) xs nil_t
let snoc xs x = app "append" [ xs; app "cons" [ x; nil_t ] ]

(* From the head: `((10 - 1) - 2) - 3`. *)
let p_fold : E.native_op E.eff =
  E.Eff_succeed
    (E.Term_fold (None, nat_list [ 1; 2; 3 ], nat_lit 10, app "sub" [ E.Term_var 0; E.Term_var 1 ]))

(* A bound `100`; the body reads it below the fold's level: `(0 + (1 + 100)) + (2 + 100)`. *)
let p_fold_capture : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_succeed (nat_lit 100),
      E.Eff_succeed
        (E.Term_fold
           ( None, nat_list [ 1; 2 ], nat_lit 0,
             app "add" [ E.Term_var 1; app "add" [ E.Term_var 2; E.Term_var 0 ] ] )) )

(* A fold inside a fold, with a stated accumulator type: the inner body reads the outer element
   (`var 2`), and pairs each item with the length of its own list. *)
let p_fold_nested : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_succeed (app "cons" [ nat_list [ 1; 2 ]; app "cons" [ nat_list [ 3 ]; nil_t ] ]),
      E.Eff_succeed
        (E.Term_fold
           ( Some (E.Ty_list (E.Ty_prod (E.Ty_nat, E.Ty_nat))), E.Term_var 0, nil_t,
             E.Term_fold
               ( None, E.Term_var 2, E.Term_var 1,
                 snoc (E.Term_var 3) (app "tuple" [ E.Term_var 4; app "length" [ E.Term_var 2 ] ]) ) )) )

(* `Ref.make(5)`, then `Ref.modify(ref, a => [fold(xs, a, (b, x) => b + x), a])`: the term's
   binder is `var 1`, so the fold inside it binds `var 2` and `var 3`.  One store step answers
   `5 + 1 + 2 + 3` and stores the `5` it read. *)
let p_fold_in_op : E.native_op E.eff =
  E.Eff_bind
    ( E.Eff_perform (E.NativeOp_refMake, nat_lit 5),
      E.Eff_perform
        ( E.NativeOp_refModifyWith
            (app "pair"
               [ E.Term_fold
                   ( None, nat_list [ 1; 2; 3 ], E.Term_var 1,
                     app "add" [ E.Term_var 2; E.Term_var 3 ] );
                 E.Term_var 1 ]),
          E.Term_var 0 ) )

(* An empty list answers the initial value, and the body, which would refuse, is not run. *)
let p_fold_empty : E.native_op E.eff =
  E.Eff_succeed (E.Term_fold (None, nil_t, nat_lit 7, E.Term_tupleAt (E.Term_var 1, 5)))

(* A body that refuses on an element refuses the fold: no partial answer. *)
let p_fold_refuses : E.native_op E.eff =
  E.Eff_succeed (E.Term_fold (None, nat_list [ 1; 2 ], nat_lit 0, E.Term_tupleAt (E.Term_var 1, 0)))

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
  | E4_engine.Outside_profile r -> "Outside_profile " ^ r
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

  let report (p : E.native_op E.eff) ~(fuel : int) : report = of_t (En.run p ~fuel)

  (* The instance's OWN generated `Effect4.Api.run`, so the drive loop is checked against
     the function it is a re-implementation of. *)
  let api_outcome (p : E.native_op E.eff) ~(fuel : int) : string = En.api_run (En.compile p) ~fuel
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
  print_endline "== 1. G0 on both instances (fuel 1000) ==";
  let one name (p : E.native_op E.eff) expect_outcome expect_fibers expect_root =
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
  one "pAwait" p_await "frontier" 1 None;
  (* The term rows' environment, on both carriers, against Lean's pinned values. *)
  one "pCapture" p_capture "finished" 1 (Some "success 15");
  one "pLevel@2" (p_level (succ_at 2)) "finished" 1 (Some "success 6");
  one "pModifyOther" p_modify_other "finished" 1 (Some "success \"s\"");
  (* Red controls.  The image one level down reads the outer `10`, not the cell.  The image one
     level up is out of scope: the store step stops and the machine answers the thunk's pure
     value, the unit. *)
  one "pLevel@1" (p_level (succ_at 1)) "finished" 1 (Some "success 11");
  one "pLevel@3" (p_level (succ_at 3)) "finished" 1 (Some "success unit");
  (* The list fold, on both carriers, against Lean's pinned values. *)
  one "pFold" p_fold "finished" 1 (Some "success 4");
  one "pFoldCapture" p_fold_capture "finished" 1 (Some "success 203");
  one "pFoldNested" p_fold_nested "finished" 1
    (Some "success list[list[1,2],list[2,2],list[3,1]]");
  one "pFoldInOp" p_fold_in_op "finished" 1 (Some "success 11");
  (* Controls.  An empty list answers the initial value and never runs the body.  A body that
     refuses on an element refuses the fold, and the machine answers its wrong-shape defect. *)
  one "pFoldEmpty" p_fold_empty "finished" 1 (Some "success 7");
  one "pFoldRefuses" p_fold_refuses "finished" 1 (Some "failure [die(badName)]")

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

(* ================================================================ 4. replay_steps *)

let replay_steps_check () =
  print_endline "";
  print_endline "== 4. replay_steps (EN4) ==";
  let tape =
    [ En_fast.evaluate 0; En_fast.flush; En_fast.flush; En_fast.fire 0;
      En_fast.yield_verdict 0 true ]
  in
  let one name (p : E.native_op E.eff) fuel =
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

(* Handwritten carrier substitutions must retain creation provenance. These checks call
   the prelude functions actually spliced into each generated engine instance. *)
let origin_prelude_check () =
  let () =
    let module I = Api_engine_inst in
    let program = p42 in
    let machine = I.load program ~fuel:100 in
    let parent = List.assoc 0 (I.fibers machine) in
    check "Fast creation origin: the root has no fork record"
      (match machine.forks with [] -> true | _ -> false);
    let options = { Eff_types.start_immediately = true; daemon = true; mask_mode = Eff_types.MaskMode_inherit } in
    let spawned, (_, child_id) = I.sh_spawn (I.interp_of program) machine parent
      parent.frame.current options [3; 1] in
    let _child = List.assoc child_id (I.fibers spawned) in
    check "Fast creation origin: spawn retains parent, daemon and exact site"
      (match spawned.forks with
       | [(record : I.fork_record)] ->
           record.child = child_id && record.parent = 0 && record.daemon && record.site = [3; 1]
       | _ -> false)
  in
  let () =
    let module I = Api_engine_ref in
    let program = p42 in
    let machine = I.load program ~fuel:100 in
    let parent = List.assoc 0 (I.fibers machine) in
    check "Ref creation origin: the root has no fork record"
      (match machine.forks with [] -> true | _ -> false);
    let options = { Eff_types.start_immediately = true; daemon = true; mask_mode = Eff_types.MaskMode_inherit } in
    let spawned, (_, child_id) = I.sh_spawn (I.interp_of program) machine parent
      parent.frame.current options [3; 1] in
    let _child = List.assoc child_id (I.fibers spawned) in
    check "Ref creation origin: spawn retains parent, daemon and exact site"
      (match spawned.forks with
       | [(record : I.fork_record)] ->
           record.child = child_id && record.parent = 0 && record.daemon && record.site = [3; 1]
       | _ -> false)
  in
  ()

(* DI-56: clock storage remains exact; number-valued clockNow refuses at the host
   boundary. The refusal retains the input snapshot and its unread decision. *)
let clock_profile_check () =
  (* Read the actual generated machine: store_row deliberately omits timers, so accepting
     a decision through the public wrapper alone cannot detect a narrowed clock. Expected
     decimals are independent of the clock arithmetic used by the machine. *)
  let check_generated name load advance evaluate now deadlines root_succeeded =
    let prefix = name ^ " generated clock: " in
    let step label f m =
      let next, settled = f m in
      check (prefix ^ label ^ " settles") settled;
      next
    in
    let clock_is m expected = E4_clock.to_decimal (now m) = expected in
    let deadlines_are m expected =
      List.map E4_clock.to_decimal (deadlines m) = expected
    in
    let huge = E4_clock.literal "4611686018427387905" in
    let m0 = load () in
    check (prefix ^ "load starts at zero") (clock_is m0 "0");
    let m1 = step "advance beyond max_int" (advance huge) m0 in
    check (prefix ^ "large advance retains every digit")
      (clock_is m1 "4611686018427387905");
    let m2 = step "add seven" (advance (E4_clock.of_nat 7)) m1 in
    check (prefix ^ "addition beyond max_int is exact")
      (clock_is m2 "4611686018427387912");
    let asleep = step "register sleep" evaluate m2 in
    check (prefix ^ "sleep stores the exact now plus duration")
      (clock_is asleep "4611686018427387912"
       && deadlines_are asleep ["4611686018427387929"]
       && not (root_succeeded asleep));
    let early = step "advance before deadline" (advance (E4_clock.of_nat 16)) asleep in
    check (prefix ^ "timer remains pending one millisecond before its deadline")
      (clock_is early "4611686018427387928"
       && deadlines_are early ["4611686018427387929"]
       && not (root_succeeded early));
    let fired = step "cross deadline" (advance (E4_clock.of_nat 4)) early in
    check (prefix ^ "timer fires and advance finishes at its exact target")
      (clock_is fired "4611686018427387932"
       && deadlines_are fired [] && root_succeeded fired);
    let later = step "add another large advance" (advance huge) fired in
    check (prefix ^ "successive large advances exceed signed 64-bit exactly")
      (clock_is later "9223372036854775837")
  in
  let sleep_then_42 = E.Eff_bind
    (E.Eff_perform (E.NativeOp_sleep, E.Term_lit (E.Lit_nat 17)), p42) in
  let () =
    let module I = Api_engine_inst in
    let p = sleep_then_42 in
    let step m d = I.step p (I.interp_of p) ~fuel:100 m d in
    check_generated I.name (fun () -> I.load p ~fuel:100)
      (fun millis m -> step m (I.RunDecision_advance millis))
      (fun m -> step m (I.RunDecision_evaluate 0))
      (fun m -> (I.stores_of m).timers.now)
      (fun m -> List.map (fun (w : E4_clock.t I.waiter) -> w.payload)
        (I.stores_of m).timers.wake.waiters)
      (fun m -> match List.assoc_opt 0 (I.completed_exits m) with
        | Some (I.Exit_success (I.Val_nat 42)) -> true | _ -> false)
  in
  let () =
    let module I = Api_engine_ref in
    let p = sleep_then_42 in
    let step m d = I.step p (I.interp_of p) ~fuel:100 m d in
    check_generated I.name (fun () -> I.load p ~fuel:100)
      (fun millis m -> step m (I.RunDecision_advance millis))
      (fun m -> step m (I.RunDecision_evaluate 0))
      (fun m -> (I.stores_of m).timers.now)
      (fun m -> List.map (fun (w : E4_clock.t I.waiter) -> w.payload)
        (I.stores_of m).timers.wake.waiters)
      (fun m -> match List.assoc_opt 0 (I.completed_exits m) with
        | Some (I.Exit_success (I.Val_nat 42)) -> true | _ -> false)
  in
  let check_instance (module En : E4_engine.ENGINE) =
    let module Projection = E4_diff.Of (En) in
    let p = E.Eff_bind
      (E.Eff_perform (E.NativeOp_refMake, E.Term_lit (E.Lit_nat 7)),
       E.Eff_perform (E.NativeOp_clockNow, E.Term_lit E.Lit_unit)) in
    let prefix = En.name ^ " exact clock: " in
    let m0 = En.load p ~fuel:100 in
    let m = En.step m0 (En.advance_exact (E4_clock.literal "4611686018427387904")) in
    check (prefix ^ "large adjustment is accepted")
      (match En.answer m with E4_engine.Outside_profile _ -> false | _ -> true);
    let before = (En.refs m, En.trace_rows m, En.fiber_rows m, En.store_row m) in
    let refused, residue = En.replay_to m [En.evaluate 0; En.flush] in
    check (prefix ^ "clockNow explicitly refuses the numeric profile")
      (match En.answer refused with E4_engine.Outside_profile _ -> true | _ -> false);
    check (prefix ^ "mid-decision refusal retains the input machine")
      (before = (En.refs refused, En.trace_rows refused, En.fiber_rows refused, En.store_row refused));
    check (prefix ^ "refused decision stays unread") (List.length residue = 2);
    check (prefix ^ "refusal cannot become differential agreement")
      (match Projection.project refused with
       | _ -> false
       | exception E4_clock.Profile_refusal _ -> true);
    check (prefix ^ "halted refusal holds the input machine")
      (En.step refused En.flush == refused)
  in
  check_instance (module En_fast);
  check_instance (module En_ref)

(* The generated multiplication row observes exact products only inside the profile.
   Out-of-profile products refuse at the decision boundary and retain its input. *)
let multiplication_profile_check () =
  let program a b = E.Eff_bind
    (E.Eff_perform (E.NativeOp_refMake, nat_lit 7),
     E.Eff_succeed (E.Term_app ("mul",
       E.Terms_cons (nat_lit a, E.Terms_cons (nat_lit b, E.Terms_nil))))) in
  let check_instance (module En : E4_engine.ENGINE) =
    let prefix = En.name ^ " multiplication profile: " in
    List.iter (fun (label, a, b, expected) ->
      let result = En.run (program a b) ~fuel:100 in
      check (prefix ^ label)
        (En.root_exit result = Some ("success " ^ string_of_int expected)))
      ["ordinary", 6, 7, 42;
       "zero at the boundary", 0, Int64.to_int 9007199254740991L, 0;
       "largest admitted product", Int64.to_int 9007199254740991L, 1,
         Int64.to_int 9007199254740991L];
    List.iter (fun (label, a, b) ->
      let before = En.load (program a b) ~fuel:100 in
      let observation m = En.refs m, En.trace_rows m, En.fiber_rows m, En.store_row m in
      let result, remaining = En.replay_to before [En.evaluate 0; En.flush] in
      check (prefix ^ label ^ " refuses")
        (match En.answer result with E4_engine.Outside_profile _ -> true | _ -> false);
      check (prefix ^ label ^ " retains the input")
        (observation result = observation before);
      check (prefix ^ label ^ " retains the decision") (List.length remaining = 2))
      ["first product above the boundary", Int64.to_int 4503599627370496L, 2;
       "rounded double product", 134217729, 134217729;
       "product above machine integers", Int64.to_int 9007199254740991L,
         Int64.to_int 9007199254740991L]
  in
  check_instance (module En_fast);
  check_instance (module En_ref)

(* Public engine inputs refuse before narrowing or constructing a decision. *)
let numeric_ingress_check () =
  let refused f = match f () with
    | _ -> false | exception E4_clock.Profile_refusal _ -> true
  in
  let check_instance (module En : E4_engine.ENGINE) =
    let prefix = En.name ^ " numeric ingress: " in
    check (prefix ^ "negative natural refused")
      (refused (fun () -> En.answer_async_success 0 0 (-1)));
    check (prefix ^ "large natural refused")
      (refused (fun () -> En.answer_async_success 0 0 (Int64.to_int 9007199254740992L)));
    ignore (En.answer_async_success 0 0 0);
    ignore (En.answer_async_success 0 0 (Int64.to_int 9007199254740991L));
    check (prefix ^ "negative literal refused")
      (refused (fun () -> En.compile (E.Eff_succeed (E.Term_lit (E.Lit_nat (-1))))));
    check (prefix ^ "large literal refused")
      (refused (fun () -> En.compile
        (E.Eff_succeed (E.Term_lit (E.Lit_nat (Int64.to_int 9007199254740992L))))));
    check (prefix ^ "large wire literal refused")
      (refused (fun () -> En.of_bytes (Eff_wire.encode_program
        (E.Eff_succeed (E.Term_lit (E.Lit_nat (Int64.to_int 9007199254740992L)))))));
    ignore (En.answer_async_float 0 0 0.0);
    ignore (En.answer_async_float 0 0 1.5);
    ignore (En.answer_async_float 0 0 (Int64.float_of_bits (Int64.of_int max_int)));
    List.iter (fun value ->
      check (prefix ^ "unrepresentable float refused")
        (refused (fun () -> En.answer_async_float 0 0 value)))
      [2.0; -0.0; -1.0; infinity; nan]
  in
  check_instance (module En_fast);
  check_instance (module En_ref)

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
  let w1_pair prog (p : E.native_op E.eff) =
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

(* E4-PROV-CE-005: the layer's lexical environment starts closed, matching its checker. *)
let layer_environment_check () =
  let key = {
    E.name = 4;
    service = 4;
  } in
  let program =
    E.Eff_bind (E.Eff_succeed (E.Term_lit (E.Lit_nat 9)),
      E.Eff_scoped (E.Eff_provideLayer (
        E.LayerTerm_effect (key,
          E.Eff_bind (E.Eff_succeed (E.Term_lit (E.Lit_str "x")),
            E.Eff_fail (E.Term_var 0))),
        false, E.Eff_service key)))
  in
  let expected = Some "failure [fail(text x)]" in
  let fast = En_fast.root_exit (En_fast.run program ~fuel:200) in
  let reference = En_ref.root_exit (En_ref.run program ~fuel:200) in
  Printf.printf "layer environment Fast: %s\n" (Option.value fast ~default:"frontier");
  Printf.printf "layer environment Ref: %s\n" (Option.value reference ~default:"frontier");
  check "layer environment Fast uses the body binding" (fast = expected);
  check "layer environment Ref uses the body binding" (reference = expected)

(* ================================================================ main *)

let () =
  print_endline
    "== lane D: the drive loop, the conversion, the two instances of the generated engine ==";
  Printf.printf "  Fast = %s\n  Ref  = %s\n" En_fast.carriers En_ref.carriers;
  print_endline "";
  g0 ();
  goldens ();
  replay_steps_check ();
  clock_profile_check ();
  numeric_ingress_check ();
  multiplication_profile_check ();
  origin_prelude_check ();
  layer_environment_check ();
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
