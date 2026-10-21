(* test_engine.ml -- lane D: the drive loop over the generated engine, its whole report against
   the generated machine's, and the first W1/W2 numbers.

   What it checks (docs/research/2026-09-08-engine-brief.md §2.1; the lane's acceptance):

     1  G0 reproduced on `Fast`.  `p42` / `pFork` / `pAwait` -- the byte-pinned
        corpus of p42 (src/Effect4/Store/Domain/ProgramWire.lean), written in `Eff_types`, the one
        program type of the wire and both engines -- give `finished ... success 42`, `finished fibers=2 success
        ctor 0 [7]` and `frontier fibers=1`; and `Fast` answers the whole report the generated
        machine answers (`Gen`, `E4_engine.Make (Api_gen_inst)`: ocaml/gen/api_gen.ml, Lean's
        lists and no extern row).
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
     2  The goldens' Gen = Fast differential is `test_diff`'s (every corpus, every position),
        and `replay_steps` is `test_replay_steps`': this file repeats neither since 2026-10-15.
     3  The profile at ingress, Lean's profile support lowered on both instances: a natural
        literal outside it is refused at its node's address, from a value and from the wire
        (EN8, `numeric_ingress_check`). A host's answer is refused at ingress when it is no
        Lean value or the profile does not support it, at its path (EN9,
        `answer_ingress_check`). The run itself is exact (M4): the clock past max_int
        (`clock_exactness_check`) and a product past the profile and past the host's int
        (`multiplication_exactness_check`); a crossing's refusal retains the input machine
        (EN3, `crossing_retention_check`, over a stand-in whose flush refuses). The ordinal pin went with the conversion on 2026-10-15:
        both instances open `Eff_types`, so `ocamlopt` holds the one alphabet.
     5  The two `failwith` rows of the generated prelude (`sh_dispatcher_mk`,
        `sh_memo_map_mk`, api_engine.ml's PRELUDE) never fire in this file's runs: counted.
        Over every corpus, a raise fails `test_diff`.
     6  E4-PROV-CE-005: a layer body binds its own string, even under an outer number
        binder; both generated-engine carriers must fail with that string.

   And it measures W1 (`Api.run pFork` at fuel 100) and W2 (the chain of `refMake` at
   n = 100 / 300 / 1000) on Fast and on Gen, Lean's lists -- the first numbers of the
   substitution.  A measurement is not a gate: the bench prints a table and fails nothing.

   Run: cd ocaml && dune build @engine/test/runtest --force *)

open Effect4_engine
module E = Eff_types
module En_fast = E4_engine.Fast

(* The generated machine, the oracle: the whole report Fast must answer, and the bench's
   baseline over Lean's own lists. *)
module En_gen = E4_engine.Make (Api_gen_inst)

let check = E4_check.check
let fail_note name why = check (name ^ " -- " ^ why) false

(* The two run-time holes of the seam (lane G receipt N2). *)
let extern_holes = ref 0

let is_hole m =
  let needle = "extern table incomplete" in
  let n = String.length needle
  and l = String.length m in
  let rec go i = i + n <= l && (String.sub m i n = needle || go (i + 1)) in
  go 0
;;

let guard (f : unit -> 'a) : ('a, string) result =
  match f () with
  | v -> Ok v
  | exception Failure m ->
    if is_hole m then incr extern_holes;
    Error ("Failure: " ^ m)
  | exception e -> Error (Printexc.to_string e)
;;

(* ================================================================ the G0 programs *)

let p42 : E.NativeOp.t E.Eff.t = E.Eff.Succeed (E.Term.Lit (E.Lit.Nat (Z.of_int 42)))

let fork_opts : E.ForkOptions.t =
  { E.ForkOptions.start_immediately = false
  ; daemon = false
  ; mask_mode = E.MaskMode.Inherit
  }
;;

let p_fork : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.WithFiber
        (E.ActionTerm.Fork
           ( E.Eff.Bind
               ( E.Eff.YieldNow (Z.of_int 0)
               , E.Eff.Succeed (E.Term.Lit (E.Lit.Nat (Z.of_int 7))) )
           , fork_opts ))
    , E.Eff.AwaitFiber (E.Term.Var (Z.of_int 0), E.ObserverMode.AwaitValue) )
;;

let p_await : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Perform (E.NativeOp.DeferredMakeOf (E.Ty.Nat, E.Ty.Nat), E.Term.Lit E.Lit.Unit)
    , E.Eff.Perform (E.NativeOp.DeferredAwait, E.Term.Var (Z.of_int 0)) )
;;

(* `chain 0 = succeed unit`, `chain (n+1) = bind (perform refMake (lit (nat n))) (chain n)`
   -- Test/Program/RuntimeRContract.lean's `chain`, the quadratic detector (A1 §6.1 W2). *)
let rec chain n : E.NativeOp.t E.Eff.t =
  if n <= 0
  then E.Eff.Succeed (E.Term.Lit E.Lit.Unit)
  else
    E.Eff.Bind
      ( E.Eff.Perform (E.NativeOp.RefMake, E.Term.Lit (E.Lit.Nat (Z.of_int (n - 1))))
      , chain (n - 1) )
;;

(* The term rows' environment (decisions row 43; the state plan's T3b).  A read-modify-write
   row's binder term runs at the node's environment extended by the cell's current value, so it
   reads the current value at the node's level and every outer binder below it.  In the
   generated engine that environment is the point's carrier (`field Effect4.Machine.SyncOp.env
   E.t`, externs.txt) and `sh_ref_step` extends it with `E.snoc`.  The programs and their
   values are Test/Program/CompileContract.lean's `pRefUpdateCapture`, `pRefUpdateLevel` and
   `pRefModifyOther`. *)
let nat_lit n = E.Term.Lit (E.Lit.Nat (Z.of_int n))
let succ_at n = E.Term.App ("succ", E.Terms.Cons (E.Term.Var (Z.of_int n), E.Terms.Nil))

(* `Ref.make(5)`, a bound `10`, `Ref.update(ref, a => add(a, x))`, then `Ref.get(ref)`: the
   term captures the outer `x` (`var 1`) and reads the cell's value at the node's level
   (`var 2`). *)
let p_capture : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Perform (E.NativeOp.RefMake, nat_lit 5)
    , E.Eff.Bind
        ( E.Eff.Succeed (nat_lit 10)
        , E.Eff.Bind
            ( E.Eff.Perform
                ( E.NativeOp.RefUpdateWith
                    (E.Term.App
                       ( "add"
                       , E.Terms.Cons
                           ( E.Term.Var (Z.of_int 2)
                           , E.Terms.Cons (E.Term.Var (Z.of_int 1), E.Terms.Nil) ) ))
                , E.Term.Var (Z.of_int 0) )
            , E.Eff.Perform (E.NativeOp.RefGet, E.Term.Var (Z.of_int 0)) ) ) )
;;

(* `Ref.make(5)`, then `Ref.modify(ref, a => ["s", a])`: the row answers the string and stores
   the number it read (`pRefModifyOther`).  `B` is the term's, not the cell's. *)
let p_modify_other : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Perform (E.NativeOp.RefMake, nat_lit 5)
    , E.Eff.Perform
        ( E.NativeOp.RefModifyWith
            (E.Term.App
               ( "pair"
               , E.Terms.Cons
                   ( E.Term.Lit (E.Lit.Str "s")
                   , E.Terms.Cons (E.Term.Var (Z.of_int 1), E.Terms.Nil) ) ))
        , E.Term.Var (Z.of_int 0) ) )
;;

(* `Ref.make(5)`, a bound `10`, then `Ref.updateAndGet(ref, f)` at a node of level 2. *)
let p_level (f : E.Term.t) : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Perform (E.NativeOp.RefMake, nat_lit 5)
    , E.Eff.Bind
        ( E.Eff.Succeed (nat_lit 10)
        , E.Eff.Perform (E.NativeOp.RefUpdateAndGetWith f, E.Term.Var (Z.of_int 0)) ) )
;;

(* The list fold with two binders (decisions row 228).  A fold's body runs at the environment
   extended by the accumulator and the element, so it reads the accumulator at the fold's level
   and the element one above it.  In the generated engine that environment is the point's
   carrier, extended by `E.append` in the evaluator's own loop
   (`list_foldl_m_at_program_eval_term_spec_0`, api_engine.ml).  The programs and their values
   are Test/Program/FoldContract.lean's. *)
let app f args =
  E.Term.App (f, List.fold_right (fun a t -> E.Terms.Cons (a, t)) args E.Terms.Nil)
;;

let nil_t = app "nil" []
let nat_list xs = List.fold_right (fun x acc -> app "cons" [ nat_lit x; acc ]) xs nil_t
let snoc xs x = app "append" [ xs; app "cons" [ x; nil_t ] ]

(* From the head: `((10 - 1) - 2) - 3`. *)
let p_fold : E.NativeOp.t E.Eff.t =
  E.Eff.Succeed
    (E.Term.Fold
       ( None
       , nat_list [ 1; 2; 3 ]
       , nat_lit 10
       , app "sub" [ E.Term.Var (Z.of_int 0); E.Term.Var (Z.of_int 1) ] ))
;;

(* A bound `100`; the body reads it below the fold's level: `(0 + (1 + 100)) + (2 + 100)`. *)
let p_fold_capture : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Succeed (nat_lit 100)
    , E.Eff.Succeed
        (E.Term.Fold
           ( None
           , nat_list [ 1; 2 ]
           , nat_lit 0
           , app
               "add"
               [ E.Term.Var (Z.of_int 1)
               ; app "add" [ E.Term.Var (Z.of_int 2); E.Term.Var (Z.of_int 0) ]
               ] )) )
;;

(* A fold inside a fold, with a stated accumulator type: the inner body reads the outer element
   (`var 2`), and pairs each item with the length of its own list. *)
let p_fold_nested : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Succeed
        (app "cons" [ nat_list [ 1; 2 ]; app "cons" [ nat_list [ 3 ]; nil_t ] ])
    , E.Eff.Succeed
        (E.Term.Fold
           ( Some (E.Ty.List (E.Ty.Prod (E.Ty.Nat, E.Ty.Nat)))
           , E.Term.Var (Z.of_int 0)
           , nil_t
           , E.Term.Fold
               ( None
               , E.Term.Var (Z.of_int 2)
               , E.Term.Var (Z.of_int 1)
               , snoc
                   (E.Term.Var (Z.of_int 3))
                   (app
                      "tuple"
                      [ E.Term.Var (Z.of_int 4)
                      ; app "length" [ E.Term.Var (Z.of_int 2) ]
                      ]) ) )) )
;;

(* `Ref.make(5)`, then `Ref.modify(ref, a => [fold(xs, a, (b, x) => b + x), a])`: the term's
   binder is `var 1`, so the fold inside it binds `var 2` and `var 3`.  One store step answers
   `5 + 1 + 2 + 3` and stores the `5` it read. *)
let p_fold_in_op : E.NativeOp.t E.Eff.t =
  E.Eff.Bind
    ( E.Eff.Perform (E.NativeOp.RefMake, nat_lit 5)
    , E.Eff.Perform
        ( E.NativeOp.RefModifyWith
            (app
               "pair"
               [ E.Term.Fold
                   ( None
                   , nat_list [ 1; 2; 3 ]
                   , E.Term.Var (Z.of_int 1)
                   , app "add" [ E.Term.Var (Z.of_int 2); E.Term.Var (Z.of_int 3) ] )
               ; E.Term.Var (Z.of_int 1)
               ])
        , E.Term.Var (Z.of_int 0) ) )
;;

(* An empty list answers the initial value, and the body, which would refuse, is not run. *)
let p_fold_empty : E.NativeOp.t E.Eff.t =
  E.Eff.Succeed
    (E.Term.Fold
       (None, nil_t, nat_lit 7, E.Term.TupleAt (E.Term.Var (Z.of_int 1), Z.of_int 5)))
;;

(* A body that refuses on an element refuses the fold: no partial answer. *)
let p_fold_refuses : E.NativeOp.t E.Eff.t =
  E.Eff.Succeed
    (E.Term.Fold
       ( None
       , nat_list [ 1; 2 ]
       , nat_lit 0
       , E.Term.TupleAt (E.Term.Var (Z.of_int 1), Z.zero) ))
;;

(* ================================================================ one report per run *)

type report =
  { r_outcome : string
  ; r_answer : string
  ; r_fibers : int
  ; r_trace_len : int
  ; r_exits : (int * string) list
  ; r_rows : (int * string) list
  ; r_trace : string list
  ; r_store : string
  ; r_root : string option
  }

let show_frontier (f : E4_engine.frontier) =
  Printf.sprintf
    "parked=[%s] armed=[%s] due=%d"
    (String.concat
       ","
       (List.map (fun (a, b) -> Printf.sprintf "%d:%d" a b) f.E4_engine.parked))
    (String.concat "," (List.map string_of_int f.E4_engine.armed))
    f.E4_engine.due
;;

let show_answer (a : E4_engine.answer) =
  match a with
  | E4_engine.Finished -> "Finished"
  | E4_engine.Suspended f -> "Suspended " ^ show_frontier f
  | E4_engine.Refused r -> "Refused " ^ r
  | E4_engine.Outside_profile r -> "Outside_profile " ^ Lcnf_crossing.refusal_text r
  | E4_engine.Delay f -> "Delay " ^ show_frontier f
;;

module Rep (En : E4_engine.ENGINE) = struct
  let of_t (t : En.t) : report =
    { r_outcome = En.outcome t
    ; r_answer = show_answer (En.answer t)
    ; r_fibers = En.fiber_count t
    ; r_trace_len = En.trace_length t
    ; r_exits = En.exits t
    ; r_rows = En.fiber_rows t
    ; r_trace = En.trace_rows t
    ; r_store = En.store_row t
    ; r_root = En.root_exit t
    }
  ;;

  let report (p : E.NativeOp.t E.Eff.t) ~(fuel : int) : report = of_t (En.run p ~fuel)

  (* The instance's OWN generated `Effect4.Api.run`, so the drive loop is checked against
     the function it is a re-implementation of. *)
  let api_outcome (p : E.NativeOp.t E.Eff.t) ~(fuel : int) : string = En.api_run p ~fuel
end

module RF = Rep (En_fast)
module RG = Rep (En_gen)

let differ (a : report) (b : report) : string list =
  let d = ref [] in
  let cmp label x y = if x <> y then d := label :: !d in
  cmp "outcome" a.r_outcome b.r_outcome;
  cmp "answer" a.r_answer b.r_answer;
  cmp "fibers" (string_of_int a.r_fibers) (string_of_int b.r_fibers);
  cmp "trace_len" (string_of_int a.r_trace_len) (string_of_int b.r_trace_len);
  cmp
    "exits"
    (String.concat "|" (List.map snd a.r_exits))
    (String.concat "|" (List.map snd b.r_exits));
  cmp
    "fiber_rows"
    (String.concat "|" (List.map snd a.r_rows))
    (String.concat "|" (List.map snd b.r_rows));
  cmp "trace" (String.concat "|" a.r_trace) (String.concat "|" b.r_trace);
  cmp "store" a.r_store b.r_store;
  cmp
    "root_exit"
    (match a.r_root with
     | None -> "-"
     | Some s -> s)
    (match b.r_root with
     | None -> "-"
     | Some s -> s);
  List.rev !d
;;

(* ================================================================ 1. G0 *)

let g0 () =
  print_endline "== 1. G0 on Fast, and its whole report against Gen (fuel 1000) ==";
  let one name (p : E.NativeOp.t E.Eff.t) expect_outcome expect_fibers expect_root =
    match guard (fun () -> RF.report p ~fuel:1000, RG.report p ~fuel:1000) with
    | Error e -> fail_note ("G0 " ^ name) e
    | Ok (f, g) ->
      Printf.printf
        "  %-7s Fast: outcome=%s fibers=%d exit=%s trace=%d\n"
        name
        f.r_outcome
        f.r_fibers
        (match f.r_root with
         | None -> "<no exit>"
         | Some s -> s)
        f.r_trace_len;
      check
        (Printf.sprintf
           "G0 %s on Fast (%s, fibers=%d, %s)"
           name
           expect_outcome
           expect_fibers
           (match expect_root with
            | None -> "no exit"
            | Some s -> s))
        (f.r_outcome = expect_outcome
         && f.r_fibers = expect_fibers
         && f.r_root = expect_root);
      check (Printf.sprintf "G0 %s: Fast = Gen, whole report" name) (differ f g = []);
      check
        (Printf.sprintf "G0 %s: the drive loop = the generated Api.run (Fast)" name)
        (RF.api_outcome p ~fuel:1000 = f.r_outcome)
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
  one
    "pFoldNested"
    p_fold_nested
    "finished"
    1
    (Some "success list[list[1,2],list[2,2],list[3,1]]");
  one "pFoldInOp" p_fold_in_op "finished" 1 (Some "success 11");
  (* Controls.  An empty list answers the initial value and never runs the body.  A body that
     refuses on an element refuses the fold, and the machine answers its wrong-shape defect. *)
  one "pFoldEmpty" p_fold_empty "finished" 1 (Some "success 7");
  one "pFoldRefuses" p_fold_refuses "finished" 1 (Some "failure [die(badName)]")
;;

(* Handwritten carrier substitutions must retain creation provenance. These checks call
   the prelude function actually spliced into the generated engine's instance. *)
let origin_prelude_check () =
  let () =
    let module I = Api_engine_inst in
    let program = p42 in
    let machine = I.load program ~fuel:(Z.of_int 100) in
    let parent = List.assoc Z.zero (I.fibers machine) in
    check
      "Fast creation origin: the root has no fork record"
      (match machine.forks with
       | [] -> true
       | _ -> false);
    let options =
      { Eff_types.ForkOptions.start_immediately = true
      ; daemon = true
      ; mask_mode = Eff_types.MaskMode.Inherit
      }
    in
    let site = [ Z.of_int 3; Z.one ] in
    let spawned, (_, child_id) =
      I.sh_spawn (I.interp_of [] program) machine parent parent.frame.current options site
    in
    let _child = List.assoc child_id (I.fibers spawned) in
    check
      "Fast creation origin: spawn retains parent, daemon and exact site"
      (match spawned.forks with
       | [ (record : I.fork_record) ] ->
         Z.equal record.child child_id
         && Z.equal record.parent Z.zero
         && record.daemon
         && List.equal Z.equal record.site site
       | _ -> false)
  in
  ()
;;

(* The clock is an ordinary natural, Zarith's `Z.t` (M4): its storage, its arithmetic and its
   reading are exact past max_int, on the generated machine and through the engine. Expected
   decimals are independent of the clock arithmetic used by the machine. *)
let clock_exactness_check () =
  (* Read the actual generated machine: store_row deliberately omits timers, so accepting
     a decision through the public wrapper alone cannot detect a narrowed clock. *)
  let check_generated name load advance evaluate now deadlines root_succeeded =
    let prefix = name ^ " generated clock: " in
    let step label f m =
      let next, settled = f m in
      check (prefix ^ label ^ " settles") settled;
      next
    in
    let clock_is m expected = String.equal (Z.to_string (now m)) expected in
    let deadlines_are m expected =
      List.equal String.equal (List.map Z.to_string (deadlines m)) expected
    in
    let huge = Z.of_string "4611686018427387905" in
    let m0 = load () in
    check (prefix ^ "load starts at zero") (clock_is m0 "0");
    let m1 = step "advance beyond max_int" (advance huge) m0 in
    check
      (prefix ^ "large advance retains every digit")
      (clock_is m1 "4611686018427387905");
    let m2 = step "add seven" (advance (Z.of_int 7)) m1 in
    check
      (prefix ^ "addition beyond max_int is exact")
      (clock_is m2 "4611686018427387912");
    let asleep = step "register sleep" evaluate m2 in
    check
      (prefix ^ "sleep stores the exact now plus duration")
      (clock_is asleep "4611686018427387912"
       && deadlines_are asleep [ "4611686018427387929" ]
       && not (root_succeeded asleep));
    let early = step "advance before deadline" (advance (Z.of_int 16)) asleep in
    check
      (prefix ^ "timer remains pending one millisecond before its deadline")
      (clock_is early "4611686018427387928"
       && deadlines_are early [ "4611686018427387929" ]
       && not (root_succeeded early));
    let fired = step "cross deadline" (advance (Z.of_int 4)) early in
    check
      (prefix ^ "timer fires and advance finishes at its exact target")
      (clock_is fired "4611686018427387932"
       && deadlines_are fired []
       && root_succeeded fired);
    let later = step "add another large advance" (advance huge) fired in
    check
      (prefix ^ "successive large advances exceed signed 64-bit exactly")
      (clock_is later "9223372036854775837")
  in
  let sleep_then_42 =
    E.Eff.Bind
      (E.Eff.Perform (E.NativeOp.Sleep, E.Term.Lit (E.Lit.Nat (Z.of_int 17))), p42)
  in
  let () =
    let module I = Api_engine_inst in
    let p = sleep_then_42 in
    let prepared = I.prepare [] p in
    let step m d = I.step prepared ~fuel:(Z.of_int 100) m d in
    check_generated
      I.name
      (fun () -> I.load p ~fuel:(Z.of_int 100))
      (fun millis m -> step m (I.RunDecision_advance millis))
      (fun m -> step m (I.RunDecision_evaluate Z.zero))
      (fun m -> (I.stores_of m).timers.now)
      (fun m ->
         List.map
           (fun (w : Z.t I.waiter) -> w.payload)
           (I.stores_of m).timers.wake.waiters)
      (fun m ->
         match List.assoc_opt Z.zero (I.completed_exits m) with
         | Some (Eff_types.Exit.Success (Eff_types.Val.Nat n)) -> Z.equal n (Z.of_int 42)
         | _ -> false)
  in
  (* `clockNow` answers the clock as a natural: past max_int it is the exact number, where
     until M4 it refused at the clock crossing. *)
  let check_instance (module En : E4_engine.ENGINE) =
    let p =
      E.Eff.Bind
        ( E.Eff.Perform (E.NativeOp.RefMake, E.Term.Lit (E.Lit.Nat (Z.of_int 7)))
        , E.Eff.Perform (E.NativeOp.ClockNow, E.Term.Lit E.Lit.Unit) )
    in
    let prefix = En.name ^ " exact clock: " in
    let m0 = En.load p ~fuel:100 in
    let m = En.step m0 (En.advance_exact (Z.of_string "4611686018427387904")) in
    check
      (prefix ^ "large adjustment is accepted")
      (match En.answer m with
       | E4_engine.Outside_profile _ -> false
       | _ -> true);
    let read = En.replay m [ En.evaluate 0; En.flush ] in
    check
      (prefix ^ "clockNow answers the exact clock past max_int")
      (Option.equal String.equal (En.root_exit read) (Some "success 4611686018427387904"));
    (* the red control: the host's int does not hold the clock it read *)
    check
      (prefix ^ "(red control) the host's int does not hold 2^62")
      (not (Z.fits_int (Z.of_string "4611686018427387904")))
  in
  check_instance (module En_fast);
  check_instance (module En_gen)
;;

(* A crossing's refusal (`Lcnf_crossing.Refused`) is a host boundary result (EN3): the step
   that raised it is not taken, the input machine is retained and the decision stays unread.
   No program reaches a crossing since M4 (no atom narrows a natural to the target's int), so
   the stand-in is the generated machine whose flush computes a shift past the target's int,
   which the runtime library refuses at the arithmetic crossing. *)
module Refusing = struct
  include Api_engine_inst

  let name = "Refusing"

  let step prepared ~fuel m d =
    match d with
    | RunDecision_flush ->
      (* 2^62 is no shift the target's int holds: `Lcnf_nat.to_shift_exn` refuses *)
      ignore (Lcnf_nat.shift_left Z.one (Z.shift_left Z.one 62));
      Api_engine_inst.step prepared ~fuel m d
    | _ -> Api_engine_inst.step prepared ~fuel m d
  ;;
end

module En_refusing = E4_engine.Make (Refusing)

let crossing_retention_check () =
  let module En = En_refusing in
  let module Projection = E4_diff.Of (En) in
  let prefix = En.name ^ " crossing: " in
  let p =
    E.Eff.Bind
      ( E.Eff.Perform (E.NativeOp.RefMake, E.Term.Lit (E.Lit.Nat (Z.of_int 7)))
      , E.Eff.Perform (E.NativeOp.ClockNow, E.Term.Lit E.Lit.Unit) )
  in
  let m = En.load p ~fuel:100 in
  let before = En.refs m, En.trace_rows m, En.fiber_rows m, En.store_row m in
  let refused, residue = En.replay_to m [ En.flush; En.evaluate 0 ] in
  check
    (prefix ^ "a refused step answers Outside_profile, at the arithmetic crossing")
    (match En.answer refused with
     | E4_engine.Outside_profile r -> r.Lcnf_crossing.crossing = Lcnf_crossing.Arithmetic
     | _ -> false);
  check
    (prefix ^ "mid-decision refusal retains the input machine")
    (before
     = ( En.refs refused
       , En.trace_rows refused
       , En.fiber_rows refused
       , En.store_row refused ));
  check (prefix ^ "refused decision stays unread") (List.length residue = 2);
  check
    (prefix ^ "refusal cannot become differential agreement")
    (match Projection.project refused with
     | _ -> false
     | exception Lcnf_crossing.Refused _ -> true);
  check
    (prefix ^ "halted refusal holds the input machine")
    (En.step refused En.flush == refused)
;;

(* The run is exact (M4, decisions row 417 (1)): a product past the rc.112 profile's bound and
   past the host's int is the exact natural, on the native profile, which has no bound. The
   profile is a datum checked at ingress, not by the run's arithmetic (D3). *)
let multiplication_exactness_check () =
  let program a b =
    E.Eff.Bind
      ( E.Eff.Perform (E.NativeOp.RefMake, nat_lit 7)
      , E.Eff.Succeed
          (E.Term.App
             ( "mul"
             , E.Terms.Cons
                 ( E.Term.Lit (E.Lit.Nat a)
                 , E.Terms.Cons (E.Term.Lit (E.Lit.Nat b), E.Terms.Nil) ) )) )
  in
  let edge = Z.of_string "9007199254740991" in
  let check_instance (module En : E4_engine.ENGINE) =
    let prefix = En.name ^ " multiplication: " in
    List.iter
      (fun (label, a, b, expected) ->
         let result = En.run (program a b) ~fuel:100 in
         check
           (prefix ^ label)
           (Option.equal
              String.equal
              (En.root_exit result)
              (Some ("success " ^ expected))))
      [ "ordinary", Z.of_int 6, Z.of_int 7, "42"
      ; "zero at the boundary", Z.zero, edge, "0"
      ; "largest product inside the rc.112 profile", edge, Z.one, "9007199254740991"
      ; ( "first product past the rc.112 profile is exact"
        , Z.of_string "4503599627370496"
        , Z.of_int 2
        , "9007199254740992" )
      ; ( "an odd square past 2^53 is exact"
        , Z.of_int 134217729
        , Z.of_int 134217729
        , "18014398777917441" )
      ; ( "a product past the host's int is exact"
        , edge
        , edge
        , "81129638414606663681390495662081" )
      ];
    (* the red control: binary64 rounds the odd square, which is what the exact product rules out *)
    check
      (prefix ^ "(red control) binary64 rounds 134217729^2 to an even number")
      (Float.equal (134217729.0 *. 134217729.0) 18014398777917440.0)
  in
  check_instance (module En_fast);
  check_instance (module En_gen)
;;

(* EN8: a program's literals are profile support's, Lean's, lowered (`literal_refusal`, at
   rc.112's profile): the first literal above the bound is refused at the address of its node,
   from a value and from the wire, on both instances. The decision constructors check nothing:
   a raw decision is a trusted input, and ingress is the driver's question. *)
let numeric_ingress_check () =
  let edge = Z.of_string "9007199254740991" in
  let past = Z.succ edge in
  let lit n = E.Eff.Succeed (E.Term.Lit (E.Lit.Nat n)) in
  let above at n = Some { E.Located.site = at; reason = E.ProfileReason.AboveBound n } in
  let check_instance (module En : E4_engine.ENGINE) =
    let prefix = En.name ^ " numeric ingress: " in
    check
      (prefix ^ "the largest literal inside the profile")
      (En.literal_refusal (lit edge) = None);
    check
      (prefix ^ "a literal above the profile, refused at its node")
      (En.literal_refusal (lit past) = above [] past);
    check
      (prefix ^ "a literal in a bind's continuation, refused at its address")
      (En.literal_refusal (E.Eff.Bind (p42, lit past)) = above [ Z.one ] past);
    check
      (prefix ^ "a literal above the profile from the wire, refused")
      (match Eff_codec.decode_program (Eff_codec.encode_program (lit past)) with
       | Some p -> En.literal_refusal p = above [] past
       | None -> false);
    check
      (prefix ^ "a literal past the host's int, refused at its node")
      (let huge = Z.shift_left Z.one 64 in
       En.literal_refusal (lit huge) = above [] huge);
    check
      (prefix ^ "a constructor checks nothing")
      (match En.answer_async_success 0 0 (Z.to_int past) with
       | _ -> true
       | exception _ -> false)
  in
  check_instance (module En_fast);
  check_instance (module En_gen)
;;

(* EN9: a host's answer is host ingress (`ingress`): an answer that is no Lean value is
   `Not_a_value` (`Eff_val.valid` over its value tree), and one that Lean's profile support
   refuses is `Unsupported`, at its path in the answer's value tree (`answerTree`, lowered), on
   both instances. The red controls answer a natural outside the profile or a string that is
   not valid UTF-8, at the top and nested; the green ones answer naturals inside the profile,
   valid UTF-8 outside ASCII, and fields that are no naturals. *)
let answer_ingress_check () =
  let success v = E.Completion.OfExit (E.Exit.Success v) in
  let failure reasons = E.Completion.OfExit (E.Exit.Failure reasons) in
  let top = Z.of_string "9007199254740991" in
  let above = Z.succ top in
  let unsupported = function
    | Some (E4_engine.Unsupported _) -> true
    | _ -> false
  and not_a_value = function
    | Some E4_engine.Not_a_value -> true
    | _ -> false
  in
  let check_instance (module En : E4_engine.ENGINE) =
    let prefix = En.name ^ " answer ingress: " in
    List.iter
      (fun (label, refused, answer) ->
         check (prefix ^ label ^ " refused") (refused (En.ingress answer)))
      [ "a natural above the profile", unsupported, success (E.Val.Nat above)
      ; "a negative natural", not_a_value, success (E.Val.Nat (Z.of_int (-1)))
      ; ( "a nested natural"
        , unsupported
        , success (E.Val.List [ E.Val.Pair (E.Val.Unit, E.Val.Some (E.Val.Nat above)) ]) )
      ; "a constructor index", unsupported, success (E.Val.Ctor (above, []))
      ; "a handle key", not_a_value, success (E.Val.Handle (0, Z.of_int (-1)))
      ; "a negative integer's magnitude", unsupported, success (E.Val.NegInt above)
      ; ( "the least negative integer past the profile"
        , unsupported
        , success (E.Val.NegInt top) )
      ; "an error code", unsupported, failure [ E.Reason.Fail (E.Err.Tag above, []) ]
      ; ( "an error's payload"
        , not_a_value
        , failure [ E.Reason.Fail (E.Err.Payload (E.Val.Nat (Z.of_int (-1))), []) ] )
      ; ( "a defect's payload"
        , unsupported
        , failure [ E.Reason.Die (E.Defect.User above, []) ] )
      ; ( "an interrupting fiber"
        , not_a_value
        , failure [ E.Reason.Interrupt (Some (Z.of_int (-1)), []) ] )
      ; "a ref key", not_a_value, E.Completion.OfRefGet (Z.of_int (-1))
      ; (* a Lean String is valid UTF-8, so a reply's string must be (2.2a's open item) *)
        ( "a string with a byte no UTF-8 starts with"
        , not_a_value
        , success (E.Val.Str "\xff") )
      ; ( "a nested truncated sequence"
        , not_a_value
        , success (E.Val.List [ E.Val.Some (E.Val.Str "caf\xc3") ]) )
      ; "an encoded surrogate", not_a_value, success (E.Val.Str "\xed\xa0\x80")
      ; "an error's text", not_a_value, failure [ E.Reason.Fail (E.Err.Text "\xff", []) ]
      ; ( "an error's tag"
        , not_a_value
        , failure [ E.Reason.Fail (E.Err.Tagged ("\xc0\xaf", "message"), []) ] )
      ; ( "an error's tagged message"
        , not_a_value
        , failure [ E.Reason.Fail (E.Err.Tagged ("tag", "\xff"), []) ] )
      ; ( "an annotation's key"
        , not_a_value
        , failure [ E.Reason.Die (E.Defect.BadName, [ "\xff", () ]) ] )
      ];
    (* The refusal is located: the nested natural's path in the exit's value tree, the success
       frame's child 0, the list's item 0, the pair's child 1, the option's child 0. *)
    check
      (prefix ^ "a nested natural is refused at its path")
      (En.ingress
         (success (E.Val.List [ E.Val.Pair (E.Val.Unit, E.Val.Some (E.Val.Nat above)) ]))
       = Some
           (E4_engine.Unsupported
              { E.Located.site = [ Z.zero; Z.zero; Z.one; Z.zero ]
              ; reason = E.ProfileReason.AboveBound above
              }));
    (* a negative integer's reason names its magnitude, n + 1 (M4) *)
    check
      (prefix ^ "a negative integer is refused with its magnitude")
      (En.ingress (success (E.Val.NegInt top))
       = Some
           (E4_engine.Unsupported
              { E.Located.site = [ Z.zero ]; reason = E.ProfileReason.BelowBound above })
      );
    List.iter
      (fun (label, answer) ->
         check (prefix ^ label ^ " passes") (Option.is_none (En.ingress answer)))
      [ "the top natural", success (E.Val.Nat top)
      ; ( "nested naturals"
        , success (E.Val.Ctor (Z.of_int 0, [ E.Val.Nat top; E.Val.NegInt (Z.of_int 0) ]))
        )
      ; ( "the least negative integer inside the profile"
        , success (E.Val.NegInt (Z.pred top)) )
      ; ( "no natural"
        , success
            (E.Val.List
               [ E.Val.Str "x"
               ; E.Val.Bytes [ 255 ]
               ; E.Val.Float (Z.of_int 1)
               ; E.Val.Ref (1, [ 2 ])
               ]) )
      ; ( "a failure"
        , failure
            [ E.Reason.Die (E.Defect.Error (E.Err.Tag top), [])
            ; E.Reason.Interrupt (Some Z.zero, [])
            ] )
      ; "a ref key", E.Completion.OfRefGet top
      ; (* the red controls' green twins: valid UTF-8 outside ASCII passes *)
        "a string outside ASCII", success (E.Val.Str "caf\xc3\xa9 \xf0\x9f\x98\x80")
      ; ( "texts outside ASCII"
        , failure
            [ E.Reason.Fail
                (E.Err.Tagged ("t\xc3\xa9", "\xe2\x82\xac"), [ "k\xc3\xa9", () ])
            ] )
      ]
  in
  check_instance (module En_fast);
  check_instance (module En_gen)
;;

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
;;

let bench () =
  print_endline "";
  print_endline "== W1: the GENERATED Api.run, fuel 100, 20 000 iterations, best of 3 ==";
  print_endline "  program  instance  ms         iterations/s   decisions/s";
  let iters = 20_000 in
  let w1 (prog : string) (name : string) (run : unit -> unit) =
    let ms = best_of 3 run *. 1000.0 in
    Printf.printf
      "  %-8s %-9s %-10.2f %-14.0f %.0f\n"
      prog
      name
      ms
      (float_of_int iters /. (ms /. 1000.0))
      (2.0 *. float_of_int iters /. (ms /. 1000.0))
  in
  let w1_pair prog (p : E.NativeOp.t E.Eff.t) =
    let pf = p
    and pg = p in
    w1 prog "Fast" (fun () ->
      for _ = 1 to iters do
        ignore (En_fast.api_run pf ~fuel:100)
      done);
    w1 prog "Gen" (fun () ->
      for _ = 1 to iters do
        ignore (En_gen.api_run pg ~fuel:100)
      done)
  in
  w1_pair "p42" p42;
  w1_pair "pAwait" p_await;
  w1_pair "pFork" p_fork;
  print_endline "";
  print_endline "== W2: the chain of refMake, fuel 8n+400, best of 5 ==";
  print_endline
    "  n     instance  steps  refs  load ms   run ms     steps/s      held words   held \
     bytes";
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
       let w2 name api_run load_program run trace_length refs =
         let prog = p in
         let t = run prog ~fuel in
         let steps = trace_length t
         and nrefs = List.length (refs t) in
         let load_ms = best_of 5 (fun () -> ignore (load_program prog ~fuel)) *. 1000.0 in
         let ms = best_of 5 (fun () -> ignore (api_run prog ~fuel)) *. 1000.0 in
         let words = held_words (fun () -> run p ~fuel) in
         Printf.printf
           "  %-5d %-9s %-6d %-5d %-9.3f %-10.3f %-12.0f %-12d %d\n"
           n
           name
           steps
           nrefs
           load_ms
           ms
           (float_of_int steps /. (ms /. 1000.0))
           words
           (words * 8)
       in
       w2
         "Fast"
         (fun p ~fuel -> En_fast.api_run p ~fuel)
         (fun p ~fuel -> En_fast.load_program p ~fuel)
         (fun p ~fuel -> En_fast.run_program p ~fuel)
         En_fast.trace_length
         En_fast.refs;
       w2
         "Gen"
         (fun p ~fuel -> En_gen.api_run p ~fuel)
         (fun p ~fuel -> En_gen.load_program p ~fuel)
         (fun p ~fuel -> En_gen.run_program p ~fuel)
         En_gen.trace_length
         En_gen.refs)
    [ 50; 100; 300; 500; 1000 ]
;;

(* E4-PROV-CE-005: the layer's lexical environment starts closed, matching its checker. *)
let layer_environment_check () =
  let key = { E.ServiceKey.name = Z.of_int 4; service = Z.of_int 4 } in
  let program =
    E.Eff.Bind
      ( E.Eff.Succeed (E.Term.Lit (E.Lit.Nat (Z.of_int 9)))
      , E.Eff.Scoped
          (E.Eff.ProvideLayer
             ( E.LayerTerm.Effect
                 ( key
                 , E.Eff.Bind
                     ( E.Eff.Succeed (E.Term.Lit (E.Lit.Str "x"))
                     , E.Eff.Fail (E.Term.Var (Z.of_int 0)) ) )
             , false
             , E.Eff.Service key )) )
  in
  let expected = Some "failure [fail(text x)]" in
  let fast = En_fast.root_exit (En_fast.run program ~fuel:200) in
  let generated = En_gen.root_exit (En_gen.run program ~fuel:200) in
  Printf.printf "layer environment Fast: %s\n" (Option.value fast ~default:"frontier");
  Printf.printf "layer environment Gen: %s\n" (Option.value generated ~default:"frontier");
  check "layer environment Fast uses the body binding" (fast = expected);
  check "layer environment Gen uses the body binding" (generated = expected)
;;

(* ================================================================ main *)

let () =
  print_endline
    "== lane D: the drive loop, the conversion, the generated engine against the \
     generated machine ==";
  Printf.printf "  Fast = %s\n  Gen  = %s\n" En_fast.carriers En_gen.carriers;
  print_endline "";
  g0 ();
  clock_exactness_check ();
  crossing_retention_check ();
  numeric_ingress_check ();
  answer_ingress_check ();
  multiplication_exactness_check ();
  origin_prelude_check ();
  layer_environment_check ();
  print_endline "";
  print_endline "== 5. the two failwith rows of the generated prelude ==";
  check
    (Printf.sprintf
       "sh_dispatcher_mk / sh_memo_map_mk never fired in this file's runs (%d hits); \
        over every corpus, a raise fails test_diff"
       !extern_holes)
    (!extern_holes = 0);
  bench ();
  print_endline "";
  E4_check.finish ()
;;
