(* prop_wire — the property test of the wire on random untyped values (hand-written).
   Generator: a size-bounded random walk over every constructor of eff, stmt, stmts, effs,
   action_term, term, terms, cause_term, lit, ty, native_op, fork_options, row and eff_ty,
   with nats spread over 0 .. 2^62 - 1 and strings drawn from a list of valid UTF-8 (ASCII,
   two-, three- and four-byte scalars, quotes, backslashes, control characters).
   Properties, N = 400 programs, 400 types, 200 rows, 200 eff_tys, seed 42:
     P1  decode_exact (encode v) = Some v                      (stability)
     P2  decode (encode v ^ junk) = Some (v, |encode v|)       (self-delimiting; junk not read)
     P3  decode_exact (encode v ^ junk) = None                 (exactness)
     P4  encode is injective on the sample (a hash table of the encodings)
     P5  the JSON printer terminates on every sample
   Exit status 1 on any failure. *)

open Eff_types

let rng = Random.State.make [| 42 |]
let ri n = Random.State.int rng n
let rb () = Random.State.bool rng
let pick xs = List.nth xs (ri (List.length xs))

let rand_nat () =
  match ri 5 with
  | 0 -> ri 10
  | 1 -> ri 256
  | 2 -> ri 100000
  | 3 -> Random.State.bits rng
  | _ -> (Random.State.bits rng lsl 32) lor Random.State.bits rng

let strings =
  [ ""; "a"; "succ"; "Ref.Ref<number>"; "h\xc3\xa9llo"; "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e"; "\xf0\x9f\x98\x80"
  ; "quote\"back\\slash"; "\n\t\001\127"; "Deferred.Deferred<number, number>" ]

let rand_string () = pick strings

(* All 53 op values — every constructor, and inside them every FnName and every
   FinalizerStrategy — are enumerated by Eff_native.all_ops, so drawing from it covers
   the op alphabet without a separate FnName/FinalizerStrategy generator. *)
let rand_op () = pick Eff_native.all_ops
let rand_mask () = pick [ Mask_mode_interruptible; Mask_mode_uninterruptible; Mask_mode_inherit ]
let rand_mode () = pick [ Observer_mode_awaitValue; Observer_mode_joinEffect ]

let rand_options () =
  { fork_options_startImmediately = rb (); fork_options_daemon = rb (); fork_options_maskMode = rand_mask () }

let rand_lit () =
  match ri 4 with
  | 0 -> Lit_unit
  | 1 -> Lit_nat (rand_nat ())
  | 2 -> Lit_bool (rb ())
  | _ -> Lit_str (rand_string ())

let rec rand_term d =
  if d <= 0 then (if rb () then Term_var (ri 20) else Term_lit (rand_lit ()))
  else
    match ri 3 with
    | 0 -> Term_var (rand_nat ())
    | 1 -> Term_lit (rand_lit ())
    | _ -> Term_app (rand_string (), rand_terms (d - 1))

and rand_terms d = if d <= 0 || ri 3 = 0 then Terms_nil else Terms_cons (rand_term (d - 1), rand_terms (d - 1))

let rec rand_cause d =
  match if d <= 0 then ri 3 else ri 4 with
  | 0 -> Cause_term_fail (rand_term d)
  | 1 -> Cause_term_die (rand_term d)
  | 2 -> Cause_term_interrupt (if rb () then None else Some (rand_term d))
  | _ -> Cause_term_both (rand_cause (d - 1), rand_cause (d - 1))

let rec rand_eff d =
  let t () = rand_term (min d 2) in
  if d <= 0 then
    match ri 4 with
    | 0 -> Eff_succeed (t ())
    | 1 -> Eff_yieldNow (rand_nat ())
    | 2 -> Eff_fail (t ())
    | _ -> Eff_perform (rand_op (), t ())
  else
    let e () = rand_eff (d - 1) in
    match ri 24 with
    | 0 -> Eff_succeed (t ())
    | 1 -> Eff_fail (t ())
    | 2 -> Eff_failCause (rand_cause (d - 1))
    | 3 -> Eff_yieldError (t ())
    | 4 -> Eff_sync (t ())
    | 5 -> Eff_suspend (e ())
    | 6 -> Eff_perform (rand_op (), t ())
    | 7 -> Eff_bind (e (), e ())
    | 8 -> Eff_gen (rand_stmts (d - 1))
    | 9 -> Eff_catchCause (e (), e ())
    | 10 -> Eff_matchCause (e (), e (), e ())
    | 11 -> Eff_onExit (e (), e ())
    | 12 -> Eff_exit (e ())
    | 13 -> Eff_uninterruptible (e ())
    | 14 -> Eff_interruptible (e ())
    | 15 -> Eff_branch (t (), e (), e ())
    | 16 -> Eff_whileLoop (t (), t (), t (), e ())
    | 17 -> Eff_yieldNow (rand_nat ())
    | 18 -> Eff_callback (rand_op (), t ())
    | 19 -> Eff_awaitFiber (t (), rand_mode ())
    | 20 -> Eff_withFiber (rand_action (d - 1))
    | 21 -> Eff_scoped (e ())
    | 22 -> Eff_acquireRelease (e (), e ())
    | _ -> Eff_choose (rand_nat (), e (), e ())

and rand_stmt d =
  match ri 6 with
  | 0 -> Stmt_bindYield (rand_eff d)
  | 1 -> Stmt_yieldDiscard (rand_eff d)
  | 2 -> Stmt_ret (rand_term d)
  | 3 -> Stmt_ifElse (rand_term d, rand_stmts (d - 1), rand_stmts (d - 1))
  | 4 -> Stmt_whileTrue (rand_stmts (d - 1))
  | _ -> Stmt_breakLoop

and rand_stmts d = if d <= 0 || ri 3 = 0 then Stmts_nil else Stmts_cons (rand_stmt (d - 1), rand_stmts (d - 1))
and rand_effs d = if d <= 0 || ri 3 = 0 then Effs_nil else Effs_cons (rand_eff (d - 1), rand_effs (d - 1))

and rand_action d =
  let t () = rand_term (min d 2) in
  match ri 16 with
  | 0 -> Action_term_fork (rand_eff d, rand_options ())
  | 1 -> Action_term_forkIn (rand_eff d, rand_options (), t ())
  | 2 -> Action_term_forkScoped (rand_eff d, rand_options ())
  | 3 -> Action_term_runIn (t (), t ())
  | 4 -> Action_term_interrupt (t ())
  | 5 -> Action_term_interruptScoped (t ())
  | 6 -> Action_term_interruptAll (t (), if rb () then None else Some (t ()))
  | 7 -> Action_term_awaitAll (t ())
  | 8 -> Action_term_awaitAllFailFast (t ())
  | 9 -> Action_term_snapshotChildren
  | 10 -> Action_term_awaitNewChildren (t ())
  | 11 -> Action_term_raceAll (rand_effs d)
  | 12 -> Action_term_setContext (t ())
  | 13 -> Action_term_getContext
  | 14 -> Action_term_getId
  | _ -> Action_term_closeScope (t (), t ())

let rec rand_ty d =
  match if d <= 0 then ri 7 else ri 15 with
  | 0 -> Ty_never
  | 1 -> Ty_unit
  | 2 -> Ty_nat
  | 3 -> Ty_int
  | 4 -> Ty_string
  | 5 -> Ty_bool
  | 6 -> Ty_handle (rand_string ())
  | 7 -> Ty_option (rand_ty (d - 1))
  | 8 -> Ty_list (rand_ty (d - 1))
  | 9 -> Ty_prod (rand_ty (d - 1), rand_ty (d - 1))
  | 10 -> Ty_except (rand_ty (d - 1), rand_ty (d - 1))
  | 11 -> Ty_exitOf (rand_ty (d - 1), rand_ty (d - 1))
  | 12 -> Ty_causeOf (rand_ty (d - 1))
  | 13 -> Ty_fiberOf (rand_ty (d - 1), rand_ty (d - 1))
  | _ -> Ty_union (rand_ty (d - 1), rand_ty (d - 1))

let rand_key () =
  { service_key_name = { service_name_value = rand_nat () }; service_key_service = { service_type_code_value = rand_nat () } }

let rand_list f = List.init (ri 4) (fun _ -> f ())

let rand_row () =
  { row_name = rand_string (); row_spelling = rand_string ();
    row_shape = pick [ Row_shape_call; Row_shape_value ]; row_trailing = rand_list rand_string;
    row_kind = pick [ Row_kind_sync; Row_kind_async; Row_kind_program ];
    row_request = rand_ty 2; row_answer = rand_ty 2; row_error = rand_ty 2;
    row_requires = rand_list rand_key; row_cite = rand_string () }

let rand_eff_ty () = { eff_ty_answer = rand_ty 3; eff_ty_error = rand_ty 3; eff_ty_requires = rand_list rand_key }

let checks = ref 0
let failures = ref 0

let fail what i = incr failures; Printf.printf "FAIL: %s at sample %d\n%!" what i

let property (what : string) (n : int) (gen : unit -> 'a) (encode : 'a -> string)
    (decode_exact : string -> 'a option) (decode : string -> ('a * int) option) (print : 'a -> string) : unit =
  let seen = Hashtbl.create 1024 in
  for i = 1 to n do
    let v = gen () in
    let b = encode v in
    let junk = "\000\001\002" in
    incr checks;
    if decode_exact b <> Some v then fail (what ^ ": P1 decode_exact (encode v) = Some v") i;
    incr checks;
    if decode (b ^ junk) <> Some (v, String.length b) then fail (what ^ ": P2 self-delimiting") i;
    incr checks;
    if decode_exact (b ^ junk) <> None then fail (what ^ ": P3 trailing bytes refused") i;
    incr checks;
    (match Hashtbl.find_opt seen b with
     | Some v' when v' <> v -> fail (what ^ ": P4 two values with one encoding") i
     | _ -> Hashtbl.replace seen b v);
    incr checks;
    if String.length (print v) = 0 then fail (what ^ ": P5 JSON") i
  done

let () =
  let at d s p l = d s p l in
  property "eff" 400 (fun () -> rand_eff (ri 7)) Eff_wire.encode_eff Eff_wire.decode_eff_exact
    (fun s -> at Eff_wire.decode_eff s 0 (String.length s)) Eff_json.print_eff;
  property "ty" 400 (fun () -> rand_ty (ri 6)) Eff_wire.encode_ty Eff_wire.decode_ty_exact
    (fun s -> at Eff_wire.decode_ty s 0 (String.length s)) Eff_json.print_ty;
  property "row" 200 rand_row Eff_wire.encode_row Eff_wire.decode_row_exact
    (fun s -> at Eff_wire.decode_row s 0 (String.length s)) Eff_json.print_row;
  property "eff_ty" 200 rand_eff_ty Eff_wire.encode_eff_ty Eff_wire.decode_eff_ty_exact
    (fun s -> at Eff_wire.decode_eff_ty s 0 (String.length s)) Eff_json.print_eff_ty;
  property "fork_options" 50 rand_options Eff_wire.encode_fork_options Eff_wire.decode_fork_options_exact
    (fun s -> at Eff_wire.decode_fork_options s 0 (String.length s)) Eff_json.print_fork_options;
  Printf.printf "prop_wire: %d checks, %d failures (seed 42)\n%!" !checks !failures;
  if !failures > 0 then exit 1
