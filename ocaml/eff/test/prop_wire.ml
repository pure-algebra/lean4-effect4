(* prop_wire — the property test of the wire on random untyped values (hand-written).
   Generator: size-bounded random walks through program syntax and types.
   Focused controls retain record metadata, list lengths, read modes, tuple indices,
   and record-tag strings,
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

let rand_mask () = pick [ MaskMode_interruptible; MaskMode_uninterruptible; MaskMode_inherit ]
let rand_mode () = pick [ ObserverMode_awaitValue; ObserverMode_joinEffect ]

let rand_options () =
  { start_immediately = rb (); daemon = rb (); mask_mode = rand_mask () }

let rand_service_key () =
  { name = (rand_nat ()); service = (rand_nat ()) }

(* A canonical row of keys: strictly ascending by name, then service (`Effect4.Row`, `ServiceKey.Lt`). *)
let rand_keys () = List.sort_uniq compare (List.init (ri 4) (fun _ -> rand_service_key ()))

let rand_lit () =
  match ri 4 with
  | 0 -> Lit_unit
  | 1 -> Lit_nat (rand_nat ())
  | 2 -> Lit_bool (rb ())
  | _ -> Lit_str (rand_string ())

let rec rand_term d =
  if d <= 0 then (if rb () then Term_var (ri 20) else Term_lit (rand_lit ()))
  else
    match ri 8 with
    | 0 -> Term_var (rand_nat ())
    | 1 -> Term_lit (rand_lit ())
    | 2 -> Term_app (rand_string (), rand_terms (d - 1))
    | 3 -> Term_record
        (List.init (ri 4) (fun _ -> rand_string (), (rb (), pick [Ty_nat; Ty_int; Ty_number; Ty_string])),
         List.init (ri 4) (fun _ -> rand_string ()), rand_terms (d - 1))
    | 4 -> Term_field
        (pick [FieldReadMode_required; FieldReadMode_optional], rand_term (d - 1), rand_string ())
    | 5 -> Term_recordSet (rand_term (d - 1), rand_string (), rand_term (d - 1))
    | 6 -> Term_tupleAt (rand_term (d - 1), rand_nat ())
    | _ -> Term_fold
        ((if rb () then None else Some (pick [Ty_nat; Ty_string; Ty_list Ty_nat])),
         rand_term (d - 1), rand_term (d - 1), rand_term (d - 1))

and rand_terms d = if d <= 0 || ri 3 = 0 then Terms_nil else Terms_cons (rand_term (d - 1), rand_terms (d - 1))

(* The 23 built-in op values (`Eff_native.all_ops`) enumerate every FinalizerStrategy and hold
   each of the eight read-modify-write rows once, at its face: the unit literal for its binder
   term (the state plan's T5; the faces print the term as a function and spell no name).
   A row's binder term is any term (decisions row 43; the state plan's T3b), so one draw in
   four puts a random term in one of the eight rows.  External operations additionally sample
   scalar row indices. *)
let rand_term_op () =
  let f = rand_term 2 in
  match ri 8 with
  | 0 -> NativeOp_refUpdateWith f
  | 1 -> NativeOp_refGetAndUpdateWith f
  | 2 -> NativeOp_refUpdateAndGetWith f
  | 3 -> NativeOp_refUpdateSomeWith f
  | 4 -> NativeOp_refGetAndUpdateSomeWith f
  | 5 -> NativeOp_refUpdateSomeAndGetWith f
  | 6 -> NativeOp_refModifyWith f
  | _ -> NativeOp_refModifySomeWith f

let rand_op () =
  match ri 4 with
  | 0 -> NativeOp_external (rand_nat ())
  | 1 -> rand_term_op ()
  | _ -> pick Eff_native.all_ops

let rec rand_cause d =
  match if d <= 0 then ri 3 else ri 4 with
  | 0 -> CauseTerm_fail (rand_term d)
  | 1 -> CauseTerm_die (rand_term d)
  | 2 -> CauseTerm_interrupt (if rb () then None else Some (rand_term d))
  | _ -> CauseTerm_both (rand_cause (d - 1), rand_cause (d - 1))

let rand_decision () =
  pick [Decision_bool; Decision_option; Decision_tag (rand_string ());
        Decision_recordTag (rand_string ())]

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
    match ri 29 with
    | 0 -> Eff_succeed (t ())
    | 1 -> Eff_fail (t ())
    | 2 -> Eff_failCause (rand_cause (d - 1))
    | 3 -> Eff_fail (t ())
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
    | 15 -> Eff_select (t (), rand_decision (), e (), e ())
    | 16 -> Eff_iterate ((if rb () then None else Some Ty_nat), t (), t (), t (), t (), e ())
    | 17 -> Eff_yieldNow (rand_nat ())
    | 18 -> Eff_perform (rand_op (), t ())
    | 19 -> Eff_awaitFiber (t (), rand_mode ())
    | 20 -> Eff_withFiber (rand_action (d - 1))
    | 21 -> Eff_scoped (e ())
    | 22 -> Eff_acquireRelease (e (), e ())
    | 23 -> Eff_provideLayer (rand_layer (d - 1), rb (), e ())
    | 24 -> Eff_service (rand_service_key ())
    | 25 -> Eff_provideService (rand_service_key (), t (), e ())
    | 26 -> Eff_restore (t (), e ())
    | 27 -> Eff_provideContext (t (), e ())
    | _ -> Eff_catchIf (t (), e (), e ())

and rand_layer d =
  if d <= 0 then LayerTerm_succeed (rand_service_key (), rand_lit ())
  else
    match ri 8 with
    | 0 -> LayerTerm_succeed (rand_service_key (), rand_lit ())
    | 1 -> LayerTerm_effect (rand_service_key (), rand_eff (d - 1))
    | 2 -> LayerTerm_effectDiscard (rand_eff (d - 1))
    | 3 -> LayerTerm_provide (rand_layer (d - 1), rand_layer (d - 1))
    | 4 -> LayerTerm_provideMerge (rand_layer (d - 1), rand_layer (d - 1))
    | 5 -> LayerTerm_merge (rand_layer (d - 1), rand_layer (d - 1))
    | 6 -> LayerTerm_fresh (rand_layer (d - 1))
    | _ -> LayerTerm_orDie (rand_layer (d - 1))

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
  match ri 17 with
  | 0 -> ActionTerm_fork (rand_eff d, rand_options ())
  | 1 -> ActionTerm_forkIn (rand_eff d, rand_options (), t ())
  | 2 -> ActionTerm_forkScoped (rand_eff d, rand_options ())
  | 3 -> ActionTerm_runIn (t (), t ())
  | 4 -> ActionTerm_interrupt (t ())
  | 5 -> ActionTerm_interruptScoped (t ())
  | 6 -> ActionTerm_interruptAll (t (), if rb () then None else Some (t ()))
  | 7 -> ActionTerm_awaitAll (t ())
  | 8 -> ActionTerm_awaitAllFailFast (t ())
  | 9 -> ActionTerm_snapshotChildren
  | 10 -> ActionTerm_awaitNewChildren (t ())
  | 11 -> ActionTerm_raceAll (rand_effs d)
  | 12 -> ActionTerm_context (rand_keys ())
  | 13 -> ActionTerm_getId
  | 14 -> ActionTerm_getInterruptible
  | 15 -> ActionTerm_closeScope (t (), t ())
  | _ -> ActionTerm_raceAllFirst (rand_effs d)

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
  { name = (rand_nat ()); service = (rand_nat ()) }

let rand_list f = List.init (ri 4) (fun _ -> f ())

(* Requirement rows are canonical sets in the Lean source image. Invalid ordering and
   duplicates are tested separately by test_metadata; round-trip samples stay in-domain. *)
let rand_requirements () =
  let key (k : service_key) = k.name, k.service in
  List.sort_uniq (fun a b -> compare (key a) (key b)) (rand_list rand_key)

let rand_row_arg () =
  if rb () then RowArg_name (rand_string ()) else RowArg_str (rand_string ())

let rand_row () =
  { name = rand_string (); spelling = rand_string ();
    shape = pick [ RowShape_call; RowShape_value; RowShape_tupleCall; RowShape_method ]; trailing = rand_list rand_row_arg;
    kind = pick [ RowKind_sync; RowKind_async; RowKind_program ];
    request = rand_ty 2; answer = rand_ty 2; error = rand_ty 2;
    requires = rand_requirements (); cite = rand_string ();
    type_args = rand_list rand_string;
    registration = pick [ Registration_deferred; Registration_external ] }

let rand_eff_ty () = { answer = rand_ty 3; error = rand_ty 3; requires = rand_requirements () }

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

let record_controls =
  let raw = Term_record
      (["z", (true, Ty_int); "z", (false, Ty_number); "__proto__", (true, Ty_nat)],
       ["unknown"; "unknown"], Terms_cons (Term_lit (Lit_nat 1), Terms_nil)) in
  [ raw;
    Term_record (["x", (true, Ty_nat)], [], Terms_cons (Term_lit (Lit_nat 1), Terms_nil));
    Term_record (["x", (true, Ty_nat)], [], Terms_nil);
    Term_field (FieldReadMode_required, raw, "__proto__");
    Term_field (FieldReadMode_optional, raw, "a-b");
    Term_recordSet (raw, "a-b", Term_var 3) ]

let tuple_controls =
  [ Term_tupleAt (Term_var 0, 0);
    Term_tupleAt (Term_var 1, 9007199254740993);
    Term_tupleAt (Term_tupleAt (Term_var 2, 65537), max_int);
    Term_field (FieldReadMode_optional, Term_tupleAt (Term_var 3, 1), "a-b") ]

(* The list fold (decisions row 228): with no stated type and with one, and a fold inside a
   fold's body. *)
let fold_controls =
  [ Term_fold (None, Term_var 0, Term_lit (Lit_nat 0), Term_var 1);
    Term_fold (Some (Ty_list Ty_nat), Term_var 0, Term_app ("nil", Terms_nil), Term_var 1);
    Term_fold (None, Term_var 0, Term_var 1,
      Term_fold (Some Ty_never, Term_var 3, Term_var 2, Term_tupleAt (Term_var 5, 0))) ]

let decision_controls =
  [ Decision_bool; Decision_option; Decision_tag "Found";
    Decision_recordTag "Found"; Decision_recordTag "";
    Decision_recordTag "é\n\"raw" ]

let () =
  let at d s p l = d s p l in
  List.iteri (fun i term ->
      property ("record-term-" ^ string_of_int i) 1 (fun () -> term)
        Eff_wire.encode_term Eff_wire.decode_term_exact
        (fun s -> at Eff_wire.decode_term s 0 (String.length s)) Eff_json.print_term)
    record_controls;
  List.iteri (fun i term ->
      property ("tuple-term-" ^ string_of_int i) 1 (fun () -> term)
        Eff_wire.encode_term Eff_wire.decode_term_exact
        (fun s -> at Eff_wire.decode_term s 0 (String.length s)) Eff_json.print_term)
    tuple_controls;
  List.iteri (fun i term ->
      property ("fold-term-" ^ string_of_int i) 1 (fun () -> term)
        Eff_wire.encode_term Eff_wire.decode_term_exact
        (fun s -> at Eff_wire.decode_term s 0 (String.length s)) Eff_json.print_term)
    fold_controls;
  List.iteri (fun i decision ->
      property ("decision-" ^ string_of_int i) 1 (fun () -> decision)
        Eff_wire.encode_decision Eff_wire.decode_decision_exact
        (fun s -> at Eff_wire.decode_decision s 0 (String.length s)) Eff_json.print_decision)
    decision_controls;
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
