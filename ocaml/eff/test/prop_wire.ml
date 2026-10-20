(* prop_wire — the property test of the program codec on random untyped values (hand-written).
   Generator: size-bounded random walks through program syntax and types.
   Focused controls retain record metadata, list lengths, read modes, tuple indices,
   and record-tag strings,
   with nats spread over 0 .. 2^62 - 1 and strings drawn from a list of valid UTF-8 (ASCII,
   two-, three- and four-byte scalars, quotes, backslashes, control characters).
   The codec is Lean's exact embedding, lowered (Eff_codec over Eff_image and the framing kernel).
   A term, a decision, a type and fork options cross inside a program that holds them; a row and a
   program type cross by their own images.
   Properties, N = 400 programs, 400 types, 200 rows, 200 eff_tys, seed 42:
     P1  decode_program (encode_program p) = Some p             (stability); for a row and a
         program type, their lowered reading of their tree's bytes gives them back
     P2  the frames are self-delimiting: the kernel reads the program's tree from
         encode_program p ^ junk and stops at the end of its bytes, not reading the junk
     P3  decode_program (encode_program p ^ junk) = None        (exactness)
     P4  encode_program is injective on the sample (a hash table of the encodings)
     P5  Lean's JSON, lowered: the sample's print as the tools print it (`ShapeDoc.printTree`)
         reads back to the sample under Lean's located reader (`ShapeDoc.readLocated`), or is
         refused for a natural above the profile's limit (2^53 - 1); a term, a decision and fork
         options are read inside a program that holds them
   Exit status 1 on any failure. *)

open Eff_types
module G = Effect4_gen.Api_gen

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
;;

let strings =
  [ ""
  ; "a"
  ; "succ"
  ; "Ref.Ref<number>"
  ; "h\xc3\xa9llo"
  ; "\xe6\x97\xa5\xe6\x9c\xac\xe8\xaa\x9e"
  ; "\xf0\x9f\x98\x80"
  ; "quote\"back\\slash"
  ; "\n\t\001\127"
  ; "Deferred.Deferred<number, number>"
  ]
;;

let rand_string () = pick strings

let rand_mask () =
  pick [ MaskMode.Interruptible; MaskMode.Uninterruptible; MaskMode.Inherit ]
;;

let rand_mode () = pick [ ObserverMode.AwaitValue; ObserverMode.JoinEffect ]

let rand_options () =
  { ForkOptions.start_immediately = rb (); daemon = rb (); mask_mode = rand_mask () }
;;

let rand_service_key () = { ServiceKey.name = rand_nat (); service = rand_nat () }

(* A canonical row of keys: strictly ascending by name, then service (`Effect4.Row`, `ServiceKey.Lt`). *)
let rand_keys () =
  List.sort_uniq compare (List.init (ri 4) (fun _ -> rand_service_key ()))
;;

let rand_lit () =
  match ri 4 with
  | 0 -> Lit.Unit
  | 1 -> Lit.Nat (rand_nat ())
  | 2 -> Lit.Bool (rb ())
  | _ -> Lit.Str (rand_string ())
;;

let rec rand_term d =
  if d <= 0
  then if rb () then Term.Var (ri 20) else Term.Lit (rand_lit ())
  else (
    match ri 8 with
    | 0 -> Term.Var (rand_nat ())
    | 1 -> Term.Lit (rand_lit ())
    | 2 -> Term.App (rand_string (), rand_terms (d - 1))
    | 3 ->
      Term.Record
        ( List.init (ri 4) (fun _ ->
            rand_string (), (rb (), pick [ Ty.Nat; Ty.Int; Ty.Number; Ty.String ]))
        , List.init (ri 4) (fun _ -> rand_string ())
        , rand_terms (d - 1) )
    | 4 ->
      Term.Field
        ( pick [ FieldReadMode.Required; FieldReadMode.Optional ]
        , rand_term (d - 1)
        , rand_string () )
    | 5 -> Term.RecordSet (rand_term (d - 1), rand_string (), rand_term (d - 1))
    | 6 -> Term.TupleAt (rand_term (d - 1), rand_nat ())
    | _ ->
      Term.Fold
        ( (if rb () then None else Some (pick [ Ty.Nat; Ty.String; Ty.List Ty.Nat ]))
        , rand_term (d - 1)
        , rand_term (d - 1)
        , rand_term (d - 1) ))

and rand_terms d =
  if d <= 0 || ri 3 = 0
  then Terms.Nil
  else Terms.Cons (rand_term (d - 1), rand_terms (d - 1))
;;

(* The 23 built-in op values (`Eff_native.all_ops`) enumerate every FinalizerStrategy and hold
   each of the eight read-modify-write rows once, at its face: the unit literal for its binder
   term (the state plan's T5; the faces print the term as a function and spell no name).
   A row's binder term is any term (decisions row 43; the state plan's T3b), so one draw in
   four puts a random term in one of the eight rows.  External operations additionally sample
   scalar row indices. *)
let rand_term_op () =
  let f = rand_term 2 in
  match ri 8 with
  | 0 -> NativeOp.RefUpdateWith f
  | 1 -> NativeOp.RefGetAndUpdateWith f
  | 2 -> NativeOp.RefUpdateAndGetWith f
  | 3 -> NativeOp.RefUpdateSomeWith f
  | 4 -> NativeOp.RefGetAndUpdateSomeWith f
  | 5 -> NativeOp.RefUpdateSomeAndGetWith f
  | 6 -> NativeOp.RefModifyWith f
  | _ -> NativeOp.RefModifySomeWith f
;;

let rand_op () =
  match ri 4 with
  | 0 -> NativeOp.External (rand_nat ())
  | 1 -> rand_term_op ()
  | _ -> pick Eff_native.all_ops
;;

let rec rand_cause d =
  match if d <= 0 then ri 3 else ri 4 with
  | 0 -> CauseTerm.Fail (rand_term d)
  | 1 -> CauseTerm.Die (rand_term d)
  | 2 -> CauseTerm.Interrupt (if rb () then None else Some (rand_term d))
  | _ -> CauseTerm.Both (rand_cause (d - 1), rand_cause (d - 1))
;;

let rand_decision () =
  pick
    [ Decision.Bool
    ; Decision.Option
    ; Decision.Tag (rand_string ())
    ; Decision.RecordTag (rand_string ())
    ]
;;

let rec rand_eff d =
  let t () = rand_term (min d 2) in
  if d <= 0
  then (
    match ri 4 with
    | 0 -> Eff.Succeed (t ())
    | 1 -> Eff.YieldNow (rand_nat ())
    | 2 -> Eff.Fail (t ())
    | _ -> Eff.Perform (rand_op (), t ()))
  else (
    let e () = rand_eff (d - 1) in
    match ri 29 with
    | 0 -> Eff.Succeed (t ())
    | 1 -> Eff.Fail (t ())
    | 2 -> Eff.FailCause (rand_cause (d - 1))
    | 3 -> Eff.Fail (t ())
    | 4 -> Eff.Sync (t ())
    | 5 -> Eff.Suspend (e ())
    | 6 -> Eff.Perform (rand_op (), t ())
    | 7 -> Eff.Bind (e (), e ())
    | 8 -> Eff.Gen (rand_stmts (d - 1))
    | 9 -> Eff.CatchCause (e (), e ())
    | 10 -> Eff.MatchCause (e (), e (), e ())
    | 11 -> Eff.OnExit (e (), e ())
    | 12 -> Eff.Exit (e ())
    | 13 -> Eff.Uninterruptible (e ())
    | 14 -> Eff.Interruptible (e ())
    | 15 -> Eff.Select (t (), rand_decision (), e (), e ())
    | 16 ->
      Eff.Iterate ((if rb () then None else Some Ty.Nat), t (), t (), t (), t (), e ())
    | 17 -> Eff.YieldNow (rand_nat ())
    | 18 -> Eff.Perform (rand_op (), t ())
    | 19 -> Eff.AwaitFiber (t (), rand_mode ())
    | 20 -> Eff.WithFiber (rand_action (d - 1))
    | 21 -> Eff.Scoped (e ())
    | 22 -> Eff.AcquireRelease (e (), e ())
    | 23 -> Eff.ProvideLayer (rand_layer (d - 1), rb (), e ())
    | 24 -> Eff.Service (rand_service_key ())
    | 25 -> Eff.ProvideService (rand_service_key (), t (), e ())
    | 26 -> Eff.Restore (t (), e ())
    | 27 -> Eff.ProvideContext (t (), e ())
    | _ -> Eff.CatchIf (t (), e (), e ()))

and rand_layer d =
  if d <= 0
  then LayerTerm.Succeed (rand_service_key (), rand_lit ())
  else (
    match ri 8 with
    | 0 -> LayerTerm.Succeed (rand_service_key (), rand_lit ())
    | 1 -> LayerTerm.Effect (rand_service_key (), rand_eff (d - 1))
    | 2 -> LayerTerm.EffectDiscard (rand_eff (d - 1))
    | 3 -> LayerTerm.Provide (rand_layer (d - 1), rand_layer (d - 1))
    | 4 -> LayerTerm.ProvideMerge (rand_layer (d - 1), rand_layer (d - 1))
    | 5 -> LayerTerm.Merge (rand_layer (d - 1), rand_layer (d - 1))
    | 6 -> LayerTerm.Fresh (rand_layer (d - 1))
    | _ -> LayerTerm.OrDie (rand_layer (d - 1)))

and rand_stmt d =
  match ri 6 with
  | 0 -> Stmt.BindYield (rand_eff d)
  | 1 -> Stmt.YieldDiscard (rand_eff d)
  | 2 -> Stmt.Ret (rand_term d)
  | 3 -> Stmt.IfElse (rand_term d, rand_stmts (d - 1), rand_stmts (d - 1))
  | 4 -> Stmt.WhileTrue (rand_stmts (d - 1))
  | _ -> Stmt.BreakLoop

and rand_stmts d =
  if d <= 0 || ri 3 = 0
  then Stmts.Nil
  else Stmts.Cons (rand_stmt (d - 1), rand_stmts (d - 1))

and rand_effs d =
  if d <= 0 || ri 3 = 0 then Effs.Nil else Effs.Cons (rand_eff (d - 1), rand_effs (d - 1))

and rand_action d =
  let t () = rand_term (min d 2) in
  match ri 17 with
  | 0 -> ActionTerm.Fork (rand_eff d, rand_options ())
  | 1 -> ActionTerm.ForkIn (rand_eff d, rand_options (), t ())
  | 2 -> ActionTerm.ForkScoped (rand_eff d, rand_options ())
  | 3 -> ActionTerm.RunIn (t (), t ())
  | 4 -> ActionTerm.Interrupt (t ())
  | 5 -> ActionTerm.InterruptScoped (t ())
  | 6 -> ActionTerm.InterruptAll (t (), if rb () then None else Some (t ()))
  | 7 -> ActionTerm.AwaitAll (t ())
  | 8 -> ActionTerm.AwaitAllFailFast (t ())
  | 9 -> ActionTerm.SnapshotChildren
  | 10 -> ActionTerm.AwaitNewChildren (t ())
  | 11 -> ActionTerm.RaceAll (rand_effs d)
  | 12 -> ActionTerm.Context (rand_keys ())
  | 13 -> ActionTerm.GetId
  | 14 -> ActionTerm.GetInterruptible
  | 15 -> ActionTerm.CloseScope (t (), t ())
  | _ -> ActionTerm.RaceAllFirst (rand_effs d)
;;

let rec rand_ty d =
  match if d <= 0 then ri 7 else ri 15 with
  | 0 -> Ty.Never
  | 1 -> Ty.Unit
  | 2 -> Ty.Nat
  | 3 -> Ty.Int
  | 4 -> Ty.String
  | 5 -> Ty.Bool
  | 6 -> Ty.Handle (rand_string ())
  | 7 -> Ty.Option (rand_ty (d - 1))
  | 8 -> Ty.List (rand_ty (d - 1))
  | 9 -> Ty.Prod (rand_ty (d - 1), rand_ty (d - 1))
  | 10 -> Ty.Except (rand_ty (d - 1), rand_ty (d - 1))
  | 11 -> Ty.ExitOf (rand_ty (d - 1), rand_ty (d - 1))
  | 12 -> Ty.CauseOf (rand_ty (d - 1))
  | 13 -> Ty.FiberOf (rand_ty (d - 1), rand_ty (d - 1))
  | _ -> Ty.Union (rand_ty (d - 1), rand_ty (d - 1))
;;

let rand_key () = { ServiceKey.name = rand_nat (); service = rand_nat () }
let rand_list f = List.init (ri 4) (fun _ -> f ())

(* Requirement rows are canonical sets in the Lean source image. Invalid ordering and
   duplicates are test_eff's control (C3); round-trip samples stay in-domain. *)
let rand_requirements () =
  let key (k : ServiceKey.t) = k.ServiceKey.name, k.ServiceKey.service in
  List.sort_uniq (fun a b -> compare (key a) (key b)) (rand_list rand_key)
;;

let rand_row_arg () =
  if rb () then RowArg.Name (rand_string ()) else RowArg.Str (rand_string ())
;;

let rand_row () =
  { Row.name = rand_string ()
  ; spelling = rand_string ()
  ; shape = pick [ RowShape.Call; RowShape.Value; RowShape.TupleCall; RowShape.Method ]
  ; trailing = rand_list rand_row_arg
  ; kind = pick [ RowKind.Sync; RowKind.Async; RowKind.Program ]
  ; request = rand_ty 2
  ; answer = rand_ty 2
  ; error = rand_ty 2
  ; requires = rand_requirements ()
  ; cite = rand_string ()
  ; type_args = rand_list rand_string
  ; registration = pick [ Registration.Deferred; Registration.External ]
  }
;;

let rand_eff_ty () =
  { EffTy.answer = rand_ty 3; error = rand_ty 3; requires = rand_requirements () }
;;

let checks = ref 0
let failures = ref 0

let fail what i =
  incr failures;
  Printf.printf "FAIL: %s at sample %d\n%!" what i
;;

(* P5: a value tree's JSON print reads back to it, or is refused for a natural above the
   profile's limit, the only refusal a print earns (the printer writes no numeral). *)
let reads_back (doc : G.shape_doc) (v : Val.t) : bool =
  match G.store_shape_doc_read_located doc (G.store_shape_doc_print_tree doc v) with
  | Ok v' -> Eff_val.equal v v'
  | Error { Eff_types.Located.reason = G.JsonReason_naturalOutsideProfile _; _ } -> true
  | Error _ -> false
;;

let program_reads_back (p : NativeOp.t Eff.t) : bool =
  reads_back G.run_kit_program_shape (G.run_kit_program_to_val p)
;;

let unit_program : NativeOp.t Eff.t = Eff.Succeed (Term.Lit Lit.Unit)

(* A program that carries a type: `Deferred.make` at its type arguments. *)
let carrying_ty (t : Ty.t) : NativeOp.t Eff.t =
  Eff.Perform (NativeOp.DeferredMakeOf (t, Ty.Nat), Term.Lit Lit.Unit)
;;

(* P1-P4 on the program a sample makes, through the program codec (Eff_codec), and P5 on the
   sample. *)
let property
      (what : string)
      (n : int)
      (gen : unit -> 'a)
      (program : 'a -> NativeOp.t Eff.t)
      (json : 'a -> bool)
  : unit
  =
  let seen = Hashtbl.create 1024 in
  for i = 1 to n do
    let v = gen () in
    let p = program v in
    let b = Eff_codec.encode_program p in
    let junk = "\000\001\002" in
    incr checks;
    if Eff_codec.decode_program b <> Some p
    then fail (what ^ ": P1 decode_program (encode_program p) = Some p") i;
    incr checks;
    (match Eff_val.decode (b ^ junk) 0 (String.length b + String.length junk) with
     | Some (tree, next)
       when next = String.length b
            && Eff_val.equal tree (Eff_image.run_kit_program_to_val p) -> ()
     | _ -> fail (what ^ ": P2 self-delimiting") i);
    incr checks;
    if Eff_codec.decode_program (b ^ junk) <> None
    then fail (what ^ ": P3 trailing bytes refused") i;
    incr checks;
    (match Hashtbl.find_opt seen b with
     | Some p' when p' <> p -> fail (what ^ ": P4 two programs with one encoding") i
     | _ -> Hashtbl.replace seen b p);
    incr checks;
    if not (json v) then fail (what ^ ": P5 Lean's JSON reads back") i
  done
;;

(* P1 through a carrier's own image, for the carriers no program holds, and P5. *)
let image_property
      (what : string)
      (n : int)
      (gen : unit -> 'a)
      (round_trip : 'a -> bool)
      (json : 'a -> bool)
  : unit
  =
  for i = 1 to n do
    let v = gen () in
    incr checks;
    if not (round_trip v) then fail (what ^ ": P1 the lowered reading of its bytes") i;
    incr checks;
    if not (json v) then fail (what ^ ": P5 Lean's JSON reads back") i
  done
;;

let record_controls =
  let raw =
    Term.Record
      ( [ "z", (true, Ty.Int); "z", (false, Ty.Number); "__proto__", (true, Ty.Nat) ]
      , [ "unknown"; "unknown" ]
      , Terms.Cons (Term.Lit (Lit.Nat 1), Terms.Nil) )
  in
  [ raw
  ; Term.Record ([ "x", (true, Ty.Nat) ], [], Terms.Cons (Term.Lit (Lit.Nat 1), Terms.Nil))
  ; Term.Record ([ "x", (true, Ty.Nat) ], [], Terms.Nil)
  ; Term.Field (FieldReadMode.Required, raw, "__proto__")
  ; Term.Field (FieldReadMode.Optional, raw, "a-b")
  ; Term.RecordSet (raw, "a-b", Term.Var 3)
  ]
;;

let tuple_controls =
  [ Term.TupleAt (Term.Var 0, 0)
  ; Term.TupleAt (Term.Var 1, 9007199254740993)
  ; Term.TupleAt (Term.TupleAt (Term.Var 2, 65537), max_int)
  ; Term.Field (FieldReadMode.Optional, Term.TupleAt (Term.Var 3, 1), "a-b")
  ]
;;

(* The list fold (decisions row 228): with no stated type and with one, and a fold inside a
   fold's body. *)
let fold_controls =
  [ Term.Fold (None, Term.Var 0, Term.Lit (Lit.Nat 0), Term.Var 1)
  ; Term.Fold (Some (Ty.List Ty.Nat), Term.Var 0, Term.App ("nil", Terms.Nil), Term.Var 1)
  ; Term.Fold
      ( None
      , Term.Var 0
      , Term.Var 1
      , Term.Fold (Some Ty.Never, Term.Var 3, Term.Var 2, Term.TupleAt (Term.Var 5, 0)) )
  ]
;;

let decision_controls =
  [ Decision.Bool
  ; Decision.Option
  ; Decision.Tag "Found"
  ; Decision.RecordTag "Found"
  ; Decision.RecordTag ""
  ; Decision.RecordTag "é\n\"raw"
  ]
;;

let () =
  let succeed t = Eff.Succeed t in
  let selecting d = Eff.Select (Term.Var 0, d, unit_program, unit_program) in
  let forking o = Eff.WithFiber (ActionTerm.Fork (unit_program, o)) in
  List.iteri
    (fun i term ->
       property
         ("record-term-" ^ string_of_int i)
         1
         (fun () -> term)
         succeed
         (fun t -> program_reads_back (succeed t)))
    record_controls;
  List.iteri
    (fun i term ->
       property
         ("tuple-term-" ^ string_of_int i)
         1
         (fun () -> term)
         succeed
         (fun t -> program_reads_back (succeed t)))
    tuple_controls;
  List.iteri
    (fun i term ->
       property
         ("fold-term-" ^ string_of_int i)
         1
         (fun () -> term)
         succeed
         (fun t -> program_reads_back (succeed t)))
    fold_controls;
  List.iteri
    (fun i decision ->
       property
         ("decision-" ^ string_of_int i)
         1
         (fun () -> decision)
         selecting
         (fun d -> program_reads_back (selecting d)))
    decision_controls;
  property "eff" 400 (fun () -> rand_eff (ri 7)) Fun.id program_reads_back;
  property
    "ty"
    400
    (fun () -> rand_ty (ri 6))
    carrying_ty
    (fun t -> reads_back G.run_kit_ty_shape (G.run_kit_ty_to_val t));
  image_property
    "row"
    200
    rand_row
    (fun r ->
       match G.run_kit_rows_to_val [ r ] with
       | Val.List [ tree ] -> Eff_codec.decode_rows [ Eff_val.to_bytes tree ] = Some [ r ]
       | _ -> false)
    (fun r -> reads_back G.run_kit_rows_shape (G.run_kit_rows_to_val [ r ]));
  image_property
    "eff_ty"
    200
    rand_eff_ty
    (fun t ->
       Eff_codec.decode_eff_ty (Eff_val.to_bytes (G.run_kit_eff_ty_to_val t)) = Some t)
    (fun t -> reads_back G.run_kit_eff_ty_shape (G.run_kit_eff_ty_to_val t));
  property "fork_options" 50 rand_options forking (fun o ->
    program_reads_back (forking o));
  Printf.printf "prop_wire: %d checks, %d failures (seed 42)\n%!" !checks !failures;
  if !failures > 0 then exit 1
;;
