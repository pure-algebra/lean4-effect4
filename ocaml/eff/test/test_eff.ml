(* test_eff — the battery of effect4_eff (hand-written).
   1. Goldens: every goldens/<name>.bin decodes exactly, re-encodes byte for byte, prints the
      JSON of goldens/<name>.json, and types as goldens/<name>.ty; structural corruptions of
      the bytes are refused.
   2. The GADT corpus: every well-typed corpus program rebuilt through Eff_typed erases and
      encodes to the golden bytes, is well-typed by the checker, and the checker's answer and
      error are the erased witnesses.
   3. Pins: constructor counts and indices read off the Lean sources on 2026-09-04, the atom
      table, the 53 op values and their rows, the requirement and union algebra.
   4. The wire kernel: nat digits, the bound, UTF-8, refusals.
   Exit status 1 on any failure; the counts are printed last. *)

open Eff_types

let checks = ref 0
let failures = ref 0

let check (name : string) (ok : bool) : unit =
  incr checks;
  if not ok then begin
    incr failures;
    Printf.printf "FAIL: %s\n%!" name
  end

let read_file (path : string) : string =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic;
  s

let strip (s : string) : string =
  let n = ref (String.length s) in
  while !n > 0 && (s.[!n - 1] = '\n' || s.[!n - 1] = '\r') do decr n done;
  String.sub s 0 !n

let goldens = "../goldens/"

let corpus : (string * bool) list =
  read_file (goldens ^ "corpus.txt")
  |> String.split_on_char '\n'
  |> List.filter (fun l -> l <> "")
  |> List.map (fun l ->
         match String.split_on_char '\t' l with
         | [ name; status ] -> (name, status = "well-typed")
         | _ -> failwith ("corpus.txt: bad line " ^ l))

let golden_bin name = read_file (goldens ^ name ^ ".bin")

let ellipsis (n : int) (s : string) : string =
  if String.length s <= n then s else String.sub s 0 (n - 1) ^ "\226\128\166"

(* ---- 1. goldens ---- *)

let () =
  check "corpus has 37 programs" (List.length corpus = 37);
  Printf.printf "  %-16s %6s %-8s %-10s %-6s %s\n" "program" "bytes" "decode" "re-encode" "JSON" "typeOf";
  List.iter
    (fun (name, typed) ->
      let bin = golden_bin name in
      let json = strip (read_file (goldens ^ name ^ ".json")) in
      let ty = strip (read_file (goldens ^ name ^ ".ty")) in
      match Eff_wire.decode_program_exact bin with
      | None ->
        check (name ^ ": decodes") false;
        Printf.printf "  %-16s %6d %-8s %-10s %-6s %s\n" name (String.length bin) "REFUSED" "-" "-" "-"
      | Some p ->
        Printf.printf "  %-16s %6d %-8s %-10s %-6s %s\n" name (String.length bin) "ok"
          (if Eff_wire.encode_program p = bin then "identical" else "DIFFERS")
          (if Eff_json.print_eff p = json then "equal" else "DIFFERS")
          (ellipsis 44 ty);
        check (name ^ ": re-encodes byte for byte") (Eff_wire.encode_program p = bin);
        check (name ^ ": JSON equals the Lean printer's") (Eff_json.print_eff p = json);
        check (name ^ ": type equals Lean's typeOf") (Eff_typing.print_type p = ty);
        check (name ^ ": well-typed flag") (Eff_typing.well_typed p = typed);
        check (name ^ ": decode reports the whole length as rest")
          (Eff_wire.decode_program bin = Some (p, String.length bin));
        check (name ^ ": a trailing byte is refused") (Eff_wire.decode_program_exact (bin ^ "\000") = None);
        check (name ^ ": a trailing byte is not consumed by decode")
          (Eff_wire.decode_program (bin ^ "\000") = Some (p, String.length bin));
        check (name ^ ": truncation is refused")
          (Eff_wire.decode_program_exact (String.sub bin 0 (String.length bin - 1)) = None);
        let flipped = Bytes.of_string bin in
        Bytes.set flipped 0 '\004';
        check (name ^ ": a wrong tag is refused") (Eff_wire.decode_program_exact (Bytes.to_string flipped) = None);
        let longer = Bytes.of_string bin in
        Bytes.set longer 8 (Char.chr (Char.code (Bytes.get longer 8) + 1));
        check (name ^ ": a length past the end is refused")
          (Eff_wire.decode_program_exact (Bytes.to_string longer) = None))
    corpus

let () =
  let bad_index i = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b i (fun _ -> ())) () in
  check "Eff index 24 is refused" (Eff_wire.decode_eff_exact (bad_index 24) = None);
  check "Eff index 99 is refused" (Eff_wire.decode_eff_exact (bad_index 99) = None);
  check "Eff index 17 with no payload is refused (yieldNow needs a nat)"
    (Eff_wire.decode_eff_exact (bad_index 17) = None);
  let yield0 = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b 17 (fun b -> Eff_frame.emit_nat b 0)) () in
  check "Eff index 17 with a nat is yieldNow 0" (Eff_wire.decode_eff_exact yield0 = Some (Eff_yieldNow 0));
  let extra = Eff_frame.to_string (fun b () -> Eff_frame.emit_ctor b 17 (fun b -> Eff_frame.emit_nat b 0; Eff_frame.emit_nat b 0)) () in
  check "an extra argument inside the frame is refused" (Eff_wire.decode_eff_exact extra = None)

(* ---- 2. the GADT corpus ---- *)

open Eff_typed

let opts = fork_options ()

(* A constructor application only, so it generalises over the environment. *)
let child = Bind (Yield_now 0, Succeed (Nat_lit 7))

(* child's error index: (never, never) union *)
let child_err = Union (Never, Never)
let i0 = Z
let i1 = S i0
let i2 = S i1
let i3 = S i2
let i4 = S i3
let i5 = S i4
let i6 = S i5
let i7 = S i6
let i8 = S i7
let i9 = S i8
let i10 = S i9
let i11 = S i10
let i12 = S i11
let i13 = S i12
let un e = Union (Never, e)
let un4 e = un (un (un (un e)))
let un16 e = un4 (un4 (un4 (un4 e)))

let typed_corpus : (string * program) list =
  [ ("p42", Program (Succeed (nat 42), Nat, Never))
  ; ("pBind", Program (Bind (Succeed (nat 1), Succeed (Succ v0)), Nat, un Never))
  ; ("pFork", Program (Bind (With_fiber (Fork (child, opts)), Await_fiber (v0, Await_value)), Exit_of (Nat, child_err), un Never))
  ; ( "pTwo"
    , Program
        ( Bind
            ( With_fiber (Fork (child, opts))
            , Bind
                ( With_fiber (Fork (child, fork_options ~start_immediately:true ~mask:Mask_mode_interruptible ()))
                , Bind (Await_fiber (v1, Await_value), Await_fiber (v1, Await_value)) ) )
        , Exit_of (Nat, child_err)
        , un (un (un Never)) ) )
  ; ("pAwait", Program (Bind (Perform (Deferred_make, unit_), Perform (Deferred_await, v0)), Nat, un Nat))
  ; ("pGen", Program (Gen (Bind_yield (Succeed (nat 1), Ret (Succ v0)), G_ret), Nat, un Never))
  ; ("pWhile", Program (While_loop (nat 0, Lt (v0, nat 3), Succ v1, Yield_now 0), Unit, Never))
  ; ("pCatch", Program (Catch_cause (Fail (nat 1), Succeed (nat 0), Left_never), Nat, Never))
  ; ("pStr", Program (Succeed (str "hi \"there\"\n"), String, Never))
  ; ( "pFailCause"
    , Program
        ( Fail_cause
            (C_both (C_fail (nat 1), C_both (C_die (nat 2), C_both (C_interrupt (Some (nat 3)), C_interrupt None))))
        , Never
        , Union (Nat, Union (Never, Union (Never, Never))) ) )
  ; ("pYieldError", Program (Yield_error (bool true), Never, Bool))
  ; ("pSync", Program (Sync (Add (nat 2, nat 3)), Nat, Never))
  ; ("pSuspend", Program (Suspend (Succeed unit_), Unit, Never))
  ; ( "pMatch"
    , Program
        ( Match_cause (Succeed (nat 1), Succeed (Is_zero v0), Succeed (bool false), Same)
        , Bool
        , Union (Never, Never) ) )
  ; ("pOnExit", Program (On_exit (Succeed (nat 1), Yield_now 1), Nat, Union (Never, Never)))
  ; ("pExit", Program (Exit (Fail (nat 9)), Exit_of (Never, Nat), Never))
  ; ("pMasks", Program (Uninterruptible (Interruptible (Succeed (nat 1))), Nat, Never))
  ; ("pBranch", Program (Branch (bool true, Succeed (nat 1), Fail (nat 2), Right_never), Nat, Union (Never, Nat)))
  ; ("pCallback", Program (Bind (Perform (Deferred_make, unit_), Callback (Deferred_await, v0)), Nat, un Nat))
  ; ( "pJoin"
    , Program
        ( Bind
            ( With_fiber (Fork (child, fork_options ~daemon:true ~mask:Mask_mode_uninterruptible ()))
            , Await_fiber (v0, Join_effect) )
        , Nat
        , un child_err ) )
  ; ( "pScoped"
    , Program
        ( Scoped
            (Bind
               ( Perform (Scope_make Finalizer_strategy_parallel, unit_)
               , With_fiber
                   (Fork_in
                      ( Succeed (nat 1)
                      , fork_options ~start_immediately:true ~daemon:true ~mask:Mask_mode_uninterruptible ()
                      , v0 )) ))
        , Fiber_of (Nat, Never)
        , un Never ) )
  ; ( "pAcquire"
    , Program
        ( Acquire_release (Perform (Ref_make, nat 0), Perform (Ref_get, v1))
        , Handle Ref_number
        , Never ) )
  ; ("pChoose", Program (Choose (3, Succeed (nat 1), Succeed (nat 2), Same), Nat, Union (Never, Never)))
  ; ("pPair", Program (Succeed (Fst (Pair (nat 1, bool true))), Nat, Never))
  ; ( "pStmts"
    , Program
        ( Gen
            ( Bind_yield
                ( Succeed (nat 0)
                , While_true
                    ( If_else (Lt (v0, nat 3), Yield_discard (Yield_now 0, Nil), Break Nil, R_same, Nil, R_same)
                    , Ret v0
                    , R_left_none ) )
            , G_ret )
        , Nat
        , Union (Never, Union (Union (Union (Union (Never, Never), Never), Never), Never)) ) )
  ; ( "pActions"
    , Program
        ( Bind
            ( With_fiber (Fork_scoped (child, opts))
            , Bind
                ( Perform (Scope_make Finalizer_strategy_sequential, unit_)
                , Bind
                    ( With_fiber (Run_in (Var i1, Var i0))
                    , Bind
                        ( With_fiber (Interrupt (Var i2))
                        , Bind
                            ( With_fiber (Interrupt_scoped (Var i3))
                            , Bind
                                ( With_fiber Snapshot_children
                                , Bind
                                    ( With_fiber (Await_new_children (Var i0))
                                    , Bind
                                        ( With_fiber Get_context
                                        , Bind
                                            ( With_fiber (Set_context (Var i0))
                                            , Bind
                                                ( With_fiber Get_id
                                                , Bind
                                                    ( With_fiber (Interrupt_all (Var i4, Some (Var i0)))
                                                    , Bind
                                                        ( With_fiber (Interrupt_all (Var i5, None))
                                                        , Bind
                                                            ( With_fiber (Await_all (Var i6))
                                                            , Bind
                                                                ( With_fiber (Await_all_fail_fast (Var i7))
                                                                , Bind
                                                                    ( Exit (Succeed (nat 1))
                                                                    , Bind
                                                                        ( With_fiber (Close_scope (Var i13, Var i0))
                                                                        , With_fiber
                                                                            (Race_all
                                                                               (Effs_cons
                                                                                  ( child
                                                                                  , Effs_cons (Succeed (nat 3), Effs_nil, Right_never)
                                                                                  , Same ))) ) ) ) ) ) ) ) )
                                        ) ) ) ) ) ) ) )
        , Nat
        , un16 (Union (child_err, Union (Never, Never))) ) )
  ; ( "pOps"
    , Program
        ( Bind
            ( Perform (Ref_make, nat 1)
            , Bind
                ( Perform (Ref_get, Var i0)
                , Bind
                    ( Perform (Ref_set, Pair (Var i1, nat 2))
                    , Bind
                        ( Perform (Ref_get_and_set, Pair (Var i2, nat 3))
                        , Bind
                            ( Perform (Ref_set_and_get, Pair (Var i3, nat 4))
                            , Bind
                                ( Perform (Ref_update Fn_name_incr, Var i4)
                                , Bind
                                    ( Perform (Ref_get_and_update Fn_name_double, Var i5)
                                    , Bind
                                        ( Perform (Ref_update_and_get Fn_name_zeroWhenPositive, Var i6)
                                        , Bind
                                            ( Perform (Ref_update_some Fn_name_noChange, Var i7)
                                            , Bind
                                                ( Perform (Ref_get_and_update_some Fn_name_takeAndBump, Var i8)
                                                , Bind
                                                    ( Perform (Ref_update_some_and_get Fn_name_incr, Var i9)
                                                    , Bind
                                                        ( Perform (Ref_modify Fn_name_double, Var i10)
                                                        , Bind
                                                            ( Perform (Ref_modify_some Fn_name_noChange, Var i11)
                                                            , Bind
                                                                ( Perform (Deferred_make, unit_)
                                                                , Bind
                                                                    ( Perform (Deferred_is_done, Var i0)
                                                                    , Bind
                                                                        ( Perform (Deferred_poll, Var i1)
                                                                        , Bind
                                                                            ( Perform (Deferred_succeed, Pair (Var i2, nat 1))
                                                                            , Bind
                                                                                ( Perform (Deferred_fail, Pair (Var i3, nat 2))
                                                                                , Bind
                                                                                    ( Perform (Scope_make Finalizer_strategy_sequential, unit_)
                                                                                    , Bind
                                                                                        ( Perform (Scope_make Finalizer_strategy_parallel, unit_)
                                                                                        , Callback (Deferred_await, Var i6) ) ) )
                                                                            ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) ) )
        , Nat
        , un16 (un4 Nat) ) )
  ]

let () =
  check "the typed corpus is every well-typed golden"
    (List.sort compare (List.map fst typed_corpus)
     = List.sort compare (List.filter_map (fun (n, t) -> if t then Some n else None) corpus));
  Printf.printf "  %-16s %-22s %-11s %s\n" "program" "GADT erase+encode" "well-typed" "answer/error = witness";
  List.iter
    (fun (name, prog) ->
      match prog with
      | Program (p, a, e) ->
        let u = erase p in
        let same = Eff_wire.encode_program u = golden_bin name in
        check (name ^ ": GADT erases and encodes to the golden bytes") same;
        check (name ^ ": GADT erasure is well-typed") (Eff_typing.well_typed u);
        let witness =
          match Eff_typing.type_of u with
          | Error _ -> "no type"
          | Ok t ->
            check (name ^ ": the checker's answer is the erased witness") (t.eff_ty_answer = to_ty a);
            check (name ^ ": the checker's error is the erased witness") (t.eff_ty_error = to_ty e);
            if t.eff_ty_answer = to_ty a && t.eff_ty_error = to_ty e then "both agree" else "DISAGREE"
        in
        Printf.printf "  %-16s %-22s %-11s %s\n" name
          (if same then "identical to golden" else "DIFFERS FROM GOLDEN")
          (if Eff_typing.well_typed u then "yes" else "NO")
          witness)
    typed_corpus;
  check "Handle Ref_number is the ref row's handle" (to_ty (Handle Ref_number) = Eff_native.ref_ty);
  check "Handle Deferred_number is the deferred row's handle" (to_ty (Handle Deferred_number) = Eff_native.deferred_ty);
  check "Handle Scope is Ty.scope" (to_ty (Handle Scope) = Eff_native.scope_ty);
  check "Handle Context is Ty.context" (to_ty (Handle Context) = Eff_native.context_ty);
  (* every typed op's signature is its row *)
  let row (type r a e k) (op : (r, a, e, k) op) (req : r ty) (ans : a ty) (err : e ty) (async : bool) =
    let r = Eff_native.row_of (erase_op op) in
    check (r.row_name ^ ": the typed op signature is the row")
      (r.row_request = to_ty req && r.row_answer = to_ty ans && r.row_error = to_ty err
       && (r.row_kind = Row_kind_async) = async)
  in
  let refh = Handle Ref_number and defh = Handle Deferred_number in
  row Ref_make Nat refh Never false;
  row Ref_get refh Nat Never false;
  row Ref_set (Prod (refh, Nat)) refh Never false;
  row Ref_get_and_set (Prod (refh, Nat)) Nat Never false;
  row Ref_set_and_get (Prod (refh, Nat)) Nat Never false;
  List.iter
    (fun f ->
      row (Ref_update f) refh Unit Never false;
      row (Ref_get_and_update f) refh Nat Never false;
      row (Ref_update_and_get f) refh Nat Never false;
      row (Ref_update_some f) refh Unit Never false;
      row (Ref_get_and_update_some f) refh Nat Never false;
      row (Ref_update_some_and_get f) refh Nat Never false;
      row (Ref_modify f) refh Nat Never false;
      row (Ref_modify_some f) refh Nat Never false)
    [ Fn_name_incr; Fn_name_double; Fn_name_zeroWhenPositive; Fn_name_noChange; Fn_name_takeAndBump ];
  row Deferred_make Unit defh Never false;
  row Deferred_is_done defh Bool Never false;
  row Deferred_poll defh Bool Never false;
  row Deferred_succeed (Prod (defh, Nat)) Bool Never false;
  row Deferred_fail (Prod (defh, Nat)) Bool Never false;
  row Deferred_await defh Nat Nat true;
  row (Scope_make Finalizer_strategy_sequential) Unit (Handle Scope) Never false;
  row (Scope_make Finalizer_strategy_parallel) Unit (Handle Scope) Never false

(* The four term atoms no golden program exercises (pred, not, eq, snd): built through the
   GADT, erased, and put to the checker here. There is no Lean golden for them — see
   REPORT.md, "what is not covered" — so this is E1 without E2. *)
let () =
  let p : (empty, bool, never) eff =
    Succeed (Not (Eq (Pred (Snd (Pair (Bool_lit true, Nat_lit 3))), Nat_lit 2)))
  in
  let u = erase p in
  check "pred/not/eq/snd: the GADT erasure is well-typed" (Eff_typing.well_typed u);
  check "pred/not/eq/snd: the checker answers bool with no error"
    (match Eff_typing.type_of u with
     | Ok t -> t.eff_ty_answer = Ty_bool && t.eff_ty_error = Ty_never
     | Error _ -> false)

(* ---- 3. pins ---- *)

let () =
  check "Ty has 15 constructors" (List.length ctor_names_ty = 15);
  check "Lit has 4" (List.length ctor_names_lit = 4);
  check "Term has 3" (List.length ctor_names_term = 3);
  check "CauseTerm has 4" (List.length ctor_names_cause_term = 4);
  check "MaskMode has 3" (List.length ctor_names_mask_mode = 3);
  check "ObserverMode has 2" (List.length ctor_names_observer_mode = 2);
  check "FinalizerStrategy has 2" (List.length ctor_names_finalizer_strategy = 2);
  check "FnName has 5" (List.length ctor_names_fn_name = 5);
  check "NativeOp has 20" (List.length ctor_names_native_op = 20);
  check "Eff has 24" (List.length ctor_names_eff = 24);
  check "Stmt has 6" (List.length ctor_names_stmt = 6);
  check "ActionTerm has 16" (List.length ctor_names_action_term = 16);
  check "Eff.succeed is 0" (ctor_index_eff (Eff_yieldNow 0) = 17 && ctor_index_eff (Eff_succeed (Term_var 0)) = 0);
  check "Eff.choose is 23" (ctor_index_eff (Eff_choose (0, Eff_yieldNow 0, Eff_yieldNow 0)) = 23);
  check "Eff.gen is 8, perform 6, bind 7" (ctor_index_eff (Eff_gen Stmts_nil) = 8 && ctor_index_eff (Eff_perform (Native_op_refGet, Term_var 0)) = 6 && ctor_index_eff (Eff_bind (Eff_yieldNow 0, Eff_yieldNow 0)) = 7);
  check "ActionTerm.closeScope is 15" (ctor_index_action_term (Action_term_closeScope (Term_var 0, Term_var 0)) = 15);
  check "NativeOp.scopeMake is 19" (ctor_index_native_op (Native_op_scopeMake Finalizer_strategy_parallel) = 19);
  check "NativeOp.refUpdate is 5" (ctor_index_native_op (Native_op_refUpdate Fn_name_incr) = 5);
  check "Ty.union is 14, handle 6" (ctor_index_ty (Ty_union (Ty_nat, Ty_nat)) = 14 && ctor_index_ty (Ty_handle "") = 6);
  check "nil is 0 and cons is 1 in Terms, Stmts, Effs"
    (ctor_index_terms Terms_nil = 0 && ctor_index_terms (Terms_cons (Term_var 0, Terms_nil)) = 1
     && ctor_index_stmts Stmts_nil = 0 && ctor_index_stmts (Stmts_cons (Stmt_breakLoop, Stmts_nil)) = 1
     && ctor_index_effs Effs_nil = 0 && ctor_index_effs (Effs_cons (Eff_yieldNow 0, Effs_nil)) = 1);
  check "MaskMode: interruptible 0, uninterruptible 1, inherit 2"
    (ctor_index_mask_mode Mask_mode_interruptible = 0 && ctor_index_mask_mode Mask_mode_inherit = 2);
  check "ObserverMode: awaitValue 0, joinEffect 1" (ctor_index_observer_mode Observer_mode_joinEffect = 1);
  check "Lit.str is 3" (ctor_index_lit (Lit_str "") = 3);
  check "ctor_name agrees with ctor_names at every index"
    (List.for_all (fun op -> List.nth ctor_names_native_op (ctor_index_native_op op) = ctor_name_native_op op) Eff_native.all_ops);
  let contains (s : string) (sub : string) : bool =
    let n = String.length s and m = String.length sub in
    let rec go i = i + m <= n && (String.sub s i m = sub || go (i + 1)) in
    go 0
  in
  let manifest = read_file "../eff_manifest.txt" |> String.split_on_char '\n' |> List.filter (fun l -> l <> "") in
  check "the manifest has 23 families" (List.length manifest = 23);
  check "the manifest's Eff line names the 24 constructors with their carriers"
    (List.exists
       (fun l ->
         contains l "Effect4.Program.Eff (eff) inductive: succeed(term) fail(term)"
         && contains l "whileLoop(term,term,term,eff)" && contains l "choose(int,eff,eff)")
       manifest);
  check "the manifest's NativeOp line ends with scopeMake(finalizer_strategy)"
    (List.exists (fun l -> contains l "(native_op) inductive: refMake" && contains l "deferredAwait scopeMake(finalizer_strategy)") manifest);
  (* atoms *)
  let open Eff_native in
  check "succ : nat -> nat" (atom_ty "succ" [ Ty_nat ] = Some Ty_nat);
  check "the atoms no corpus program uses are still typed by the table"
    (atom_ty "pred" [ Ty_nat ] = Some Ty_nat
     && atom_ty "not" [ Ty_bool ] = Some Ty_bool
     && atom_ty "eq" [ Ty_nat; Ty_nat ] = Some Ty_bool
     && atom_ty "isZero" [ Ty_nat ] = Some Ty_bool
     && atom_ty "lt" [ Ty_nat; Ty_nat ] = Some Ty_bool
     && atom_ty "add" [ Ty_nat; Ty_nat ] = Some Ty_nat);
  check "pair is polymorphic" (atom_ty "pair" [ Ty_bool; Ty_handle "x" ] = Some (Ty_prod (Ty_bool, Ty_handle "x")));
  check "fst/snd project" (atom_ty "fst" [ Ty_prod (Ty_nat, Ty_bool) ] = Some Ty_nat && atom_ty "snd" [ Ty_prod (Ty_nat, Ty_bool) ] = Some Ty_bool);
  check "atoms refuse wrong arities and types"
    (atom_ty "succ" [ Ty_bool ] = None && atom_ty "succ" [] = None && atom_ty "add" [ Ty_nat ] = None
     && atom_ty "fst" [ Ty_nat ] = None && atom_ty "mul" [ Ty_nat; Ty_nat ] = None);
  check "10 atom names" (List.length atom_names = 10);
  (* ops *)
  check "53 op values, none repeated"
    (List.length all_ops = 53 && List.length (List.sort_uniq compare all_ops) = 53);
  check "every row is named after its constructor"
    (List.for_all (fun op -> (row_of op).row_name = ctor_name_native_op op) all_ops);
  check "deferredAwait is the one async row"
    (List.filter (fun op -> (row_of op).row_kind = Row_kind_async) all_ops = [ Native_op_deferredAwait ]);
  check "the scope key is <0, 0>"
    (scope_key = { service_key_name = { service_name_value = 0 }; service_key_service = { service_type_code_value = 0 } });
  (* Ty.join and rows *)
  let open Eff_typing in
  check "join nat never = nat" (join Ty_nat Ty_never = Ty_nat && join Ty_never Ty_nat = Ty_nat);
  check "join is idempotent" (join Ty_nat Ty_nat = Ty_nat);
  check "join sorts by key: nat before bool" (join Ty_bool Ty_nat = Ty_union (Ty_nat, Ty_bool) && join Ty_nat Ty_bool = Ty_union (Ty_nat, Ty_bool));
  check "join flattens and right-nests"
    (join (Ty_union (Ty_nat, Ty_bool)) Ty_unit = Ty_union (Ty_unit, Ty_union (Ty_nat, Ty_bool)));
  check "join_answer" (join_answer Ty_nat Ty_never = Some Ty_nat && join_answer Ty_nat Ty_bool = None && join_answer Ty_never Ty_never = Some Ty_never);
  let k n s = { service_key_name = { service_name_value = n }; service_key_service = { service_type_code_value = s } } in
  check "requirement rows are ascending and deduplicated"
    (req_of_list [ k 1 0; k 0 1; k 0 0; k 1 0 ] = [ k 0 0; k 0 1; k 1 0 ]
     && req_union [ k 0 0 ] [ k 0 0; k 2 2 ] = [ k 0 0; k 2 2 ])

(* ---- 4. the wire kernel ---- *)

let () =
  let open Eff_frame in
  check "nat digits: 0 is empty, 255 one byte, 256 two" (nat_digits 0 = "" && nat_digits 255 = "\255" && nat_digits 256 = "\001\000");
  check "nat digits: max_int is 8 bytes" (String.length (nat_digits max_int) = 8);
  let rt n = exact decode_nat (to_string emit_nat n) = Some n in
  check "nat round trip at 0, 1, 255, 256, 65535, 2^32, max_int" (rt 0 && rt 1 && rt 255 && rt 256 && rt 65535 && rt (1 lsl 32) && rt max_int);
  check "a negative int has no encoding" (try ignore (nat_digits (-1)); false with Invalid_argument _ -> true);
  let frame tag payload = to_string (fun b () -> emit_frame b tag payload) () in
  check "a nat with a leading zero digit is refused" (exact decode_nat (frame tag_nat "\000\001") = None);
  check "a nat of nine digits is refused" (exact decode_nat (frame tag_nat "\001\000\000\000\000\000\000\000\000") = None);
  check "a nat of eight digits above max_int is refused" (exact decode_nat (frame tag_nat "\064\000\000\000\000\000\000\000") = None);
  check "a nat of eight digits at max_int is accepted" (exact decode_nat (frame tag_nat "\063\255\255\255\255\255\255\255") = Some max_int);
  check "a bool byte other than 0/1 is refused" (exact decode_bool (frame tag_bool "\002") = None && exact decode_bool (frame tag_bool "\001\000") = None);
  check "unit with a payload is refused" (exact decode_unit (frame tag_unit "\000") = None);
  check "the empty string round-trips" (exact decode_string (to_string emit_string "") = Some "");
  check "UTF-8: multi-byte scalars are accepted" (utf8_valid "h\xc3\xa9llo \xe6\x97\xa5\xe6\x9c\xac \xf0\x9f\x98\x80");
  check "UTF-8: a stray continuation byte is refused" (not (utf8_valid "\x80") && exact decode_string (frame tag_string "\xff") = None);
  check "UTF-8: overlong and surrogate encodings are refused" (not (utf8_valid "\xc0\x80") && not (utf8_valid "\xed\xa0\x80") && not (utf8_valid "\xf4\x90\x80\x80"));
  check "UTF-8: a truncated sequence is refused" (not (utf8_valid "\xe6\x97"));
  check "emit_string refuses invalid UTF-8" (try ignore (to_string emit_string "\xff"); false with Invalid_argument _ -> true);
  check "a frame shorter than nine bytes is refused" (read_frame "\002\000" 0 2 = None && exact decode_nat "" = None);
  check "an option's some must fill its payload" (exact (decode_option decode_nat) (frame tag_some (nat_digits 1)) = None);
  check "a list decodes its elements exactly"
    (exact (decode_list decode_nat) (to_string (fun b xs -> emit_list b emit_nat xs) [ 1; 2; 3 ]) = Some [ 1; 2; 3 ]);
  check "a pair with a third element is refused"
    (exact (decode_pair decode_nat decode_nat) (frame tag_pair (to_string emit_nat 1 ^ to_string emit_nat 2 ^ to_string emit_nat 3)) = None)

let () =
  Printf.printf "test_eff: %d checks, %d failures\n%!" !checks !failures;
  if !failures > 0 then exit 1
