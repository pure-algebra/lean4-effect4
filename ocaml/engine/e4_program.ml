(* E4_program -- see e4_program.mli. *)

exception Ordinal_mismatch of string

module type PROGRAM_TYPES = E4_program_layout.PROGRAM_TYPES

(* ------------------------------------------------------------------ the ordinal ledger *)

(* Both lists are generated from the selected source description and the actual frozen
   engine declarations. Existing source appends remain explicit unsupported execution. *)
let source_ctor_names = E4_program_layout.source_ctor_names
let engine_ctor_names = E4_program_layout.engine_ctor_names

let rec prefix_at family i xs ys =
  match xs, ys with
  | [], _ -> Ok ()
  | x :: _, [] ->
    Error (Printf.sprintf "%s: the engine has %d constructors, the wire has more (%s at %d)"
             family i x i)
  | x :: xs', y :: ys' ->
    if String.equal x y then prefix_at family (i + 1) xs' ys'
    else Error (Printf.sprintf "%s ordinal %d: the wire says %S, the engine says %S"
                  family i x y)

let pin () =
  let rec go = function
    | [] -> Ok ()
    | (family, src) :: rest ->
      (match List.assoc_opt family engine_ctor_names with
       | None -> Error (Printf.sprintf "%s: no such family in the engine's alphabet" family)
       | Some eng ->
         (match prefix_at family 0 src eng with Error e -> Error e | Ok () -> go rest))
  in
  go source_ctor_names

let pin_exn () = match pin () with Ok () -> () | Error e -> raise (Ordinal_mismatch e)

(* ------------------------------------------------------------------ the content table *)

(* One line of eff_manifest.txt is
     <Lean name> (<ocaml name>) inductive: <ctor>(<args>) <ctor> ...
   or the same with `structure:` and `field:type` items.  Arguments contain spaces
   (`interrupt(term option)`), so the item split respects parenthesis depth. *)
let split_items (s : string) : string list =
  let out = ref [] and buf = Buffer.create 32 and depth = ref 0 in
  let flush () = if Buffer.length buf > 0 then (out := Buffer.contents buf :: !out;
                                                Buffer.clear buf) in
  String.iter
    (fun c ->
       match c with
       | '(' -> incr depth; Buffer.add_char buf c
       | ')' -> decr depth; Buffer.add_char buf c
       | ' ' when !depth = 0 -> flush ()
       | _ -> Buffer.add_char buf c)
    s;
  flush ();
  List.rev !out

let ctor_of_item (it : string) : string =
  match String.index_opt it '(' with None -> it | Some i -> String.sub it 0 i

let read_lines path =
  let ic = open_in_bin path in
  let rec go acc =
    match input_line ic with
    | line -> go (line :: acc)
    | exception End_of_file -> close_in ic; List.rev acc
  in
  go []

let parse_manifest path =
  match read_lines path with
  | exception Sys_error e -> Error ("eff_manifest.txt: " ^ e)
  | lines ->
    let rows =
      List.filter_map
        (fun line ->
           match String.index_opt line '(', String.index_opt line ')' with
           | Some i, Some j when j > i + 1 ->
             let name = String.sub line (i + 1) (j - i - 1) in
             let tail = String.sub line (j + 1) (String.length line - j - 1) in
             let marker = " inductive: " in
             let ml = String.length marker in
             if String.length tail > ml && String.sub tail 0 ml = marker then
               let items = split_items (String.sub tail ml (String.length tail - ml)) in
               Some (name, List.map ctor_of_item items)
             else None
           | _ -> None)
        lines
    in
    if rows = [] then Error "eff_manifest.txt: no inductive rows parsed" else Ok rows

let check_manifest path =
  match parse_manifest path with
  | Error e -> Error e
  | Ok rows ->
    let rec go = function
      | [] -> Ok ()
      | (family, names) :: rest ->
        (match List.assoc_opt family source_ctor_names with
         | None -> go rest (* a family Eff_types publishes no ctor table for *)
         | Some src ->
           if src <> names then
             Error (Printf.sprintf
                      "%s: eff_manifest.txt says [%s]; Eff_types says [%s]"
                      family (String.concat "; " names) (String.concat "; " src))
           else
             (match List.assoc_opt family engine_ctor_names with
              | None -> Error (Printf.sprintf "%s: no such family in the engine" family)
              | Some eng ->
                (match prefix_at family 0 names eng with
                 | Error e -> Error e
                 | Ok () -> go rest)))
    in
    go rows

(* ------------------------------------------------------------------ the conversion *)

module Make (A : PROGRAM_TYPES) = struct
  let of_lit : Eff_types.lit -> A.lit = function
    | Eff_types.Lit_unit -> A.Lit_unit
    | Eff_types.Lit_nat n -> A.Lit_nat n
    | Eff_types.Lit_bool b -> A.Lit_bool b
    | Eff_types.Lit_str s -> A.Lit_str s

  let rec of_term : Eff_types.term -> A.term = function
    | Eff_types.Term_var i -> A.Term_var i
    | Eff_types.Term_lit l -> A.Term_lit (of_lit l)
    | Eff_types.Term_app (f, ts) -> A.Term_app (f, of_terms ts)

  and of_terms : Eff_types.terms -> A.terms = function
    | Eff_types.Terms_nil -> A.Terms_nil
    | Eff_types.Terms_cons (t, ts) -> A.Terms_cons (of_term t, of_terms ts)

  let rec of_cause_term : Eff_types.cause_term -> A.cause_term = function
    | Eff_types.Cause_term_fail t -> A.CauseTerm_fail (of_term t)
    | Eff_types.Cause_term_die t -> A.CauseTerm_die (of_term t)
    | Eff_types.Cause_term_interrupt t -> A.CauseTerm_interrupt (Option.map of_term t)
    | Eff_types.Cause_term_both (a, b) -> A.CauseTerm_both (of_cause_term a, of_cause_term b)

  let of_mask_mode : Eff_types.mask_mode -> A.mask_mode = function
    | Eff_types.Mask_mode_interruptible -> A.MaskMode_interruptible
    | Eff_types.Mask_mode_uninterruptible -> A.MaskMode_uninterruptible
    | Eff_types.Mask_mode_inherit -> A.MaskMode_inherit

  let of_fork_options (o : Eff_types.fork_options) : A.fork_options =
    { A.start_immediately = o.Eff_types.fork_options_startImmediately;
      daemon = o.Eff_types.fork_options_daemon;
      mask_mode = of_mask_mode o.Eff_types.fork_options_maskMode }

  let of_observer_mode : Eff_types.observer_mode -> A.observer_mode = function
    | Eff_types.Observer_mode_awaitValue -> A.ObserverMode_awaitValue
    | Eff_types.Observer_mode_joinEffect -> A.ObserverMode_joinEffect

  let of_finalizer_strategy : Eff_types.finalizer_strategy -> A.finalizer_strategy = function
    | Eff_types.Finalizer_strategy_sequential -> A.FinalizerStrategy_sequential
    | Eff_types.Finalizer_strategy_parallel -> A.FinalizerStrategy_parallel

  let of_fn_name : Eff_types.fn_name -> A.fn_name = function
    | Eff_types.Fn_name_incr -> A.FnName_incr
    | Eff_types.Fn_name_double -> A.FnName_double
    | Eff_types.Fn_name_zeroWhenPositive -> A.FnName_zeroWhenPositive
    | Eff_types.Fn_name_noChange -> A.FnName_noChange
    | Eff_types.Fn_name_takeAndBump -> A.FnName_takeAndBump

  let of_service_key (k : Eff_types.service_key) : A.service_key =
    { A.name = k.service_key_name.service_name_value;
      service = k.service_key_service.service_type_code_value }

  let of_native_op : Eff_types.native_op -> A.native_op = function
    | Eff_types.Native_op_refMake -> A.NativeOp_refMake
    | Eff_types.Native_op_refGet -> A.NativeOp_refGet
    | Eff_types.Native_op_refSet -> A.NativeOp_refSet
    | Eff_types.Native_op_refGetAndSet -> A.NativeOp_refGetAndSet
    | Eff_types.Native_op_refSetAndGet -> A.NativeOp_refSetAndGet
    | Eff_types.Native_op_refUpdate f -> A.NativeOp_refUpdate (of_fn_name f)
    | Eff_types.Native_op_refGetAndUpdate f -> A.NativeOp_refGetAndUpdate (of_fn_name f)
    | Eff_types.Native_op_refUpdateAndGet f -> A.NativeOp_refUpdateAndGet (of_fn_name f)
    | Eff_types.Native_op_refUpdateSome f -> A.NativeOp_refUpdateSome (of_fn_name f)
    | Eff_types.Native_op_refGetAndUpdateSome f ->
      A.NativeOp_refGetAndUpdateSome (of_fn_name f)
    | Eff_types.Native_op_refUpdateSomeAndGet f ->
      A.NativeOp_refUpdateSomeAndGet (of_fn_name f)
    | Eff_types.Native_op_refModify f -> A.NativeOp_refModify (of_fn_name f)
    | Eff_types.Native_op_refModifySome f -> A.NativeOp_refModifySome (of_fn_name f)
    | Eff_types.Native_op_deferredMake -> A.NativeOp_deferredMake
    | Eff_types.Native_op_deferredIsDone -> A.NativeOp_deferredIsDone
    | Eff_types.Native_op_deferredPoll -> A.NativeOp_deferredPoll
    | Eff_types.Native_op_deferredSucceed -> A.NativeOp_deferredSucceed
    | Eff_types.Native_op_deferredFail -> A.NativeOp_deferredFail
    | Eff_types.Native_op_deferredAwait -> A.NativeOp_deferredAwait
    | Eff_types.Native_op_scopeMake s -> A.NativeOp_scopeMake (of_finalizer_strategy s)
    | Eff_types.Native_op_sleep | Eff_types.Native_op_clockNow
    | Eff_types.Native_op_external _ ->
      raise (Ordinal_mismatch
        "engine cut before the timer and external rows; regenerate (plan v2 Phase 1)")

  let rec of_eff : Eff_types.eff -> A.native_op A.eff = function
    | Eff_types.Eff_succeed t -> A.Eff_succeed (of_term t)
    | Eff_types.Eff_fail t -> A.Eff_fail (of_term t)
    | Eff_types.Eff_failCause c -> A.Eff_failCause (of_cause_term c)
    | Eff_types.Eff_yieldError t -> A.Eff_yieldError (of_term t)
    | Eff_types.Eff_sync t -> A.Eff_sync (of_term t)
    | Eff_types.Eff_suspend e -> A.Eff_suspend (of_eff e)
    | Eff_types.Eff_perform (op, t) -> A.Eff_perform (of_native_op op, of_term t)
    | Eff_types.Eff_bind (a, b) -> A.Eff_bind (of_eff a, of_eff b)
    | Eff_types.Eff_gen s -> A.Eff_gen (of_stmts s)
    | Eff_types.Eff_catchCause (a, b) -> A.Eff_catchCause (of_eff a, of_eff b)
    | Eff_types.Eff_catchIf _ ->
      raise (Ordinal_mismatch
        "catchIf: engine cut before Phase 1 regeneration")
    | Eff_types.Eff_matchCause (a, b, c) ->
      A.Eff_matchCause (of_eff a, of_eff b, of_eff c)
    | Eff_types.Eff_onExit (a, b) -> A.Eff_onExit (of_eff a, of_eff b)
    | Eff_types.Eff_exit e -> A.Eff_exit (of_eff e)
    | Eff_types.Eff_uninterruptible e -> A.Eff_uninterruptible (of_eff e)
    | Eff_types.Eff_interruptible e -> A.Eff_interruptible (of_eff e)
    | Eff_types.Eff_branch (t, a, b) -> A.Eff_branch (of_term t, of_eff a, of_eff b)
    | Eff_types.Eff_whileLoop (t1, t2, t3, e) ->
      A.Eff_whileLoop (of_term t1, of_term t2, of_term t3, of_eff e)
    | Eff_types.Eff_yieldNow n -> A.Eff_yieldNow n
    | Eff_types.Eff_callback (op, t) -> A.Eff_callback (of_native_op op, of_term t)
    | Eff_types.Eff_awaitFiber (t, m) -> A.Eff_awaitFiber (of_term t, of_observer_mode m)
    | Eff_types.Eff_withFiber a -> A.Eff_withFiber (of_action_term a)
    | Eff_types.Eff_scoped e -> A.Eff_scoped (of_eff e)
    | Eff_types.Eff_acquireRelease (a, b) -> A.Eff_acquireRelease (of_eff a, of_eff b)
    | Eff_types.Eff_choose (n, a, b) -> A.Eff_choose (n, of_eff a, of_eff b)
    | Eff_types.Eff_provideLayer (l, local, e) ->
      A.Eff_provideLayer (of_layer_term l, local, of_eff e)
    | Eff_types.Eff_service k -> A.Eff_service (of_service_key k)
    | Eff_types.Eff_provideService (k, t, e) ->
      A.Eff_provideService (of_service_key k, of_term t, of_eff e)

  and of_layer_term : Eff_types.layer_term -> A.native_op A.layer_term = function
    | Eff_types.Layer_term_succeed (k, l) ->
      A.LayerTerm_succeed (of_service_key k, of_lit l)
    | Eff_types.Layer_term_effect (k, e) -> A.LayerTerm_effect (of_service_key k, of_eff e)
    | Eff_types.Layer_term_effectDiscard e -> A.LayerTerm_effectDiscard (of_eff e)
    | Eff_types.Layer_term_provide (a, b) ->
      A.LayerTerm_provide (of_layer_term a, of_layer_term b)
    | Eff_types.Layer_term_provideMerge (a, b) ->
      A.LayerTerm_provideMerge (of_layer_term a, of_layer_term b)
    | Eff_types.Layer_term_merge (a, b) ->
      A.LayerTerm_merge (of_layer_term a, of_layer_term b)
    | Eff_types.Layer_term_fresh l -> A.LayerTerm_fresh (of_layer_term l)
    | Eff_types.Layer_term_orDie l -> A.LayerTerm_orDie (of_layer_term l)
    (* the host rows slice (2026-09-08): the wire carries `ref` and `mergeAll`, the engine's
       frozen LCNF projection (`api_engine.ml`, cut before this slice) does not; a program
       that reaches them is refused here until plan v2 Phase 1 regenerates the engine *)
    | Eff_types.Layer_term_ref _ ->
      failwith "e4_program: LayerTerm.ref predates the engine's regeneration (Phase 1)"
    | Eff_types.Layer_term_mergeAll _ ->
      failwith "e4_program: LayerTerm.mergeAll predates the engine's regeneration (Phase 1)"

  and of_stmt : Eff_types.stmt -> A.native_op A.stmt = function
    | Eff_types.Stmt_bindYield e -> A.Stmt_bindYield (of_eff e)
    | Eff_types.Stmt_yieldDiscard e -> A.Stmt_yieldDiscard (of_eff e)
    | Eff_types.Stmt_ret t -> A.Stmt_ret (of_term t)
    | Eff_types.Stmt_ifElse (t, a, b) -> A.Stmt_ifElse (of_term t, of_stmts a, of_stmts b)
    | Eff_types.Stmt_whileTrue s -> A.Stmt_whileTrue (of_stmts s)
    | Eff_types.Stmt_breakLoop -> A.Stmt_breakLoop

  and of_stmts : Eff_types.stmts -> A.native_op A.stmts = function
    | Eff_types.Stmts_nil -> A.Stmts_nil
    | Eff_types.Stmts_cons (s, ss) -> A.Stmts_cons (of_stmt s, of_stmts ss)

  and of_effs : Eff_types.effs -> A.native_op A.effs = function
    | Eff_types.Effs_nil -> A.Effs_nil
    | Eff_types.Effs_cons (e, es) -> A.Effs_cons (of_eff e, of_effs es)

  and of_action_term : Eff_types.action_term -> A.native_op A.action_term = function
    | Eff_types.Action_term_fork (e, o) -> A.ActionTerm_fork (of_eff e, of_fork_options o)
    | Eff_types.Action_term_forkIn (e, o, t) ->
      A.ActionTerm_forkIn (of_eff e, of_fork_options o, of_term t)
    | Eff_types.Action_term_forkScoped (e, o) ->
      A.ActionTerm_forkScoped (of_eff e, of_fork_options o)
    | Eff_types.Action_term_runIn (a, b) -> A.ActionTerm_runIn (of_term a, of_term b)
    | Eff_types.Action_term_interrupt t -> A.ActionTerm_interrupt (of_term t)
    | Eff_types.Action_term_interruptScoped t -> A.ActionTerm_interruptScoped (of_term t)
    | Eff_types.Action_term_interruptAll (t, u) ->
      A.ActionTerm_interruptAll (of_term t, Option.map of_term u)
    | Eff_types.Action_term_awaitAll t -> A.ActionTerm_awaitAll (of_term t)
    | Eff_types.Action_term_awaitAllFailFast t -> A.ActionTerm_awaitAllFailFast (of_term t)
    | Eff_types.Action_term_snapshotChildren -> A.ActionTerm_snapshotChildren
    | Eff_types.Action_term_awaitNewChildren t -> A.ActionTerm_awaitNewChildren (of_term t)
    | Eff_types.Action_term_raceAll es -> A.ActionTerm_raceAll (of_effs es)
    | Eff_types.Action_term_setContext t -> A.ActionTerm_setContext (of_term t)
    | Eff_types.Action_term_getContext -> A.ActionTerm_getContext
    | Eff_types.Action_term_getId -> A.ActionTerm_getId
    | Eff_types.Action_term_closeScope (a, b) ->
      A.ActionTerm_closeScope (of_term a, of_term b)

  let load p = pin_exn (); of_eff p

  let of_bytes s =
    match Eff_wire.decode_program_exact s with None -> None | Some p -> Some (load p)

  (* -- the engine side of the ordinal pin ------------------------------------------- *)

  let ctor_index_lit : A.lit -> int = function
    | A.Lit_unit -> 0 | A.Lit_nat _ -> 1 | A.Lit_bool _ -> 2 | A.Lit_str _ -> 3

  let ctor_index_term : A.term -> int = function
    | A.Term_var _ -> 0 | A.Term_lit _ -> 1 | A.Term_app _ -> 2

  let ctor_index_terms : A.terms -> int = function
    | A.Terms_nil -> 0 | A.Terms_cons _ -> 1

  let ctor_index_cause_term : A.cause_term -> int = function
    | A.CauseTerm_fail _ -> 0 | A.CauseTerm_die _ -> 1
    | A.CauseTerm_interrupt _ -> 2 | A.CauseTerm_both _ -> 3

  let ctor_index_mask_mode : A.mask_mode -> int = function
    | A.MaskMode_interruptible -> 0 | A.MaskMode_uninterruptible -> 1
    | A.MaskMode_inherit -> 2

  let ctor_index_observer_mode : A.observer_mode -> int = function
    | A.ObserverMode_awaitValue -> 0 | A.ObserverMode_joinEffect -> 1

  let ctor_index_finalizer_strategy : A.finalizer_strategy -> int = function
    | A.FinalizerStrategy_sequential -> 0 | A.FinalizerStrategy_parallel -> 1

  let ctor_index_fn_name : A.fn_name -> int = function
    | A.FnName_incr -> 0 | A.FnName_double -> 1 | A.FnName_zeroWhenPositive -> 2
    | A.FnName_noChange -> 3 | A.FnName_takeAndBump -> 4

  let ctor_index_native_op : A.native_op -> int = function
    | A.NativeOp_refMake -> 0
    | A.NativeOp_refGet -> 1
    | A.NativeOp_refSet -> 2
    | A.NativeOp_refGetAndSet -> 3
    | A.NativeOp_refSetAndGet -> 4
    | A.NativeOp_refUpdate _ -> 5
    | A.NativeOp_refGetAndUpdate _ -> 6
    | A.NativeOp_refUpdateAndGet _ -> 7
    | A.NativeOp_refUpdateSome _ -> 8
    | A.NativeOp_refGetAndUpdateSome _ -> 9
    | A.NativeOp_refUpdateSomeAndGet _ -> 10
    | A.NativeOp_refModify _ -> 11
    | A.NativeOp_refModifySome _ -> 12
    | A.NativeOp_deferredMake -> 13
    | A.NativeOp_deferredIsDone -> 14
    | A.NativeOp_deferredPoll -> 15
    | A.NativeOp_deferredSucceed -> 16
    | A.NativeOp_deferredFail -> 17
    | A.NativeOp_deferredAwait -> 18
    | A.NativeOp_scopeMake _ -> 19

  let ctor_index_eff : 'op A.eff -> int = function
    | A.Eff_succeed _ -> 0
    | A.Eff_fail _ -> 1
    | A.Eff_failCause _ -> 2
    | A.Eff_yieldError _ -> 3
    | A.Eff_sync _ -> 4
    | A.Eff_suspend _ -> 5
    | A.Eff_perform _ -> 6
    | A.Eff_bind _ -> 7
    | A.Eff_gen _ -> 8
    | A.Eff_catchCause _ -> 9
    | A.Eff_matchCause _ -> 10
    | A.Eff_onExit _ -> 11
    | A.Eff_exit _ -> 12
    | A.Eff_uninterruptible _ -> 13
    | A.Eff_interruptible _ -> 14
    | A.Eff_branch _ -> 15
    | A.Eff_whileLoop _ -> 16
    | A.Eff_yieldNow _ -> 17
    | A.Eff_callback _ -> 18
    | A.Eff_awaitFiber _ -> 19
    | A.Eff_withFiber _ -> 20
    | A.Eff_scoped _ -> 21
    | A.Eff_acquireRelease _ -> 22
    | A.Eff_choose _ -> 23
    | A.Eff_provideLayer _ -> 24
    | A.Eff_service _ -> 25
    | A.Eff_provideService _ -> 26

  let ctor_index_stmt : 'op A.stmt -> int = function
    | A.Stmt_bindYield _ -> 0 | A.Stmt_yieldDiscard _ -> 1 | A.Stmt_ret _ -> 2
    | A.Stmt_ifElse _ -> 3 | A.Stmt_whileTrue _ -> 4 | A.Stmt_breakLoop -> 5

  let ctor_index_stmts : 'op A.stmts -> int = function
    | A.Stmts_nil -> 0 | A.Stmts_cons _ -> 1

  let ctor_index_effs : 'op A.effs -> int = function
    | A.Effs_nil -> 0 | A.Effs_cons _ -> 1

  let ctor_index_action_term : 'op A.action_term -> int = function
    | A.ActionTerm_fork _ -> 0
    | A.ActionTerm_forkIn _ -> 1
    | A.ActionTerm_forkScoped _ -> 2
    | A.ActionTerm_runIn _ -> 3
    | A.ActionTerm_interrupt _ -> 4
    | A.ActionTerm_interruptScoped _ -> 5
    | A.ActionTerm_interruptAll _ -> 6
    | A.ActionTerm_awaitAll _ -> 7
    | A.ActionTerm_awaitAllFailFast _ -> 8
    | A.ActionTerm_snapshotChildren -> 9
    | A.ActionTerm_awaitNewChildren _ -> 10
    | A.ActionTerm_raceAll _ -> 11
    | A.ActionTerm_setContext _ -> 12
    | A.ActionTerm_getContext -> 13
    | A.ActionTerm_getId -> 14
    | A.ActionTerm_closeScope _ -> 15
end
