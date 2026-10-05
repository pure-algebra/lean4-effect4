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

(* STOPGAP. `of_ty` below is a hand copy of the source's `Ty` alphabet; its own totality is
   checked by the compiler against `Eff_types.ty`, which is generated, so an appended source
   constructor is already a build error at the match. What this line adds is the case that
   exhaustiveness cannot see: a catch-all put back into `of_ty`, which would make the match
   total again and the copy silently short. `Eff_types.ctor_names_ty` is the source's own
   name list, generated by `src/OCaml5/Tools/EffGen.lean` from the Lean inductive, so the
   number is the source's, not ours. The runner plan's step 1 (`Api.ofBytes`/`bytesOf` as the
   engine roots) deletes this module, the layout mirror and this assertion together. *)
let () = assert (List.length Eff_types.ctor_names_ty = 28)

module Make (A : PROGRAM_TYPES) = struct
  let rec of_ty : Eff_types.ty -> A.ty = function
    | Eff_types.Ty_never -> A.Ty_never
    | Eff_types.Ty_unit -> A.Ty_unit
    | Eff_types.Ty_nat -> A.Ty_nat
    | Eff_types.Ty_int -> A.Ty_int
    | Eff_types.Ty_string -> A.Ty_string
    | Eff_types.Ty_bool -> A.Ty_bool
    | Eff_types.Ty_handle h -> A.Ty_handle h
    | Eff_types.Ty_option a -> A.Ty_option (of_ty a)
    | Eff_types.Ty_list a -> A.Ty_list (of_ty a)
    | Eff_types.Ty_prod (a, b) -> A.Ty_prod (of_ty a, of_ty b)
    | Eff_types.Ty_except (a, b) -> A.Ty_except (of_ty a, of_ty b)
    | Eff_types.Ty_exitOf (a, b) -> A.Ty_exitOf (of_ty a, of_ty b)
    | Eff_types.Ty_causeOf a -> A.Ty_causeOf (of_ty a)
    | Eff_types.Ty_fiberOf (a, b) -> A.Ty_fiberOf (of_ty a, of_ty b)
    | Eff_types.Ty_union (a, b) -> A.Ty_union (of_ty a, of_ty b)
    | Eff_types.Ty_lit s -> A.Ty_lit s
    (* `Ref.Ref<A>` and `Deferred.Deferred<A, E>` (decisions row 42), the row template's
       parameter and the top `unknown` (row 46), in the source's declaration order. The
       engine's alphabet used to end at `lit` and the four were refused by name here; the
       mirror is at twenty now, so the match is total and the catch-all is gone. *)
    | Eff_types.Ty_refOf a -> A.Ty_refOf (of_ty a)
    | Eff_types.Ty_deferredOf (a, b) -> A.Ty_deferredOf (of_ty a, of_ty b)
    | Eff_types.Ty_var i -> A.Ty_var i
    | Eff_types.Ty_unknown -> A.Ty_unknown
    (* The data wave's forms (decisions rows 119, 125, 157-162), in the source's order. *)
    | Eff_types.Ty_record fs -> A.Ty_record (List.map (fun (n, (o, t)) -> (n, (o, of_ty t))) fs)
    | Eff_types.Ty_map (k, v) -> A.Ty_map (of_ty k, of_ty v)
    | Eff_types.Ty_tuple ts -> A.Ty_tuple (List.map of_ty ts)
    | Eff_types.Ty_app (n, ts) -> A.Ty_app (n, List.map of_ty ts)
    | Eff_types.Ty_null -> A.Ty_null
    | Eff_types.Ty_undefined -> A.Ty_undefined
    | Eff_types.Ty_number -> A.Ty_number
    | Eff_types.Ty_bytes -> A.Ty_bytes

  let of_lit : Eff_types.lit -> A.lit = function
    | Eff_types.Lit_unit -> A.Lit_unit
    | Eff_types.Lit_nat n -> A.Lit_nat n
    | Eff_types.Lit_bool b -> A.Lit_bool b
    | Eff_types.Lit_str s -> A.Lit_str s

  let of_field_read_mode : Eff_types.field_read_mode -> A.field_read_mode = function
    | Eff_types.Field_read_mode_required -> A.FieldReadMode_required
    | Eff_types.Field_read_mode_optional -> A.FieldReadMode_optional

  let rec of_term : Eff_types.term -> A.term = function
    | Eff_types.Term_var i -> A.Term_var i
    | Eff_types.Term_lit l -> A.Term_lit (of_lit l)
    | Eff_types.Term_app (f, ts) -> A.Term_app (f, of_terms ts)
    | Eff_types.Term_record (fields, names, values) ->
      A.Term_record
        (List.map (fun (name, (optional, ty)) -> (name, (optional, of_ty ty))) fields,
         names, of_terms values)
    | Eff_types.Term_field (mode, target, name) ->
      A.Term_field (of_field_read_mode mode, of_term target, name)
    | Eff_types.Term_recordSet (target, name, value) ->
      A.Term_recordSet (of_term target, name, of_term value)
    | Eff_types.Term_tupleAt (target, index) -> A.Term_tupleAt (of_term target, index)
    | Eff_types.Term_fold (acc_ty, list, init, body) ->
      A.Term_fold (Option.map of_ty acc_ty, of_term list, of_term init, of_term body)

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

  let of_service_key (k : Eff_types.service_key) : A.service_key =
    { A.name = k.service_key_name.service_name_value;
      service = k.service_key_service.service_type_code_value }

  let of_native_op : Eff_types.native_op -> A.native_op = function
    | Eff_types.Native_op_refMake -> A.NativeOp_refMake
    | Eff_types.Native_op_refGet -> A.NativeOp_refGet
    | Eff_types.Native_op_refSet -> A.NativeOp_refSet
    | Eff_types.Native_op_refGetAndSet -> A.NativeOp_refGetAndSet
    | Eff_types.Native_op_refSetAndGet -> A.NativeOp_refSetAndGet
    | Eff_types.Native_op_deferredIsDone -> A.NativeOp_deferredIsDone
    | Eff_types.Native_op_deferredPoll -> A.NativeOp_deferredPoll
    | Eff_types.Native_op_deferredSucceed -> A.NativeOp_deferredSucceed
    | Eff_types.Native_op_deferredFail -> A.NativeOp_deferredFail
    | Eff_types.Native_op_deferredAwait -> A.NativeOp_deferredAwait
    | Eff_types.Native_op_scopeMake s -> A.NativeOp_scopeMake (of_finalizer_strategy s)
    | Eff_types.Native_op_sleep -> A.NativeOp_sleep
    | Eff_types.Native_op_clockNow -> A.NativeOp_clockNow
    | Eff_types.Native_op_external d -> A.NativeOp_external d
    | Eff_types.Native_op_deferredMakeOf (v, e) -> A.NativeOp_deferredMakeOf (of_ty v, of_ty e)
    (* The eight read-modify-write rows carry their binder term (decisions row 43; the state
       plan's T3b): the term reads the cell's current value at the node's level. *)
    | Eff_types.Native_op_refUpdateWith f -> A.NativeOp_refUpdateWith (of_term f)
    | Eff_types.Native_op_refGetAndUpdateWith f -> A.NativeOp_refGetAndUpdateWith (of_term f)
    | Eff_types.Native_op_refUpdateAndGetWith f -> A.NativeOp_refUpdateAndGetWith (of_term f)
    | Eff_types.Native_op_refUpdateSomeWith f -> A.NativeOp_refUpdateSomeWith (of_term f)
    | Eff_types.Native_op_refGetAndUpdateSomeWith f ->
      A.NativeOp_refGetAndUpdateSomeWith (of_term f)
    | Eff_types.Native_op_refUpdateSomeAndGetWith f ->
      A.NativeOp_refUpdateSomeAndGetWith (of_term f)
    | Eff_types.Native_op_refModifyWith f -> A.NativeOp_refModifyWith (of_term f)
    | Eff_types.Native_op_refModifySomeWith f -> A.NativeOp_refModifySomeWith (of_term f)

  let of_decision : Eff_types.decision -> A.decision = function
    | Eff_types.Decision_bool -> A.Decision_bool
    | Eff_types.Decision_option -> A.Decision_option
    | Eff_types.Decision_tag t -> A.Decision_tag t
    | Eff_types.Decision_recordTag t -> A.Decision_recordTag t

  let rec of_eff : Eff_types.eff -> A.native_op A.eff = function
    | Eff_types.Eff_succeed t -> A.Eff_succeed (of_term t)
    | Eff_types.Eff_fail t -> A.Eff_fail (of_term t)
    | Eff_types.Eff_failCause c -> A.Eff_failCause (of_cause_term c)
    | Eff_types.Eff_sync t -> A.Eff_sync (of_term t)
    | Eff_types.Eff_suspend e -> A.Eff_suspend (of_eff e)
    | Eff_types.Eff_perform (op, t) -> A.Eff_perform (of_native_op op, of_term t)
    | Eff_types.Eff_bind (a, b) -> A.Eff_bind (of_eff a, of_eff b)
    | Eff_types.Eff_gen s -> A.Eff_gen (of_stmts s)
    | Eff_types.Eff_catchCause (a, b) -> A.Eff_catchCause (of_eff a, of_eff b)
    | Eff_types.Eff_catchIf (t, a, b) -> A.Eff_catchIf (of_term t, of_eff a, of_eff b)
    | Eff_types.Eff_matchCause (a, b, c) ->
      A.Eff_matchCause (of_eff a, of_eff b, of_eff c)
    | Eff_types.Eff_onExit (a, b) -> A.Eff_onExit (of_eff a, of_eff b)
    | Eff_types.Eff_exit e -> A.Eff_exit (of_eff e)
    | Eff_types.Eff_uninterruptible e -> A.Eff_uninterruptible (of_eff e)
    | Eff_types.Eff_interruptible e -> A.Eff_interruptible (of_eff e)
    | Eff_types.Eff_select (t, d, a, b) ->
      A.Eff_select (of_term t, of_decision d, of_eff a, of_eff b)
    | Eff_types.Eff_iterate (c, t1, t2, t3, t4, e) ->
      A.Eff_iterate (Option.map of_ty c, of_term t1, of_term t2, of_term t3, of_term t4, of_eff e)
    | Eff_types.Eff_yieldNow n -> A.Eff_yieldNow n
    | Eff_types.Eff_awaitFiber (t, m) -> A.Eff_awaitFiber (of_term t, of_observer_mode m)
    | Eff_types.Eff_withFiber a -> A.Eff_withFiber (of_action_term a)
    | Eff_types.Eff_scoped e -> A.Eff_scoped (of_eff e)
    | Eff_types.Eff_acquireRelease (a, b) -> A.Eff_acquireRelease (of_eff a, of_eff b)
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
    | Eff_types.Layer_term_ref path -> A.LayerTerm_ref path
    | Eff_types.Layer_term_mergeAll layers -> A.LayerTerm_mergeAll (of_layer_terms layers)

  and of_layer_terms : Eff_types.layer_terms -> A.native_op A.layer_terms = function
    | Eff_types.Layer_terms_nil -> A.LayerTerms_nil
    | Eff_types.Layer_terms_cons (h, t) -> A.LayerTerms_cons (of_layer_term h, of_layer_terms t)

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

  let ctor_index_field_read_mode : A.field_read_mode -> int = function
    | A.FieldReadMode_required -> 0 | A.FieldReadMode_optional -> 1

  let ctor_index_term : A.term -> int = function
    | A.Term_var _ -> 0 | A.Term_lit _ -> 1 | A.Term_app _ -> 2
    | A.Term_record _ -> 3 | A.Term_field _ -> 4 | A.Term_recordSet _ -> 5
    | A.Term_tupleAt _ -> 6 | A.Term_fold _ -> 7

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

  let ctor_index_native_op : A.native_op -> int = function
    | A.NativeOp_refMake -> 0
    | A.NativeOp_refGet -> 1
    | A.NativeOp_refSet -> 2
    | A.NativeOp_refGetAndSet -> 3
    | A.NativeOp_refSetAndGet -> 4
    | A.NativeOp_deferredIsDone -> 5
    | A.NativeOp_deferredPoll -> 6
    | A.NativeOp_deferredSucceed -> 7
    | A.NativeOp_deferredFail -> 8
    | A.NativeOp_deferredAwait -> 9
    | A.NativeOp_scopeMake _ -> 10
    | A.NativeOp_sleep -> 11
    | A.NativeOp_clockNow -> 12
    | A.NativeOp_external _ -> 13
    | A.NativeOp_deferredMakeOf _ -> 14
    | A.NativeOp_refUpdateWith _ -> 15
    | A.NativeOp_refGetAndUpdateWith _ -> 16
    | A.NativeOp_refUpdateAndGetWith _ -> 17
    | A.NativeOp_refUpdateSomeWith _ -> 18
    | A.NativeOp_refGetAndUpdateSomeWith _ -> 19
    | A.NativeOp_refUpdateSomeAndGetWith _ -> 20
    | A.NativeOp_refModifyWith _ -> 21
    | A.NativeOp_refModifySomeWith _ -> 22

  let ctor_index_decision : A.decision -> int = function
    | A.Decision_bool -> 0 | A.Decision_option -> 1 | A.Decision_tag _ -> 2
    | A.Decision_recordTag _ -> 3

  let ctor_index_eff : 'op A.eff -> int = function
    | A.Eff_succeed _ -> 0
    | A.Eff_fail _ -> 1
    | A.Eff_failCause _ -> 2
    | A.Eff_sync _ -> 3
    | A.Eff_suspend _ -> 4
    | A.Eff_perform _ -> 5
    | A.Eff_bind _ -> 6
    | A.Eff_gen _ -> 7
    | A.Eff_catchCause _ -> 8
    | A.Eff_matchCause _ -> 9
    | A.Eff_onExit _ -> 10
    | A.Eff_exit _ -> 11
    | A.Eff_uninterruptible _ -> 12
    | A.Eff_interruptible _ -> 13
    | A.Eff_yieldNow _ -> 14
    | A.Eff_awaitFiber _ -> 15
    | A.Eff_withFiber _ -> 16
    | A.Eff_scoped _ -> 17
    | A.Eff_acquireRelease _ -> 18
    | A.Eff_provideLayer _ -> 19
    | A.Eff_service _ -> 20
    | A.Eff_provideService _ -> 21
    | A.Eff_catchIf _ -> 22
    | A.Eff_select _ -> 23
    | A.Eff_iterate _ -> 24

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
