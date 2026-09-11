(* Eff_typing — the typing judgement of src/Effect4/Program/Typing.lean over the untyped
   carrier (hand-written).

   What it is: `typeOf` at the native signature (`nativeSignature`: the rows of Eff_native,
   the atom table, the scope key), rule for rule. `Ty.join` (canonical unions, Eff.lean),
   `EffTy.joinAnswer`, `GenTy.merge` and the requirement row (`Row ServiceKey`, Data/Row.lean,
   carried as the strictly ascending key list) are restated here, with the join's two tables
   (2026-09-07): the service table `service_ty` (`nativeServiceTy`, Program/Native.lean: the
   Scope key, nothing under the other reserved names, a free name's carrier by its type code)
   and `LayerTy` (Typing.lean: `Layer<ROut, E, RIn>` as three rows, its four operations, and
   `layer_of` = `layerTy` over the layer term, whose bodies are typed closed).
   Depends on: Eff_types, Eff_native (generated), Eff_json (for print_type).

   Behaviours it holds itself to:
   T1  Acceptance agrees with Lean: type_of p is Ok exactly when Lean's `typeOf nativeSignature
       p` is `some`, and the answer, error and requirement row are the same values.
                                              tested (goldens/<name>.ty for every corpus program)
   T2  Structural and total: every arm is a pattern of the carrier; refusals are Error with the
       rule that refused, never an exception.                        by construction
   T3  Unions are canonical: join sorts members by Ty.key, drops duplicates and `never`,
       right-nests; requirement rows are strictly ascending by the name-major key order.
                                                                      by construction; tested
   The refusal messages are this side's own; Lean answers `none`. Only acceptance and the
   accepted type are the contract. *)

open Eff_types

(* ---- Ty.join (Eff.lean: key, ltKey, insertMember, ofMembers, members, join) ---- *)

let rec key : ty -> int list = function
  | Ty_never -> [ 0 ]
  | Ty_unit -> [ 1 ]
  | Ty_nat -> [ 2 ]
  | Ty_int -> [ 3 ]
  | Ty_string -> [ 4 ]
  | Ty_bool -> [ 5 ]
  | Ty_handle target -> 6 :: List.init (String.length target) (fun i -> Char.code target.[i])
  | Ty_option inner -> 7 :: key inner
  | Ty_list inner -> 8 :: key inner
  | Ty_prod (l, r) ->
    let kl = key l in
    (9 :: List.length kl :: kl) @ key r
  | Ty_except (e, v) ->
    let ke = key e in
    (10 :: List.length ke :: ke) @ key v
  | Ty_exitOf (v, e) ->
    let kv = key v in
    (11 :: List.length kv :: kv) @ key e
  | Ty_causeOf e -> 12 :: key e
  | Ty_fiberOf (v, e) ->
    let kv = key v in
    (13 :: List.length kv :: kv) @ key e
  | Ty_union (l, r) ->
    let kl = key l in
    (14 :: List.length kl :: kl) @ key r
  | Ty_lit value -> 15 :: List.init (String.length value) (fun i -> Char.code value.[i])

let rec lt_key (a : int list) (b : int list) : bool =
  match a, b with
  | [], [] -> false
  | [], _ :: _ -> true
  | _ :: _, [] -> false
  | x :: xs, y :: ys -> if x < y then true else if y < x then false else lt_key xs ys

let rec members : ty -> ty list = function
  | Ty_never -> []
  | Ty_union (l, r) -> members l @ members r
  | t -> [ t ]

let rec insert_member (t : ty) : ty list -> ty list = function
  | [] -> [ t ]
  | u :: rest ->
    if t = u then u :: rest
    else if lt_key (key t) (key u) then t :: u :: rest
    else u :: insert_member t rest

let rec of_members : ty list -> ty = function
  | [] -> Ty_never
  | [ t ] -> t
  | t :: rest -> Ty_union (t, of_members rest)

(* Deep normalization mirrors Program/Ty.lean. Row.normalize is right-folded sorted
   insertion; the key and unique member order remain unchanged. *)
let rec normalize : ty -> ty = function
  | Ty_option t -> Ty_option (normalize t)
  | Ty_list t -> Ty_list (normalize t)
  | Ty_prod (a, b) -> Ty_prod (normalize a, normalize b)
  | Ty_except (a, b) -> Ty_except (normalize a, normalize b)
  | Ty_exitOf (a, b) -> Ty_exitOf (normalize a, normalize b)
  | Ty_causeOf t -> Ty_causeOf (normalize t)
  | Ty_fiberOf (a, b) -> Ty_fiberOf (normalize a, normalize b)
  | Ty_union (a, b) ->
    of_members (List.fold_right insert_member (members (normalize a) @ members (normalize b)) [])
  | t -> t

let join (a : ty) (b : ty) : ty = normalize (Ty_union (a, b))

let is_never : ty -> bool = function Ty_never -> true | _ -> false

(* ---- Requirement = Row ServiceKey: the strictly ascending key list ---- *)

type requirement = service_key list

let key_lt (a : service_key) (b : service_key) : bool =
  a.service_key_name.service_name_value < b.service_key_name.service_name_value
  || a.service_key_name = b.service_key_name
     && a.service_key_service.service_type_code_value < b.service_key_service.service_type_code_value

let req_empty : requirement = []

let rec req_insert (x : service_key) : requirement -> requirement = function
  | [] -> [ x ]
  | y :: rest ->
    if key_lt x y then x :: y :: rest else if x = y then y :: rest else y :: req_insert x rest

(* Row.normalize: insert x (normalize xs) *)
let req_of_list (keys : service_key list) : requirement = List.fold_right req_insert keys []
let req_single (k : service_key) : requirement = [ k ]
let req_union (r : requirement) (s : requirement) : requirement = req_of_list (r @ s)

(* Row.diff (Data/Row.lean:414): the members of r outside s; a subrow stays ascending. *)
let req_diff (r : requirement) (s : requirement) : requirement = List.filter (fun k -> not (List.mem k s)) r

(* ---- the service table: nativeServiceTy (Program/Native.lean), read off the key ---- *)

(* Env.firstFreeName (Machine/ContextMap.lean:797): names 0-3 are the reserved keys. *)
let first_free_name : int = 4

(* The Scope key answers Ty.scope; the other reserved names type nothing; a free name is typed
   by its own type code: 4 a number, 5 a boolean, 6 unit, 7 a Ref.Ref<number> handle,
   8 a SqlClient.SqlClient handle, 9 a KeyValueStore.KeyValueStore handle. *)
let service_ty (key : service_key) : ty option =
  if key = Eff_native.scope_key then Some Eff_native.scope_ty
  else if key.service_key_name.service_name_value < first_free_name then None
  else
    match key.service_key_service.service_type_code_value with
    | 4 -> Some Ty_nat
    | 5 -> Some Ty_bool
    | 6 -> Some Ty_unit
    | 7 -> Some Eff_native.ref_ty
    | 8 -> Some (Ty_handle "SqlClient.SqlClient")
    | 9 -> Some (Ty_handle "KeyValueStore.KeyValueStore")
    | _ -> None

(* ---- LayerTy (Typing.lean): Layer<ROut, E, RIn> as three rows, and its four operations ---- *)

type layer_ty = { layer_out : requirement; layer_error : ty; layer_requires : requirement }

(* self.pipe(Layer.provide(that)): the dependency discharges what it provides. *)
let layer_provide (self : layer_ty) (that : layer_ty) : layer_ty =
  { layer_out = self.layer_out; layer_error = join self.layer_error that.layer_error;
    layer_requires = req_union (req_diff self.layer_requires that.layer_out) that.layer_requires }

(* self.pipe(Layer.provideMerge(that)): the same requirement column, both outputs kept. *)
let layer_provide_merge (self : layer_ty) (that : layer_ty) : layer_ty =
  { layer_out = req_union self.layer_out that.layer_out; layer_error = join self.layer_error that.layer_error;
    layer_requires = req_union (req_diff self.layer_requires that.layer_out) that.layer_requires }

(* Layer.merge(a, b): siblings share nothing. *)
let layer_merge (a : layer_ty) (b : layer_ty) : layer_ty =
  { layer_out = req_union a.layer_out b.layer_out; layer_error = join a.layer_error b.layer_error;
    layer_requires = req_union a.layer_requires b.layer_requires }

(* Layer.orDie(l): the error column becomes never. *)
let layer_or_die (l : layer_ty) : layer_ty = { l with layer_error = Ty_never }

(* bodyRequires: Exclude<R, Scope.Scope> — the layer's own scope answers the body's. *)
let body_requires (t : eff_ty) : requirement = req_diff t.eff_ty_requires (req_single Eff_native.scope_key)

(* litVal: strings are not layer values (PROV-FB-STRING-VALUE). *)
let lit_is_value : lit -> bool = function Lit_str _ -> false | _ -> true

(* ---- EffTy, GenTy ---- *)

let mk answer error requires = { eff_ty_answer = answer; eff_ty_error = error; eff_ty_requires = requires }
let pure (answer : ty) : eff_ty = mk answer Ty_never req_empty

let join_answer (a : ty) (b : ty) : ty option =
  let a = normalize a and b = normalize b in
  if a = b then Some a else if is_never a then Some b else if is_never b then Some a else None

type gen_ty = { gen_answer : ty option; gen_error : ty; gen_requires : requirement }

let gen_join_answer (a : ty option) (b : ty option) : ty option option =
  match a, b with
  | None, b -> Some b
  | a, None -> Some a
  | Some a, Some b -> Option.map (fun t -> Some t) (join_answer a b)

let fiber_ty : ty -> (ty * ty) option = function
  | Ty_fiberOf (v, e) -> Some (v, e)
  | _ -> None

(* ---- the judgement ---- *)

type env = ty list
type refusal = string
type 'a checked = ('a, refusal) result

let ( let* ) = Result.bind
let refuse (rule : string) : 'a checked = Error rule

let lit_ty : lit -> ty = function
  | Lit_unit -> Ty_unit
  | Lit_nat _ -> Ty_nat
  | Lit_bool _ -> Ty_bool
  | Lit_str _ -> Ty_string

let rec term_ty (env : env) : term -> ty checked = function
  | Term_var i ->
    if i >= 0 && i < List.length env then Ok (List.nth env i)
    else refuse (Printf.sprintf "var %d: the environment has %d entries" i (List.length env))
  | Term_lit l -> Ok (lit_ty l)
  | Term_app (atom, args) ->
    let* tys = terms_ty env args in
    (match Eff_native.atom_ty atom tys with
     | Some t -> Ok t
     | None -> refuse ("atom " ^ atom ^ ": refused at these argument types"))

and terms_ty (env : env) : terms -> ty list checked = function
  | Terms_nil -> Ok []
  | Terms_cons (h, t) ->
    let* x = term_ty env h in
    let* xs = terms_ty env t in
    Ok (x :: xs)

(* DI-62: the closed error image; all three failure introductions consult this. *)
let rec supported_error_ty : ty -> bool = function
  | Ty_never | Ty_nat | Ty_string | Ty_prod (Ty_string, Ty_string) -> true
  | Ty_union (l, r) -> supported_error_ty l && supported_error_ty r
  | _ -> false

(* The GADT witnesses construct a safe subset of raw spellings; the decision checker
   also admits representable columns exposed by canonical normalization. *)
let admitted_error_ty t = supported_error_ty (normalize t)

let rec cause_ty (env : env) : cause_term -> ty checked = function
  | Cause_term_fail e ->
    let* t = term_ty env e in
    if admitted_error_ty t then Ok t else refuse "cause fail: unsupported error type"
  | Cause_term_die d ->
    let* _ = term_ty env d in
    Ok Ty_never
  | Cause_term_interrupt None -> Ok Ty_never
  | Cause_term_interrupt (Some who) ->
    let* t = term_ty env who in
    if t = Ty_nat then Ok Ty_never else refuse "interrupt: the interruptor is not a nat"
  | Cause_term_both (l, r) ->
    let* l = cause_ty env l in
    let* r = cause_ty env r in
    Ok (join l r)

let gen_merge (a : gen_ty) (b : gen_ty) : gen_ty checked =
  match gen_join_answer a.gen_answer b.gen_answer with
  | None -> refuse "gen: the returns of two branches do not join"
  | Some answer ->
    Ok { gen_answer = answer; gen_error = join a.gen_error b.gen_error;
         gen_requires = req_union a.gen_requires b.gen_requires }

let row_answer (row : row) : eff_ty =
  mk row.row_answer row.row_error (req_of_list row.row_requires)

let rec check_eff (env : env) (p : eff) : eff_ty checked =
  match p with
  | Eff_succeed v ->
    let* t = term_ty env v in
    Ok (pure t)
  | Eff_fail e ->
    let* t = term_ty env e in
    if admitted_error_ty t then Ok (mk Ty_never t req_empty)
    else refuse "fail: unsupported error type"
  | Eff_failCause c ->
    let* e = cause_ty env c in
    Ok (mk Ty_never e req_empty)
  | Eff_yieldError e ->
    let* t = term_ty env e in
    if admitted_error_ty t then Ok (mk Ty_never t req_empty)
    else refuse "yieldError: unsupported error type"
  | Eff_sync t ->
    let* t = term_ty env t in
    Ok (pure t)
  | Eff_suspend body -> check_eff env body
  | Eff_perform (Native_op_external _, _) ->
    refuse "perform: external index is outside the empty row table"
  | Eff_perform (op, request) ->
    let row = Eff_native.row_of op in
    let* r = term_ty env request in
    if normalize r = normalize row.row_request then Ok (row_answer row)
    else refuse ("perform " ^ row.row_name ^ ": the request type is not the row's")
  | Eff_bind (first, rest) ->
    let* f = check_eff env first in
    let* r = check_eff (env @ [ f.eff_ty_answer ]) rest in
    Ok (mk r.eff_ty_answer (join f.eff_ty_error r.eff_ty_error) (req_union f.eff_ty_requires r.eff_ty_requires))
  | Eff_gen body ->
    let* g = check_stmts env false body in
    Ok (mk (match g.gen_answer with Some a -> a | None -> Ty_unit) g.gen_error g.gen_requires)
  | Eff_catchCause (body, handler) ->
    let* b = check_eff env body in
    let* h = check_eff (env @ [ Ty_causeOf b.eff_ty_error ]) handler in
    (match join_answer b.eff_ty_answer h.eff_ty_answer with
     | None -> refuse "catchCause: the answers do not join"
     | Some answer -> Ok (mk answer h.eff_ty_error (req_union b.eff_ty_requires h.eff_ty_requires)))
  | Eff_catchIf (test, body, handler) ->
    let* b = check_eff env body in
    let error_env = env @ [ b.eff_ty_error ] in
    let* predicate = term_ty error_env test in
    if predicate <> Ty_bool then refuse "catchIf: predicate must be Boolean" else
    let* h = check_eff error_env handler in
    (match join_answer b.eff_ty_answer h.eff_ty_answer with
     | None -> refuse "catchIf: the answers do not join"
     | Some answer ->
       let error = if test = Term_lit (Lit_bool true) then h.eff_ty_error else join b.eff_ty_error h.eff_ty_error in
       Ok (mk answer error (req_union b.eff_ty_requires h.eff_ty_requires)))
  | Eff_matchCause (body, on_value, on_cause) ->
    let* b = check_eff env body in
    let* v = check_eff (env @ [ b.eff_ty_answer ]) on_value in
    let* c = check_eff (env @ [ Ty_causeOf b.eff_ty_error ]) on_cause in
    (match join_answer v.eff_ty_answer c.eff_ty_answer with
     | None -> refuse "matchCause: the answers do not join"
     | Some answer ->
       Ok (mk answer (join v.eff_ty_error c.eff_ty_error)
             (req_union (req_union b.eff_ty_requires v.eff_ty_requires) c.eff_ty_requires)))
  | Eff_onExit (body, finalizer) ->
    let* b = check_eff env body in
    let* f = check_eff (env @ [ Ty_exitOf (b.eff_ty_answer, b.eff_ty_error) ]) finalizer in
    Ok (mk b.eff_ty_answer (join b.eff_ty_error f.eff_ty_error) (req_union b.eff_ty_requires f.eff_ty_requires))
  | Eff_exit body ->
    let* b = check_eff env body in
    Ok (mk (Ty_exitOf (b.eff_ty_answer, b.eff_ty_error)) Ty_never b.eff_ty_requires)
  | Eff_uninterruptible body -> check_eff env body
  | Eff_interruptible body -> check_eff env body
  | Eff_branch (test, then_b, else_b) ->
    let* t = term_ty env test in
    if t = Ty_bool then
      let* a = check_eff env then_b in
      let* b = check_eff env else_b in
      match join_answer a.eff_ty_answer b.eff_ty_answer with
      | None -> refuse "branch: the answers do not join"
      | Some answer ->
        Ok (mk answer (join a.eff_ty_error b.eff_ty_error) (req_union a.eff_ty_requires b.eff_ty_requires))
    else refuse "branch: the test is not a bool"
  | Eff_whileLoop (initial, test, step, body) ->
    let* cursor = term_ty env initial in
    let* t = term_ty (env @ [ cursor ]) test in
    let* b = check_eff (env @ [ cursor ]) body in
    let* s = term_ty (env @ [ cursor; b.eff_ty_answer ]) step in
    if t = Ty_bool && s = cursor then Ok (mk Ty_unit b.eff_ty_error b.eff_ty_requires)
    else refuse "whileLoop: the test is not a bool or the step is not the cursor's type"
  | Eff_yieldNow _ -> Ok (pure Ty_unit)
  | Eff_callback (Native_op_external _, _) ->
    refuse "callback: external index is outside the empty row table"
  | Eff_callback (register, request) ->
    let row = Eff_native.row_of register in
    let* r = term_ty env request in
    if row.row_kind = Row_kind_async && normalize r = normalize row.row_request then Ok (row_answer row)
    else refuse ("callback " ^ row.row_name ^ ": the row is not async or the request type is not the row's")
  | Eff_awaitFiber (fiber, mode) ->
    let* t = term_ty env fiber in
    (match fiber_ty t with
     | None -> refuse "awaitFiber: not a fiber handle"
     | Some (value, error) ->
       (match mode with
        | Observer_mode_joinEffect -> Ok (mk value error req_empty)
        | Observer_mode_awaitValue -> Ok (pure (Ty_exitOf (value, error)))))
  | Eff_withFiber action -> check_action env action
  (* DI-63: Effect.scoped excludes only Scope; the row operation is shared with layers. *)
  | Eff_scoped body ->
    let* t = check_eff env body in
    Ok { t with eff_ty_requires = body_requires t }
  | Eff_acquireRelease (acquire, release) ->
    let* a = check_eff env acquire in
    let* r = check_eff (env @ [ a.eff_ty_answer; Ty_exitOf (a.eff_ty_answer, a.eff_ty_error) ]) release in
    Ok (mk a.eff_ty_answer a.eff_ty_error
          (req_union (req_union a.eff_ty_requires r.eff_ty_requires) (req_single Eff_native.scope_key)))
  (* Effect.provide(self, layer): the layer's requirements join, what it provides is discharged
     from the body's (internal/layer.ts:8-14). *)
  | Eff_provideLayer (layer, _, body) ->
    let* l = check_layer layer in
    let* b = check_eff env body in
    Ok (mk b.eff_ty_answer (join b.eff_ty_error l.layer_error)
          (req_union l.layer_requires (req_diff b.eff_ty_requires l.layer_out)))
  (* Effect.service(key): the carrier from the service table, requiring the key. *)
  | Eff_service key ->
    (match service_ty key with
     | None -> refuse "service: the signature does not type this key"
     | Some ty -> Ok (mk ty Ty_never (req_single key)))
  (* Effect.provideService(self, key, value): the value at the key's carrier, the key
     discharged from the body's requirements. *)
  | Eff_provideService (key, value, body) ->
    (match service_ty key with
     | None -> refuse "provideService: the signature does not type this key"
     | Some ty ->
       let* v = term_ty env value in
       let* b = check_eff env body in
       if normalize v = normalize ty then Ok (mk b.eff_ty_answer b.eff_ty_error (req_diff b.eff_ty_requires (req_single key)))
       else refuse "provideService: the value is not the key's carrier")

and check_stmts (env : env) (in_loop : bool) (body : stmts) : gen_ty checked =
  match body with
  | Stmts_nil -> Ok { gen_answer = None; gen_error = Ty_never; gen_requires = req_empty }
  | Stmts_cons (Stmt_bindYield effect, rest) ->
    let* t = check_eff env effect in
    let* r = check_stmts (env @ [ t.eff_ty_answer ]) in_loop rest in
    Ok { gen_answer = r.gen_answer; gen_error = join t.eff_ty_error r.gen_error;
         gen_requires = req_union t.eff_ty_requires r.gen_requires }
  | Stmts_cons (Stmt_yieldDiscard effect, rest) ->
    let* t = check_eff env effect in
    let* r = check_stmts env in_loop rest in
    Ok { gen_answer = r.gen_answer; gen_error = join t.eff_ty_error r.gen_error;
         gen_requires = req_union t.eff_ty_requires r.gen_requires }
  | Stmts_cons (Stmt_ret value, rest) ->
    (match rest with
     | Stmts_nil ->
       let* t = term_ty env value in
       Ok { gen_answer = Some t; gen_error = Ty_never; gen_requires = req_empty }
     | Stmts_cons _ -> refuse "ret: statements after a return")
  | Stmts_cons (Stmt_ifElse (test, then_b, else_b), rest) ->
    let* t = term_ty env test in
    if t = Ty_bool then
      let* a = check_stmts env in_loop then_b in
      let* b = check_stmts env in_loop else_b in
      let* r = check_stmts env in_loop rest in
      let* ab = gen_merge a b in
      gen_merge ab r
    else refuse "ifElse: the test is not a bool"
  | Stmts_cons (Stmt_whileTrue body, rest) ->
    let* b = check_stmts env true body in
    let* r = check_stmts env in_loop rest in
    gen_merge b r
  | Stmts_cons (Stmt_breakLoop, rest) ->
    if in_loop then check_stmts env in_loop rest else refuse "break outside a loop"

and check_effs (env : env) : effs -> eff_ty checked = function
  | Effs_nil -> Ok (mk Ty_never Ty_never req_empty)
  | Effs_cons (head, tail) ->
    let* h = check_eff env head in
    let* t = check_effs env tail in
    (match join_answer h.eff_ty_answer t.eff_ty_answer with
     | None -> refuse "raceAll: the answers do not join"
     | Some answer ->
       Ok (mk answer (join h.eff_ty_error t.eff_ty_error) (req_union h.eff_ty_requires t.eff_ty_requires)))

and check_action (env : env) : action_term -> eff_ty checked = function
  | Action_term_fork (program, _) ->
    let* p = check_eff env program in
    Ok (mk (Ty_fiberOf (p.eff_ty_answer, p.eff_ty_error)) Ty_never p.eff_ty_requires)
  | Action_term_forkIn (program, _, scope) ->
    let* p = check_eff env program in
    let* s = term_ty env scope in
    if s = Eff_native.scope_ty then Ok (mk (Ty_fiberOf (p.eff_ty_answer, p.eff_ty_error)) Ty_never p.eff_ty_requires)
    else refuse "forkIn: not a scope"
  | Action_term_forkScoped (program, _) ->
    let* p = check_eff env program in
    Ok (mk (Ty_fiberOf (p.eff_ty_answer, p.eff_ty_error)) Ty_never
          (req_union p.eff_ty_requires (req_single Eff_native.scope_key)))
  | Action_term_runIn (target, scope) ->
    let* t = term_ty env target in
    (match fiber_ty t with
     | None -> refuse "runIn: not a fiber handle"
     | Some _ ->
       let* s = term_ty env scope in
       if s = Eff_native.scope_ty then Ok (pure Ty_unit) else refuse "runIn: not a scope")
  | Action_term_interrupt target ->
    let* t = term_ty env target in
    (match fiber_ty t with None -> refuse "interrupt: not a fiber handle" | Some _ -> Ok (pure Ty_unit))
  | Action_term_interruptScoped target ->
    let* t = term_ty env target in
    (match fiber_ty t with None -> refuse "interruptScoped: not a fiber handle" | Some _ -> Ok (pure Ty_unit))
  | Action_term_interruptAll (targets, interruptor) ->
    let* ts = term_ty env targets in
    (match ts with
     | Ty_list inner ->
       (match fiber_ty inner with
        | None -> refuse "interruptAll: not a list of fiber handles"
        | Some _ ->
          (match interruptor with
           | None -> Ok (pure Ty_unit)
           | Some who ->
             let* w = term_ty env who in
             if w = Ty_nat then Ok (pure Ty_unit) else refuse "interruptAll: the interruptor is not a nat"))
     | _ -> refuse "interruptAll: not a list")
  | Action_term_awaitAll targets ->
    let* ts = term_ty env targets in
    (match ts with
     | Ty_list inner ->
       (match fiber_ty inner with
        | None -> refuse "awaitAll: not a list of fiber handles"
        | Some (value, error) -> Ok (pure (Ty_list (Ty_exitOf (value, error)))))
     | _ -> refuse "awaitAll: not a list")
  | Action_term_awaitAllFailFast targets ->
    let* ts = term_ty env targets in
    (match ts with
     | Ty_list inner ->
       (match fiber_ty inner with
        | None -> refuse "awaitAllFailFast: not a list of fiber handles"
        | Some (value, error) -> Ok (pure (Ty_list (Ty_exitOf (value, error)))))
     | _ -> refuse "awaitAllFailFast: not a list")
  | Action_term_snapshotChildren ->
    Ok (pure (Ty_list (Ty_fiberOf (Ty_handle "unknown", Ty_handle "unknown"))))
  | Action_term_awaitNewChildren snapshot ->
    let* s = term_ty env snapshot in
    if s = Ty_list (Ty_fiberOf (Ty_handle "unknown", Ty_handle "unknown")) then Ok (pure Ty_unit)
    else refuse "awaitNewChildren: not a children snapshot"
  | Action_term_raceAll entrants -> check_effs env entrants
  | Action_term_setContext context ->
    let* c = term_ty env context in
    if c = Eff_native.context_ty then Ok (pure Ty_unit) else refuse "setContext: not a context"
  | Action_term_getContext -> Ok (pure Eff_native.context_ty)
  | Action_term_getId -> Ok (pure Ty_nat)
  | Action_term_closeScope (scope, exit) ->
    let* s = term_ty env scope in
    let* e = term_ty env exit in
    (match e with
     | Ty_exitOf _ -> if s = Eff_native.scope_ty then Ok (pure Ty_unit) else refuse "closeScope: not a scope"
     | _ -> refuse "closeScope: not an exit")

(* layerTy: structural in the layer term; a body is closed, typed at the empty environment.
   Layer.succeed provides its key and requires nothing; Layer.effect provides its key with the
   body's error and scope-free requirements; effectDiscard provides nothing; fresh keeps the
   signature; orDie clears the error. *)
and check_layer : layer_term -> layer_ty checked = function
  | Layer_term_succeed (key, value) ->
    if lit_is_value value then Ok { layer_out = req_single key; layer_error = Ty_never; layer_requires = req_empty }
    else refuse "Layer.succeed: a string is not a layer value"
  | Layer_term_effect (key, body) ->
    let* t = check_eff [] body in
    Ok { layer_out = req_single key; layer_error = t.eff_ty_error; layer_requires = body_requires t }
  | Layer_term_effectDiscard body ->
    let* t = check_eff [] body in
    Ok { layer_out = req_empty; layer_error = t.eff_ty_error; layer_requires = body_requires t }
  | Layer_term_provide (self, that) ->
    let* s = check_layer self in
    let* t = check_layer that in
    Ok (layer_provide s t)
  | Layer_term_provideMerge (self, that) ->
    let* s = check_layer self in
    let* t = check_layer that in
    Ok (layer_provide_merge s t)
  | Layer_term_merge (left, right) ->
    let* a = check_layer left in
    let* b = check_layer right in
    Ok (layer_merge a b)
  | Layer_term_fresh inner -> check_layer inner
  | Layer_term_orDie inner ->
    let* l = check_layer inner in
    Ok (layer_or_die l)
  (* the host rows slice (2026-09-08): a reference is typed by the whole program in Lean
     (`typeOfProgram` expands it to its target); structurally it is nothing, as `layerTy`
     answers. `mergeAll` merges its layers to the right; none is nothing. *)
  | Layer_term_ref _ -> refuse "LayerTerm.ref: a reference is typed by the whole program"
  | Layer_term_mergeAll layers -> check_layers layers

and check_layers : layer_terms -> layer_ty checked = function
  | Layer_terms_nil -> refuse "Layer.mergeAll: no layers"
  | Layer_terms_cons (head, Layer_terms_nil) -> check_layer head
  | Layer_terms_cons (head, tail) ->
    let* a = check_layer head in
    let* b = check_layers tail in
    Ok (layer_merge a b)

(* ---- the face ---- *)

let type_of (p : eff) : eff_ty checked = check_eff [] p
let well_typed (p : eff) : bool = Result.is_ok (type_of p)

(* The signature of a layer term (layerTy), and WellTypedLayer. *)
let layer_of (l : layer_term) : layer_ty checked = check_layer l
let well_typed_layer (l : layer_term) : bool = Result.is_ok (layer_of l)

(* The .ty golden form: the JSON of the EffTy, or "ill-typed". *)
let print_type (p : eff) : string =
  match type_of p with
  | Ok t -> Eff_json.print_eff_ty t
  | Error _ -> "ill-typed"
