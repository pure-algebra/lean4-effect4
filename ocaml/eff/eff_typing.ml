(* Eff_typing — the typing judgement of src/Effect4/Program/Typing.lean over the untyped
   carrier (hand-written).

   What it is: `typeOf` at the native signature (`nativeSignature`: the rows of Eff_native,
   the atom table, the scope key), rule for rule. `Ty.join` (canonical unions, Eff.lean),
   `EffTy.joinAnswer`, `GenTy.merge` and the requirement row (`Row ServiceKey`, Data/Row.lean,
   carried as the strictly ascending key list) are restated here.
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

let join (a : ty) (b : ty) : ty =
  of_members (List.fold_left (fun acc t -> insert_member t acc) [] (members a @ members b))

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

(* ---- EffTy, GenTy ---- *)

let mk answer error requires = { eff_ty_answer = answer; eff_ty_error = error; eff_ty_requires = requires }
let pure (answer : ty) : eff_ty = mk answer Ty_never req_empty

let join_answer (a : ty) (b : ty) : ty option =
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

let rec cause_ty (env : env) : cause_term -> ty checked = function
  | Cause_term_fail e -> term_ty env e
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
    Ok (mk Ty_never t req_empty)
  | Eff_failCause c ->
    let* e = cause_ty env c in
    Ok (mk Ty_never e req_empty)
  | Eff_yieldError e ->
    let* t = term_ty env e in
    Ok (mk Ty_never t req_empty)
  | Eff_sync t ->
    let* t = term_ty env t in
    Ok (pure t)
  | Eff_suspend body -> check_eff env body
  | Eff_perform (op, request) ->
    let row = Eff_native.row_of op in
    let* r = term_ty env request in
    if r = row.row_request then Ok (row_answer row)
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
  | Eff_callback (register, request) ->
    let row = Eff_native.row_of register in
    let* r = term_ty env request in
    if row.row_kind = Row_kind_async && r = row.row_request then Ok (row_answer row)
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
  | Eff_scoped body -> check_eff env body
  | Eff_acquireRelease (acquire, release) ->
    let* a = check_eff env acquire in
    let* r = check_eff (env @ [ a.eff_ty_answer; Ty_exitOf (a.eff_ty_answer, a.eff_ty_error) ]) release in
    Ok (mk a.eff_ty_answer a.eff_ty_error
          (req_union (req_union a.eff_ty_requires r.eff_ty_requires) (req_single Eff_native.scope_key)))
  | Eff_choose (_, left, right) ->
    let* l = check_eff env left in
    let* r = check_eff env right in
    (match join_answer l.eff_ty_answer r.eff_ty_answer with
     | None -> refuse "choose: the answers do not join"
     | Some answer ->
       Ok (mk answer (join l.eff_ty_error r.eff_ty_error) (req_union l.eff_ty_requires r.eff_ty_requires)))

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

(* ---- the face ---- *)

let type_of (p : eff) : eff_ty checked = check_eff [] p
let well_typed (p : eff) : bool = Result.is_ok (type_of p)

(* The .ty golden form: the JSON of the EffTy, or "ill-typed". *)
let print_type (p : eff) : string =
  match type_of p with
  | Ok t -> Eff_json.print_eff_ty t
  | Error _ -> "ill-typed"
