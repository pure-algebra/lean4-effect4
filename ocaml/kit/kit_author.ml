(* Kit_author — see kit_author.mli for what it is and the behaviours it holds itself to. *)

open Eff_types

type term = Eff_types.term

let rec terms = function [] -> Terms_nil | t :: ts -> Terms_cons (t, terms ts)
let nat n = Term_lit (Lit_nat n)
let str s = Term_lit (Lit_str s)
let bool b = Term_lit (Lit_bool b)
let unit = Term_lit Lit_unit
let atom name args = Term_app (name, terms args)
let ( + ) a b = atom "add" [ a; b ]
let ( - ) a b = atom "sub" [ a; b ]
let ( * ) a b = atom "mul" [ a; b ]
let ( < ) a b = atom "lt" [ a; b ]
let ( = ) a b = atom "eq" [ a; b ]
let ( && ) a b = atom "and" [ a; b ]
let ( || ) a b = atom "or" [ a; b ]
let not a = atom "not" [ a ]
let pair a b = atom "pair" [ a; b ]
let some a = atom "some" [ a ]
let none = atom "none" []
let nil = atom "nil" []
let cons a b = atom "cons" [ a; b ]
let length a = atom "length" [ a ]
let append a b = atom "append" [ a; b ]

(* Where a builder is placed: the depth of its environment, the row names and the definition
   names. A name that does not resolve raises [Unresolved], which [build] turns into a refusal. *)
type refusal = Unbound_row of string | Unbound_def of string

exception Unresolved of refusal

type scope = { depth : int; rows : string list; defs : string list }
type t = scope -> native_op eff

let index_of what name names =
  let rec go i = function
    | [] -> raise (Unresolved (what name))
    | n :: rest -> if String.equal n name then i else go (Stdlib.( + ) i 1) rest
  in
  go 0 names

let deeper sc n = { sc with depth = Stdlib.( + ) sc.depth n }
let var sc = Term_var sc.depth
let succeed v : t = fun _ -> Eff_succeed v
let fail e : t = fun _ -> Eff_fail e
let sync v : t = fun _ -> Eff_sync v
let suspend b : t = fun sc -> Eff_suspend (b sc)
let ( let* ) (a : t) (k : term -> t) : t = fun sc -> Eff_bind (a sc, (k (var sc)) (deeper sc 1))
let ( >> ) (a : t) (b : t) : t = fun sc -> Eff_bind (a sc, b (deeper sc 1))

let perform name request : t =
 fun sc -> Eff_perform (NativeOp_external (index_of (fun n -> Unbound_row n) name sc.rows), request)

let cell init : t = fun _ -> Eff_perform (NativeOp_refMake, init)
let get c : t = fun _ -> Eff_perform (NativeOp_refGet, c)
let set c v : t = fun _ -> Eff_perform (NativeOp_refSet, pair c v)
let if_ c ~then_ ~else_ : t = fun sc -> Eff_select (c, Decision_bool, then_ sc, else_ sc)

(* `Decision.option`: arm 0 is `none` and binds nothing, arm 1 is `some` and binds its value *)
let on_option o ~none ~some : t =
 fun sc -> Eff_select (o, Decision_option, none sc, (some (var sc)) (deeper sc 1))

(* `iterate`: the test, the result and the body see the cursor at `depth`; the step sees the cursor
   and the body's answer at `depth + 1` *)
let loop ~init ~test ~step ~result body : t =
 fun sc ->
  let c = var sc and a = Term_var (Stdlib.( + ) sc.depth 1) in
  Eff_iterate (None, init, test c, step c a, result c, (body c) (deeper sc 1))

let catch body handler : t = fun sc -> Eff_catchCause (body sc, (handler (var sc)) (deeper sc 1))
let on_exit body finalizer : t = fun sc -> Eff_onExit (body sc, (finalizer (var sc)) (deeper sc 1))
let exit_of body : t = fun sc -> Eff_exit (body sc)

type def = { name : string; decl : def_decl; body : term -> t }

let def name ~request ~answer ?(error = Ty_never) body =
  { name;
    decl = { name; request; answer; error; requires = []; role = DefRole_plain; params = [] };
    body }

let call name request : t =
 fun sc -> Eff_perform (NativeOp_call (index_of (fun n -> Unbound_def n) name sc.defs), request)

let rec effs = function [] -> Effs_nil | e :: es -> Effs_cons (e, effs es)

(* A body runs at its request alone: depth 1, the request at level 0. *)
let program (ds : def list) (main : t) : t =
 fun sc ->
  let sc = { sc with defs = List.map (fun d -> d.name) ds } in
  let body d = (d.body (Term_var 0)) { sc with depth = 1 } in
  Eff_defs (List.map (fun d -> d.decl) ds, effs (List.map body ds), main sc, LayerTerms_nil)

(* `Row.host` (src/Effect4/Program/Authoring.lean): `kind := .async` and `registration :=
   .external` are what the machine's reply admission demands of a row the host answers. *)
let row name ~request ~answer ?(error = Ty_never) ?(cite = "") () : row =
  { name; spelling = name; shape = RowShape_call; trailing = []; kind = RowKind_async;
    request; answer; error; requires = []; cite; type_args = [];
    registration = Registration_external }

let refusal_text = function
  | Unbound_row n -> Printf.sprintf "no row is named %S" n
  | Unbound_def n -> Printf.sprintf "no definition is named %S" n

let build ?(app = Kit.app ()) (p : t) =
  let rows = List.map (fun (r : row) -> r.name) app.Kit_gen.rows in
  match p { depth = 0; rows; defs = [] } with
  | e -> Ok e
  | exception Unresolved r -> Error r

let build_checked ?(app = Kit.app ()) p =
  match build ~app p with
  | Error r -> Error (`Name r)
  | Ok e -> (match Kit.check app e with Ok t -> Ok (e, t) | Error r -> Error (`Type r))
