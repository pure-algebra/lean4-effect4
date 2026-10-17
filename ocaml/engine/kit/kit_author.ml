(* Kit_author — see kit_author.mli for what it is and the behaviours it holds itself to. *)

open Eff_types
module G = Effect4_gen.Api_gen

type refusal = G.effect4_program_authoring_refusal
type term = G.env -> int list -> (Eff_types.term, refusal) result
type t = G.env -> int list -> (native_op eff, refusal) result

(* A literal reads no scope, so LCNF lowers it at its reduced arity (`_redArg`); the scope is
   taken here. *)
let nat n : term = fun _ _ -> G.program_authoring_nat n
let str s : term = fun _ _ -> G.program_authoring_str s
let bool b : term = fun _ _ -> G.program_authoring_bool b
let unit : term = G.program_authoring_unit
let atom name args : term = G.program_authoring_app name args
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

let succeed v : t = G.program_authoring_succeed v
let fail e : t = G.program_authoring_fail e
let sync v : t = G.program_authoring_sync v
let suspend b : t = G.program_authoring_suspend b
let ( let* ) (a : t) (k : term -> t) : t = G.program_authoring_bind_with a k
let ( >> ) (a : t) (b : t) : t = G.program_authoring_and_then a b
let perform name request : t = G.program_authoring_row_call_named name request
let cell init : t = G.program_authoring_ref_make init
let get c : t = G.program_authoring_ref_get c
let set c v : t = G.program_authoring_ref_set c v

(* `ifElse` keeps its erased type argument `Op` as a parameter; any value stands for it. *)
let if_ c ~then_ ~else_ : t = G.program_authoring_if_else () c then_ else_
let on_option o ~none ~some : t = G.program_authoring_select_option_with o none some
let loop ~init ~test ~step ~result body : t = G.program_authoring_loop_with init test body step result
let catch body handler : t = G.program_authoring_catch_with body handler
let on_exit body finalizer : t = G.program_authoring_on_exit_with body finalizer
let exit_of body : t = G.program_authoring_exit_ body

type def = native_op G.def_src

(* One parameter: Lean reads its request through `requestParts 1`, a list of one term. *)
let def name ~request ~answer ?(error = Ty_never) (body : term -> t) : def =
  { G.name; params = [ ("request", request) ]; answer; error; requires = [];
    body = (function r :: _ -> body r | [] -> body unit);
    role = DefRole_plain; program_params = [] }

let call name request : t = G.program_authoring_def_invoke name [ request ]

let row name ~request ~answer ?(error = Ty_never) ?(cite = "") () : row =
  G.program_authoring_row_host name request answer error cite

let refusal_text (r : refusal) =
  let at = match r.path with [] -> "the root" | path -> "node " ^ String.concat "." (List.map string_of_int path) in
  let why =
    match r.reason with
    | G.Effect4_program_authoring_reason_unbound n -> Printf.sprintf "no binder names %S" n
    | G.Effect4_program_authoring_reason_unboundLayer n -> Printf.sprintf "no layer is named %S" n
    | G.Effect4_program_authoring_reason_duplicateLayer n -> Printf.sprintf "two layers are named %S" n
    | G.Effect4_program_authoring_reason_placement n -> Printf.sprintf "the layer %S could not be placed" n
    | G.Effect4_program_authoring_reason_unboundRow n -> Printf.sprintf "no row is named %S" n
    | G.Effect4_program_authoring_reason_reservedName n -> Printf.sprintf "%S is a name only the surface writes" n
    | G.Effect4_program_authoring_reason_duplicateRow n -> Printf.sprintf "two rows are named %S" n
    | G.Effect4_program_authoring_reason_unboundDef n -> Printf.sprintf "no definition is named %S" n
    | G.Effect4_program_authoring_reason_duplicateDef n -> Printf.sprintf "two definitions are named %S" n
    | G.Effect4_program_authoring_reason_unboundParam n -> Printf.sprintf "no program parameter is named %S" n
    | G.Effect4_program_authoring_reason_duplicateParam n -> Printf.sprintf "two program parameters are named %S" n
  in
  Printf.sprintf "%s, at %s" why at

let build ?(app = Kit.app ()) ?(defs = []) (main : t) : (Kit.program, refusal) result =
  G.program_authoring_elaborate_at app.G.rows defs main

let build_checked ?(app = Kit.app ()) ?defs main =
  match build ~app ?defs main with
  | Error r -> Error (`Name r)
  | Ok e -> (match Kit.check app e with Ok t -> Ok (e, t) | Error r -> Error (`Type r))
