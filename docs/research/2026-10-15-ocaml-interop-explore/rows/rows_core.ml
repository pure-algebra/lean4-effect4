(* Rows_core: the row language, membership, hosts and the guard. No transport: the HTTP half
   (transport.ml) and the in-process JavaScript half (../jsoo/fpath_js.ml) both use it.

   From transport.ml's original header: one HTTP transport for every row table, written once,
   parameterized by the table.

   Exploration probe (2026-10-15). Dependencies: eio_main, yojson. OCaml 5.1.1, Eio 1.2.

   A host answers a row's call: the row's spelling and its request in, a success or a failure
   out, or no answer (Effect4's `Run.Reactor`, src/Effect4/Run/Basic.lean). The transport has two
   halves, both generic in the table:
   - `serve table host`: an HTTP edge that admits each request at the row's request type, asks
     the host, and admits the host's answer at the row's answer or error type (`hostGuard`);
   - `remote table url`: a host that forwards each call over HTTP.
   The law the probe checks, on one script: `remote table url` against `serve table host` answers
   as `host` does. The table is also served as data (GET /rows), so a client can build its side
   of the interface at run time. *)

(* ------------------------------------------------------------------ types and rows, as data *)

type ty =
  | Unit | Nat | Int | Str | Bool
  | List of ty | Option of ty | Prod of ty * ty | Record of (string * ty) list
  | Tagged of (string * ty option) list  (* a closed sum: `{_tag, value?}`, as Effect's tagged unions *)

type row = { spelling : string; request : ty; answer : ty; error : ty }

let rec ty_json = function
  | Unit -> `String "unit" | Nat -> `String "nat" | Int -> `String "int" | Str -> `String "string"
  | Bool -> `String "bool"
  | List t -> `Assoc [ "list", ty_json t ] | Option t -> `Assoc [ "option", ty_json t ]
  | Prod (a, b) -> `Assoc [ "prod", `List [ ty_json a; ty_json b ] ]
  | Record fs -> `Assoc [ "record", `List (List.map (fun (n, t) -> `List [ `String n; ty_json t ]) fs) ]
  | Tagged cs ->
    `Assoc [ "tagged", `List (List.map (fun (c, t) ->
        `List (`String c :: (match t with Some t -> [ ty_json t ] | None -> []))) cs) ]

let row_json r =
  `Assoc [ "spelling", `String r.spelling; "request", ty_json r.request;
           "answer", ty_json r.answer; "error", ty_json r.error ]

(* Membership of a JSON value at a type, as a located refusal: the path and the reason. The JSON
   image: unit is null, a pair is a two-element array, an option is null or the value. *)
let rec refusal path ty (v : Yojson.Safe.t) =
  let here what = Some (Printf.sprintf "%s: %s" path what) in
  match ty, v with
  | Unit, `Null -> None
  | Nat, `Int n when n >= 0 -> None
  | Nat, `Int _ -> here "a negative natural"
  | Int, `Int _ -> None
  | Str, `String _ | Bool, `Bool _ -> None
  | List t, `List xs ->
    List.find_map Fun.id (List.mapi (fun i x -> refusal (Printf.sprintf "%s[%d]" path i) t x) xs)
  | Option _, `Null -> None
  | Option t, v -> refusal path t v
  | Prod (a, b), `List [ x; y ] ->
    (match refusal (path ^ "[0]") a x with None -> refusal (path ^ "[1]") b y | r -> r)
  | Record fs, `Assoc kvs ->
    if List.length kvs <> List.length fs then here "the wrong fields"
    else List.find_map (fun (n, t) -> match List.assoc_opt n kvs with
        | Some x -> refusal (path ^ "." ^ n) t x
        | None -> here ("no field " ^ n)) fs
  | Tagged cs, `Assoc kvs ->
    (match List.assoc_opt "_tag" kvs with
     | Some (`String c) ->
       (match List.assoc_opt c cs, List.assoc_opt "value" kvs with
        | Some None, None -> None
        | Some (Some t), Some x -> refusal (path ^ ".value") t x
        | Some _, _ -> here ("the payload of " ^ c)
        | None, _ -> here ("no case " ^ c))
     | _ -> here "no _tag")
  | _ -> here "not of its type"

(* --------------------------------------------------------------------------------- hosts *)

type completion = Success of Yojson.Safe.t | Failure of Yojson.Safe.t

(* A host: a row's spelling and request in; a completion out, or no answer. *)
type host = string -> Yojson.Safe.t -> completion option

(* The guard, generic in the table: an answer outside the row's types is refused (no answer). *)
let guard table (host : host) : host = fun spelling request ->
  match List.find_opt (fun r -> r.spelling = spelling) table with
  | None -> None
  | Some row ->
    match host spelling request with
    | Some (Success v) when refusal "$" row.answer v = None -> Some (Success v)
    | Some (Failure e) when refusal "$" row.error e = None -> Some (Failure e)
    | _ -> None

let completion_json = function
  | Success v -> `Assoc [ "_tag", `String "Success"; "value", v ]
  | Failure e -> `Assoc [ "_tag", `String "Failure"; "error", e ]

