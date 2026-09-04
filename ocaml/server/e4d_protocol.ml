(* The daemon's wire: the request and response carriers, and their codec.

   Everything the protocol says about a *message* is here; everything it says about a
   *program* is in `effect4_daemon.ml`. The two are separate so that the codec can be
   replaced without touching a handler.

   ## The swap to derived codecs (`docs/research/2026-09-04-ocaml-packages-plan.md`)

   This module is the seam. The plan's §2 wants `sexp`/`bin_prot`/`yojson` derived from the
   carriers rather than written; §4 wants everything representable in `OCaml5.Ml` and admits
   ppx-generated code only as the plain first-order OCaml it expands to. The swap is:

     `E4d_json.t`     becomes `Yojson.Safe.t`. The accessor API of `e4d_json.ml`
                      (`member`, `str`, `int_`, `bool_`, `strings`, `to_list`, `of_string`,
                      `to_string`) is a subset of `Yojson.Safe` + `Yojson.Safe.Util` with the
                      same names and meanings, so the change is a module alias plus the
                      constructor spellings (`Str` -> `` `String ``, `Obj` -> `` `Assoc ``,
                      `List` -> `` `List ``, `Int` -> `` `Int ``, `Null` -> `` `Null ``).
     `request`        gains `[@@deriving sexp, yojson]`, and `request_of_json` below becomes
                      the generated `request_of_yojson` -- except for `body`, which stays an
                      open JSON object until every request has its own variant.
     `response`       gains `[@@deriving sexp, bin_io, yojson]`; `json_of_response` becomes
                      `yojson_of_response`, and `payload` becomes a variant per request so
                      that the schema is derived rather than an association list.
     the schema       `README.md` §5 is then generated from the types instead of written.

   Until then nothing here is magic in the plan's §4 sense: no `Obj`, no `Marshal`, no
   polymorphic comparison on an abstract type, and every function is first-order over a
   first-order carrier. *)

open E4d_json

type failure = { kind : string; message : string }

exception Bad_request of failure

let bad kind message = raise (Bad_request { kind; message })

let protocol = "effect4d/1"

(* ------------------------------------------------------------------------- requests *)

(* `body` is the request object itself. Each handler reads the fields it needs out of it;
   when every request has its own variant (the swap above), `body` goes and the variant
   carries the fields. *)
type request = { id : E4d_json.t; what : string; body : E4d_json.t }

let request_of_json (body : E4d_json.t) : request =
  { id = E4d_json.member "id" body; what = E4d_json.str "request" body; body }

let request_of_line (line : string) : (request, failure) result =
  match E4d_json.of_string line with
  | body -> Ok (request_of_json body)
  | exception E4d_json.Parse_error message -> Error { kind = "bad-json"; message }

(* ------------------------------------------------------------------------ responses *)

type response = {
  ok : bool;
  what : string;                            (* the request name, echoed *)
  rid : E4d_json.t;                         (* the request's `id`, echoed *)
  host : string;
  header : string list;                     (* the golden header block, as TSV lines *)
  header_fields : E4d_json.t;               (* the same, as an object *)
  payload : (string * E4d_json.t) list;     (* the request's own answer *)
  error : failure option;
}

let ok_response ~what ~rid ~host ~header ~header_fields ~payload =
  { ok = true; what; rid; host; header; header_fields; payload; error = None }

let error_response ~what ~rid ~host failure =
  { ok = false; what; rid; host; header = []; header_fields = E4d_json.Null; payload = [];
    error = Some failure }

let json_of_response (r : response) : E4d_json.t =
  E4d_json.Obj
    ([ ("protocol", Str protocol);
       ("ok", Bool r.ok);
       ("request", Str r.what);
       ("id", r.rid);
       ("host", Str r.host) ]
    @ (if r.ok then [ ("header", E4d_json.of_strings r.header);
                      ("header_fields_placeholder", Null) ]
       else [])
    @ (match r.error with
       | Some f -> [ ("error", Obj [ ("kind", Str f.kind); ("message", Str f.message) ]) ]
       | None -> [])
    @ r.payload)

(* The response object with `headerFields` in its place. `json_of_response` above builds the
   field order; this substitutes the object, so the two never disagree about where the header
   sits. *)
let json_of_response (r : response) : E4d_json.t =
  match json_of_response r with
  | E4d_json.Obj fields ->
    E4d_json.Obj
      (List.map
         (fun (key, value) ->
           if key = "header_fields_placeholder" then ("headerFields", r.header_fields)
           else (key, value))
         fields)
  | other -> other

let line_of_response (r : response) : string = E4d_json.to_string (json_of_response r)
