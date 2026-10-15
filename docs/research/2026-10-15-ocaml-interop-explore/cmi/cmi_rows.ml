(* cmi_rows: an OCaml library's compiled interface, read as data, made into rows.

   Exploration probe (2026-10-15). Dependencies: compiler-libs.common. OCaml 5.1.1.

   The OCaml compiler writes each module's typed signature to a .cmi file; `Cmi_format.read_cmi`
   reads it back as `Types.signature`, the compiler's own data. That is to OCaml what persisted
   LCNF is to Lean: the toolchain's typed form, read rather than re-parsed.

   For each value of the module this generator gives one row (request, answer, error) or a
   located refusal. It writes two artifacts from the same classification:
   - `<mod>_host.ml`: the OCaml glue that makes the library a host of those rows (rows_core.ml);
   - `<mod>.service.ts`: the Effect service declaration a client would compile against.

   Usage: cmi_rows <path/to/m.cmi> <Module> <out-dir> *)

open Types

(* The row type language, as in transport.ml. *)
type ty =
  | Unit | Nat | Int | Str | Bool
  | List of ty | Option of ty | Prod of ty * ty | Record of (string * ty) list
  | Tagged of (string * ty option) list

(* A type with an image: how its values cross the boundary.
   `codec` names the OCaml expressions that decode and encode it, around its row type. *)
type image = { row : ty; decode : string; encode : string }

exception Refuse of string

let modname = ref ""

(* The module's own type declarations, by name, for abbreviations and abstract types. *)
let local_types : (string, type_declaration) Hashtbl.t = Hashtbl.create 16

(* The module's own values, by name, to find a string embedding of an abstract type. *)
let local_values : (string, type_expr) Hashtbl.t = Hashtbl.create 64

(* A path's spelling, with the standard library's own prefix dropped: `Stdlib.result` is `result`. *)
let pname p =
  let n = Path.name p in
  if String.length n > 7 && String.sub n 0 7 = "Stdlib." && not (String.contains (String.sub n 7 (String.length n - 7)) '.')
  then String.sub n 7 (String.length n - 7) else n

let rec show t =
  match get_desc t with
  | Tvar (Some v) -> "'" ^ v | Tvar None -> "'_"
  | Tarrow (Nolabel, a, b, _) -> Printf.sprintf "%s -> %s" (show_arg a) (show b)
  | Tarrow (Labelled l, a, b, _) -> Printf.sprintf "%s:%s -> %s" l (show_arg a) (show b)
  | Tarrow (Optional l, a, b, _) -> Printf.sprintf "?%s:%s -> %s" l (show_arg a) (show b)
  | Ttuple ts -> String.concat " * " (List.map show_arg ts)
  | Tconstr (p, [], _) -> pname p
  | Tconstr (p, [ a ], _) -> Printf.sprintf "%s %s" (show_arg a) (pname p)
  | Tconstr (p, args, _) -> Printf.sprintf "(%s) %s" (String.concat ", " (List.map show args)) (pname p)
  | Tvariant row ->
    let tags = List.map (fun (l, f) -> match row_field_repr f with
        | Rpresent (Some a) -> Printf.sprintf "`%s of %s" l (show a)
        | _ -> "`" ^ l) (row_fields row) in
    "[" ^ String.concat " | " tags ^ "]"
  | Tpoly (t, _) -> show t
  | _ -> "<other>"
and show_arg t = match get_desc t with
  | Tarrow _ | Ttuple _ -> "(" ^ show t ^ ")"
  | _ -> show t

(* The image of a type, or a refusal naming why it has none. *)
let rec image t : image =
  match get_desc t with
  | Tvar _ -> raise (Refuse "a type variable: a polymorphic value needs an instance first")
  | Tarrow _ -> raise (Refuse "a function in argument or result position: a callback needs the host's continuation")
  | Ttuple [ a; b ] ->
    let a = image a and b = image b in
    { row = Prod (a.row, b.row);
      decode = Printf.sprintf "(function `List [ x; y ] -> (%s x, %s y) | _ -> raise Exit)" a.decode b.decode;
      encode = Printf.sprintf "(fun (x, y) -> `List [ %s x; %s y ])" a.encode b.encode }
  | Ttuple _ -> raise (Refuse "a tuple of three or more: the row language has pairs")
  | Tconstr (p, args, _) ->
    (match pname p, args with
     | "string", [] -> { row = Str; decode = "(function `String s -> s | _ -> raise Exit)"; encode = "(fun s -> `String s)" }
     | "int", [] -> { row = Int; decode = "(function `Int n -> n | _ -> raise Exit)"; encode = "(fun n -> `Int n)" }
     | "bool", [] -> { row = Bool; decode = "(function `Bool b -> b | _ -> raise Exit)"; encode = "(fun b -> `Bool b)" }
     | "unit", [] -> { row = Unit; decode = "(function `Null -> () | _ -> raise Exit)"; encode = "(fun () -> `Null)" }
     | "list", [ a ] ->
       let a = image a in
       { row = List a.row;
         decode = Printf.sprintf "(function `List xs -> List.map %s xs | _ -> raise Exit)" a.decode;
         encode = Printf.sprintf "(fun xs -> `List (List.map %s xs))" a.encode }
     | "option", [ a ] ->
       let a = image a in
       { row = Option a.row;
         decode = Printf.sprintf "(function `Null -> None | v -> Some (%s v))" a.decode;
         encode = Printf.sprintf "(function None -> `Null | Some v -> %s v)" a.encode }
     | name, [] when Hashtbl.mem local_types name -> local_image name
     | name, _ -> raise (Refuse (Printf.sprintf "type %s has no image: a handle, which needs a resource row" name)))
  | Tvariant row ->
    let cases = List.map (fun (l, f) -> match row_field_repr f with
        | Rpresent (Some a) -> (l, Some (image a))
        | Rpresent None -> (l, None)
        | _ -> raise (Refuse "an open polymorphic variant: its cases are not fixed")) (row_fields row) in
    { row = Tagged (List.map (fun (l, i) -> (l, Option.map (fun i -> i.row) i)) cases);
      decode = "(fun _ -> raise Exit)";
      encode = "(function " ^ String.concat " | " (List.map (fun (l, i) -> match i with
          | Some i -> Printf.sprintf "`%s v -> `Assoc [ \"_tag\", `String %S; \"value\", %s v ]" l l i.encode
          | None -> Printf.sprintf "`%s -> `Assoc [ \"_tag\", `String %S ]" l l) cases) ^ ")" }
  | Tpoly (t, []) -> image t
  | _ -> raise (Refuse "a type form outside the row language")

(* A local type: an abbreviation is its manifest; an abstract type has an image only through an
   exact string embedding the library itself supplies (`of_string`, `to_string`). *)
and local_image name =
  let decl = Hashtbl.find local_types name in
  match decl.type_manifest, decl.type_kind with
  | Some m, _ -> image m
  | None, Type_abstract ->
    let has n shape = match Hashtbl.find_opt local_values n with Some t -> show t = shape | None -> false in
    let m = !modname in
    if has "to_string" (name ^ " -> string")
    && (has "of_string" (Printf.sprintf "string -> (%s, [`Msg of string]) result" name)) then
      { row = Str;
        decode = Printf.sprintf
            "(fun v -> match %s.of_string ((function `String s -> s | _ -> raise Exit) v) with Ok x -> x | Error _ -> raise Exit)" m;
        encode = Printf.sprintf "(fun x -> `String (%s.to_string x))" m }
    else raise (Refuse (Printf.sprintf "abstract type %s has no string embedding: a handle" name))
  | None, _ -> raise (Refuse (Printf.sprintf "type %s is a record or variant: not yet read" name))

(* A value's row: its arguments make the request, its result the answer; a `result` splits into
   the answer and error columns; an exception is the error case `Raised`. *)
type row_plan = {
  name : string; ocaml : string; request : image; answer : image; error : ty;
  error_encode : string option;  (* the encoder of a `result`'s error, when the value returns one *)
  arity : int; dropped : string list }

let raised = Tagged [ "Raised", Some Str ]

let plan name t =
  let rec args t acc dropped = match get_desc t with
    | Tarrow (Nolabel, a, b, _) -> args b (a :: acc) dropped
    | Tarrow (Optional l, _, b, _) -> args b acc (l :: dropped)
    | Tarrow (Labelled l, _, _, _) -> raise (Refuse ("the labelled argument ~" ^ l ^ ": the row language has positions"))
    | _ -> (List.rev acc, t, List.rev dropped) in
  let params, result, dropped = args t [] [] in
  let request = match params with
    | [] -> image (Btype.newgenty (Tconstr (Predef.path_unit, [], ref Mnil)))
    | [ a ] -> image a
    | [ a; b ] -> image (Btype.newgenty (Ttuple [ a; b ]))
    | _ -> raise (Refuse "three or more arguments: the row language has pairs") in
  let answer, error, error_encode = match get_desc result with
    | Tconstr (p, [ ok; err ], _) when pname p = "result" ->
      let e = image err in
      (match e.row with
       | Tagged cs -> (image ok, Tagged (cs @ [ "Raised", Some Str ]), Some e.encode)
       | _ -> raise (Refuse "a result whose error is not a tagged sum"))
    | _ -> (image result, raised, None) in
  { name; ocaml = show t; request; answer; error; error_encode; arity = List.length params; dropped }

let is_ident name = name <> "" && (match name.[0] with 'a' .. 'z' | '_' -> true | _ -> false)

(* ------------------------------------------------------------------ the two artifacts *)

let rec ocaml_ty = function
  | Unit -> "Unit" | Nat -> "Nat" | Int -> "Int" | Str -> "Str" | Bool -> "Bool"
  | List t -> "List (" ^ ocaml_ty t ^ ")" | Option t -> "Option (" ^ ocaml_ty t ^ ")"
  | Prod (a, b) -> "Prod (" ^ ocaml_ty a ^ ", " ^ ocaml_ty b ^ ")"
  | Record fs -> "Record [" ^ String.concat "; " (List.map (fun (n, t) -> Printf.sprintf "%S, %s" n (ocaml_ty t)) fs) ^ "]"
  | Tagged cs -> "Tagged [" ^ String.concat "; " (List.map (fun (c, t) -> Printf.sprintf "%S, %s" c
      (match t with Some t -> "Some (" ^ ocaml_ty t ^ ")" | None -> "None")) cs) ^ "]"

let host_ml plans =
  let m = !modname in
  let b = Buffer.create 4096 in
  let p fmt = Printf.bprintf b fmt in
  p "(* Generated by cmi_rows from %s's compiled interface. Do not edit. *)\nopen Rows_core\n\n" m;
  p "let table = [\n";
  List.iter (fun r -> p "  { spelling = %S; request = %s; answer = %s; error = %s };\n"
      (m ^ "." ^ r.name) (ocaml_ty r.request.row) (ocaml_ty r.answer.row) (ocaml_ty r.error)) plans;
  p "]\n\nlet raised e = Failure (`Assoc [ \"_tag\", `String \"Raised\"; \"value\", `String (Printexc.to_string e) ])\n\n";
  p "let host : host = fun spelling request ->\n  match spelling with\n";
  List.iter (fun r ->
      let call = match r.arity with
        | 0 -> Printf.sprintf "(fun () -> %s.%s)" m r.name
        | 1 -> Printf.sprintf "%s.%s" m r.name
        | _ -> Printf.sprintf "(fun (a, b) -> %s.%s a b)" m r.name in
      let finish = match r.error_encode with
        | Some enc_e -> Printf.sprintf "(match %s x with Ok a -> Success (%s a) | Error e -> Failure (%s e))"
                          call r.answer.encode enc_e
        | None -> Printf.sprintf "Success (%s (%s x))" r.answer.encode call in
      p "  | %S -> (match %s request with\n" (m ^ "." ^ r.name) r.request.decode;
      p "      | exception Exit -> None\n      | x -> (try Some (%s) with e -> Some (raised e)))\n" finish) plans;
  p "  | _ -> None\n";
  Buffer.contents b

let rec ts_ty = function
  | Unit -> "null" | Nat | Int -> "number" | Str -> "string" | Bool -> "boolean"
  | List t -> "ReadonlyArray<" ^ ts_ty t ^ ">" | Option t -> ts_ty t ^ " | null"
  | Prod (a, b) -> "readonly [" ^ ts_ty a ^ ", " ^ ts_ty b ^ "]"
  | Record fs -> "{ " ^ String.concat "; " (List.map (fun (n, t) -> Printf.sprintf "readonly %s: %s" n (ts_ty t)) fs) ^ " }"
  | Tagged cs -> String.concat " | " (List.map (fun (c, t) -> match t with
      | Some t -> Printf.sprintf "{ readonly _tag: %S; readonly value: %s }" c (ts_ty t)
      | None -> Printf.sprintf "{ readonly _tag: %S }" c) cs)

let service_ts plans =
  let m = !modname in
  let b = Buffer.create 4096 in
  let p fmt = Printf.bprintf b fmt in
  p "// Generated by cmi_rows from %s's compiled interface. Do not edit.\n" m;
  p "// The service an Effect client compiles against; an OCaml host implements it (%s_host.ml).\n\n"
    (String.lowercase_ascii m);
  p "import { Context, Effect } from \"effect\"\n\n";
  p "export class %s extends Context.Service<%s, {\n" m m;
  List.iter (fun r ->
      let arg = match r.arity with 0 -> "" | _ -> "request: " ^ ts_ty r.request.row in
      p "  /** `%s` */\n  readonly %s: (%s) => Effect.Effect<%s, %s>\n" r.ocaml r.name arg (ts_ty r.answer.row) (ts_ty r.error))
    plans;
  p "}>()(\"ocaml/%s\") {}\n" m;
  Buffer.contents b

let () =
  let cmi_path = Sys.argv.(1) and out = Sys.argv.(3) in
  modname := Sys.argv.(2);
  let cmi = Cmi_format.read_cmi cmi_path in
  List.iter (function
      | Sig_type (id, decl, _, _) -> Hashtbl.replace local_types (Ident.name id) decl
      | Sig_value (id, vd, _) -> Hashtbl.replace local_values (Ident.name id) vd.val_type
      | _ -> ()) cmi.cmi_sign;
  let rows = ref [] and refused = ref [] and skipped = ref [] in
  List.iter (function
      | Sig_value (id, vd, _) ->
        let name = Ident.name id in
        if not (is_ident name) then skipped := (name, "an operator: its named form is a row") :: !skipped
        else (match plan name vd.val_type with
            | r -> rows := r :: !rows
            | exception Refuse why -> refused := (name, show vd.val_type, why) :: !refused)
      | Sig_module (id, _, _, _, _) -> skipped := (Ident.name id, "a submodule: read on its own") :: !skipped
      | _ -> ()) cmi.cmi_sign;
  let rows = List.rev !rows and refused = List.rev !refused and skipped = List.rev !skipped in
  Printf.printf "%s (%s): %d values as rows, %d refused, %d skipped\n\n" !modname cmi_path
    (List.length rows) (List.length refused) (List.length skipped);
  List.iter (fun r ->
      Printf.printf "ROW     %-16s %-42s  %s -> %s / %s%s\n" r.name r.ocaml (ocaml_ty r.request.row)
        (ocaml_ty r.answer.row) (ocaml_ty r.error)
        (if r.dropped = [] then "" else "   (optional ?" ^ String.concat " ?" r.dropped ^ " left at its default)")) rows;
  List.iter (fun (n, t, why) -> Printf.printf "REFUSED %-16s %-42s  %s\n" n t why) refused;
  List.iter (fun (n, why) -> Printf.printf "SKIPPED %-16s %s\n" n why) skipped;
  let write file text = let oc = open_out (Filename.concat out file) in output_string oc text; close_out oc in
  write (String.lowercase_ascii !modname ^ "_host.ml") (host_ml rows);
  write (!modname ^ ".service.ts") (service_ts rows)
