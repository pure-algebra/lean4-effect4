(* Typed_lint: rules 7 and 6 of ocaml/STANDARDS.md, read off OCaml's typed tree.
   Depends on compiler-libs.common. The behaviours T1-T4 are stated in typed_lint.mli and
   tested by the fixtures of test/. *)

type rule = Compare | Raise

type finding = { rule : rule; loc : Location.t; operator : string; at : string }

type refusal =
  | Unreadable of string * string
  | No_source of string * string
  | Environment of string * string

let message = function
  | Unreadable (cmt, why) -> Printf.sprintf "%s: unreadable typed tree: %s" cmt why
  | No_source (source, why) -> Printf.sprintf "%s: unreadable source: %s" source why
  | Environment (where, missing) ->
      Printf.sprintf "%s: the environment cannot be rebuilt: %s is not on the load path" where
        missing

let[@inline never] [@local never] [@specialise never] refuse why = Error why

(* Where the compared type sits: the first argument's own type, or the key type of the generic
   Hashtbl.t that is the first argument. *)
type position = Value | Table_key

let watched =
  List.map (fun name -> name, Value)
    [ "Stdlib.="; "Stdlib.<>"; "Stdlib.<"; "Stdlib.>"; "Stdlib.<="; "Stdlib.>=";
      "Stdlib.compare"; "Stdlib.min"; "Stdlib.max"; "Stdlib.Hashtbl.hash";
      "Stdlib.List.mem"; "Stdlib.List.assoc"; "Stdlib.List.assoc_opt"; "Stdlib.List.mem_assoc";
      "Stdlib.List.remove_assoc"; "Stdlib.ListLabels.mem"; "Stdlib.ListLabels.assoc";
      "Stdlib.ListLabels.assoc_opt"; "Stdlib.ListLabels.mem_assoc";
      "Stdlib.ListLabels.remove_assoc"; "Stdlib.Array.mem"; "Stdlib.ArrayLabels.mem" ]
  @ List.map (fun name -> name, Table_key)
      [ "Stdlib.Hashtbl.add"; "Stdlib.Hashtbl.replace"; "Stdlib.Hashtbl.find";
        "Stdlib.Hashtbl.find_opt"; "Stdlib.Hashtbl.find_all"; "Stdlib.Hashtbl.mem";
        "Stdlib.Hashtbl.remove" ]

let raisers = [ "Stdlib.raise"; "Stdlib.raise_notrace"; "Stdlib.failwith"; "Stdlib.invalid_arg" ]

(* The typer may name a standard module by its unit, Stdlib__List, rather than by the alias. *)
let operator_name path =
  let name = Path.name path in
  let unit = "Stdlib__" in
  if String.starts_with ~prefix:unit name then
    "Stdlib." ^ String.sub name (String.length unit) (String.length name - String.length unit)
  else name

let position name =
  List.find_map (fun (watched, at) -> if String.equal watched name then Some at else None) watched

(* Polymorphic comparison serves exactly these, after abbreviations are expanded. *)
let base = [ Predef.path_int; Predef.path_char; Predef.path_bool; Predef.path_string ]

(* The one escape of the traversal: the environment of a use cannot be rebuilt. It never
   leaves [check]. *)
exception Lost of Location.t * string

let env_at_exn (e : Typedtree.expression) =
  try Envaux.env_of_only_summary e.exp_env
  with Envaux.Error (Envaux.Module_not_found path) -> raise (Lost (e.exp_loc, Path.name path))

let compared_type position ty =
  match Types.get_desc ty, position with
  | Types.Tarrow (_, argument, _, _), Value -> Some argument
  | Types.Tarrow (_, table, _, _), Table_key -> (
      match Types.get_desc table with
      | Types.Tconstr (_, key :: _, _) -> Some key
      | _ -> None)
  | _ -> None

(* A constructor the environment does not declare would stop expansion silently and pass for
   a nominal type, so it refuses instead. *)
let comparable_exn env loc ty =
  let ty = Ctype.expand_head env ty in
  match Types.get_desc ty with
  | Types.Tconstr (path, arguments, _) -> (
      match Env.find_type path env with
      | exception Not_found -> raise (Lost (loc, Path.name path))
      | _ -> (match arguments with [] -> List.exists (Path.same path) base | _ :: _ -> false))
  | _ -> false

let type_text env ty =
  let buffer = Buffer.create 64 in
  let formatter = Format.formatter_of_buffer buffer in
  Format.pp_set_margin formatter 10_000;
  Printtyp.wrap_printing_env ~error:false env (fun () -> Printtyp.type_expr formatter ty);
  Format.pp_print_flush formatter ();
  Buffer.contents buffer

let has_exception_case (case : Typedtree.computation Typedtree.case) =
  match Typedtree.split_pattern case.c_lhs with _, Some _ -> true | _, None -> false

let structure_findings_exn ~raises structure =
  let found = ref [] in
  let names = ref [] in
  let guards = ref 0 in
  (* The constructor a raise applies, when its argument is one; set by the application just
     before the iterator reaches the raise itself. *)
  let raised = ref None in
  let ident (e : Typedtree.expression) path =
    let operator = operator_name path in
    (match position operator with
     | None -> ()
     | Some at -> (
         match compared_type at e.exp_type with
         | None -> ()
         | Some ty ->
             let env = env_at_exn e in
             if not (comparable_exn env e.exp_loc ty) then
               found := { rule = Compare; loc = e.exp_loc; operator; at = type_text env ty }
                        :: !found));
    let constructor = !raised in
    raised := None;
    if raises && List.exists (String.equal operator) raisers && !guards = 0
       && not (List.exists (String.ends_with ~suffix:"_exn") !names)
    then
      let binding = match List.rev !names with outer :: _ -> outer | [] -> "the top level" in
      let operator = match constructor with Some name -> operator ^ " " ^ name | None -> operator in
      found := { rule = Raise; loc = e.exp_loc; operator; at = binding } :: !found
  in
  let guarded sub e = incr guards; sub.Tast_iterator.expr sub e; decr guards in
  let expr sub (e : Typedtree.expression) =
    (match e.exp_desc with
     | Typedtree.Texp_ident (path, _, _) -> ident e path
     | Typedtree.Texp_apply
         ( { exp_desc = Typedtree.Texp_ident _; _ },
           (_, Some { exp_desc = Typedtree.Texp_construct (_, constructor, _); _ }) :: _ ) ->
         raised := Some constructor.cstr_name
     | _ -> ());
    match e.exp_desc with
    | Typedtree.Texp_try (body, cases) ->
        guarded sub body;
        List.iter (sub.Tast_iterator.case sub) cases
    | Typedtree.Texp_match (scrutinee, cases, _) when List.exists has_exception_case cases ->
        guarded sub scrutinee;
        List.iter (sub.Tast_iterator.case sub) cases
    | _ -> Tast_iterator.default_iterator.expr sub e
  in
  let value_binding sub (binding : Typedtree.value_binding) =
    let name = match binding.vb_pat.pat_desc with
      | Typedtree.Tpat_var (_, name) | Typedtree.Tpat_alias (_, _, name) -> Some name.txt
      | _ -> None in
    let outer = !names in
    Option.iter (fun name -> names := name :: outer) name;
    Tast_iterator.default_iterator.value_binding sub binding;
    names := outer
  in
  let iterator = { Tast_iterator.default_iterator with expr; value_binding } in
  iterator.structure iterator structure;
  List.rev !found

(* A system error's text already opens with the path. *)
let reason path why =
  let prefix = path ^ ": " in
  if String.starts_with ~prefix why then
    String.sub why (String.length prefix) (String.length why - String.length prefix)
  else why

let generated source =
  match In_channel.with_open_text source In_channel.input_line with
  | Some line -> Ok (String.starts_with ~prefix:"(* GENERATED" line)
  | None -> Ok false
  | exception Sys_error why -> refuse (No_source (source, reason source why))

let read cmt =
  match Cmt_format.read_cmt cmt with
  | info -> Ok info
  | exception Sys_error why -> refuse (Unreadable (cmt, reason cmt why))
  | exception Cmt_format.Error (Cmt_format.Not_a_typedtree why) -> refuse (Unreadable (cmt, why))
  | exception Cmi_format.Error _ -> refuse (Unreadable (cmt, "not a typed tree"))
  | exception (End_of_file | Failure _) -> refuse (Unreadable (cmt, "truncated"))

let check ~raises cmt =
  match read cmt with
  | Error why -> Error why
  | Ok info -> (
      match info.cmt_annots, info.cmt_sourcefile with
      | Cmt_format.Implementation _, None -> refuse (No_source (cmt, "none recorded"))
      | Cmt_format.Implementation structure, Some source -> (
          match generated source with
          | Error why -> Error why
          | Ok true -> Ok []
          | Ok false -> (
              Load_path.init ~auto_include:Load_path.no_auto_include info.cmt_loadpath;
              Envaux.reset_cache ();
              try Ok (structure_findings_exn ~raises structure)
              with Lost (loc, missing) ->
                refuse (Environment (Format.asprintf "%a" Location.print_loc loc, missing))))
      | _ -> Ok [])

let render { rule; loc; operator; at } =
  match rule with
  | Compare -> Format.asprintf "%a: rule 7: %s at %s" Location.print_loc loc operator at
  | Raise -> Format.asprintf "%a: rule 6: %s in %s" Location.print_loc loc operator at
