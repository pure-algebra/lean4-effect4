(* Lcnf_interface: infer a generated unit's public interface from its fresh typed tree.
   Depends on compiler-libs. It reads no previous .mli.
   Properties:
   I1 Every exported value is a requested root or a prelude value. Tested by test_interface.
   I2 Selected packages lose their representation as a whole. Tested by the sealing controls.
   I3 Final nominal ascriptions replace earlier inferred bindings. Tested by test_interface.
   I4 Missing roots or packages refuse as values. Tested by test_interface.
   I5 Prelude values remain public until their source owner deletes them. By construction. *)

open Types

type refusal =
  | Input of string
  | Not_implementation
  | Missing_values of string list
  | Missing_types of string list

let message = function
  | Input why -> why
  | Not_implementation -> "an implementation typed tree is required"
  | Missing_values names -> "missing public roots: " ^ String.concat ", " names
  | Missing_types names -> "missing abstract packages: " ^ String.concat ", " names

let[@inline never] [@local never] [@specialise never] refuse why = Error why
let member name names = List.exists (String.equal name) names

let last_values signature =
  let _, kept = List.fold_right (fun item (seen, kept) -> match item with
    | Sig_value (id, _, _) ->
        let name = Ident.name id in
        if member name seen then seen, kept else name :: seen, item :: kept
    | _ -> seen, item :: kept) signature ([], []) in
  kept

let rec names signature =
  List.fold_left (fun (values, types) -> function
    | Sig_value (id, _, _) -> Ident.name id :: values, types
    | Sig_type (id, _, _, _) -> values, Ident.name id :: types
    | Sig_module (_, _, declaration, _, _) ->
        let v, t = module_names declaration.md_type in v @ values, t @ types
    | _ -> values, types) ([], []) signature
and module_names = function
  | Mty_signature signature -> names signature
  | Mty_functor (_, result) -> module_names result
  | _ -> [], []

let rec filter ~roots ~abstract_types signature =
  List.filter_map (function
    | Sig_value (id, _, _) as item ->
        if member (Ident.name id) roots then Some item else None
    | Sig_type (id, declaration, recursion, visibility)
        when member (Ident.name id) abstract_types ->
        Some (Sig_type (id,
          { declaration with type_kind = Type_abstract; type_manifest = None;
            type_private = Asttypes.Public }, recursion, visibility))
    | Sig_module (id, presence, declaration, recursion, visibility) ->
        Some (Sig_module (id, presence,
          { declaration with md_type = filter_module ~roots ~abstract_types declaration.md_type },
          recursion, visibility))
    | item -> Some item) (last_values signature)
and filter_module ~roots ~abstract_types = function
  | Mty_signature signature -> Mty_signature (filter ~roots ~abstract_types signature)
  | Mty_functor (parameter, result) ->
      Mty_functor (parameter, filter_module ~roots ~abstract_types result)
  | other -> other

let select ~roots ~abstract_types signature =
  let values, types = names signature in
  let missing_values = List.filter (fun name -> not (member name values)) roots in
  let missing_types = List.filter (fun name -> not (member name types)) abstract_types in
  if missing_values <> [] then refuse (Missing_values missing_values)
  else if missing_types <> [] then refuse (Missing_types missing_types)
  else Ok (filter ~roots ~abstract_types signature)

let prelude_values path =
  let input = open_in path in
  Fun.protect ~finally:(fun () -> close_in input) (fun () ->
    let lexer = Lexing.from_channel input in
    Location.init lexer path;
    let structure = Parse.implementation lexer in
    List.concat_map (fun item -> match item.Parsetree.pstr_desc with
      | Parsetree.Pstr_value (_, bindings) ->
          List.concat_map (fun binding ->
            let found = ref [] in
            let visitor = { Ast_iterator.default_iterator with pat = (fun self pattern ->
              (match pattern.Parsetree.ppat_desc with
               | Parsetree.Ppat_var name | Parsetree.Ppat_alias (_, name) ->
                   found := name.Location.txt :: !found
               | _ -> ());
              Ast_iterator.default_iterator.pat self pattern) } in
            visitor.pat visitor binding.Parsetree.pvb_pat;
            !found) bindings
      | _ -> []) structure)

let generate ~cmt ~roots ~abstract_types ~prelude =
  try
    let roots = roots @ (match prelude with None -> [] | Some path -> prelude_values path) in
    let info = Cmt_format.read_cmt cmt in
    match info.Cmt_format.cmt_annots with
    | Cmt_format.Implementation structure ->
        (match select ~roots ~abstract_types structure.Typedtree.str_type with
         | Error why -> Error why
         | Ok signature ->
             let rendered = Printtyp.wrap_printing_env ~error:false info.cmt_initial_env (fun () ->
               Format.asprintf "%a" Printtyp.signature signature) in
             Ok ("(* GENERATED by Lcnf_interface from a fresh OCaml typed tree. Do not edit.\n"
                 ^ "   Regenerate: python3 scripts/generate.py --only lcnf *)\n"
                 ^ "[@@@warning \"-30\"]\n" ^ rendered ^ "\n"))
    | _ -> refuse Not_implementation
  with exn -> refuse (Input (Printexc.to_string exn))
