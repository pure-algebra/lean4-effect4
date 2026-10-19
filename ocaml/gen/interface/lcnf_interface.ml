(* Lcnf_interface: infer a generated unit's public interface from its fresh typed tree.
   Depends on compiler-libs. It reads no previous .mli.
   Properties:
   I1 Every exported value is a requested root or a prelude value. Tested by test_interface.
   I2 Selected packages lose their representation as a whole. Tested by the sealing controls.
   I3 Final nominal ascriptions replace earlier inferred bindings. Tested by test_interface.
   I4 Missing roots or packages refuse as values. Tested by test_interface.
   I5 Prelude values remain public until their source owner deletes them. By construction.
   I6 With [Reachable], a top-level type stays only when an exported value's type, a selected
      package or another kept type's declaration names it: a consumer's facade exports the
      types its roots name, not every type of the unit it includes. Tested by test_interface. *)

open Types

type refusal =
  | Input of string
  | Not_implementation
  | Missing_values of string list
  | Missing_types of string list

type types =
  | All
  | Reachable

let message = function
  | Input why -> why
  | Not_implementation -> "an implementation typed tree is required"
  | Missing_values names -> "missing public roots: " ^ String.concat ", " names
  | Missing_types names -> "missing abstract packages: " ^ String.concat ", " names
;;

let[@inline never] [@local never] [@specialise never] refuse why = Error why
let member name names = List.exists (String.equal name) names

let last_values signature =
  let _, kept =
    List.fold_right
      (fun item (seen, kept) ->
         match item with
         | Sig_value (id, _, _) ->
           let name = Ident.name id in
           if member name seen then seen, kept else name :: seen, item :: kept
         | _ -> seen, item :: kept)
      signature
      ([], [])
  in
  kept
;;

let rec names signature =
  List.fold_left
    (fun (values, types) -> function
       | Sig_value (id, _, _) -> Ident.name id :: values, types
       | Sig_type (id, _, _, _) -> values, Ident.name id :: types
       | Sig_module (_, _, declaration, _, _) ->
         let v, t = module_names declaration.md_type in
         v @ values, t @ types
       | _ -> values, types)
    ([], [])
    signature

and module_names = function
  | Mty_signature signature -> names signature
  | Mty_functor (_, result) -> module_names result
  | _ -> [], []
;;

let rec filter ~roots ~abstract_types signature =
  List.filter_map
    (function
      | Sig_value (id, _, _) as item ->
        if member (Ident.name id) roots then Some item else None
      | Sig_type (id, declaration, recursion, visibility)
        when member (Ident.name id) abstract_types ->
        Some
          (Sig_type
             ( id
             , { declaration with
                 type_kind = Type_abstract
               ; type_manifest = None
               ; type_private = Asttypes.Public
               }
             , recursion
             , visibility ))
      | Sig_module (id, presence, declaration, recursion, visibility) ->
        Some
          (Sig_module
             ( id
             , presence
             , { declaration with
                 md_type = filter_module ~roots ~abstract_types declaration.md_type
               }
             , recursion
             , visibility ))
      | item -> Some item)
    (last_values signature)

and filter_module ~roots ~abstract_types = function
  | Mty_signature signature -> Mty_signature (filter ~roots ~abstract_types signature)
  | Mty_functor (parameter, result) ->
    Mty_functor (parameter, filter_module ~roots ~abstract_types result)
  | other -> other
;;

(* The unit's own type names (the [Pident] constructors) a type expression mentions. Each node is
   read once: [get_id] is an int, so the table compares ints. *)
let local_types ty =
  let seen = Hashtbl.create 64 in
  let found = ref [] in
  let rec visit ty =
    let id = get_id ty in
    if not (Hashtbl.mem seen id)
    then (
      Hashtbl.add seen id ();
      (match get_desc ty with
       | Tconstr (Path.Pident ident, _, _) -> found := Ident.name ident :: !found
       | _ -> ());
      Btype.iter_type_expr visit ty)
  in
  visit ty;
  !found
;;

(* The unit's own type names a type declaration mentions: its manifest and its representation. *)
let declaration_types declaration =
  let found = ref [] in
  let add ty = found := local_types ty @ !found in
  Option.iter add declaration.type_manifest;
  Btype.iter_type_expr_kind add declaration.type_kind;
  !found
;;

(* I6: the top-level types that an exported value, a selected package or a kept type's
   declaration names, closed under the declarations; every other item stays as it is. *)
let reachable ~abstract_types signature =
  let declarations =
    List.filter_map
      (function
        | Sig_type (id, declaration, _, _) -> Some (Ident.name id, declaration)
        | _ -> None)
      signature
  in
  let start =
    List.concat_map
      (function
        | Sig_value (_, value, _) -> local_types value.val_type
        | _ -> [])
      signature
    @ abstract_types
  in
  let rec close kept = function
    | [] -> kept
    | name :: rest when member name kept -> close kept rest
    | name :: rest ->
      let next =
        match List.find_opt (fun (other, _) -> String.equal other name) declarations with
        | Some (_, declaration) -> declaration_types declaration
        | None -> []
      in
      close (name :: kept) (next @ rest)
  in
  let kept = close [] start in
  List.filter
    (function
      | Sig_type (id, _, _, _) -> member (Ident.name id) kept
      | _ -> true)
    signature
;;

let select ~types ~roots ~abstract_types signature =
  let values, declared = names signature in
  let missing_values = List.filter (fun name -> not (member name values)) roots in
  let missing_types =
    List.filter (fun name -> not (member name declared)) abstract_types
  in
  if not (List.is_empty missing_values)
  then refuse (Missing_values missing_values)
  else if not (List.is_empty missing_types)
  then refuse (Missing_types missing_types)
  else (
    let selected = filter ~roots ~abstract_types signature in
    match types with
    | All -> Ok selected
    | Reachable -> Ok (reachable ~abstract_types selected))
;;

let prelude_values path =
  let input = open_in path in
  Fun.protect
    ~finally:(fun () -> close_in input)
    (fun () ->
       let lexer = Lexing.from_channel input in
       Location.init lexer path;
       let structure = Parse.implementation lexer in
       List.concat_map
         (fun item ->
            match item.Parsetree.pstr_desc with
            | Parsetree.Pstr_value (_, bindings) ->
              List.concat_map
                (fun binding ->
                   let found = ref [] in
                   let visitor =
                     { Ast_iterator.default_iterator with
                       pat =
                         (fun self pattern ->
                           (match pattern.Parsetree.ppat_desc with
                            | Parsetree.Ppat_var name | Parsetree.Ppat_alias (_, name) ->
                              found := name.Location.txt :: !found
                            | _ -> ());
                           Ast_iterator.default_iterator.pat self pattern)
                     }
                   in
                   visitor.pat visitor binding.Parsetree.pvb_pat;
                   !found)
                bindings
            | _ -> [])
         structure)
;;

let generate ~types ~cmt ~roots ~abstract_types ~prelude =
  try
    let roots =
      roots
      @
      match prelude with
      | None -> []
      | Some path -> prelude_values path
    in
    let info = Cmt_format.read_cmt cmt in
    match info.Cmt_format.cmt_annots with
    | Cmt_format.Implementation structure ->
      (match select ~types ~roots ~abstract_types structure.Typedtree.str_type with
       | Error why -> Error why
       | Ok signature ->
         let rendered =
           Printtyp.wrap_printing_env ~error:false info.cmt_initial_env (fun () ->
             Format.asprintf "%a" Printtyp.signature signature)
         in
         Ok
           ("(* GENERATED by Lcnf_interface from a fresh OCaml typed tree. Do not edit.\n"
            ^ "   Regenerate: python3 scripts/generate.py --only lcnf *)\n"
            ^ "[@@@warning \"-30\"]\n"
            ^ rendered
            ^ "\n"))
    | _ -> refuse Not_implementation
  with
  | exn -> refuse (Input (Printexc.to_string exn))
;;
