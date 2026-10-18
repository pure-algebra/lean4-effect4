(* typed_lint.ml -- probe: STANDARDS rule 7 checked on the typed tree. Reads each .cmt named on
   the command line and reports every polymorphic comparison or hash applied at a type other than
   int, char, bool, string or unit, with its location and the type. A ppx cannot see this: it runs
   before typing. *)

let watched =
  [ "Stdlib.compare"; "Stdlib.="; "Stdlib.<>"; "Stdlib.<"; "Stdlib.>"; "Stdlib.<="; "Stdlib.>=";
    "Stdlib.min"; "Stdlib.max"; "Stdlib.Hashtbl.hash"; "Stdlib.List.mem"; "Stdlib.List.assoc";
    "Stdlib.List.assoc_opt"; "Stdlib.List.mem_assoc" ]

let allowed = [ "int"; "char"; "bool"; "string"; "unit" ]

let findings = ref 0

let first_arg_type ty =
  match Types.get_desc ty with
  | Types.Tarrow (_, t1, _, _) -> Some t1
  | _ -> None

let ok_type env ty =
  let ty = try Ctype.expand_head env ty with _ -> ty in
  match Types.get_desc ty with
  | Types.Tconstr (p, [], _) -> List.mem (Path.last p) allowed
  | _ -> false

let check file =
  let cmt = Cmt_format.read_cmt file in
  Load_path.init ~auto_include:Load_path.no_auto_include (cmt.Cmt_format.cmt_loadpath);
  match cmt.Cmt_format.cmt_annots with
  | Cmt_format.Implementation str ->
    let expr sub (e : Typedtree.expression) =
      (match e.exp_desc with
       | Typedtree.Texp_ident (p, _, _) when List.mem (Path.name p) watched -> (
         let env = try Envaux.env_of_only_summary e.exp_env with _ -> e.exp_env in
         (* List.mem / assoc compare their first argument: the element or key. *)
         match first_arg_type e.exp_type with
         | Some t when not (ok_type env t) ->
           incr findings;
           Format.printf "%a: %s at %a@." Location.print_loc e.exp_loc (Path.name p)
             Printtyp.type_expr t
         | _ -> ())
       | _ -> ());
      Tast_iterator.default_iterator.expr sub e
    in
    let it = { Tast_iterator.default_iterator with expr } in
    it.structure it str
  | _ -> ()

let () =
  for i = 1 to Array.length Sys.argv - 1 do
    try check Sys.argv.(i) with e -> Format.eprintf "%s: %s@." Sys.argv.(i) (Printexc.to_string e)
  done;
  Format.printf "%d finding(s)@." !findings
