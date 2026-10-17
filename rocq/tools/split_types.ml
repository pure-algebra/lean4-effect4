(* split_types.ml -- one recursive OCaml type group, printed again as its strongly connected
   components in dependency order.

   What it is: the LCNF route declares the program types of ocaml/eff/eff_types.ml as one
   `type ... and ...` group. Rocq needs the same parameters on every type of a mutual inductive,
   and `'op eff` has one while `ty` has none, so rocq-of-ocaml's translation of the one group is
   refused. This tool reads a structure, splits each recursive type group into its components
   (Tarjan), and prints each component as its own group, dependencies first. Nothing else in the
   structure changes. Depends on: compiler-libs (Parse, Pprintast).

   Properties:
   S1  Every declaration of the input appears once in the output, unchanged.   by construction
   S2  A component lists only declarations that reach each other through their type
       expressions; a declaration comes after every component it names.      by construction
   S3  The output type-checks as the input does: a check by `ocamlfind ocamlc -c` of both files
       is the test (the receipt's commands).                                 tested

   Run: ocamlfind ocamlopt -package compiler-libs.common -linkpkg split_types.ml -o split_types
        ./split_types eff_types.ml > eff_types_split.ml *)

open Parsetree

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* The type constructor names a declaration mentions, unqualified. *)
let mentions (decl : type_declaration) : string list =
  let acc = ref [] in
  let iterator =
    { Ast_iterator.default_iterator with
      typ =
        (fun self t ->
          (match t.ptyp_desc with
           | Ptyp_constr ({ txt = Longident.Lident name; _ }, _) -> acc := name :: !acc
           | _ -> ());
          Ast_iterator.default_iterator.typ self t) }
  in
  iterator.type_declaration iterator decl;
  !acc

(* Tarjan's strongly connected components, in reverse topological order of the condensation:
   a component is emitted after every component it reaches. *)
let components (names : string array) (edges : int list array) : int list list =
  let n = Array.length names in
  let index = Array.make n (-1) and low = Array.make n 0 and on_stack = Array.make n false in
  let stack = ref [] and counter = ref 0 and out = ref [] in
  let rec visit v =
    index.(v) <- !counter;
    low.(v) <- !counter;
    incr counter;
    stack := v :: !stack;
    on_stack.(v) <- true;
    List.iter
      (fun w ->
        if index.(w) < 0 then begin
          visit w;
          low.(v) <- min low.(v) low.(w)
        end
        else if on_stack.(w) then low.(v) <- min low.(v) index.(w))
      edges.(v);
    if low.(v) = index.(v) then begin
      let rec pop acc =
        match !stack with
        | w :: rest ->
          stack := rest;
          on_stack.(w) <- false;
          if w = v then w :: acc else pop (w :: acc)
        | [] -> acc
      in
      out := List.sort compare (pop []) :: !out
    end
  in
  for v = 0 to n - 1 do
    if index.(v) < 0 then visit v
  done;
  List.rev !out

let split_item (item : structure_item) : structure_item list =
  match item.pstr_desc with
  | Pstr_type (flag, decls) when List.length decls > 1 ->
    let names = Array.of_list (List.map (fun d -> d.ptype_name.txt) decls) in
    let decls = Array.of_list decls in
    let position name =
      let rec go i = if i >= Array.length names then None else if names.(i) = name then Some i else go (i + 1) in
      go 0
    in
    let edges = Array.map (fun d -> List.sort_uniq compare (List.filter_map position (mentions d))) decls in
    List.map
      (fun component ->
        { item with pstr_desc = Pstr_type (flag, List.map (fun i -> decls.(i)) component) })
      (components names edges)
  | _ -> [ item ]

let () =
  let path = Sys.argv.(1) in
  let structure = Parse.implementation (Lexing.from_string (read_file path)) in
  Format.printf "%a@." Pprintast.structure (List.concat_map split_item structure)
