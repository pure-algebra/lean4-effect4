(* split_types.ml -- the program types of ocaml/eff/eff_types.ml, printed again as one flat type
   group split into its strongly connected components in dependency order; and, with --extract,
   the Rocq extraction directives that send each flat type back to its owner's module.

   What it is: the LCNF route declares each program type in its own module named as Lean names it
   (`module Ty = struct type t = Never | ... end`), and a cycle as `module rec`. rocq-of-ocaml
   reads neither shape, and Rocq needs the same parameters on every type of a mutual inductive
   (`'op Eff.t` has one, `Ty.t` none). So this tool does two things:
   1. flatten: each module's `t` becomes one flat type named after the module in snake case
      (`Ty.t` is `ty`, `CauseTerm.t` is `cause_term`; `val` and `exit` take a trailing `_`), each
      constructor takes its module as a prefix (`Eff.Succeed` is `Eff_succeed`), and every
      `M.t` in a type expression names the flat type of `M`;
   2. split: the flat group is printed as its components (Tarjan), dependencies first.
   These are the names and the order the Rocq workspace was built on, so `Eff_types.v` keeps its
   spelling when the OCaml layout changes.
   With --extract it prints the inverse of step 1 as Rocq directives, one `Extract Inductive` per
   variant and per record (`E4.Eff_types.eff` is `Eff_types.Eff.t`, `Eff_succeed` is
   `Eff_types.Eff.Succeed`). Rocq code extracted over `Eff_types.v` then speaks the estate's own
   types, so the comparison lane's runner (rocq/LaneExtract.v, `make gen-rocq-lane`) meets Lean's
   lowered code with no second copy of a type. A type abbreviation needs no directive: Rocq unfolds
   it. A record crosses through a building function and a matching function, by the OCaml labels.
   Depends on: compiler-libs (Parse, Pprintast).

   Properties:
   S0  Every module of the input is one type module or one `module rec` of type signatures, and
       nothing else: any other item inside a module is refused by name.  by construction
   S1  Every type declaration of the input appears once in the output, renamed as in step 1 and
       otherwise unchanged.                                                by construction
   S2  A component lists only declarations that reach each other through their type
       expressions; a declaration comes after every component it names.  by construction
   S3  The output type-checks: `ocamlfind ocamlc -c` of the output is the test (`make gen-rocq`).
                                                                          tested
   S4  For the types of 6689f0833 the Rocq file is the one the flat layout of 81f9a4354 gave,
       byte for byte (the receipt of 2026-10-17's seat rocq-cas).          tested
   S5  With --extract, every variant and every record of the input has exactly one directive. It
       names the flat type of S1 and the owner's type, with the constructors in declaration order;
       an abbreviation has none. S0's refusals hold in this mode too.     by construction
   S6  The directives compile against `Eff_types.v`, and Rocq's extraction over them type-checks
       against effect4_eff: `make gen-rocq-lane` and the lane's build (engine/test/rocq) are the
       test.                                                              tested

   Run: ocamlfind ocamlopt -package compiler-libs.common -linkpkg split_types.ml -o split_types
        ./split_types eff_types.ml > eff_types_split.ml
        ./split_types --extract eff_types.ml > EffExtract.v *)

open Parsetree

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

(* ---- 1. flatten ---- *)

(* `CauseTerm` is `cause_term`, `Effect4_row` is `effect4_row`; `val` and `exit` take `_`. *)
let flat_name (m : string) : string =
  let b = Buffer.create (String.length m + 4) in
  String.iteri
    (fun i c ->
      let upper = c >= 'A' && c <= 'Z' in
      if upper && i > 0 then begin
        let p = m.[i - 1] in
        if (p >= 'a' && p <= 'z') || (p >= '0' && p <= '9') then Buffer.add_char b '_'
      end;
      Buffer.add_char b (Char.lowercase_ascii c))
    m;
  let s = Buffer.contents b in
  if List.mem s [ "val"; "exit" ] then s ^ "_" else s

let refuse what = failwith ("split_types: refused: " ^ what)

(* One declaration of module `m`: `t` is the flat name, `M'.t` names `M'`'s flat type, and each
   constructor takes `m` as a prefix. *)
let rename_decl (m : string) (d : type_declaration) : type_declaration =
  let retarget lid =
    match lid with
    | Longident.Lident "t" -> Longident.Lident (flat_name m)
    | Longident.Ldot ({ txt = Longident.Lident m'; _ }, { txt = "t"; _ }) -> Longident.Lident (flat_name m')
    | Longident.Lident _ -> lid
    | _ -> refuse ("a type path in module " ^ m)
  in
  let mapper =
    { Ast_mapper.default_mapper with
      typ =
        (fun self t ->
          match t.ptyp_desc with
          | Ptyp_constr (lid, args) ->
            { t with
              ptyp_desc =
                Ptyp_constr ({ lid with txt = retarget lid.txt }, List.map (self.typ self) args) }
          | _ -> Ast_mapper.default_mapper.typ self t);
      constructor_declaration =
        (fun self c ->
          let c = Ast_mapper.default_mapper.constructor_declaration self c in
          { c with
            pcd_name = { c.pcd_name with txt = m ^ "_" ^ String.uncapitalize_ascii c.pcd_name.txt } })
    }
  in
  if d.ptype_name.txt <> "t" then refuse ("type " ^ d.ptype_name.txt ^ " in module " ^ m);
  let d = mapper.type_declaration mapper d in
  { d with ptype_name = { d.ptype_name with txt = flat_name m } }

let module_name (mb : module_binding) : string =
  match mb.pmb_name.txt with Some m -> m | None -> refuse "an anonymous module"

(* The type declarations a module item carries, each with its module, as the input spells them;
   `None` for an item outside any module. *)
let owned (item : structure_item) : (string * type_declaration) list option =
  match item.pstr_desc with
  | Pstr_module mb ->
    let m = module_name mb in
    (match mb.pmb_expr.pmod_desc with
     | Pmod_structure items ->
       Some
         (List.concat_map
            (fun i ->
              match i.pstr_desc with
              | Pstr_type (_, ds) -> List.map (fun d -> m, d) ds
              | _ -> refuse ("an item other than a type in module " ^ m))
            items)
     | _ -> refuse ("module " ^ m ^ ", which is no structure"))
  | Pstr_recmodule mbs ->
    Some
      (List.concat_map
         (fun mb ->
           let m = module_name mb in
           match mb.pmb_expr.pmod_desc with
           | Pmod_constraint (_, { pmty_desc = Pmty_signature sigs; _ }) ->
             List.concat_map
               (fun s ->
                 match s.psig_desc with
                 | Psig_type (_, ds) -> List.map (fun d -> m, d) ds
                 | _ -> refuse ("an item other than a type in module rec " ^ m))
               sigs
           | _ -> refuse ("module rec " ^ m ^ ", which has no signature"))
         mbs)
  | _ -> None

(* The type declarations a module item carries, renamed; `None` for an item outside any module. *)
let decls_of_item (item : structure_item) : type_declaration list option =
  Option.map (List.map (fun (m, d) -> rename_decl m d)) (owned item)

(* Every module's types as one recursive group, after the items that are no module. *)
let flatten (structure : structure) : structure =
  let others = List.filter (fun i -> decls_of_item i = None) structure in
  match List.concat (List.filter_map decls_of_item structure) with
  | [] -> others
  | decls -> others @ [ Ast_helper.Str.type_ Asttypes.Recursive decls ]

(* ---- 2. split ---- *)

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

(* ---- 3. extract: the directives back to the owner's modules ---- *)

(* One declaration of module `m` as an `Extract Inductive`: a variant by its constructors, a record
   by a building and a matching function over its labels; `None` for an abbreviation. *)
let directive (m : string) (d : type_declaration) : string option =
  if d.ptype_name.txt <> "t" then refuse ("type " ^ d.ptype_name.txt ^ " in module " ^ m);
  let flat = flat_name m in
  let owner = Printf.sprintf "Eff_types.%s.t" m in
  let annotation =
    match d.ptype_params with
    | [] -> owner
    | ps -> Printf.sprintf "(%s) %s" (String.concat ", " (List.map (fun _ -> "_") ps)) owner
  in
  match d.ptype_kind with
  | Ptype_variant cs ->
    let ctor c = Printf.sprintf "\"Eff_types.%s.%s\"" m c.pcd_name.txt in
    Some
      (Printf.sprintf "Extract Inductive E4.Eff_types.%s => \"%s\" [ %s ]." flat owner
         (String.concat " " (List.map ctor cs)))
  | Ptype_record fields ->
    let labels = List.map (fun f -> f.pld_name.txt) fields in
    let build =
      Printf.sprintf "(fun (%s) -> ({ %s } : %s))" (String.concat ", " labels)
        (String.concat "; " (List.map (fun l -> Printf.sprintf "Eff_types.%s.%s = %s" m l l) labels))
        annotation
    in
    let case =
      Printf.sprintf "(fun g (r : %s) -> g %s)" annotation
        (String.concat " " (List.map (fun l -> Printf.sprintf "r.Eff_types.%s.%s" m l) labels))
    in
    Some
      (Printf.sprintf "Extract Inductive E4.Eff_types.%s.record => \"%s\" [ \"%s\" ] \"%s\"." flat owner
         build case)
  | Ptype_abstract | Ptype_open -> None

let extract (structure : structure) : string list =
  "(* GENERATED by `make gen-rocq-lane` (rocq/tools/split_types.ml --extract of ocaml/eff/eff_types.ml); do not edit. *)"
  :: "From Stdlib Require Import Extraction."
  :: "Require E4.Eff_types."
  :: List.filter_map (fun (m, d) -> directive m d) (List.concat (List.filter_map owned structure))

let () =
  match Array.to_list Sys.argv with
  | [ _; path ] when path <> "--extract" ->
    let structure = Parse.implementation (Lexing.from_string (read_file path)) in
    Format.printf "%a@." Pprintast.structure (List.concat_map split_item (flatten structure))
  | [ _; "--extract"; path ] ->
    let structure = Parse.implementation (Lexing.from_string (read_file path)) in
    List.iter print_endline (extract structure)
  | _ ->
    prerr_endline "usage: split_types [--extract] eff_types.ml";
    exit 2
