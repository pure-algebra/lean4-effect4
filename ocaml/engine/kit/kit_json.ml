(* Kit_json — JSON text, and every carrier's JSON through its shape document (hand-written).

   What it is: the kit's one JSON reader and one JSON printer. A carrier's JSON is its value tree
   (Eff_types.Val.t) printed under its shape document (Effect4_gen.Api_gen.shape_doc, which Lean lowers from
   the carrier's `Canonical.shape`). So a program, a row table, a type, an exit and a refusal print
   as the session tool prints them (`Tools.JsonBridge.printJson`), and read back where the value
   tree reads. This file is the OCaml twin of `ShapeDoc.print`
   (src/Effect4/Store/Domain/Shape.lean) and of `ShapeDoc.order`, `ShapeDoc.arrays` and
   `ShapeDoc.read` (src/Effect4/Store/Domain/ShapeRead.lean), arm for arm.
   Depends on: Eff_types, Eff_json_text (the tree and its renderer), Effect4_gen.Api_gen (the shape types).

   Behaviours it holds itself to:
   K1  A number is a natural. The tree's own JSON keeps a number as a binary64 bit pattern, which
       the lowered UInt64 does not hold exactly; here a number is an OCaml int, read and printed
       in decimal. The tool's profile carries naturals up to 2^53 - 1 (`CodecProfile.carries`,
       checked in Lean for both drivers), where the two spellings agree. Text this parser cannot
       hold (a fraction, an integer past the int range) refuses here as a parse failure.
                                                                       by construction
   K2  Printing follows `printIn`: the shape names fields and cases, the value gives structure,
       a value that fits no shape prints by structure under "_ctor"/"args".  tested (T3, corpus)
   K3  Reading follows `orderIn` then `readIn`: objects in any key order, a list family as an
       array or as its "cons" cases, the steps bounded by 8 a node plus 64.  tested (T3, corpus)
   K4  The text parser takes RFC 8259 JSON with integer numbers; a fraction, an exponent or a
       number outside OCaml's int is refused with its offset.          tested (T2) *)

open Eff_types
module J = Eff_json_text

(* ------------------------------------------------------------------------------------------ *)
(* JSON text *)

exception Bad_json of int * string

(** Parse one JSON value, with nothing after it but white space. *)
let parse (s : string) : (J.t, string) result =
  let n = String.length s in
  let pos = ref 0 in
  let fail what = raise (Bad_json (!pos, what)) in
  let peek () = if !pos < n then s.[!pos] else '\000' in
  let rec ws () =
    if !pos < n then
      match s.[!pos] with
      | ' ' | '\t' | '\n' | '\r' -> incr pos; ws ()
      | _ -> ()
  in
  let expect c = if peek () = c then incr pos else fail (Printf.sprintf "expected '%c'" c) in
  let word w v =
    let l = String.length w in
    if !pos + l <= n && String.sub s !pos l = w then (pos := !pos + l; v) else fail "unknown word"
  in
  let utf8 b code =
    if code < 0x80 then Buffer.add_char b (Char.chr code)
    else if code < 0x800 then begin
      Buffer.add_char b (Char.chr (0xC0 lor (code lsr 6)));
      Buffer.add_char b (Char.chr (0x80 lor (code land 0x3F)))
    end else if code < 0x10000 then begin
      Buffer.add_char b (Char.chr (0xE0 lor (code lsr 12)));
      Buffer.add_char b (Char.chr (0x80 lor ((code lsr 6) land 0x3F)));
      Buffer.add_char b (Char.chr (0x80 lor (code land 0x3F)))
    end else begin
      Buffer.add_char b (Char.chr (0xF0 lor (code lsr 18)));
      Buffer.add_char b (Char.chr (0x80 lor ((code lsr 12) land 0x3F)));
      Buffer.add_char b (Char.chr (0x80 lor ((code lsr 6) land 0x3F)));
      Buffer.add_char b (Char.chr (0x80 lor (code land 0x3F)))
    end
  in
  let hex4 () =
    if !pos + 4 > n then fail "short \\u escape";
    let v = int_of_string_opt ("0x" ^ String.sub s !pos 4) in
    pos := !pos + 4;
    match v with Some v -> v | None -> fail "bad \\u escape"
  in
  let str () =
    expect '"';
    let b = Buffer.create 16 in
    let rec go () =
      if !pos >= n then fail "unterminated string";
      let c = s.[!pos] in
      incr pos;
      match c with
      | '"' -> Buffer.contents b
      | '\\' ->
        let e = peek () in
        incr pos;
        (match e with
         | '"' -> Buffer.add_char b '"' | '\\' -> Buffer.add_char b '\\'
         | '/' -> Buffer.add_char b '/' | 'b' -> Buffer.add_char b '\b'
         | 'f' -> Buffer.add_char b '\012' | 'n' -> Buffer.add_char b '\n'
         | 'r' -> Buffer.add_char b '\r' | 't' -> Buffer.add_char b '\t'
         | 'u' ->
           let hi = hex4 () in
           if hi >= 0xD800 && hi < 0xDC00 then begin
             expect '\\'; expect 'u';
             let lo = hex4 () in
             if lo < 0xDC00 || lo >= 0xE000 then fail "bad surrogate pair";
             utf8 b (0x10000 + ((hi - 0xD800) lsl 10) + (lo - 0xDC00))
           end else utf8 b hi
         | _ -> fail "bad escape");
        go ()
      | c when Char.code c < 0x20 -> fail "control character in string"
      | c -> Buffer.add_char b c; go ()
    in
    go ()
  in
  let number () =
    let start = !pos in
    if peek () = '-' then incr pos;
    while !pos < n && (match s.[!pos] with '0' .. '9' -> true | _ -> false) do incr pos done;
    (match peek () with '.' | 'e' | 'E' -> fail "only integer numbers are read" | _ -> ());
    match int_of_string_opt (String.sub s start (!pos - start)) with
    | Some v -> J.Int v
    | None -> fail "number outside the int range"
  in
  let rec value () =
    ws ();
    match peek () with
    | '{' ->
      incr pos; ws ();
      if peek () = '}' then (incr pos; J.Object [])
      else
        let rec fields acc =
          ws ();
          let k = str () in
          ws (); expect ':';
          let v = value () in
          ws ();
          match peek () with
          | ',' -> incr pos; fields ((k, v) :: acc)
          | '}' -> incr pos; J.Object (List.rev ((k, v) :: acc))
          | _ -> fail "expected ',' or '}'"
        in
        fields []
    | '[' ->
      incr pos; ws ();
      if peek () = ']' then (incr pos; J.Array [])
      else
        let rec items acc =
          let v = value () in
          ws ();
          match peek () with
          | ',' -> incr pos; items (v :: acc)
          | ']' -> incr pos; J.Array (List.rev (v :: acc))
          | _ -> fail "expected ',' or ']'"
        in
        items []
    | '"' -> J.String (str ())
    | 't' -> word "true" (J.Bool true)
    | 'f' -> word "false" (J.Bool false)
    | 'n' -> word "null" J.Null
    | '-' | '0' .. '9' -> number ()
    | _ -> fail "expected a value"
  in
  try
    let v = value () in
    ws ();
    if !pos <> n then fail "text after the value" else Ok v
  with Bad_json (at, what) -> Error (Printf.sprintf "JSON at byte %d: %s" at what)

let render = J.render

(* ------------------------------------------------------------------------------------------ *)
(* Shapes *)

open Effect4_gen.Api_gen

let lookup_all (name : string) defs =
  List.filter_map (fun (n, s) -> if String.equal n name then Some s else None) defs

(** The first candidate of a shape, or the shape itself (`headShape`). *)
let head_shape defs s =
  match s with
  | Shape_named n -> (match lookup_all n defs with s' :: _ -> s' | [] -> s)
  | _ -> s

let all_nullary cases = List.for_all (fun (_, (_, fields)) -> List.is_empty fields) cases

let case_at (tag : int) cases =
  List.find_map (fun (n, (t, fields)) -> if Int.equal t tag then Some (n, fields) else None) cases

let hex_string (bytes : int list) : string =
  String.concat "" (List.map (Printf.sprintf "%02x") bytes)

let be64_hex (bits : int) : string =
  String.concat "" (List.init 8 (fun i -> Printf.sprintf "%02x" ((bits lsr (8 * (7 - i))) land 0xFF)))

(** The printer under a shape (`printIn`). *)
let rec print_in defs (s : shape) (v : Val.t) : J.t =
  match v with
  | Val.Unit -> J.Null
  | Val.Bool b -> J.Bool b
  | Val.Nat n -> J.Int n
  | Val.Str t -> J.String t
  | Val.Bytes d -> J.String (hex_string d)
  | Val.None -> J.Null
  | Val.Some a ->
    (match head_shape defs s with
     | Shape_option item -> print_in defs item a
     | _ -> print_in defs Shape_unit a)
  | Val.List xs ->
    (match head_shape defs s with
     | Shape_list item -> J.Array (List.map (print_in defs item) xs)
     | _ -> J.Array (List.map (print_in defs Shape_unit) xs))
  | Val.Pair (a, b) ->
    (match head_shape defs s with
     | Shape_pair (f, g) -> J.Array [print_in defs f a; print_in defs g b]
     | _ -> J.Array [print_in defs Shape_unit a; print_in defs Shape_unit b])
  | Val.Ctor (i, args) ->
    let by_structure () =
      J.Object [("_ctor", J.Int i); ("args", J.Array (List.map (print_in defs Shape_unit) args))]
    in
    (match head_shape defs s with
     | Shape_struct (_, fields) -> J.Object (print_fields defs fields args)
     | Shape_sum (_, cases) ->
       (match case_at i cases with
        | Some (name, fields) ->
          if all_nullary cases then J.String name
          else J.Object (("_tag", J.String name) :: print_fields defs fields args)
        | None -> by_structure ())
     | _ -> by_structure ())
  | Val.Ref (_, d) ->
    (* the kind table is not lowered: an `anyRef`'s kind prints as null (`kindJson`'s miss) *)
    (match head_shape defs s with
     | Shape_anyRef -> J.Object [("kind", J.Null); ("address", J.String (hex_string d))]
     | _ -> J.String (hex_string d))
  | Val.Handle (k, n) -> J.Object [("handle", J.Int k); ("key", J.Int n)]
  | Val.NegInt n -> J.Object [("int", J.String (string_of_int (- (n + 1))))]
  | Val.Float b -> J.Object [("float64", J.String (be64_hex b))]

and print_fields defs fields args =
  match fields, args with
  | (n, s) :: fields, a :: args -> (n, print_in defs s a) :: print_fields defs fields args
  | _, _ -> []

(** The list rule (`listItem?`): a sum of `nil` and `cons` with `head` and `tail`. *)
let list_item cases =
  match cases with
  | [ ("nil", (t0, [])); ("cons", (t1, [ ("head", head); ("tail", _) ])) ] when not (Int.equal t0 t1) ->
    Some head
  | _ -> None

let entry_of (name : string) entries = List.assoc_opt name entries

let tag_of_name name cases =
  match List.find_opt (fun (n, _) -> String.equal n name) cases with
  | Some (_, (tag, _)) ->
    (match case_at tag cases with
     | Some (name', fields) when String.equal name' name -> Some (tag, fields)
     | _ -> None)
  | None -> None

let rec json_nodes (j : J.t) =
  match j with
  | J.Array js -> 1 + List.fold_left (fun a j -> a + json_nodes j) 0 js
  | J.Object es -> 1 + List.fold_left (fun a (_, j) -> a + json_nodes j) 0 es
  | _ -> 1

let read_budget j = (8 * json_nodes j) + 64

let rec cons_objects = function
  | [] -> J.Object [("_tag", J.String "nil")]
  | j :: js -> J.Object [("_tag", J.String "cons"); ("head", j); ("tail", cons_objects js)]

(** Each object's entries in its shape's field order (`orderIn`). *)
let rec order_in defs fuel s (j : J.t) : J.t =
  if fuel = 0 then j
  else
    let fuel = fuel - 1 in
    match head_shape defs s, j with
    | Shape_option _, J.Null -> J.Null
    | Shape_option item, j' -> order_in defs fuel item j'
    | Shape_list item, J.Array js -> J.Array (order_list defs fuel item js)
    | Shape_pair (f, g), J.Array [ a; b ] -> J.Array [ order_in defs fuel f a; order_in defs fuel g b ]
    | Shape_sum (_, cases), J.Array js ->
      (match list_item cases with
       | Some item -> cons_objects (order_list defs fuel item js)
       | None -> J.Array js)
    | Shape_struct (_, fields), J.Object entries ->
      (match order_fields defs fuel fields entries with
       | Some ordered when List.length ordered = List.length entries -> J.Object ordered
       | _ -> J.Object entries)
    | Shape_sum (_, cases), J.Object entries ->
      (match entry_of "_tag" entries with
       | Some (J.String name) ->
         (match tag_of_name name cases with
          | Some (_, fields) ->
            (match order_fields defs fuel fields entries with
             | Some ordered when List.length ordered + 1 = List.length entries ->
               J.Object (("_tag", J.String name) :: ordered)
             | _ -> J.Object entries)
          | None -> J.Object entries)
       | _ -> J.Object entries)
    | _, j' -> j'

and order_list defs fuel item js =
  if fuel = 0 then js
  else match js with [] -> [] | j :: js -> order_in defs (fuel - 1) item j :: order_list defs (fuel - 1) item js

and order_fields defs fuel fields entries =
  match fields with
  | [] -> Some []
  | (n, s) :: fields ->
    if fuel = 0 then None
    else
      match entry_of n entries with
      | Some j ->
        Option.map (fun rest -> (n, order_in defs (fuel - 1) s j) :: rest)
          (order_fields defs (fuel - 1) fields entries)
      | None -> None

(** Each list family as an array (`arraysIn`). *)
let rec arrays_in defs fuel s (j : J.t) : J.t =
  if fuel = 0 then j
  else
    let fuel = fuel - 1 in
    match head_shape defs s, j with
    | Shape_option _, J.Null -> J.Null
    | Shape_option item, j' -> arrays_in defs fuel item j'
    | Shape_list item, J.Array js -> J.Array (arrays_list defs fuel item js)
    | Shape_pair (f, g), J.Array [ a; b ] -> J.Array [ arrays_in defs fuel f a; arrays_in defs fuel g b ]
    | Shape_struct (_, fields), J.Object entries -> J.Object (arrays_fields defs fuel fields entries)
    | Shape_sum (_, cases), J.Object entries ->
      (match list_item cases with
       | Some item -> J.Array (arrays_spine defs fuel item (J.Object entries))
       | None ->
         (match entry_of "_tag" entries with
          | Some (J.String name) ->
            (match tag_of_name name cases with
             | Some (_, fields) -> J.Object (arrays_fields defs fuel fields entries)
             | None -> J.Object entries)
          | _ -> J.Object entries))
    | _, j' -> j'

and arrays_list defs fuel item js =
  if fuel = 0 then js
  else match js with [] -> [] | j :: js -> arrays_in defs (fuel - 1) item j :: arrays_list defs (fuel - 1) item js

and arrays_fields defs fuel fields entries =
  if fuel = 0 then entries
  else
    match entries with
    | [] -> []
    | (k, j) :: entries ->
      (k, (match List.assoc_opt k fields with Some s -> arrays_in defs (fuel - 1) s j | None -> j))
      :: arrays_fields defs (fuel - 1) fields entries

and arrays_spine defs fuel item j =
  match j with
  | J.Object [ ("_tag", J.String "cons"); ("head", h); ("tail", t) ] when fuel > 0 ->
    arrays_in defs (fuel - 1) item h :: arrays_spine defs (fuel - 1) item t
  | _ -> []

let canonical_hex (h : string) : int list option =
  let n = String.length h in
  if n mod 2 <> 0 then None
  else
    let digit c = match c with '0' .. '9' -> Some (Char.code c - 48) | 'a' .. 'f' -> Some (Char.code c - 87) | _ -> None in
    let rec go i acc =
      if i >= n then Some (List.rev acc)
      else match digit h.[i], digit h.[i + 1] with
        | Some a, Some b -> go (i + 2) ((a * 16 + b) :: acc)
        | _ -> None
    in
    go 0 []

(** Read a value tree under a shape (`readIn`). *)
let rec read_in defs budget s (j : J.t) : Val.t option =
  if budget = 0 then None
  else
    let n = budget - 1 in
    match head_shape defs s, j with
    | Shape_unit, J.Null -> Some Val.Unit
    | Shape_option _, J.Null -> Some Val.None
    | Shape_option item, j' -> Option.map (fun v -> Val.Some v) (read_in defs n item j')
    | Shape_bool, J.Bool b -> Some (Val.Bool b)
    | Shape_nat, J.Int x -> if x >= 0 then Some (Val.Nat x) else None
    | Shape_string, J.String t -> Some (Val.Str t)
    | (Shape_bytes | Shape_digest), J.String h -> Option.map (fun d -> Val.Bytes d) (canonical_hex h)
    | Shape_list item, J.Array js -> Option.map (fun vs -> Val.List vs) (read_list defs n item js)
    | Shape_pair (f, g), J.Array [ a; b ] ->
      Option.bind (read_in defs n f a) (fun x -> Option.map (fun y -> Val.Pair (x, y)) (read_in defs n g b))
    | Shape_struct (_, fields), J.Object entries ->
      Option.map (fun vs -> Val.Ctor (0, vs)) (read_fields defs n fields entries)
    | Shape_sum (_, cases), J.String name ->
      if all_nullary cases then
        Option.bind (tag_of_name name cases) (fun (tag, fields) ->
            if List.is_empty fields then Some (Val.Ctor (tag, [])) else None)
      else None
    | Shape_sum (_, cases), J.Object (("_tag", J.String name) :: entries) ->
      if all_nullary cases then None
      else
        Option.bind (tag_of_name name cases) (fun (tag, fields) ->
            Option.map (fun vs -> Val.Ctor (tag, vs)) (read_fields defs n fields entries))
    | _, _ -> None

and read_list defs budget item js =
  if budget = 0 then None
  else
    match js with
    | [] -> Some []
    | j :: js ->
      Option.bind (read_in defs (budget - 1) item j) (fun x ->
          Option.map (fun xs -> x :: xs) (read_list defs (budget - 1) item js))

and read_fields defs budget fields entries =
  if budget = 0 then None
  else
    match fields, entries with
    | [], [] -> Some []
    | (k, s) :: fields, (k', j) :: entries when k' = k ->
      Option.bind (read_in defs (budget - 1) s j) (fun x ->
          Option.map (fun xs -> x :: xs) (read_fields defs (budget - 1) fields entries))
    | _, _ -> None

(* ------------------------------------------------------------------------------------------ *)
(* A carrier's JSON *)

(** A value tree's JSON under a shape document, each list as an array (`Canonical.printArrays`). *)
let print (doc : shape_doc) (v : Val.t) : J.t =
  let j = print_in doc.defs doc.root v in
  arrays_in doc.defs (read_budget j) doc.root j

(** A value tree from JSON whose objects may be in any order and whose lists may be arrays
    (`ShapeDoc.order`, then `ShapeDoc.read`). *)
let read (doc : shape_doc) (j : J.t) : Val.t option =
  let ordered = order_in doc.defs (read_budget j) doc.root j in
  read_in doc.defs (read_budget ordered) doc.root ordered
