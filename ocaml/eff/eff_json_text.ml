(* Eff_json_text — a JSON syntax tree and its compact renderer (hand-written).

   What it is: the text half of the JSON printer. Eff_json (generated) maps every carrier to
   this tree; render writes it. There is no parser anywhere in this library.
   Depends on: the OCaml standard library only.

   Behaviours it holds itself to:
   J1  Compact: no whitespace, "," between items, ":" between a key and its value.
                                                                      by construction
   J2  Strings: '"' and '\' are escaped, the control characters U+0008 U+0009 U+000A U+000C
       U+000D as \b \t \n \f \r, every other byte below 0x20 as \u00XX (lowercase hex),
       every other byte verbatim (UTF-8 passes through untouched).   by construction
   J3  Byte-identical to the Lean printer EffGen.lean `V.json` on every value of the closed
       world.                                                          tested (goldens)
   J4  Integers print in decimal with no sign for non-negative values (the Lean image). *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | String of string
  | Array of t list
  | Object of (string * t) list

let escape (b : Buffer.t) (s : string) : unit =
  Buffer.add_char b '"';
  String.iter
    (fun c ->
      match c with
      | '"' -> Buffer.add_string b "\\\""
      | '\\' -> Buffer.add_string b "\\\\"
      | '\n' -> Buffer.add_string b "\\n"
      | '\r' -> Buffer.add_string b "\\r"
      | '\t' -> Buffer.add_string b "\\t"
      | '\b' -> Buffer.add_string b "\\b"
      | '\012' -> Buffer.add_string b "\\f"
      | c when Char.code c < 0x20 -> Buffer.add_string b (Printf.sprintf "\\u%04x" (Char.code c))
      | c -> Buffer.add_char b c)
    s;
  Buffer.add_char b '"'

let rec write (b : Buffer.t) (v : t) : unit =
  match v with
  | Null -> Buffer.add_string b "null"
  | Bool true -> Buffer.add_string b "true"
  | Bool false -> Buffer.add_string b "false"
  | Int n -> Buffer.add_string b (string_of_int n)
  | String s -> escape b s
  | Array xs ->
    Buffer.add_char b '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; write b x) xs;
    Buffer.add_char b ']'
  | Object kvs ->
    Buffer.add_char b '{';
    List.iteri
      (fun i (k, x) ->
        if i > 0 then Buffer.add_char b ',';
        escape b k;
        Buffer.add_char b ':';
        write b x)
      kvs;
    Buffer.add_char b '}'

let render (v : t) : string =
  let b = Buffer.create 256 in
  write b v;
  Buffer.contents b
