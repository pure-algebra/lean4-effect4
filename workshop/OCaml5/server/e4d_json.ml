(* A minimal JSON value, parser and printer.

   The 5.1.1 switch does carry Yojson, but the daemon links the avatar modules with a plain
   `ocamlc <files>` list -- the same shape `avatar/build-avatar.sh` uses -- and the same
   bytecode is handed to js_of_ocaml. One 200-line module keeps that build free of findlib
   and of any question about what a package does under `--enable effects`. Nothing here is
   clever: object keys keep insertion order so a response is byte-stable, and numbers are
   integers or IEEE doubles. *)

type t =
  | Null
  | Bool of bool
  | Int of int
  | Float of float
  | Str of string
  | List of t list
  | Obj of (string * t) list

exception Parse_error of string

(* ----------------------------------------------------------------------- printing *)

let escape (b : Buffer.t) (s : string) =
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

let rec write (b : Buffer.t) (v : t) =
  match v with
  | Null -> Buffer.add_string b "null"
  | Bool true -> Buffer.add_string b "true"
  | Bool false -> Buffer.add_string b "false"
  | Int n -> Buffer.add_string b (string_of_int n)
  | Float f ->
    if Float.is_integer f && Float.abs f < 1e15 then
      Buffer.add_string b (Printf.sprintf "%.1f" f)
    else Buffer.add_string b (Printf.sprintf "%.17g" f)
  | Str s -> escape b s
  | List items ->
    Buffer.add_char b '[';
    List.iteri (fun i x -> if i > 0 then Buffer.add_char b ','; write b x) items;
    Buffer.add_char b ']'
  | Obj fields ->
    Buffer.add_char b '{';
    List.iteri
      (fun i (k, x) ->
        if i > 0 then Buffer.add_char b ',';
        escape b k;
        Buffer.add_char b ':';
        write b x)
      fields;
    Buffer.add_char b '}'

let to_string (v : t) : string =
  let b = Buffer.create 256 in
  write b v;
  Buffer.contents b

(* Indented form, for the README's examples and for a human reading a receipt. *)
let rec write_pretty b indent v =
  let pad n = String.make (2 * n) ' ' in
  match v with
  | List [] -> Buffer.add_string b "[]"
  | Obj [] -> Buffer.add_string b "{}"
  | List items ->
    Buffer.add_string b "[\n";
    List.iteri
      (fun i x ->
        if i > 0 then Buffer.add_string b ",\n";
        Buffer.add_string b (pad (indent + 1));
        write_pretty b (indent + 1) x)
      items;
    Buffer.add_char b '\n';
    Buffer.add_string b (pad indent);
    Buffer.add_char b ']'
  | Obj fields ->
    Buffer.add_string b "{\n";
    List.iteri
      (fun i (k, x) ->
        if i > 0 then Buffer.add_string b ",\n";
        Buffer.add_string b (pad (indent + 1));
        escape b k;
        Buffer.add_string b ": ";
        write_pretty b (indent + 1) x)
      fields;
    Buffer.add_char b '\n';
    Buffer.add_string b (pad indent);
    Buffer.add_char b '}'
  | leaf -> write b leaf

let to_string_pretty (v : t) : string =
  let b = Buffer.create 256 in
  write_pretty b 0 v;
  Buffer.contents b

(* ------------------------------------------------------------------------ parsing *)

type state = { src : string; mutable pos : int }

let fail st msg =
  raise (Parse_error (Printf.sprintf "%s at byte %d" msg st.pos))

let peek st = if st.pos < String.length st.src then Some st.src.[st.pos] else None

let rec skip_ws st =
  match peek st with
  | Some (' ' | '\t' | '\n' | '\r') -> st.pos <- st.pos + 1; skip_ws st
  | _ -> ()

let expect st c =
  if peek st = Some c then st.pos <- st.pos + 1
  else fail st (Printf.sprintf "expected %c" c)

let literal st word value =
  let n = String.length word in
  if st.pos + n <= String.length st.src && String.sub st.src st.pos n = word then begin
    st.pos <- st.pos + n;
    value
  end
  else fail st ("expected " ^ word)

let hex4 st =
  if st.pos + 4 > String.length st.src then fail st "truncated \\u escape";
  let v = int_of_string ("0x" ^ String.sub st.src st.pos 4) in
  st.pos <- st.pos + 4;
  v

(* One UTF-8 encoding, so a \uXXXX escape survives the round trip. Surrogate pairs are
   joined; a lone surrogate is emitted as U+FFFD rather than raising. *)
let add_utf8 b cp =
  if cp < 0x80 then Buffer.add_char b (Char.chr cp)
  else if cp < 0x800 then begin
    Buffer.add_char b (Char.chr (0xC0 lor (cp lsr 6)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end
  else if cp < 0x10000 then begin
    Buffer.add_char b (Char.chr (0xE0 lor (cp lsr 12)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end
  else begin
    Buffer.add_char b (Char.chr (0xF0 lor (cp lsr 18)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 12) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor ((cp lsr 6) land 0x3F)));
    Buffer.add_char b (Char.chr (0x80 lor (cp land 0x3F)))
  end

let parse_string st =
  expect st '"';
  let b = Buffer.create 32 in
  let rec go () =
    match peek st with
    | None -> fail st "unterminated string"
    | Some '"' -> st.pos <- st.pos + 1
    | Some '\\' ->
      st.pos <- st.pos + 1;
      (match peek st with
       | Some '"' -> Buffer.add_char b '"'; st.pos <- st.pos + 1
       | Some '\\' -> Buffer.add_char b '\\'; st.pos <- st.pos + 1
       | Some '/' -> Buffer.add_char b '/'; st.pos <- st.pos + 1
       | Some 'n' -> Buffer.add_char b '\n'; st.pos <- st.pos + 1
       | Some 'r' -> Buffer.add_char b '\r'; st.pos <- st.pos + 1
       | Some 't' -> Buffer.add_char b '\t'; st.pos <- st.pos + 1
       | Some 'b' -> Buffer.add_char b '\b'; st.pos <- st.pos + 1
       | Some 'f' -> Buffer.add_char b '\012'; st.pos <- st.pos + 1
       | Some 'u' ->
         st.pos <- st.pos + 1;
         let hi = hex4 st in
         if hi >= 0xD800 && hi <= 0xDBFF then begin
           if st.pos + 1 < String.length st.src && st.src.[st.pos] = '\\'
              && st.src.[st.pos + 1] = 'u' then begin
             st.pos <- st.pos + 2;
             let lo = hex4 st in
             if lo >= 0xDC00 && lo <= 0xDFFF then
               add_utf8 b (0x10000 + ((hi - 0xD800) lsl 10) + (lo - 0xDC00))
             else add_utf8 b 0xFFFD
           end
           else add_utf8 b 0xFFFD
         end
         else add_utf8 b hi
       | _ -> fail st "bad escape");
      go ()
    | Some c -> Buffer.add_char b c; st.pos <- st.pos + 1; go ()
  in
  go ();
  Buffer.contents b

let parse_number st =
  let start = st.pos in
  let is_float = ref false in
  let rec go () =
    match peek st with
    | Some ('0' .. '9' | '-' | '+') -> st.pos <- st.pos + 1; go ()
    | Some ('.' | 'e' | 'E') -> is_float := true; st.pos <- st.pos + 1; go ()
    | _ -> ()
  in
  go ();
  let text = String.sub st.src start (st.pos - start) in
  if text = "" then fail st "expected a number";
  if !is_float then Float (float_of_string text)
  else match int_of_string_opt text with Some n -> Int n | None -> Float (float_of_string text)

let rec parse_value st =
  skip_ws st;
  match peek st with
  | None -> fail st "unexpected end of input"
  | Some '{' ->
    st.pos <- st.pos + 1;
    skip_ws st;
    if peek st = Some '}' then (st.pos <- st.pos + 1; Obj [])
    else begin
      let fields = ref [] in
      let rec go () =
        skip_ws st;
        let key = parse_string st in
        skip_ws st;
        expect st ':';
        let v = parse_value st in
        fields := (key, v) :: !fields;
        skip_ws st;
        match peek st with
        | Some ',' -> st.pos <- st.pos + 1; go ()
        | Some '}' -> st.pos <- st.pos + 1
        | _ -> fail st "expected , or }"
      in
      go ();
      Obj (List.rev !fields)
    end
  | Some '[' ->
    st.pos <- st.pos + 1;
    skip_ws st;
    if peek st = Some ']' then (st.pos <- st.pos + 1; List [])
    else begin
      let items = ref [] in
      let rec go () =
        let v = parse_value st in
        items := v :: !items;
        skip_ws st;
        match peek st with
        | Some ',' -> st.pos <- st.pos + 1; go ()
        | Some ']' -> st.pos <- st.pos + 1
        | _ -> fail st "expected , or ]"
      in
      go ();
      List (List.rev !items)
    end
  | Some '"' -> Str (parse_string st)
  | Some 't' -> literal st "true" (Bool true)
  | Some 'f' -> literal st "false" (Bool false)
  | Some 'n' -> literal st "null" Null
  | Some _ -> parse_number st

let of_string (s : string) : t =
  let st = { src = s; pos = 0 } in
  let v = parse_value st in
  skip_ws st;
  if st.pos <> String.length s then fail st "trailing input";
  v

(* --------------------------------------------------------------------- accessors *)

let member (key : string) (v : t) : t =
  match v with Obj fields -> (match List.assoc_opt key fields with Some x -> x | None -> Null)
             | _ -> Null

let to_string_opt = function Str s -> Some s | _ -> None
let to_int_opt = function Int n -> Some n | Float f -> Some (int_of_float f) | _ -> None
let to_bool_opt = function Bool b -> Some b | _ -> None
let to_list = function List xs -> xs | Null -> [] | x -> [ x ]

let str ?(default = "") key v = match member key v with Str s -> s | _ -> default
let int_ ?(default = 0) key v = match to_int_opt (member key v) with Some n -> n | None -> default
let bool_ ?(default = false) key v =
  match to_bool_opt (member key v) with Some b -> b | None -> default

let strings key v = List.filter_map to_string_opt (to_list (member key v))
let of_strings xs = List (List.map (fun s -> Str s) xs)
let of_ints xs = List (List.map (fun n -> Int n) xs)
