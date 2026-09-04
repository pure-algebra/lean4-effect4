(* O3 witness: char, string, bytes. Native: String_tag 252, a byte array with
   the length in the last byte (mlvalues.h:328). js_of_ocaml with the default
   use-js-string=true (config.ml:93) is a JS string of code units 0..255 --
   caml_string_of_jsbytes is the identity (mlBytes.js:707-709); with
   --disable use-js-string it is an MlBytes record {t;c;l} (mlBytes.js:410-414). *)
let p k v = Printf.printf "%s\t%s\n" k v
let opaque = Sys.opaque_identity
let codes s =
  String.concat "," (List.init (String.length s) (fun i -> string_of_int (Char.code s.[i])))

let () =
  let ascii = opaque "abc" in
  let utf8 = opaque "h\xc3\xa9llo" in          (* "héllo" as UTF-8 bytes *)
  let euro = opaque "\xe2\x82\xac" in          (* U+20AC EURO SIGN *)
  p "len_ascii" (string_of_int (String.length ascii));
  p "len_utf8" (string_of_int (String.length utf8));
  p "len_euro" (string_of_int (String.length euro));
  p "codes_utf8" (codes utf8);
  p "codes_euro" (codes euro);
  p "get_utf8_1" (string_of_int (Char.code utf8.[1]));
  p "sub_utf8" (codes (String.sub utf8 1 2));
  p "char_code_a" (string_of_int (Char.code 'a'));
  p "char_chr_255" (string_of_int (Char.code (Char.chr 255)));
  p "char_chr_0" (string_of_int (Char.code (Char.chr 0)));
  p "char_compare" (string_of_int (compare (opaque 'a') 'b'));
  p "str_len_with_nul" (string_of_int (String.length (opaque "a\x00b")));
  p "codes_with_nul" (codes (opaque "a\x00b"));
  p "concat" (codes (ascii ^ euro));
  p "string_compare_lt" (string_of_int (compare (opaque "abc") "abd"));
  p "string_compare_prefix" (string_of_int (compare (opaque "ab") "abc"));
  p "string_compare_high" (string_of_int (compare (opaque "\xff") "\x01"));
  p "string_equal" (string_of_bool (opaque "abc" = String.sub "xabcx" 1 3));
  p "string_phys_eq" (string_of_bool (opaque "abc" == String.sub "xabcx" 1 3));
  let b = Bytes.of_string "abc" in
  Bytes.set b 1 'Z';
  p "bytes_mutated" (Bytes.to_string b);
  p "bytes_mutated_codes" (codes (Bytes.to_string b));
  let b2 = Bytes.create 3 in
  Bytes.fill b2 0 3 '\x00';
  Bytes.set b2 0 '\xff';
  p "bytes_created_codes" (codes (Bytes.to_string b2));
  p "bytes_len" (string_of_int (Bytes.length b2));
  p "bytes_blit" (let d = Bytes.create 5 in
                  Bytes.fill d 0 5 '.';
                  Bytes.blit_string "xy" 0 d 2 2; Bytes.to_string d);
  p "string_tag" (string_of_int (Obj.tag (Obj.repr ascii)));
  p "bytes_tag" (string_of_int (Obj.tag (Obj.repr b)));
  p "string_uppercase_utf8" (codes (String.uppercase_ascii utf8));
  p "string_index_of_high" (string_of_int (String.index utf8 '\xc3'))
