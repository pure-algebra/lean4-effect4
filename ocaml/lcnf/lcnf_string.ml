(* Lcnf_string -- see lcnf_string.mli. The bodies are the ones the route printed into every
   generated file before slice 2.1; slice 3.2 gave a byte array its vector, `Lcnf_array`. *)

let utf8_bytes s =
  Lcnf_array.of_list (List.init (String.length s) (fun i -> Char.code (String.get s i)))

let utf8_length s =
  String.fold_left (fun n c -> if Char.code c land 192 = 128 then n else n + 1) 0 s

let of_code_points cs =
  let b = Buffer.create 16 in
  List.iter (fun c -> Buffer.add_utf_8_uchar b (Uchar.of_int c)) cs; Buffer.contents b

let of_utf8_bytes bs =
  let b = Buffer.create 16 in
  Lcnf_array.fold_left (fun () c -> Buffer.add_char b (Char.chr c)) () bs; Buffer.contents b
