(* A thin observer of the existing Eff decoder, encoder and type checker.
   Depends only on the production effect4_eff modules, copied and compiled in a
   temporary directory by the G2 receipt command. It owns no wire recursion.
   Properties: every requested file yields one row (by construction); decoded
   values, exact re-encoding and trailing-byte refusal are reported separately
   from the checker's inferred type (tested against retained historical inputs).
   No execution or host permission is inferred from successful decoding. *)

let read path =
  let channel = open_in_bin path in
  let bytes = really_input_string channel (in_channel_length channel) in
  close_in channel;
  bytes

let observe path =
  let open Eff_json_text in
  let bytes = read path in
  let result = match Eff_wire.decode_program_exact bytes with
    | None -> ["decoded", Bool false]
    | Some program ->
      ["decoded", Bool true;
       "program", String (Eff_json.print_eff program);
       "reencoded", Bool (Eff_wire.encode_program program = bytes);
       "trailing_refused", Bool (Eff_wire.decode_program_exact (bytes ^ "\000") = None);
       "type", String (Eff_typing.print_type program)]
  in
  print_endline (render (Object (("file", String (Filename.basename path)) :: result)))

let () = Array.iteri (fun index path -> if index > 0 then observe path) Sys.argv
