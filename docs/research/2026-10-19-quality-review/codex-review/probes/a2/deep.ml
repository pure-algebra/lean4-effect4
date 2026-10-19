open Effect4_kit
module G = Effect4_gen.Api_gen
let get path = let i = open_in_bin path in Fun.protect ~finally:(fun () -> close_in i) (fun () -> really_input_string i (in_channel_length i))
let () =
 let s = get Sys.argv.(2) in
 try (match Sys.argv.(1) with
 | "wire" -> Printf.printf "accepted=%b\n" (Option.is_some (Eff_wire.decode_ty_exact s))
 | "json" -> Printf.printf "accepted=%b\n" (Result.is_ok (Kit.Json.parse s))
 | "mcp" -> Printf.printf "reply=%s\n" (Option.value (Kit_mcp.line (Kit_mcp.create ()) s) ~default:"none")
 | _ -> assert false)
 with e -> Printf.printf "EXCEPTION %s\n" (Printexc.to_string e); exit 2
