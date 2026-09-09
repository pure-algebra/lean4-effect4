(* Independent OCaml oracle check. Properties: every .eff has an exact decoder result,
   the decoded program prints precisely its sibling Lean JSON, discovery is nonempty. *)
let read file =
  let ch = open_in_bin file in
  let s = really_input_string ch (in_channel_length ch) in
  close_in ch; s
let () =
  let count = ref 0 in
  Array.iteri (fun i dir -> if i > 0 then
    Array.iter (fun name -> if Filename.check_suffix name ".eff" then begin
      incr count;
      let file = Filename.concat dir name in
      let expected = Filename.concat dir (Filename.chop_suffix name ".eff" ^ ".json") in
      match Eff_wire.decode_program_exact (read file) with
      | None -> failwith ("OCaml exact decoder refused " ^ file)
      | Some p -> if Eff_json.print_eff p <> String.trim (read expected) then
          failwith ("OCaml JSON disagrees with Lean: " ^ file)
    end) (Sys.readdir dir)) Sys.argv;
  if !count = 0 then failwith "empty corpus";
  Printf.printf "PASS OCaml exact decoder and JSON oracle: %d programs\n" !count
