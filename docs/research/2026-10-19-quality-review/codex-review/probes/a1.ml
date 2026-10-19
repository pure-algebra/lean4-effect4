open Eff_types
open Effect4_kit
open Effect4_engine_cas
module A = Kit_author
module G = Effect4_gen.Api_gen

let show = function
  | Kit.Finished (Exit.Success (Val.Nat n)) -> Printf.sprintf "finished Nat %d" n
  | Kit.Finished (Exit.Success (Val.NegInt n)) -> Printf.sprintf "finished NegInt %d" n
  | Kit.Stopped s -> "stopped " ^ s
  | Kit.Refused _ -> "refused"
  | _ -> "other"

let () =
  let row = A.row "source" ~request:Ty.Unit ~answer:Ty.Int () in
  let app = Kit.app ~rows:[row] () in
  let source = A.(let* x = perform "source" unit in
    succeed (atom "minus" [atom "minus" [nat 0; nat 1]; x])) in
  let p = match A.build ~app source with Ok p -> p | Error e -> failwith (A.refusal_text e) in
  let bytes = Eff_wire.encode_program p in
  let p = Option.get (Eff_wire.decode_program_exact bytes) in
  let v = Option.get (Eff_val.decode_exact (Eff_val.to_bytes (Val.NegInt max_int))) in
  Printf.printf "wire program admitted=%b; wire answer=NegInt max_int; reply_fault=%b\n"
    (Option.is_none (Kit.admit app p)) (Option.is_some (Kit.reply_fault app 0 (Kit.succeed v)));
  List.iter (fun check ->
    let r = Kit.run ~limit:8 ~check app Kit.Reactor.tape [Kit.succeed v] p in
    Printf.printf "tape check=%b: %s; agrees=%s\n" check (show r.trace.stop)
      (match r.agrees with None -> "none" | Some b -> string_of_bool b)) [false;true];
  let r = Kit.run ~limit:8 ~check:false app (fun _ _ () -> Some (Completion.OfExit (Kit.succeed v), ())) () p in
  Printf.printf "native host: %s\n" (show r.trace.stop);
  List.iter (fun n ->
    let p = match A.build A.(succeed (nat n + nat 1)) with Ok p -> p | Error _ -> assert false in
    let p = Option.get (Eff_wire.decode_program_exact (Eff_wire.encode_program p)) in
    (try let r = Kit.run ~limit:4 ~check:false (Kit.app ()) Kit.Reactor.silent () p in
       Printf.printf "profile add %d + 1: %s\n" n (show r.trace.stop)
     with E4_clock.Profile_refusal why -> Printf.printf "profile add %d + 1: refusal %s\n" n (E4_clock.refusal_text why)))
    [9007199254740991; max_int];
  List.iter (fun f ->
    let bits = Int64.bits_of_float f in
    let narrowed = Int64.to_int bits in
    let bytes = Eff_val.to_bytes (Val.Float narrowed) in
    let wire = Bytes.create 17 in
    Bytes.set wire 0 (Char.chr 14); Bytes.set_int64_be wire 1 8L; Bytes.set_int64_be wire 9 bits;
    Printf.printf "float %g bits=%Lx carrier=%d reencoded=%s store_payload_ok=%b eff_val_decode=%b\n"
      f bits narrowed (E4_sha256.hex bytes)
      (Result.is_ok (E4_node.payload_ok (Bytes.to_string wire)))
      (Option.is_some (Eff_val.decode_exact (Bytes.to_string wire)))) [0.5; -0.5; 2.5; -0.0];
  List.iter (fun s -> match Kit.Json.parse s with
    | Ok (Kit.Json.NatJson_nat n) -> Printf.printf "json %s => nat %d\n" s n
    | Ok (Kit.Json.NatJson_numeral _) -> Printf.printf "json %s => numeral (carrier refuses)\n" s
    | _ -> Printf.printf "json %s => other\n" s) ["4611686018427387903";"13826050856027422720"]
