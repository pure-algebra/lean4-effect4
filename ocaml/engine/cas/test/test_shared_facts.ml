(* Properties: generated facts agree with node-reader refusal cases.
   This finite probe uses actual native node bytes and keeps capacity outside Admission.
   The byte mapping mutation must fail the unknown-tag control. *)
open Effect4_engine_cas

let require condition message = if not condition then failwith message

let read bytes =
  match E4_node.decode bytes with
  | Ok _ -> failwith "expected byte refusal"
  | Error why -> E4_admission.of_decode why

let frame = E4_be.framed

let () =
  require (List.length E4_kind.all = 23) "kind census";
  List.iter (fun k -> require (E4_kind.of_byte (E4_kind.byte k) = Some k) "kind round trip") E4_kind.all;
  require (List.filter E4_kind.is_run_relative E4_kind.all =
    [E4_kind.Tape; E4_kind.Log; E4_kind.Exits; E4_kind.Checkpoint]) "run-relative kinds";
  require (List.filter E4_kind.tombstoned E4_kind.all = [E4_kind.Fiber]) "tombstone";
  require (List.filter E4_kind.is_interior E4_kind.all = [E4_kind.Chunk]) "interior kind";
  require (E4_kind.of_byte E4_kind.sentinel = None) "sentinel";
  require (E4_kind.of_name "Export" = None) "case-sensitive name";
  require (read "\001\127" = E4_admission.Model E4_admission.Bad_version) "version first";
  require (read "\000\127" = E4_admission.Model (E4_admission.Unregistered_kind 127)) "kind before short spec";
  require (read "\000\004" = E4_admission.Model E4_admission.Short_spec) "short spec";
  let prefix = "\000\004" ^ E4_node.zero_digest in
  require (read (prefix ^ frame 253 "") = E4_admission.Model (E4_admission.Unknown_tag 253)) "unknown tag stays distinct";
  require (read (prefix ^ frame 4 (frame 253 "")) = E4_admission.Model (E4_admission.Unknown_tag 253)) "nested unknown tag";
  require (read (prefix ^ frame 1 "\001" ^ "\000") = E4_admission.Model E4_admission.Trailing) "trailing byte";
  require (read (prefix ^ "\001") = E4_admission.Model E4_admission.Bad_frame) "bad frame";
  require (match E4_admission.of_decode E4_node.Host_limit with
    | E4_admission.Capacity _ -> true | _ -> false) "capacity outside model";
  require (E4_root_policy.all = [E4_root_policy.Swap; E4_root_policy.Journal; E4_root_policy.Pin]) "policy alphabet";
  List.iter (fun (policy, byte, name) ->
    require (E4_root_policy.byte policy = byte) "policy byte";
    require (E4_root_policy.of_byte byte = Some policy) "policy byte round trip";
    require (E4_root_policy.name policy = name) "policy name")
    [E4_root_policy.Swap, 0, "swap"; E4_root_policy.Journal, 1, "journal"; E4_root_policy.Pin, 2, "pin"];
  require (E4_root_policy.of_byte 6 = None) "legacy pin byte stays outside new policy";
  let large = Z.shift_left Z.one 100 in
  let head : E4_control.head = {digest = E4_addr.Addr.zero; generation = large} in
  require (Z.equal (Z.sub (Z.succ head.generation) head.generation) Z.one) "exact head generation";
  print_endline "shared facts: kind, policy and node refusal controls passed"
