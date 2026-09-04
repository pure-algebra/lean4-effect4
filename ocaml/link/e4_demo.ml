(* e4_demo.ml — a thin driver: (a) four machines across two domains, (b) the cross-machine
   message. Everything it does is one call into the library; it only prints. *)

let section title = Printf.printf "\n==== %s ====\n%!" title

let print_status host id =
  match E4_host.inspect host id with
  | None -> Printf.printf "m%d: unknown\n" id
  | Some (s : E4_worker.status) ->
      Printf.printf "m%d %s @d%d: finished=%b steps=%d trace=%d armed=[%s]\n" s.id s.program s.domain s.finished
        s.steps s.trace_len
        (String.concat "," (List.map string_of_int s.armed));
      List.iter (fun f -> Printf.printf "    %s\n" (E4_bridge.pp_fiber f)) s.fibers

let print_log host =
  let entries, gap = E4_host.events host in
  Printf.printf "merged event log (%d rows%s), ordered by seq:\n" (List.length entries)
    (if gap then ", a ring overflowed" else "");
  Printf.printf "  %4s  %-6s  %-10s  %s\n" "seq" "where" "decision" "row";
  List.iter
    (fun (e : E4_ring.entry) ->
      Printf.printf "  %4d  m%d@d%d  %-10s  %s\n" e.seq e.machine e.domain e.decision e.row)
    entries

let part_a () =
  section "(a) four machines, two domains: evaluate + flush each, fires from the event-loop rule";
  let host = E4_host.start { E4_host.default_config with domains = 2 } in
  let fuel = 100 in
  let ids = List.map (fun program -> E4_host.spawn host ~program ~fuel) [ "pFork"; "pTwo"; "pFork"; "pTwo" ] in
  List.iter
    (fun id ->
      let d = Option.get (E4_host.domain_of host id) in
      Printf.printf "spawned m%d on d%d\n" id d)
    ids;
  List.iter
    (fun id ->
      List.iter
        (fun decision ->
          match E4_host.send host id decision with
          | Ok seq -> Printf.printf "send m%d %-8s -> seq %d\n" id (E4_bridge.to_wire decision) seq
          | Error `Full -> Printf.printf "send m%d refused: full\n" id
          | Error `Unknown -> Printf.printf "send m%d refused: unknown\n" id
          | Error `Stopped -> Printf.printf "send m%d refused: stopped\n" id)
        [ E4_bridge.Evaluate; E4_bridge.Flush ])
    ids;
  let ok = E4_host.run_until_quiescent ~timeout:10.0 host in
  Printf.printf "quiescent: %b (pending=%d, fire refusals=%d)\n" ok
    (E4_quiescence.outstanding (E4_host.pending host))
    (E4_host.refusals host);
  List.iter (print_status host) ids;
  print_log host;
  E4_host.shutdown host;
  ok

let part_a' () =
  section "(a') the event-loop rule alone: evaluate only, the fires come from the worker";
  let host = E4_host.start { E4_host.default_config with domains = 2 } in
  let fuel = 100 in
  let ids = List.map (fun program -> E4_host.spawn host ~program ~fuel) [ "pFork"; "pTwo" ] in
  List.iter
    (fun id ->
      match E4_host.send host id E4_bridge.Evaluate with
      | Ok seq -> Printf.printf "send m%d evaluate -> seq %d (and nothing else)\n" id seq
      | Error _ -> Printf.printf "send m%d refused\n" id)
    ids;
  let ok = E4_host.run_until_quiescent ~timeout:10.0 host in
  Printf.printf "quiescent: %b\n" ok;
  List.iter (print_status host) ids;
  let entries, _ = E4_host.events host in
  Printf.printf "decisions applied, by seq (the fires were queued by the rule, not sent):\n";
  List.iter
    (fun (seq, machine, decision) -> Printf.printf "  %4d  m%d  %s\n" seq machine decision)
    (List.sort_uniq compare (List.map (fun (e : E4_ring.entry) -> (e.seq, e.machine, e.decision)) entries));
  let finished =
    List.for_all
      (fun id -> match E4_host.inspect host id with Some { finished = true; _ } -> true | _ -> false)
      ids
  in
  E4_host.shutdown host;
  ok && finished

let part_b () =
  section "(b) the cross-machine message: A parks (pAwait), B finishes (pFork), B's finish answers A";
  let host = E4_host.start { E4_host.default_config with domains = 2 } in
  let fuel = 100 in
  let a = E4_host.spawn ~domain:0 host ~program:"pAwait" ~fuel in
  ignore (E4_host.send host a E4_bridge.Evaluate);
  ignore (E4_host.run_until_quiescent ~timeout:10.0 host);
  Printf.printf "A = m%d pAwait on d0, after evaluate:\n" a;
  print_status host a;
  let token =
    match E4_host.inspect host a with
    | Some { fibers = { id = 0; parked_token = Some t; _ } :: _; _ } -> t
    | _ -> failwith "A's root fiber is not parked"
  in
  Printf.printf "A's root fiber is parked on token %d\n" token;
  let b = E4_host.spawn ~domain:1 host ~program:"pFork" ~fuel in
  let answered = ref None in
  E4_host.subscribe_finished host (fun id ->
      if id = b then begin
        let answer = E4_bridge.Answer { fiber = 0; token; value = 7 } in
        match E4_host.send host a answer with
        | Ok seq ->
            answered := Some seq;
            Printf.printf "hook on d1: m%d finished -> send m%d %s (seq %d)\n" b a (E4_bridge.to_wire answer) seq
        | Error _ -> Printf.printf "hook: send to m%d refused\n" a
      end);
  Printf.printf "B = m%d pFork on d1: evaluate + flush\n" b;
  ignore (E4_host.send host b E4_bridge.Evaluate);
  ignore (E4_host.send host b E4_bridge.Flush);
  let ok = E4_host.run_until_quiescent ~timeout:10.0 host in
  Printf.printf "quiescent: %b\n" ok;
  print_status host b;
  print_status host a;
  let a_ok =
    match E4_host.inspect host a with
    | Some { finished = true; fibers = { id = 0; exit = Some (E4_bridge.Success tag); _ } :: _; _ } ->
        Printf.printf "A finished with %s (nat %s)\n" tag
          (match E4_bridge.nat_of_tag tag with Some n -> string_of_int n | None -> "?");
        E4_bridge.nat_of_tag tag = Some 7
    | _ ->
        Printf.printf "A did not finish with a value\n";
        false
  in
  print_log host;
  E4_host.shutdown host;
  ok && !answered <> None && a_ok

let () =
  let a = part_a () in
  let a' = part_a' () in
  let b = part_b () in
  section "result";
  Printf.printf "(a) %s  (a') %s  (b) %s\n" (if a then "ok" else "FAILED") (if a' then "ok" else "FAILED")
    (if b then "ok" else "FAILED");
  if not (a && a' && b) then exit 1
