(* Public-interface controls for Lcnf_interface.
   Depends on the compiled fixtures. Tests abstract packages, hidden helpers,
   last-binding ascriptions, missing roots, retained prelude values, and a facade's reachable
   types. *)

let contains text part =
  let rec loop index =
    index + String.length part <= String.length text
    && (String.equal (String.sub text index (String.length part)) part || loop (index + 1))
  in
  loop 0
;;

let get = function
  | Ok value -> value
  | Error why -> failwith (Lcnf_interface.message why)
;;

let () =
  let cmt = Sys.argv.(1) in
  let infer roots abstract_types prelude =
    Lcnf_interface.generate ~types:Lcnf_interface.All ~cmt ~roots ~abstract_types ~prelude
  in
  let signature = get (infer [ "empty" ] [ "memo" ] None) in
  assert (contains signature "type memo");
  assert (contains signature "type public_alias = memo");
  assert (contains signature "val empty : memo");
  assert (not (contains signature "val helper"));
  assert (not (contains signature "val empty : '"));
  assert (
    match infer [ "missing" ] [ "memo" ] None with
    | Error (Lcnf_interface.Missing_values [ "missing" ]) -> true
    | _ -> false);
  assert (
    match infer [ "empty" ] [ "missing" ] None with
    | Error (Lcnf_interface.Missing_types [ "missing" ]) -> true
    | _ -> false);
  let prelude = get (infer [ "empty" ] [ "memo" ] (Some Sys.argv.(2))) in
  assert (contains prelude "val helper : memo -> memo");
  (* I6: a facade over the fixture keeps the type its root names and drops the one no root
     names; with every type kept, the dropped one is back. *)
  let facade types =
    Lcnf_interface.generate
      ~types
      ~cmt:Sys.argv.(3)
      ~roots:[ "helper" ]
      ~abstract_types:[]
      ~prelude:None
  in
  let reachable = get (facade Lcnf_interface.Reachable) in
  assert (contains reachable "type memo");
  assert (contains reachable "val helper : memo -> memo");
  assert (not (contains reachable "public_alias"));
  assert (not (contains reachable "val empty"));
  assert (contains (get (facade Lcnf_interface.All)) "public_alias");
  print_endline
    "Interface roots, sealing, final ascriptions, refusals and facade types pass."
;;
