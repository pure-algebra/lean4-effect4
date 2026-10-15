(* Pure Eio resource provider probe. No OS resources or program syntax.
   Tested: typed provider dispatch, optional unsupported interface,
   and the public phantom-tag construction trust boundary. *)

type lookup_ty = [`Lookup]
type (_, _, _) Eio.Resource.pi +=
  Lookup : ('t, 't -> int -> string option, [> lookup_ty]) Eio.Resource.pi

let lookup (Eio.Resource.T (state, ops) : [> lookup_ty] Eio.Resource.t) key =
  Eio.Resource.get ops Lookup state key

let honest : lookup_ty Eio.Resource.t =
  let find state key = List.assoc_opt key state in
  Eio.Resource.T ([(1, "one")], Eio.Resource.handler [Eio.Resource.H (Lookup, find)])

let check name condition =
  if not condition then failwith ("FAILED: " ^ name);
  Printf.printf "PASS %s\n%!" name

let () =
  check "existential provider returns typed lookup answer" (lookup honest 1 = Some "one");
  let empty_handler = Eio.Resource.handler [] in
  check "optional lookup refuses an unsupported interface"
    (Option.is_none (Eio.Resource.get_opt empty_handler Lookup));
  let misleading : lookup_ty Eio.Resource.t = Eio.Resource.T ((), empty_handler) in
  let fails_at_dispatch =
    try ignore (lookup misleading 1); false
    with Failure message -> message = "Operation not supported!"
  in
  check "public constructor can claim a tag without its implementation" fails_at_dispatch
