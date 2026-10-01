
(* Probe U instrument (appended, not production text): which constructors of `ty` rand_ty
   reaches at the top of 2000 samples of depth 3, by Eff_types' own ordinal table. *)
let () =
  let names = Array.of_list Eff_types.ctor_names_ty in
  let seen = Array.make (Array.length names) false in
  for _ = 1 to 2000 do seen.(Eff_types.ctor_index_ty (rand_ty 3)) <- true done;
  let missing = List.filter (fun i -> not seen.(i)) (List.init (Array.length names) Fun.id) in
  Printf.printf "rand_ty coverage: %d of %d constructors; missing: [%s]\n%!"
    (Array.length names - List.length missing) (Array.length names)
    (String.concat "; " (List.map (fun i -> names.(i)) missing))
