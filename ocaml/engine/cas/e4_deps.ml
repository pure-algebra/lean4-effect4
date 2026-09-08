(* E4_deps — see e4_deps.mli.  A FACE over E4_index.Deps (lane P2), not a second index. *)

type t = E4_index.Deps.t

let fields_default = E4_shape.table

(* ---------------------------------------------------------------- building *)

let empty = E4_index.Deps.empty
let add (t : t) ~(dep : E4_addr.Addr.t) ~(by : E4_addr.Ref.t) : t = E4_index.Deps.add t ~dep ~by

let of_node ?(fields = fields_default) (n : E4_node.t) : E4_addr.Addr.t list =
  E4_index.Deps.of_node ~fields n

let add_node (t : t) ?(fields = fields_default) ~(at : E4_addr.Addr.t) (n : E4_node.t) : t =
  E4_index.Deps.add_node t ~fields ~at n

let of_nodes ?(fields = fields_default) (bs : (E4_addr.Addr.t * E4_node.t) list) : t =
  List.fold_left (fun acc (at, n) -> E4_index.Deps.add_node acc ~fields ~at n) empty bs

let of_store ?(fields = fields_default) (ro : E4_cas.ro) : t =
  of_nodes ~fields (E4_cas.nodes ro)

let rebuild ?(fields = fields_default) ~(from : int * int) (rd : E4_pack.reader) :
    t * E4_pack.scan_stop =
  E4_index.Deps.rebuild ~fields rd ~from

let rebuild_dir ?(fields = fields_default) (dir : string) : t * E4_pack.scan_stop =
  let rd = E4_pack.open_reader ~dir in
  let finish () = E4_pack.close_reader rd in
  match rebuild ~fields ~from:E4_index.from_start rd with
  | r ->
    finish ();
    r
  | exception e ->
    finish ();
    raise e

(* ---------------------------------------------------------------- querying *)

let find = E4_index.Deps.find
let mem = E4_index.Deps.mem
let cardinal = E4_index.Deps.cardinal
let edges = E4_index.Deps.edges
let iter = E4_index.Deps.iter
let dependents_of = find

let to_pairs (t : t) : (E4_addr.Addr.t * E4_addr.Ref.t list) list =
  let acc = ref [] in
  E4_index.Deps.iter t (fun dep bys -> acc := (dep, bys) :: !acc);
  List.sort (fun (a, _) (b, _) -> E4_addr.Addr.compare a b) !acc

let dependees (t : t) : E4_addr.Addr.t list = List.map fst (to_pairs t)

let rec refs_equal (a : E4_addr.Ref.t list) (b : E4_addr.Ref.t list) : bool =
  match (a, b) with
  | [], [] -> true
  | x :: xs, y :: ys -> E4_addr.Ref.equal x y && refs_equal xs ys
  | _ -> false

let equal (a : t) (b : t) : bool =
  let rec go x y =
    match (x, y) with
    | [], [] -> true
    | (da, ra) :: xs, (db, rb) :: ys ->
      E4_addr.Addr.equal da db && refs_equal ra rb && go xs ys
    | _ -> false
  in
  go (to_pairs a) (to_pairs b)

let refs_word (rs : E4_addr.Ref.t list) : string =
  "[" ^ String.concat " " (List.map E4_addr.Ref.present rs) ^ "]"

let diff (a : t) (b : t) : string option =
  let rec go x y =
    match (x, y) with
    | [], [] -> None
    | [], (db, _) :: _ ->
      Some (Printf.sprintf "only the second has a dependee %s" (E4_addr.Addr.hex db))
    | (da, _) :: _, [] ->
      Some (Printf.sprintf "only the first has a dependee %s" (E4_addr.Addr.hex da))
    | (da, ra) :: xs, (db, rb) :: ys ->
      if not (E4_addr.Addr.equal da db) then
        Some
          (Printf.sprintf "dependee %s vs %s" (E4_addr.Addr.hex da) (E4_addr.Addr.hex db))
      else if not (refs_equal ra rb) then
        Some
          (Printf.sprintf "at %s: %s vs %s" (E4_addr.Addr.hex da) (refs_word ra)
             (refs_word rb))
      else go xs ys
  in
  go (to_pairs a) (to_pairs b)
