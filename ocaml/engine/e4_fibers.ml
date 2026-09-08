(* E4_fibers — the fiber table over E4_table.  The property list is in e4_fibers.mli. *)

type 'f t = 'f E4_table.t

let empty : 'f t = E4_table.empty
let find (id : int) (t : 'f t) : 'f option = E4_table.find_opt id t
let find_opt' (t : 'f t) (id : int) : 'f option = E4_table.find_opt id t
let update_at (id : int) (f : 'f) (t : 'f t) : 'f t = E4_table.set id f t
let update ~(id_of : 'f -> int) (f : 'f) (t : 'f t) : 'f t = E4_table.set (id_of f) f t
let append (id : int) (f : 'f) (t : 'f t) : 'f t = E4_table.add id f t

let finished ~(exit_of : 'f -> 'x option) (t : 'f t) : bool =
  E4_table.for_all (fun _ f -> match exit_of f with Some _ -> true | None -> false) t

let completed_exits ~(id_of : 'f -> int) ~(exit_of : 'f -> 'x option) (t : 'f t) :
    (int * 'x) list =
  E4_table.filter_map
    (fun _ f -> match exit_of f with Some ex -> Some (id_of f, ex) | None -> None)
    t

let drop_observers (step : 'f -> 'f) (t : 'f t) : 'f t = E4_table.map step t
let map (f : 'f -> 'f) (t : 'f t) : 'f t = E4_table.map f t
let for_all (p : 'f -> bool) (t : 'f t) : bool = E4_table.for_all (fun _ f -> p f) t

let filter_map (p : 'f -> 'b option) (t : 'f t) : 'b list =
  E4_table.filter_map (fun _ f -> p f) t

let to_list (t : 'f t) : 'f list = E4_table.to_list t
let bindings (t : 'f t) : (int * 'f) list = E4_table.bindings t
let cardinal (t : 'f t) : int = E4_table.cardinal t
