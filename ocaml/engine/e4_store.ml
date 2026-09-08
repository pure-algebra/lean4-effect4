(* E4_store — the Ref heap, the Deferred cells and the Scope entries over E4_table.
   The property list is in e4_store.mli. *)

type 'a t = 'a E4_table.t

let empty : 'a t = E4_table.empty
let to_list (t : 'a t) : 'a list = E4_table.to_list t
let cardinal (t : 'a t) : int = E4_table.cardinal t
let bindings (t : 'a t) : (int * 'a) list = E4_table.bindings t

(* --- the Ref heap (Stores.lean:1116, :1119-1120, :1150) --- *)

let peek (k : int) (h : 'a t) : 'a option = E4_table.find_opt k h
let poke (k : int) (v : 'a) (h : 'a t) : 'a t = E4_table.set k v h

let grow (v : 'a) (h : 'a t) : int * 'a t =
  let key = E4_table.cardinal h in
  (key, E4_table.add key v h)

(* --- the Deferred cells (Stores.lean:1365-1374) --- *)

let cell_at (k : int) (d : 'a t) : 'a option = E4_table.find_opt k d
let set_cell (k : int) (v : 'a) (d : 'a t) : 'a t = E4_table.set k v d

let make_cell (v : 'a) (d : 'a t) : int * 'a t =
  let key = E4_table.cardinal d in
  (key, E4_table.add key v d)

(* --- the Scope entries (Stores.lean:1567-1576, :1605-1607) --- *)

let entry_at (k : int) (s : 'a t) : 'a option = E4_table.find_opt k s
let set_entry (k : int) (v : 'a) (s : 'a t) : 'a t = E4_table.set k v s
let add_entry (k : int) (v : 'a) (s : 'a t) : 'a t = E4_table.add k v s
