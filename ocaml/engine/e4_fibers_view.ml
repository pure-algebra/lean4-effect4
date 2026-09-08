(* E4_fibers_view — the fiber table plus its maintained completed view.  The property list,
   the laws and the costs are in e4_fibers_view.mli. *)

module IMap = Map.Make (Int)

(* ONE record, not a table wrapped in a view.  `E4_table` is `{ n; rep }` with `rep` a
   `Small`/`Big` variant whose small arm is dead (lane C measured `small_max = 0`: the Map
   wins `find` and `add` from one entry up), so wrapping it would cost a second block on every
   write — and this carrier is written on essentially every step.  Flat, a write allocates
   FOUR words where the wrapped form allocates eight and `E4_table` alone allocates five.

   `n` is carried so `cardinal` is O(1), for the same reason lane C carries it (E4_table D5).
   `view` is the exits of the fibers whose exit is set, ASCENDING by id: exactly the value
   `RunMachine.completedExits` answers (src/Effect4/Machine/Fibers.lean:1543), maintained by
   every write, so `completed` is this field and nothing else (FV1). *)
type ('a, 'x) t = { n : int; m : 'a IMap.t; view : (int * 'x) list }

let empty : ('a, 'x) t = { n = 0; m = IMap.empty; view = [] }
let find_opt (k : int) (t : ('a, 'x) t) : 'a option = IMap.find_opt k t.m
let mem (k : int) (t : ('a, 'x) t) : bool = IMap.mem k t.m
let is_empty (t : ('a, 'x) t) : bool = t.n = 0
let cardinal (t : ('a, 'x) t) : int = t.n
let bindings (t : ('a, 'x) t) : (int * 'a) list = IMap.bindings t.m
let to_list (t : ('a, 'x) t) : 'a list = List.map snd (IMap.bindings t.m)
let for_all (f : int -> 'a -> bool) (t : ('a, 'x) t) : bool = IMap.for_all f t.m
let completed (t : ('a, 'x) t) : (int * 'x) list = t.view

(* The view's own edit: put `x` at `id` when it is `Some`, take the id out when it is `None`,
   keeping the list ascending.  Tail-recursive (a machine may hold a hundred thousand exited
   fibers and the stack is not a place to find that out).  It is reached ONLY when a fiber's
   exit actually changes — a write that leaves every exit alone never calls it (FV8). *)
let view_put (id : int) (x : 'x option) (l : (int * 'x) list) : (int * 'x) list =
  let rec go acc l =
    match l with
    | [] -> List.rev_append acc (match x with None -> [] | Some v -> [ (id, v) ])
    | (k, _) :: rest when k = id ->
      List.rev_append acc (match x with None -> rest | Some v -> (id, v) :: rest)
    | (k, _) :: _ when k > id ->
      List.rev_append acc (match x with None -> l | Some v -> (id, v) :: l)
    | e :: rest -> go (e :: acc) rest
  in
  go [] l

(* The view derived from the table by the scan it replaces — FV1's right-hand side.  `map` is
   the one operation that has to use it, because the mapping function may change any exit. *)
let derive ~(exit_of : 'a -> 'x option) (m : 'a IMap.t) : (int * 'x) list =
  List.rev
    (IMap.fold
       (fun k v acc -> match exit_of v with None -> acc | Some x -> (k, x) :: acc)
       m [])

(* `RunMachine.update` (Fibers.lean:577-579): the replace-by-key map, a NO-OP on an absent id
   (FV2).  `IMap.update` answering `None` rebuilds nothing and the stdlib's `if l == ll then m`
   gives the absent case back PHYSICALLY, which is what makes the no-op exact.

   The view changes only when this fiber's exit does, and the test for that is PHYSICAL:
   `f.exit` is a field read, so a fiber rebuilt as `{ f with observers = … }` hands back the
   very same option block and the view is shared on (FV8).  When the two are not physically
   equal the view is rewritten, which is correct whether or not they are structurally equal. *)
let set ~(exit_of : 'a -> 'x option) (k : int) (v : 'a) (t : ('a, 'x) t) : ('a, 'x) t =
  let x = exit_of v in
  match x, t.view with
  | None, [] ->
    (* Nothing has exited and this write does not exit anything, so the view cannot move and
       the old value need not be read at all.  This is the write the machine does on almost
       every step, and it costs less than a `TABLE.set` did. *)
    let m = IMap.update k (function None -> None | Some _ -> Some v) t.m in
    if m == t.m then t else { t with m }
  | _ ->
    let old = ref None in
    let m = IMap.update k (function None -> None | Some o -> old := Some o; Some v) t.m in
    if m == t.m then t
    else
      let same = match !old with None -> false | Some o -> x == exit_of o in
      if same then { t with m } else { n = t.n; m; view = view_put k x t.view }

(* `spawn`'s `m.fibers ++ [child]` (Fibers.lean:877) and `Api.load`'s root: an insertion at a
   freshly minted id.  Written to be right at a key that is already there as well, because
   `add` is not documented to refuse one. *)
let add ~(exit_of : 'a -> 'x option) (k : int) (v : 'a) (t : ('a, 'x) t) : ('a, 'x) t =
  let x = exit_of v in
  let old = ref None in
  let fresh = ref true in
  let m = IMap.update k (function
    | None -> Some v
    | Some o -> fresh := false; old := Some o; Some v) t.m
  in
  let n = if !fresh then t.n + 1 else t.n in
  match x, t.view with
  | None, [] -> { n; m; view = [] }
  | _ ->
    let same = match !old with None -> (match x with None -> true | Some _ -> false)
                            | Some o -> x == exit_of o in
    if same then { n; m; view = t.view } else { n; m; view = view_put k x t.view }

(* `dropObservers`' bulk `fibers.map` (Fibers.lean:1256, :1344).  Id-preserving, and the view
   is re-derived rather than remapped: `f` is the caller's, so it may set or clear an exit,
   and FV1 must hold for every `f`.  Θ(N), which the map itself already is. *)
let map ~(exit_of : 'a -> 'x option) (f : 'a -> 'a) (t : ('a, 'x) t) : ('a, 'x) t =
  let m = IMap.map f t.m in
  { n = t.n; m; view = derive ~exit_of m }

let of_list ~(exit_of : 'a -> 'x option) (l : (int * 'a) list) : ('a, 'x) t =
  List.fold_left (fun t (k, v) -> add ~exit_of k v t) empty l
