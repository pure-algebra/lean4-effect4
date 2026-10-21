(* prop_fibers_view.ml — the property tests of E4_fibers_view (lane G3, docs/research/
   2026-09-08-engine-lane-g3-delivery.md; laws FV1-FV9 of e4_fibers_view.mli).

   What is under test: the fiber table that MAINTAINS the completed view, so that
   `RunMachine.completedExits` (completedExits (src/Effect4/Machine/Fibers.lean)) is a field read instead
   of a Θ(N) scan on every step.  The model is the LEAN LIST ITSELF, written out here from
   Fibers.lean (`lean_completed`, `lean_update`, `lean_spawn`, `lean_drop`: allocation order,
   and `completedExits` is Lean's `filterMap` walked at read time), and the right-hand side of
   the law that matters — FV1 — is also read off the carrier's own table (`scan`).

   The FIBERS module type the generated functor takes is declared VERBATIM below and the
   carrier is ascribed to it, so a carrier that drifts from the seam stops compiling here.

   Exit code 0 iff every line passed. *)

open Effect4_engine

(* The seam's own text (src/OCaml5/Lcnf/Externs.lean, `carrierSignatures`), so this file fails
   to compile if the carrier stops satisfying it. *)
[@@@warning "-32"]
(* A module type used only for an ascription has, by definition, no used values. *)

module type FIBERS = sig
  type ('a, 'x) t

  val empty : ('a, 'x) t
  val find_opt : Z.t -> ('a, 'x) t -> 'a option
  val set : exit_of:('a -> 'x option) -> Z.t -> 'a -> ('a, 'x) t -> ('a, 'x) t
  val add : exit_of:('a -> 'x option) -> Z.t -> 'a -> ('a, 'x) t -> ('a, 'x) t
  val map : exit_of:('a -> 'x option) -> ('a -> 'a) -> ('a, 'x) t -> ('a, 'x) t
  val for_all : (Z.t -> 'a -> bool) -> ('a, 'x) t -> bool
  val completed : ('a, 'x) t -> (Z.t * 'x) list
  val cardinal : ('a, 'x) t -> Z.t
  val bindings : ('a, 'x) t -> (Z.t * 'a) list
  val to_list : ('a, 'x) t -> 'a list
  val of_list : exit_of:('a -> 'x option) -> (Z.t * 'a) list -> ('a, 'x) t
end

module _ : FIBERS = E4_fibers_view

[@@@warning "+32"]

(* The laws drive the carrier at the host's ints, each id a Lean natural exactly (`Z.of_int`,
   M4), and read every natural back (`Z.to_int`). `shared` is the carrier's own completed list,
   for the sharing laws (FV3, FV8): the view's `completed` is a fresh list of ints. *)
module V = struct
  module C = E4_fibers_view

  type ('a, 'x) t = ('a, 'x) C.t

  let z = Z.of_int
  let empty = C.empty
  let find_opt k t = C.find_opt (z k) t
  let set ~exit_of k v t = C.set ~exit_of (z k) v t
  let add ~exit_of k v t = C.add ~exit_of (z k) v t
  let map = C.map
  let for_all f t = C.for_all (fun k v -> f (Z.to_int k) v) t
  let completed t = List.map (fun (k, x) -> Z.to_int k, x) (C.completed t)
  let shared = C.completed
  let cardinal t = Z.to_int (C.cardinal t)
  let bindings t = List.map (fun (k, v) -> Z.to_int k, v) (C.bindings t)
  let to_list = C.to_list
  let of_list ~exit_of l = C.of_list ~exit_of (List.map (fun (k, v) -> z k, v) l)
end

let check = E4_check.check
let argue name why = Printf.printf "PASS %s [%s]\n" name why

(* Java's 48-bit LCG, as every other property suite in this directory. *)
let lcg_mask = 0xFFFFFFFFFFFF
let lcg_seed = 0x1234ABCD5678
let s = ref lcg_seed
let reset () = s := lcg_seed

let next () =
  s := ((!s * 25214903917) + 11) land lcg_mask;
  !s lsr 16
;;

let rand n = if n <= 0 then 0 else next () mod n

(* ------------------------------------------------------- the smallest fiber record.
   This independent carrier fixture records the three fields these laws observe: the id
   (RunMachine.fiber? (src/Effect4/Machine/Fibers.lean)), `RunMachine.finished`, `RunMachine.completedExits`, and `dropObservers`
   (src/Effect4/Machine/Fibers.lean). *)
type fiber =
  { id : int
  ; exit_ : int option
  ; observers : int list
  }

let exit_of f = f.exit_

(* ------------------------------------------------------------- Lean, written out *)

(* RunMachine.completedExits (completedExits (src/Effect4/Machine/Fibers.lean)) over the machine's fiber list *)
let lean_completed (fs : fiber list) : (int * int) list =
  List.filter_map
    (fun f ->
       match f.exit_ with
       | Some e -> Some (f.id, e)
       | None -> None)
    fs
;;

(* RunMachine.update (src/Effect4/Machine/Fibers.lean) — the replace-by-key map, a no-op on an absent id *)
let lean_update (fs : fiber list) (f : fiber) : fiber list =
  List.map (fun g -> if g.id = f.id then f else g) fs
;;

(* spawn (src/Effect4/Machine/Fibers.lean) *)
let lean_spawn (fs : fiber list) (child : fiber) : fiber list = fs @ [ child ]

(* dropObservers (src/Effect4/Machine/Fibers.lean) *)
let drop_step (token : int) (g : fiber) : fiber =
  { g with observers = List.filter (fun t -> t <> token) g.observers }
;;

let lean_drop (fs : fiber list) (token : int) : fiber list = List.map (drop_step token) fs

(* FV1's right-hand side read off the carrier's own table: the scan the view replaces. *)
let scan (t : (fiber, int) V.t) : (int * int) list =
  List.filter_map
    (fun (id, (f : fiber)) ->
       match exit_of f with
       | None -> None
       | Some x -> Some (id, x))
    (V.bindings t)
;;

let mk_fiber i =
  { id = i
  ; exit_ = (if rand 3 = 0 then Some (i * 11) else None)
  ; observers = List.init (rand 4) (fun j -> (i + j) mod 7)
  }
;;

let build n =
  let t = ref V.empty
  and l = ref [] in
  for i = 0 to n - 1 do
    let f = mk_fiber i in
    t := V.add ~exit_of i f !t;
    l := lean_spawn !l f
  done;
  !t, !l
;;

let sizes = [ 0; 1; 2; 8; 9; 64; 300 ]

(* ------------------------------------------------------------------------ FV1 *)
let fv1 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, l = build n in
       if V.completed t <> lean_completed l then ok := false;
       if V.completed t <> scan t then ok := false;
       (* … and after every kind of write, at every id *)
       for id = -1 to n do
         List.iter
           (fun x ->
              let f = { id; exit_ = x; observers = [ 1 ] } in
              let t' = V.set ~exit_of id f t in
              let l' = lean_update l f in
              if V.completed t' <> lean_completed l' then ok := false;
              if V.completed t' <> scan t' then ok := false;
              (* `add` at an id the table already has is Lean's replace; at a fresh one it is
                 spawn's append, which the Lean list only matches when the id is fresh THERE
                 too, so the Lean side of this check is the in-range case. *)
              let t2 = V.add ~exit_of id f t' in
              if id >= 0 && id < n && V.completed t2 <> lean_completed (lean_update l' f)
              then ok := false;
              if V.completed t2 <> scan t2 then ok := false)
           [ None; Some 5; Some (id * 11) ]
       done;
       (* … and once every fiber has exited, and once none has *)
       let all = V.map ~exit_of (fun f -> { f with exit_ = Some f.id }) t in
       let all_l = List.map (fun f -> { f with exit_ = Some f.id }) l in
       if V.completed all <> lean_completed all_l then ok := false;
       if V.completed all <> scan all then ok := false;
       let non = V.map ~exit_of (fun f -> { f with exit_ = None }) t in
       if V.completed non <> [] then ok := false;
       if scan non <> [] then ok := false)
    sizes;
  check
    "FV1 completed IS the ascending filterMap of completedExits \
     (src/Effect4/Machine/Fibers.lean), after every write"
    !ok
;;

(* ------------------------------------------------------------------------ FV2 *)
let fv2 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, l = build n in
       List.iter
         (fun id ->
            let f = { id; exit_ = Some 1; observers = [] } in
            let t' = V.set ~exit_of id f t in
            if V.bindings t' <> V.bindings t then ok := false;
            if V.completed t' <> V.completed t then ok := false;
            if not (V.shared t' == V.shared t) then ok := false;
            if V.completed t' <> lean_completed (lean_update l f) then ok := false;
            if V.cardinal t' <> n then ok := false)
         [ -1; n; n + 5; 100000 ])
    sizes;
  check "FV2 set on an ABSENT key is a no-op on the table and on the view" !ok
;;

(* ------------------------------------------------------------------------ FV3 *)
let fv3 () =
  reset ();
  let ok = ref true in
  let t = ref V.empty
  and l = ref [] in
  for i = 0 to 499 do
    (* the monotone-allocation licence: the fresh id IS the cardinal *)
    if V.cardinal !t <> i then ok := false;
    let f = mk_fiber i in
    t := V.add ~exit_of i f !t;
    l := lean_spawn !l f;
    if V.to_list !t <> !l then ok := false;
    if V.completed !t <> lean_completed !l then ok := false;
    if V.completed !t <> scan !t then ok := false
  done;
  (* spawn's child has exit = none (spawn (src/Effect4/Machine/Fibers.lean)): the view does not move *)
  let before = V.shared !t in
  let after = V.add ~exit_of 500 { id = 500; exit_ = None; observers = [] } !t in
  if not (V.shared after == before) then ok := false;
  check
    "FV3 add is spawn's append; a child with no exit leaves the view PHYSICALLY alone"
    !ok
;;

(* ------------------------------------------------------------------------ FV4 *)
let fv4 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, l = build n in
       for token = 0 to 7 do
         let t' = V.map ~exit_of (drop_step token) t in
         let l' = lean_drop l token in
         if V.to_list t' <> l' then ok := false;
         if List.map fst (V.bindings t') <> List.map fst (V.bindings t) then ok := false;
         if V.completed t' <> lean_completed l' then ok := false;
         if V.completed t' <> scan t' then ok := false
       done;
       (* a mapping function that CHANGES exits: the view is re-derived, not remapped *)
       let flip f =
         { f with
           exit_ =
             (match f.exit_ with
              | None -> Some (f.id + 1)
              | Some _ -> None)
         }
       in
       let t' = V.map ~exit_of flip t in
       if V.completed t' <> lean_completed (List.map flip l) then ok := false;
       if V.completed t' <> scan t' then ok := false)
    sizes;
  check
    "FV4 map is id-preserving and re-derives the view (even when it changes exits)"
    !ok
;;

(* ------------------------------------------------------------------------ FV5 *)
let fv5 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, l = build n in
       for id = -2 to n + 2 do
         if V.find_opt id t <> List.find_opt (fun f -> f.id = id) l then ok := false
       done;
       if V.bindings t <> List.map (fun f -> f.id, f) l then ok := false;
       if V.to_list t <> l then ok := false;
       if V.cardinal t <> List.length l then ok := false;
       let fin = List.for_all (fun f -> Option.is_some f.exit_) l in
       if V.for_all (fun _ f -> Option.is_some f.exit_) t <> fin then ok := false;
       if
         V.completed (V.of_list ~exit_of (List.map (fun f -> f.id, f) l))
         <> lean_completed l
       then ok := false)
    sizes;
  check
    "FV5 the view is invisible to find_opt/bindings/to_list/cardinal/for_all/of_list"
    !ok
;;

(* ------------------------------------------------------------------------ FV6 *)
let show fs =
  String.concat
    ";"
    (List.map
       (fun f ->
          Printf.sprintf
            "%d/%s/[%s]"
            f.id
            (match f.exit_ with
             | None -> "-"
             | Some e -> string_of_int e)
            (String.concat "," (List.map string_of_int f.observers)))
       fs)
;;

let show_ex l = String.concat ";" (List.map (fun (a, b) -> Printf.sprintf "%d=%d" a b) l)

let fv6 nops =
  reset ();
  let t = ref V.empty
  and l = ref [] in
  let bad = ref None in
  let i = ref 0 in
  (try
     while !i < nops do
       incr i;
       let n = List.length !l in
       let a, b =
         match rand 7 with
         | 0 ->
           let f = mk_fiber n in
           t := V.add ~exit_of n f !t;
           l := lean_spawn !l f;
           "", ""
         | 1 ->
           let id = rand (n + 3) - 1 in
           let f =
             { id
             ; exit_ = (if rand 2 = 0 then Some (rand 100) else None)
             ; observers = List.init (rand 3) (fun j -> j)
             }
           in
           t := V.set ~exit_of id f !t;
           l := lean_update !l f;
           "", ""
         | 2 ->
           (* the shape the machine actually writes: a fiber rebuilt with its exit untouched *)
           let id = rand (n + 1) in
           (match List.find_opt (fun f -> f.id = id) !l with
            | None -> ()
            | Some g ->
              let f = { g with observers = List.init (rand 3) (fun j -> j + 1) } in
              t := V.set ~exit_of id f !t;
              l := lean_update !l f);
           "", ""
         | 3 ->
           let token = rand 7 in
           t := V.map ~exit_of (drop_step token) !t;
           l := lean_drop !l token;
           "", ""
         | 4 ->
           let id = rand (n + 3) - 1 in
           ( (match V.find_opt id !t with
              | None -> "-"
              | Some f -> show [ f ])
           , (match List.find_opt (fun f -> f.id = id) !l with
              | None -> "-"
              | Some f -> show [ f ]) )
         | 5 ->
           ( string_of_bool (V.for_all (fun _ f -> Option.is_some f.exit_) !t)
           , string_of_bool (List.for_all (fun f -> Option.is_some f.exit_) !l) )
         | _ -> show_ex (V.completed !t), show_ex (lean_completed !l)
       in
       (* every operation, every time: the maintained view against Lean's walked one AND
          against the scan of the carrier's own table. Compared as values; rendered only for
          the report of a failure. *)
       let ca = V.completed !t
       and cc = lean_completed !l
       and cd = scan !t in
       let sa = V.to_list !t in
       if a <> b || sa <> !l || ca <> cc || ca <> cd
       then (
         bad := Some (!i, a, b, show_ex ca, show_ex cc, show_ex cd, show sa, show !l);
         raise Exit)
     done
   with
   | Exit -> ());
  (match !bad with
   | None -> ()
   | Some (n, a, b, ca, cc, cd, sa, sl) ->
     Printf.printf
       "  #%d answer view=%S lean=%S\n\
       \  completed view=%s lean=%s scan=%s\n\
       \  view=%s\n\
       \  lean=%s\n"
       n
       a
       b
       ca
       cc
       cd
       sa
       sl);
  check
    (Printf.sprintf
       "FV6 agreement with the Lean list over %d random fiber-table ops"
       nops)
    (match !bad with
     | None -> true
     | Some _ -> false)
;;

(* ------------------------------------------------------------------------ FV7 *)
let fv7 () =
  reset ();
  let ok = ref true in
  let t0, l0 = build 64 in
  let c0 = V.completed t0
  and b0 = V.bindings t0 in
  let t1 = V.set ~exit_of 3 { id = 3; exit_ = Some 999; observers = [] } t0 in
  let t2 = V.add ~exit_of 64 { id = 64; exit_ = Some 1; observers = [] } t1 in
  ignore t2;
  if V.completed t0 <> c0 then ok := false;
  if V.bindings t0 <> b0 then ok := false;
  if V.completed t0 <> lean_completed l0 then ok := false;
  if V.completed t1 = c0 && List.mem_assoc 3 c0 && List.assoc 3 c0 <> 999 then ok := false;
  check "FV7 persistent: a write answers a new value and no earlier value changes" !ok
;;

(* ------------------------------------------------------------------------ FV8 *)
let fv8 () =
  reset ();
  let ok = ref true in
  let shares = ref 0
  and total = ref 0 in
  List.iter
    (fun n ->
       let t, _ = build n in
       (* the machine's own shape: `{ f with … }` with the exit untouched, every id *)
       List.iter
         (fun (id, f) ->
            let f' = { f with observers = [ 9 ] } in
            let t' = V.set ~exit_of id f' t in
            incr total;
            if V.shared t' == V.shared t then incr shares else ok := false;
            (* and a genuine exit: the view must move *)
            let t'' = V.set ~exit_of id { f with exit_ = Some (1000 + id) } t in
            if List.assoc_opt id (V.completed t'') <> Some (1000 + id) then ok := false)
         (V.bindings t))
    sizes;
  check
    (Printf.sprintf
       "FV8 a write that does not change an exit leaves the view PHYSICALLY shared \
        (%d/%d)"
       !shares
       !total)
    !ok
;;

let () =
  fv1 ();
  fv2 ();
  fv3 ();
  fv4 ();
  fv5 ();
  fv6 12000;
  fv7 ();
  fv8 ();
  argue
    "FV9 completed is O(1), set O(log n) (+O(C) when an exit changes), map O(N)"
    "by construction; the engine numbers are in the lane G3 receipt";
  E4_check.finish ()
;;
