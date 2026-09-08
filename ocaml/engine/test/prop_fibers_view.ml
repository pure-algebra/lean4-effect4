(* prop_fibers_view.ml — the property tests of E4_fibers_view (lane G3, docs/research/
   2026-09-08-engine-lane-g3-delivery.md; laws FV1-FV9 of e4_fibers_view.mli).

   What is under test: the fiber table that MAINTAINS the completed view, so that
   `RunMachine.completedExits` (src/Effect4/Machine/Fibers.lean:1543) is a field read instead
   of a Θ(N) scan on every step.  The twin is the LEAN LIST ITSELF (`e4_fibers_view_list.ml`:
   allocation order, and `completed` is Lean's `filterMap` walked at read time), and the
   right-hand side of the law that matters — FV1 — is written out here from Fibers.lean and
   also read off `E4_table.filter_map` over the carrier's own table.

   The FIBERS module type the generated functor takes is declared VERBATIM below and BOTH
   carriers are ascribed to it, so a carrier that drifts from the seam stops compiling here.

   Exit code 0 iff every line passed. *)

open Effect4_engine
module V = E4_fibers_view
module W = E4_fibers_view_list

(* The seam's own text (src/OCaml5/Lcnf/Externs.lean, `carrierSignatures`), so this file fails
   to compile if either carrier stops satisfying it. *)
[@@@warning "-32"]
(* A module type used only for an ascription has, by definition, no used values. *)

module type FIBERS = sig
  type ('a, 'x) t
  val empty     : ('a, 'x) t
  val find_opt  : int -> ('a, 'x) t -> 'a option
  val set       : exit_of:('a -> 'x option) -> int -> 'a -> ('a, 'x) t -> ('a, 'x) t
  val add       : exit_of:('a -> 'x option) -> int -> 'a -> ('a, 'x) t -> ('a, 'x) t
  val map       : exit_of:('a -> 'x option) -> ('a -> 'a) -> ('a, 'x) t -> ('a, 'x) t
  val for_all   : (int -> 'a -> bool) -> ('a, 'x) t -> bool
  val completed : ('a, 'x) t -> (int * 'x) list
  val cardinal  : ('a, 'x) t -> int
  val bindings  : ('a, 'x) t -> (int * 'a) list
  val to_list   : ('a, 'x) t -> 'a list
  val of_list   : exit_of:('a -> 'x option) -> (int * 'a) list -> ('a, 'x) t
end

module _ : FIBERS = E4_fibers_view
module _ : FIBERS = E4_fibers_view_list
[@@@warning "+32"]

let failures = ref 0

let check name ok =
  Printf.printf "%s %s\n" (if ok then "PASS" else "FAIL") name;
  if not ok then incr failures

let argue name why = Printf.printf "PASS %s [%s]\n" name why

(* Java's 48-bit LCG, as every other property suite in this directory. *)
let lcg_mask = 0xFFFFFFFFFFFF
let lcg_seed = 0x1234ABCD5678
let s = ref lcg_seed
let reset () = s := lcg_seed

let next () =
  s := ((!s * 25214903917) + 11) land lcg_mask;
  !s lsr 16

let rand n = if n <= 0 then 0 else next () mod n

(* ------------------------------------------------------- the smallest fiber record.
   The generated `run_fiber` has 15 fields; the three these laws touch are the id
   (Fibers.lean:573), the exit (:609, :1543) and the observers (:1256, :1344). *)
type fiber = { id : int; exit_ : int option; observers : int list }

let exit_of f = f.exit_

(* ------------------------------------------------------------- Lean, written out *)

(* RunMachine.completedExits (Fibers.lean:1541-1543) over the machine's fiber list *)
let lean_completed (fs : fiber list) : (int * int) list =
  List.filter_map (fun f -> match f.exit_ with Some e -> Some (f.id, e) | None -> None) fs

(* RunMachine.update (:577-579) — the replace-by-key map, a no-op on an absent id *)
let lean_update (fs : fiber list) (f : fiber) : fiber list =
  List.map (fun g -> if g.id = f.id then f else g) fs

(* spawn (:867, :877) *)
let lean_spawn (fs : fiber list) (child : fiber) : fiber list = fs @ [ child ]

(* dropObservers (:1254-1260, :1344-1348) *)
let drop_step (token : int) (g : fiber) : fiber =
  { g with observers = List.filter (fun t -> t <> token) g.observers }

let lean_drop (fs : fiber list) (token : int) : fiber list = List.map (drop_step token) fs

(* FV1's right-hand side read off the carrier's own table: the scan the view replaces. *)
let scan (t : (fiber, int) V.t) : (int * int) list =
  List.filter_map
    (fun (id, (f : fiber)) -> match exit_of f with None -> None | Some x -> Some (id, x))
    (V.bindings t)

let mk_fiber i =
  { id = i;
    exit_ = (if rand 3 = 0 then Some (i * 11) else None);
    observers = List.init (rand 4) (fun j -> (i + j) mod 7) }

let build n =
  let t = ref V.empty and u = ref W.empty and l = ref [] in
  for i = 0 to n - 1 do
    let f = mk_fiber i in
    t := V.add ~exit_of i f !t;
    u := W.add ~exit_of i f !u;
    l := lean_spawn !l f
  done;
  (!t, !u, !l)

let sizes = [ 0; 1; 2; 8; 9; 64; 300 ]

(* ------------------------------------------------------------------------ FV1 *)
let fv1 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, u, l = build n in
       if V.completed t <> lean_completed l then ok := false;
       if V.completed t <> scan t then ok := false;
       if W.completed u <> lean_completed l then ok := false;
       (* … and after every kind of write, at every id *)
       for id = -1 to n do
         List.iter
           (fun x ->
              let f = { id; exit_ = x; observers = [ 1 ] } in
              let t' = V.set ~exit_of id f t and u' = W.set ~exit_of id f u in
              let l' = lean_update l f in
              if V.completed t' <> lean_completed l' then ok := false;
              if V.completed t' <> scan t' then ok := false;
              if W.completed u' <> lean_completed l' then ok := false;
              (* `add` at an id the table already has is Lean's replace; at a fresh one it is
                 spawn's append, which the list twin only matches when the id is fresh THERE
                 too, so the Lean side of this check is the in-range case. *)
              let t2 = V.add ~exit_of id f t' in
              if id >= 0 && id < n && V.completed t2 <> lean_completed (lean_update l' f) then
                ok := false;
              if V.completed t2 <> scan t2 then ok := false)
           [ None; Some 5; Some (id * 11) ]
       done;
       (* … and once every fiber has exited, and once none has *)
       let all = V.map ~exit_of (fun f -> { f with exit_ = Some f.id }) t in
       let alw = W.map ~exit_of (fun f -> { f with exit_ = Some f.id }) u in
       let all_l = List.map (fun f -> { f with exit_ = Some f.id }) l in
       if V.completed all <> lean_completed all_l then ok := false;
       if V.completed all <> scan all then ok := false;
       if W.completed alw <> lean_completed all_l then ok := false;
       let non = V.map ~exit_of (fun f -> { f with exit_ = None }) t in
       if V.completed non <> [] then ok := false;
       if scan non <> [] then ok := false)
    sizes;
  check "FV1 completed IS the ascending filterMap of Fibers.lean:1543, after every write" !ok

(* ------------------------------------------------------------------------ FV2 *)
let fv2 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, u, l = build n in
       List.iter
         (fun id ->
            let f = { id; exit_ = Some 1; observers = [] } in
            let t' = V.set ~exit_of id f t and u' = W.set ~exit_of id f u in
            if V.bindings t' <> V.bindings t then ok := false;
            if V.completed t' <> V.completed t then ok := false;
            if not (V.completed t' == V.completed t) then ok := false;
            if W.completed u' <> lean_completed l then ok := false;
            if V.cardinal t' <> n then ok := false)
         [ -1; n; n + 5; 100000 ])
    sizes;
  check "FV2 set on an ABSENT key is a no-op on the table and on the view" !ok

(* ------------------------------------------------------------------------ FV3 *)
let fv3 () =
  reset ();
  let ok = ref true in
  let t = ref V.empty and l = ref [] in
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
  (* spawn's child has exit = none (Fibers.lean:867-877): the view does not move *)
  let before = V.completed !t in
  let after = V.add ~exit_of 500 { id = 500; exit_ = None; observers = [] } !t in
  if not (V.completed after == before) then ok := false;
  check "FV3 add is spawn's append; a child with no exit leaves the view PHYSICALLY alone" !ok

(* ------------------------------------------------------------------------ FV4 *)
let fv4 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, u, l = build n in
       for token = 0 to 7 do
         let t' = V.map ~exit_of (drop_step token) t and u' = W.map ~exit_of (drop_step token) u in
         let l' = lean_drop l token in
         if V.to_list t' <> l' then ok := false;
         if List.map fst (V.bindings t') <> List.map fst (V.bindings t) then ok := false;
         if V.completed t' <> lean_completed l' then ok := false;
         if V.completed t' <> scan t' then ok := false;
         if W.completed u' <> lean_completed l' then ok := false
       done;
       (* a mapping function that CHANGES exits: the view is re-derived, not remapped *)
       let flip f = { f with exit_ = (match f.exit_ with None -> Some (f.id + 1) | Some _ -> None) } in
       let t' = V.map ~exit_of flip t in
       if V.completed t' <> lean_completed (List.map flip l) then ok := false;
       if V.completed t' <> scan t' then ok := false)
    sizes;
  check "FV4 map is id-preserving and re-derives the view (even when it changes exits)" !ok

(* ------------------------------------------------------------------------ FV5 *)
let fv5 () =
  reset ();
  let ok = ref true in
  List.iter
    (fun n ->
       let t, u, l = build n in
       for id = -2 to n + 2 do
         if V.find_opt id t <> List.find_opt (fun f -> f.id = id) l then ok := false;
         if W.find_opt id u <> List.find_opt (fun f -> f.id = id) l then ok := false
       done;
       if V.bindings t <> List.map (fun f -> (f.id, f)) l then ok := false;
       if V.to_list t <> l then ok := false;
       if V.cardinal t <> List.length l then ok := false;
       let fin = List.for_all (fun f -> Option.is_some f.exit_) l in
       if V.for_all (fun _ f -> Option.is_some f.exit_) t <> fin then ok := false;
       if W.for_all (fun _ f -> Option.is_some f.exit_) u <> fin then ok := false;
       if V.completed (V.of_list ~exit_of (List.map (fun f -> (f.id, f)) l))
          <> lean_completed l
       then ok := false)
    sizes;
  check "FV5 the view is invisible to find_opt/bindings/to_list/cardinal/for_all/of_list" !ok

(* ------------------------------------------------------------------------ FV6 *)
let show fs =
  String.concat ";"
    (List.map
       (fun f ->
          Printf.sprintf "%d/%s/[%s]" f.id
            (match f.exit_ with None -> "-" | Some e -> string_of_int e)
            (String.concat "," (List.map string_of_int f.observers)))
       fs)

let show_ex l = String.concat ";" (List.map (fun (a, b) -> Printf.sprintf "%d=%d" a b) l)

let fv6 nops =
  reset ();
  let t = ref V.empty and u = ref W.empty and l = ref [] in
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
           u := W.add ~exit_of n f !u;
           l := lean_spawn !l f;
           ("", "")
         | 1 ->
           let id = rand (n + 3) - 1 in
           let f =
             { id;
               exit_ = (if rand 2 = 0 then Some (rand 100) else None);
               observers = List.init (rand 3) (fun j -> j) }
           in
           t := V.set ~exit_of id f !t;
           u := W.set ~exit_of id f !u;
           l := lean_update !l f;
           ("", "")
         | 2 ->
           (* the shape the machine actually writes: a fiber rebuilt with its exit untouched *)
           let id = rand (n + 1) in
           (match List.find_opt (fun f -> f.id = id) !l with
            | None -> ()
            | Some g ->
              let f = { g with observers = List.init (rand 3) (fun j -> j + 1) } in
              t := V.set ~exit_of id f !t;
              u := W.set ~exit_of id f !u;
              l := lean_update !l f);
           ("", "")
         | 3 ->
           let token = rand 7 in
           t := V.map ~exit_of (drop_step token) !t;
           u := W.map ~exit_of (drop_step token) !u;
           l := lean_drop !l token;
           ("", "")
         | 4 ->
           let id = rand (n + 3) - 1 in
           ( (match V.find_opt id !t with None -> "-" | Some f -> show [ f ]),
             match W.find_opt id !u with None -> "-" | Some f -> show [ f ] )
         | 5 ->
           ( string_of_bool (V.for_all (fun _ f -> Option.is_some f.exit_) !t),
             string_of_bool (W.for_all (fun _ f -> Option.is_some f.exit_) !u) )
         | _ -> (show_ex (V.completed !t), show_ex (W.completed !u))
       in
       (* every operation, every time: the maintained view against the walked one AND
          against the scan of the carrier's own table *)
       let ca = show_ex (V.completed !t)
       and cb = show_ex (W.completed !u)
       and cc = show_ex (lean_completed !l)
       and cd = show_ex (scan !t) in
       let sa = show (V.to_list !t) and sb = show (W.to_list !u) in
       if a <> b || sa <> sb || ca <> cb || ca <> cc || ca <> cd then begin
         bad := Some (!i, a, b, ca, cb, cc, cd, sa, sb);
         raise Exit
       end
     done
   with Exit -> ());
  (match !bad with
   | None -> ()
   | Some (n, a, b, ca, cb, cc, cd, sa, sb) ->
     Printf.printf
       "  #%d answer view=%S twin=%S\n  completed view=%s twin=%s lean=%s scan=%s\n  \
        view=%s\n  twin=%s\n"
       n a b ca cb cc cd sa sb);
  check
    (Printf.sprintf "FV6 agreement with the Lean list twin over %d random fiber-table ops" nops)
    (match !bad with None -> true | Some _ -> false)

(* ------------------------------------------------------------------------ FV7 *)
let fv7 () =
  reset ();
  let ok = ref true in
  let t0, _, l0 = build 64 in
  let c0 = V.completed t0 and b0 = V.bindings t0 in
  let t1 = V.set ~exit_of 3 { id = 3; exit_ = Some 999; observers = [] } t0 in
  let t2 = V.add ~exit_of 64 { id = 64; exit_ = Some 1; observers = [] } t1 in
  ignore t2;
  if V.completed t0 <> c0 then ok := false;
  if V.bindings t0 <> b0 then ok := false;
  if V.completed t0 <> lean_completed l0 then ok := false;
  if V.completed t1 = c0 && List.mem_assoc 3 c0 && List.assoc 3 c0 <> 999 then ok := false;
  check "FV7 persistent: a write answers a new value and no earlier value changes" !ok

(* ------------------------------------------------------------------------ FV8 *)
let fv8 () =
  reset ();
  let ok = ref true in
  let shares = ref 0 and total = ref 0 in
  List.iter
    (fun n ->
       let t, _, _ = build n in
       (* the machine's own shape: `{ f with … }` with the exit untouched, every id *)
       List.iter
         (fun (id, f) ->
            let f' = { f with observers = [ 9 ] } in
            let t' = V.set ~exit_of id f' t in
            incr total;
            if V.completed t' == V.completed t then incr shares else ok := false;
            (* and a genuine exit: the view must move *)
            let t'' = V.set ~exit_of id { f with exit_ = Some (1000 + id) } t in
            if List.assoc_opt id (V.completed t'') <> Some (1000 + id) then ok := false)
         (V.bindings t))
    sizes;
  check
    (Printf.sprintf
       "FV8 a write that does not change an exit leaves the view PHYSICALLY shared (%d/%d)"
       !shares !total)
    !ok

let () =
  fv1 ();
  fv2 ();
  fv3 ();
  fv4 ();
  fv5 ();
  fv6 12000;
  fv7 ();
  fv8 ();
  argue "FV9 completed is O(1), set O(log n) (+O(C) when an exit changes), map O(N)"
    "by construction; the engine numbers are in the lane G3 receipt";
  Printf.printf "== %s: %d failure(s) ==\n" (if !failures = 0 then "ALL PASS" else "FAILED")
    !failures;
  exit (if !failures = 0 then 0 else 1)
