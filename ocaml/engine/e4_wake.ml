(* e4_wake.ml — the one allocation-and-wake protocol.
   The property list W1-W8, DL1-DL3 and the licences are in e4_wake.mli.

   THE CARRIER: a persistent `Map.Make(Int)` from cell id to cell, and a monotone `next` for
   `alloc`. Ids are never reused -- that is half of W5: a later allocation cannot land on the
   key an outstanding wake captured, so nothing can retarget it. The other half is that a
   waiter row carries `at_phase`, written once at registration and never rewritten.

   Nothing here is mutable: no record field is `mutable`, no array, no Hashtbl, no Queue. A
   saved machine holding a `t` holds no mutable structure (brief rule 3). *)

module IMap = Map.Make (Int)

type phase = int
type waiter = { fiber : int; token : int; at_phase : phase }
type cell_id = int

type 'a step_answer =
  | Answer of 'a
  | Park of phase
  | Delay
  | Refuse

type 'a cell =
  { completion : 'a option
  ; waiters : waiter list
  ; phase : phase
  }

type 'a t = { cells : 'a cell IMap.t; next : cell_id }

(* DL3. A named constant in the file, never `max_int` (trap #17). *)
let delay_budget = 1024

let empty_cell = { completion = None; waiters = []; phase = 0 }
let empty = { cells = IMap.empty; next = 0 }

let alloc t =
  let id = t.next in
  (id, { cells = IMap.add id empty_cell t.cells; next = id + 1 })

let size t = IMap.cardinal t.cells
let get t id = IMap.find_opt id t.cells

(* W1, W2, W5. `Refuse` on an unknown cell is a frontier, never a hang (gap G1). *)
let register t id ~fiber ~token =
  match IMap.find_opt id t.cells with
  | None -> (t, Refuse)
  | Some c -> (
    match c.completion with
    (* W2 / F5b: a settled cell answers now and appends to NO reaction list. *)
    | Some v -> (t, Answer v)
    | None ->
      let w = { fiber; token; at_phase = c.phase } in
      let c = { c with waiters = c.waiters @ [ w ] } in
      ({ t with cells = IMap.add id c t.cells }, Park c.phase))

(* Splice out the first structurally equal waiter; a no-op when it is not there (it was
   already taken by a completion or a signal). *)
let waiter_eq (a : waiter) (b : waiter) =
  a.fiber = b.fiber && a.token = b.token && a.at_phase = b.at_phase

let rec remove_first w = function
  | [] -> []
  | x :: rest -> if waiter_eq x w then rest else x :: remove_first w rest

(* W4 and W4a. The discriminator is the phase, exactly as the law states it. *)
let cancel t id w =
  match IMap.find_opt id t.cells with
  | None -> (t, `Unknown)
  | Some c ->
    let waiters = remove_first w c.waiters in
    let t = { t with cells = IMap.add id { c with waiters } t.cells } in
    if w.at_phase >= c.phase then (t, `Removed)
    else (
      (* The resumer already consumed a wake on this waiter's behalf, so the cancelling step
         performs one. W4a: with nobody left to hand it to, the obligation is vacuous. *)
      match waiters with [] -> (t, `Removed) | next :: _ -> (t, `Owes_wake next))

(* W3 and F5a/F5c: the completion is stored, the waiter list is CLEARED and handed back in one
   step, and the phase bump is UNCONDITIONAL -- a cell with no waiter still bumps. *)
let complete t id v =
  match IMap.find_opt id t.cells with
  | None -> (t, `Unknown)
  | Some c -> (
    match c.completion with
    | Some _ -> (t, `Already)
    | None ->
      let c' = { completion = Some v; waiters = []; phase = c.phase + 1 } in
      ({ t with cells = IMap.add id c' t.cells }, `Completed c.waiters))

(* W6, W7: bump the phase and hand back at most [count] waiters from the head, without
   settling the cell. The waiters handed back stay OUT of the list -- they are the ones a
   resumer owes a wake to, and W4 is what a later cancel of one of them rests on. *)
let rec take n l =
  if n <= 0 then ([], l)
  else match l with [] -> ([], []) | x :: rest ->
    let taken, left = take (n - 1) rest in
    (x :: taken, left)

let signal t id ~count =
  match IMap.find_opt id t.cells with
  | None -> (t, [])
  | Some c ->
    let woken, waiters = take count c.waiters in
    let c' = { c with waiters; phase = c.phase + 1 } in
    ({ t with cells = IMap.add id c' t.cells }, woken)

(* The free rows: no fuel, no tape, no state change. *)
let poll t id = Option.map (fun c -> c.completion) (IMap.find_opt id t.cells)

let is_done t id =
  Option.map (fun c -> match c.completion with Some _ -> true | None -> false)
    (IMap.find_opt id t.cells)

let phase_of t id = Option.map (fun c -> c.phase) (IMap.find_opt id t.cells)

let waiters_of t id =
  match IMap.find_opt id t.cells with None -> [] | Some c -> c.waiters
