(* e4_timers.ml — the timer store. See e4_timers.mli for what it is, the invariants
   TIM-SORT/FRESH/PAST/UNIQ/BIJ, the properties T1-T7 and the refusals R1-R6.

   Representation (decision D-A3-3, design doc §6.1: `psq 0.2.1` measured and refused):

     by_prio : (tick, seq) -> waiter      the priority side; `min` is `Map.min_binding_opt`
     by_key  : seq -> (tick, seq)         the map side; `cancel` is two removals

   Three implementation notes that are not visible in the .mli:

   (1) THE KEY IS THE SEQ. The registration number is both the park token and the `seq` half
       of the priority, so the priority carries its own key and `by_prio` does not have to
       store one: the data side of `by_prio` is the waiter alone. That is what keeps the
       footprint at the measured 15 words/timer (bench cell B-Q2d, floor 16): one `by_prio`
       node (6), one `by_key` node (6), and one priority pair (3) SHARED between the two
       trees -- `by_key`'s data is the very tuple `by_prio` is keyed on.

   (2) THE PRIORITY'S DEADLINE IS A TICK, NOT A `time`. `Fin d` is a boxed block; a boxed
       deadline inside the priority pair would cost two more words per timer and put B-Q2d
       over its floor. Internally `Inf` is the tick `inf_tick = max_deadline_ms + 1`, which
       is unambiguous because every finite deadline is <= max_deadline_ms by construction
       (E4_time.add refuses the rest) and because every `upto` is clamped to
       max_deadline_ms before it is compared -- so an `Inf` timer can never be due, which is
       `inf_never_fires` (T5).

   (3) `count` IS CARRIED. `Map.cardinal` is O(n); `size`/`length`/`is_empty` are O(1) here
       and the field costs one word in the store record, not per timer. `wf` checks it
       against both cardinals, so a duplicate key (which two `Map.add`s would silently
       collapse) is caught rather than hidden.

   No physical clock: `Unix` is not opened, and no host clock appears in this file (C4). *)

type time = E4_time.t = Fin of int | Inf

let max_deadline_ms = E4_time.max_deadline_ms
let time_le = E4_time.le
let time_lt = E4_time.lt
let time_add = E4_time.add

type key = int

(* The internal tick of `Inf`: above every admissible finite deadline, and below `max_int`
   on a 31-bit host (E4_time.max_deadline_ms is chosen so, C5). *)
let inf_tick = max_deadline_ms + 1

let tick_of_time = function Fin ms -> ms | Inf -> inf_tick
let time_of_tick k = if k = inf_tick then Inf else Fin k

(* The priority: (deadline tick, registration number), ascending lexicographically. This is
   `Timer.before` (workshop Timer.lean:143-144) read as a comparison. *)
module Prio = struct
  type t = int * int

  let compare ((d1 : int), (s1 : int)) ((d2 : int), (s2 : int)) =
    if d1 < d2 then -1
    else if d1 > d2 then 1
    else if s1 < s2 then -1
    else if s1 > s2 then 1
    else 0
end

module Mp = Map.Make (Prio)
module Mk = Map.Make (Int)

type 'w t = {
  clock : E4_time.clock;
  next_seq : int;
  count : int;
  by_prio : 'w Mp.t;
  by_key : Prio.t Mk.t;
}

let empty =
  {
    clock = E4_time.start;
    next_seq = 0;
    count = 0;
    by_prio = Mp.empty;
    by_key = Mk.empty;
  }

let now t = E4_time.now t.clock
let size t = t.count
let length t = t.count
let is_empty t = t.count = 0
let next_seq t = t.next_seq

(* ---------------------------------------------------------------- registration *)

(* `TestClock.sleep` (:322-338) = workshop `Store.sleep` (Timer.lean:247-251). *)
let sleep t d w =
  match d with
  | Fin 0 -> (t, None)
  | _ ->
      let deadline = E4_time.add (E4_time.now t.clock) d in
      let k = t.next_seq in
      let p = (tick_of_time deadline, k) in
      ( {
          clock = t.clock;
          next_seq = k + 1;
          count = t.count + 1;
          by_prio = Mp.add p w t.by_prio;
          by_key = Mk.add k p t.by_key;
        },
        Some k )

(* `clearTimeout` = workshop `Store.cancel` (Timer.lean:498-499). Idempotent: a key that is
   not registered leaves the store as it is (physically, not just structurally). *)
let cancel t k =
  match Mk.find_opt k t.by_key with
  | None -> t
  | Some p ->
      {
        clock = t.clock;
        next_seq = t.next_seq;
        count = t.count - 1;
        by_prio = Mp.remove p t.by_prio;
        by_key = Mk.remove k t.by_key;
      }

let remove_by_key = cancel

(* ---------------------------------------------------------------- lookup (free rows) *)

let mem t k = Mk.mem k t.by_key

let deadline_of t k =
  match Mk.find_opt k t.by_key with None -> None | Some (d, _) -> Some (time_of_tick d)

let waiter_of t k =
  match Mk.find_opt k t.by_key with None -> None | Some p -> Mp.find_opt p t.by_prio

let min t =
  match Mp.min_binding_opt t.by_prio with
  | None -> None
  | Some ((d, s), w) -> Some (s, time_of_tick d, w)

(* An `upto` above the domain cannot make an `Inf` timer due (note 2). *)
let clamp_upto upto = if upto > max_deadline_ms then max_deadline_ms else upto

(* ---------------------------------------------------------------- firing *)

(* ONE STAGED FIRE: `Timer.fireNext` (Timer.lean:283-289). The clock is staged at the fired
   deadline, not at `upto` -- a fiber woken at deadline d that reads the clock reads d. *)
let pop_due t ~upto =
  let bound = clamp_upto upto in
  match Mp.min_binding_opt t.by_prio with
  | Some (((d, s) as p), w) when d <= bound ->
      Some
        ( (s, d, w),
          {
            clock = E4_time.advance_to t.clock ~target:d;
            next_seq = t.next_seq;
            count = t.count - 1;
            by_prio = Mp.remove p t.by_prio;
            by_key = Mk.remove s t.by_key;
          } )
  | _ -> None

(* THE BATCHED FORM: `Timer.advance` (Timer.lean:442-444) = `splitDue` then `now := target`.
   The clock moves first, so a backwards target is refused (R1) before anything fires. *)
let advance_to t ~target =
  let clock = E4_time.advance_to t.clock ~target in
  let bound = clamp_upto target in
  let rec go by_prio by_key count acc =
    match Mp.min_binding_opt by_prio with
    | Some (((d, s) as p), w) when d <= bound ->
        go (Mp.remove p by_prio) (Mk.remove s by_key) (count - 1) ((s, d, w) :: acc)
    | _ -> (by_prio, by_key, count, List.rev acc)
  in
  let by_prio, by_key, count, fires = go t.by_prio t.by_key t.count [] in
  ({ clock; next_seq = t.next_seq; count; by_prio; by_key }, fires)

let advance t ~by =
  (* E4_time.advance_by carries the refusal for a negative `by` and for the domain's top. *)
  let target = E4_time.now (E4_time.advance_by t.clock ~by) in
  advance_to t ~target

(* A FREE ROW: what an advance to `upto` would fire, with nothing moved. Total -- an `upto`
   below `now` answers the empty list, because a free row never refuses. *)
let fired t ~upto =
  let bound = clamp_upto upto in
  Mp.to_seq t.by_prio
  |> Seq.take_while (fun ((d, _), _) -> d <= bound)
  |> Seq.map (fun ((d, s), w) -> (s, d, w))
  |> List.of_seq

(* ---------------------------------------------------------------- canonical form *)

let to_list t =
  List.map (fun ((d, s), w) -> (s, time_of_tick d, w)) (Mp.bindings t.by_prio)

(* TIM-SORT and TIM-FRESH and TIM-PAST and TIM-UNIQ and TIM-BIJ, checked and not assumed.
   Never called on the hot path. *)
let wf t =
  let tick = E4_time.now t.clock in
  let cards_ok =
    t.count = Mk.cardinal t.by_key
    && t.count = Mp.cardinal t.by_prio (* TIM-UNIQ: no two timers share a priority *)
    && t.count >= 0
    && t.next_seq >= 0
    && E4_time.is_tick tick
  in
  let sorted_ok =
    (* TIM-SORT: `bindings` is ascending under Prio.compare, strictly. *)
    let rec asc = function
      | a :: (b :: _ as rest) -> Prio.compare a b < 0 && asc rest
      | _ -> true
    in
    asc (List.map fst (Mp.bindings t.by_prio))
  in
  let entries_ok =
    Mp.fold
      (fun (d, s) _ acc ->
        acc
        (* TIM-FRESH *)
        && s >= 0
        && s < t.next_seq
        (* TIM-PAST, and the deadline is in the domain or is exactly `Inf` *)
        && d >= tick
        && (d = inf_tick || E4_time.is_tick d)
        (* TIM-BIJ: the key side answers with the very priority we are standing on *)
        && (match Mk.find_opt s t.by_key with
           | Some (d', s') -> d' = d && s' = s
           | None -> false))
      t.by_prio true
  in
  let inverse_ok =
    Mk.fold
      (fun k (d, s) acc -> acc && k = s && Mp.mem (d, s) t.by_prio)
      t.by_key true
  in
  cards_ok && sorted_ok && entries_ok && inverse_ok

let of_list ~now:tick ~next_seq:ns l =
  if not (E4_time.is_tick tick) then
    invalid_arg "E4_timers.of_list: `now` is not a tick in [0, max_deadline_ms]";
  if ns < 0 then invalid_arg "E4_timers.of_list: negative next_seq";
  let t =
    List.fold_left
      (fun t (k, d, w) ->
        (* A finite deadline outside the domain would otherwise be indistinguishable from
           `Inf` once it is a tick, so it is refused here rather than in `wf`. *)
        if not (E4_time.wf d) then
          invalid_arg "E4_timers.of_list: a deadline outside [0, max_deadline_ms]";
        let p = (tick_of_time d, k) in
        {
          t with
          count = t.count + 1;
          by_prio = Mp.add p w t.by_prio;
          by_key = Mk.add k p t.by_key;
        })
      { empty with clock = E4_time.of_tick tick; next_seq = ns }
      l
  in
  if wf t then t else invalid_arg "E4_timers.of_list: the result would not satisfy `wf`"
