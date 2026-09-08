(* e4_time.ml — the logical clock. See e4_time.mli for what it is and the properties C1-C6.

   Implementation notes:
   * `clock` is an `int` (exported `private int`), so it is immediate: no allocation on a
     clock move, nothing mutable in a saved machine (C6).
   * Every bound check is written so that no intermediate sum can leave the host's integer
     range on a 31-bit host: `now + d` is never formed before `d <= max_deadline_ms - now`
     is known (C5, trap #17).
   * There is no host clock in this file. `Unix` is not opened and no `Sys.time` /
     `gettimeofday` appears (C4). *)

type t =
  | Fin of int
  | Inf

(* The named bound (C5). 1e9 ms = 11 d 13 h 46 m 40 s. It and `max_deadline_ms + 1` (the
   internal `Inf` tick of E4_timers) are below `max_int` on a 31-bit host (2^30 - 1). *)
let max_deadline_ms = 1_000_000_000

let is_tick (k : int) = k >= 0 && k <= max_deadline_ms

let wf = function Fin ms -> is_tick ms | Inf -> true

let le a b =
  match (a, b) with
  | Fin x, Fin y -> x <= y
  | _, Inf -> true
  | Inf, Fin _ -> false

let lt a b =
  match (a, b) with
  | Fin x, Fin y -> x < y
  | Fin _, Inf -> true
  | Inf, _ -> false

let compare a b =
  match (a, b) with
  | Fin x, Fin y -> if x < y then -1 else if x > y then 1 else 0
  | Fin _, Inf -> -1
  | Inf, Fin _ -> 1
  | Inf, Inf -> 0

let add now d =
  if not (is_tick now) then
    invalid_arg "E4_time.add: `now` is not a tick in [0, max_deadline_ms]";
  match d with
  | Inf -> Inf
  | Fin ms ->
      if ms < 0 then
        invalid_arg
          "E4_time.add: negative duration (workshop refusal R6: the fold to zero is the \
           row's, not the store's)"
      else if ms > max_deadline_ms - now then
        invalid_arg "E4_time.add: deadline above max_deadline_ms"
      else Fin (now + ms)

let to_string = function Fin ms -> string_of_int ms ^ "ms" | Inf -> "inf"

type clock = int

let start = 0

let of_tick k =
  if not (is_tick k) then invalid_arg "E4_time.of_tick: not a tick in [0, max_deadline_ms]"
  else k

let now (c : clock) = c

let advance_to (c : clock) ~target =
  if target < c then
    invalid_arg
      "E4_time.advance_to: target below `now` (refusal R1: the clock is monotone, there is \
       no clockAdjust)"
  else if target > max_deadline_ms then
    invalid_arg "E4_time.advance_to: target above max_deadline_ms"
  else target

let advance_by (c : clock) ~by =
  if by < 0 then
    invalid_arg "E4_time.advance_by: negative `by` (refusal R1: the clock is monotone)"
  else if by > max_deadline_ms - c then
    invalid_arg "E4_time.advance_by: target above max_deadline_ms"
  else c + by

let reaches (c : clock) target = target >= c && target <= max_deadline_ms
