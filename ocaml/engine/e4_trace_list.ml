(* E4_trace_list — the LIST twin of E4_trace: the same signature (`TRACE`, 2026-09-08-engine-
   a1-state.md §1.5), backed by the list Lean actually carries, in emission order.

   It reproduces `Effect4.Machine.RunMachine.emit` (src/Effect4/Machine/Fibers.lean:585-587)
   operation for operation, INCLUDING the empty guard:
       trace := if events.isEmpty then m.trace else m.trace ++ events
   so `emit [] t` is physically `t` here too, and the only difference from E4_trace is the
   Θ(steps²) copy in the non-empty arm — which is the point of the differential.

   Depends on: the OCaml standard library only (List).

   Behaviours:
   TLT1 to_list is the identity: the carrier IS the trace                by construction
   TLT2 emit evs t = t @ evs for a non-empty evs, and t itself for []    by construction
   TLT3 length is List.length: O(n), not O(1) — the twin does not maintain a count,
        because Lean does not                                           by construction *)

type 'e t = 'e list

let empty : 'e t = []
let emit (evs : 'e list) (t : 'e t) : 'e t = match evs with [] -> t | _ -> t @ evs
let to_list (t : 'e t) : 'e list = t
let length (t : 'e t) : int = List.length t
let is_empty (t : 'e t) : bool = match t with [] -> true | _ :: _ -> false
let nth_opt (i : int) (t : 'e t) : 'e option = if i < 0 then None else List.nth_opt t i
