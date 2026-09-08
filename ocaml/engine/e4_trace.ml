(* E4_trace — the machine's event log, over `E4_log.Vec`.  The property list is in
   e4_trace.mli.

   Lane Q3's proposal N2 (2026-09-08-engine-lane-q3-delivery.md), landed here.  The carrier
   WAS `{ rev : 'e list; n : int }`: `emit` was one `List.rev_append`, but `nth_opt i` walked
   `n - i` conses, so a viewer reading the trace along its own axis — the reading axis of the
   design language, §3 — cost Theta(T^2) on a T-row trace.  `E4_log.Vec` (e4_log.mli:44-75) is
   the same append-only shape with O(1) amortised append and O(log (T/256)) random access, so
   `E4_trace` IS that vector and nothing else:

     type 'e t = 'e E4_log.Vec.t

   What the TRACE signature (api_engine.ml:29-35, `type 'e t / empty / emit / to_list /
   length`) sees is unchanged, byte for byte, and so is every law of the .mli:
     - `emit [] t` returns `t` ITSELF (TR2): the `[] ->` arm below, physically.
     - `emit evs t` is O(|evs|) amortised (TR3): one cons per event onto the open chunk, plus
       one 256-element array fill and one `Map` insertion every 256 events.
     - `to_list` is emission order and O(T) (TR3): `Vec.fold` visits every row once — it walks
       the frozen chunks with `Im.iter` and the open tail by a bounded recursion, so there is
       NO map lookup per row — into an array of exactly T slots, and the list is then consed
       BACKWARDS out of it, so the result costs T conses and one array rather than 2T conses
       (`fold` then `List.rev`) or T map walks (`Vec.slice`, which is `Vec.to_list`).  All
       three were measured (test/bench_trace.ml, cell W2c): at 1e6 rows this one takes
       33.3 ms against `fold` + `List.rev`'s 63.6 ms and `Vec.slice`'s 52.2 ms.  (At 6 003
       rows all three are under 0.1 ms, which is noise.)  The transient array is T words and
       is dropped in the same expression.  This is the one call `Api.Run.trace`
       (Api.lean:185-186) makes, once per run; the reversed accumulator did it in 16.8 ms at
       1e6, so this is the one place the substitution COSTS, and it costs 2x on a read that
       happens once.
     - `length` is O(1) (TR4): `Vec.len` is maintained incrementally.
     - `nth_opt i t` is now O(log (T/256)) instead of O(T - i) (TR7).
   L5 of e4_log.mli carries brief rule 3 here as well: every array a `t` can reach was filled
   once inside the `append` that created it and is never written again, so a saved machine
   holds no mutable structure anything can observe.

   Depends on: E4_log (same library) and the OCaml standard library only. *)

type 'e t = 'e E4_log.Vec.t

let empty : 'e t = E4_log.Vec.empty
let length (t : 'e t) : int = E4_log.Vec.length t
let is_empty (t : 'e t) : bool = E4_log.Vec.is_empty t

(* TR2 is the `[] ->` arm: the argument itself, physically.  The general arm appends in list
   order, which is the order `RunMachine.emit` appends in (Fibers.lean:585-587). *)
let emit (evs : 'e list) (t : 'e t) : 'e t =
  match evs with [] -> t | _ -> List.fold_left E4_log.Vec.append t evs

let to_list (t : 'e t) : 'e list =
  let n = E4_log.Vec.length t in
  if n = 0 then []
  else begin
    let a = Array.make n (E4_log.Vec.get_exn t 0) in
    E4_log.Vec.fold t ~init:() ~f:(fun i e () -> a.(i) <- e);
    let acc = ref [] in
    for i = n - 1 downto 0 do
      acc := Array.unsafe_get a i :: !acc
    done;
    !acc
  end

(* Row i of the finished trace, counted from the front of the emission order — which is the
   vector's own index, so this is one lookup and not a walk. *)
let nth_opt (i : int) (t : 'e t) : 'e option = E4_log.Vec.get t i
