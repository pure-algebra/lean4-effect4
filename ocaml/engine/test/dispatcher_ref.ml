(* dispatcher_ref.ml — the ORACLE for E4_buckets: a literal transcription of the Lean
   dispatcher, Dispatcher (src/Effect4/Machine/Fibers.lean), into OCaml.

   It is deliberately the SLOW shape. `insert` appends with `tasks ++ [task]` exactly as
   Dispatcher.insert (src/Effect4/Machine/Fibers.lean) does, `drain` is `(d.buckets.map Bucket.tasks).flatten` exactly as Dispatcher.drain (src/Effect4/Machine/Fibers.lean)
   does, and `enqueue` sets `armed := true` exactly as Dispatcher.enqueue (src/Effect4/Machine/Fibers.lean) does. Nothing is optimised: the
   point of this file is that it can be read line by line against the Lean and seen to be the
   same function, so that a differential against it is evidence about E4_buckets and not about
   a second clever implementation.

   arm/disarm have no counterpart in `Dispatcher`; they are `RunMachine.arm`/`disarm`
   (RunMachine.arm (src/Effect4/Machine/Fibers.lean)) read at the granularity of ONE owner's dispatcher: `arm` records that
   a host callback is scheduled, `disarm` that it ran. Lane G externs them onto E4_buckets, so
   the differential covers them.

   Depends on: nothing. Test-only; not part of the library. *)

type 'a bucket =
  { priority : int
  ; tasks : 'a list
  }

type 'a t =
  { buckets : 'a bucket list
  ; armed : bool
  }

(* Dispatcher.empty (src/Effect4/Machine/Fibers.lean) *)
let empty = { buckets = []; armed = false }

(* Dispatcher.insert (src/Effect4/Machine/Fibers.lean) *)
let rec insert priority task = function
  | [] -> [ { priority; tasks = [ task ] } ]
  | bucket :: rest ->
    if bucket.priority = priority
    then { priority = bucket.priority; tasks = bucket.tasks @ [ task ] } :: rest
    else if priority < bucket.priority
    then { priority; tasks = [ task ] } :: bucket :: rest
    else bucket :: insert priority task rest
;;

(* Dispatcher.enqueue (src/Effect4/Machine/Fibers.lean) *)
let enqueue d priority task = { buckets = insert priority task d.buckets; armed = true }

(* Dispatcher.drain (src/Effect4/Machine/Fibers.lean) *)
let drain d =
  List.concat (List.map (fun b -> b.tasks) d.buckets), { buckets = []; armed = false }
;;

(* RunMachine.arm (src/Effect4/Machine/Fibers.lean), at one owner's dispatcher *)
let arm d = { d with armed = true }
let disarm d = { d with armed = false }

(* The observation the differential compares: `Dispatcher.bucketPairs` with each `Deque` read
   as its `toList` (Dispatcher.bucketPairs, git:ddb51b6c:src/OCaml5/Lib/Deque.lean). *)
let to_list d = List.map (fun b -> b.priority, b.tasks) d.buckets
let armed d = d.armed
