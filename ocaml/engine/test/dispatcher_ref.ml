(* dispatcher_ref.ml — the ORACLE for E4_buckets: a literal transcription of the Lean
   dispatcher, src/Effect4/Machine/Fibers.lean:115-155, into OCaml.

   It is deliberately the SLOW shape. `insert` appends with `tasks ++ [task]` exactly as
   Fibers.lean:140 does, `drain` is `(d.buckets.map Bucket.tasks).flatten` exactly as :153
   does, and `enqueue` sets `armed := true` exactly as :147 does. Nothing is optimised: the
   point of this file is that it can be read line by line against the Lean and seen to be the
   same function, so that a differential against it is evidence about E4_buckets and not about
   a second clever implementation.

   arm/disarm have no counterpart in `Dispatcher`; they are `RunMachine.arm`/`disarm`
   (Fibers.lean:627-634) read at the granularity of ONE owner's dispatcher: `arm` records that
   a host callback is scheduled, `disarm` that it ran. Lane G externs them onto E4_buckets, so
   the differential covers them.

   Depends on: nothing. Test-only; not part of the library. *)

type 'a bucket = { priority : int; tasks : 'a list }
type 'a t = { buckets : 'a bucket list; armed : bool }

(* Fibers.lean:134 *)
let empty = { buckets = []; armed = false }

(* Fibers.lean:136-142 *)
let rec insert priority task = function
  | [] -> [ { priority; tasks = [ task ] } ]
  | bucket :: rest ->
    if bucket.priority = priority then
      { priority = bucket.priority; tasks = bucket.tasks @ [ task ] } :: rest
    else if priority < bucket.priority then { priority; tasks = [ task ] } :: bucket :: rest
    else bucket :: insert priority task rest

(* Fibers.lean:145-147 *)
let enqueue d priority task = { buckets = insert priority task d.buckets; armed = true }

(* Fibers.lean:151-153 *)
let drain d =
  (List.concat (List.map (fun b -> b.tasks) d.buckets), { buckets = []; armed = false })

(* Fibers.lean:627-634, at one owner's dispatcher *)
let arm d = { d with armed = true }
let disarm d = { d with armed = false }

(* The observation the differential compares: `Dispatcher.bucketPairs` with each `Deque` read
   as its `toList` (src/OCaml5/Lib/Deque.lean:320-322). *)
let to_list d = List.map (fun b -> (b.priority, b.tasks)) d.buckets
let armed d = d.armed
