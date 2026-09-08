(* e4_buckets_list.ml -- the DISPATCHER carrier as Lean writes it: the list twin of
   E4_buckets, for the reference instance `Api_engine_ref`.

   What it is: a literal transcription of `Effect4.Machine.Dispatcher`
   (src/Effect4/Machine/Fibers.lean:115-155) into OCaml, behind the `DISPATCHER` module type
   the generator emits (ocaml/engine/api_engine.ml:52-64).  It is the SLOW shape on purpose:
   `insert` appends with `tasks ++ [task]` exactly as Fibers.lean:140 does, `drain` is
   `(d.buckets.map Bucket.tasks).flatten` exactly as :153 does, and `enqueue` sets
   `armed := true` exactly as :147 does.  Nothing is optimised, so the reference instance can
   be read line by line against the Lean and seen to be the same function.

   Why it exists beside test/dispatcher_ref.ml (lane Q1): that file is test-only -- it is
   `(modules test_buckets dispatcher_ref)` of a test stanza and is not part of the library, so
   `Api_engine.Make` cannot be applied to it.  This is the same transcription, in the library,
   under the signature lane G emits.  The two must stay identical; test_engine.ml does not
   compare them (they are the same eight lines), but test_buckets.ml differentials
   `dispatcher_ref` against `E4_buckets` and test_engine.ml differentials the whole engine
   over `E4_buckets` against the whole engine over this module, so both edges are covered.

   Depends on: nothing (polymorphic in the task; Stdlib only).

   Behaviours (the same B1-B7 as e4_buckets.mli; the Lean line is the licence):
   BL1  Ascending priorities, each exactly once -- `insert` keeps the order (Fibers.lean:141).
   BL2  FIFO within a bucket -- `tasks ++ [task]` (:140).
   BL3  A drain is the flatten in ascending priority (:153).
   BL4  `drain` returns `<[], false>` (:153).
   BL5  `enqueue` arms (:147); `disarm` clears the flag (RunMachine.disarm, :632-634).
   BL6  Persistence: no mutable field anywhere.                        by construction
   BL7  `of_list`/`to_list` are the canonical form E4_buckets uses, so a differential can
        compare the two carriers' dispatchers without knowing either representation. *)

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

(* Fibers.lean:145-147.  The label is the generated DISPATCHER's (api_engine.ml:58). *)
let enqueue d ~priority task =
  if priority < 0 then invalid_arg "E4_buckets_list.enqueue: negative priority";
  { buckets = insert priority task d.buckets; armed = true }

(* Fibers.lean:151-153 *)
let drain d =
  (List.concat_map (fun b -> b.tasks) d.buckets, { buckets = []; armed = false })

(* RunMachine.disarm at one owner's dispatcher, Fibers.lean:632-634. *)
let disarm d = { d with armed = false }
let armed d = d.armed
let is_empty d = List.for_all (fun b -> b.tasks = []) d.buckets
let length d = List.fold_left (fun n b -> n + List.length b.tasks) 0 d.buckets
let priorities d = List.map (fun b -> b.priority) d.buckets
let to_list d = List.map (fun b -> (b.priority, b.tasks)) d.buckets

let of_list ~armed rows =
  let rec check last = function
    | [] -> ()
    | (p, _) :: rest ->
      if p < 0 then invalid_arg "E4_buckets_list.of_list: negative priority";
      (match last with
       | Some q when q >= p -> invalid_arg "E4_buckets_list.of_list: priorities not ascending"
       | _ -> ());
      check (Some p) rest
  in
  check None rows;
  { buckets = List.map (fun (priority, tasks) -> { priority; tasks }) rows; armed }
