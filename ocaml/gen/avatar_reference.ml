(* REFERENCE COPY for the differential in gen_check.ml. Do not edit here.

   Source of truth: ocaml/avatar/deep_fibers.ml, lines 184-214 (the `task`,
   `bucket`, `dispatcher` types and the `Dispatcher` module), copied verbatim on 2026-09-04
   with ONE substitution: the avatar's `answer` type (deep_fibers.ml:174-182, the resume
   payload carrying a `value`/`cause`/`exitv list`/program) is the stand-in below, because
   the comparison only enqueues `Tstart` tasks and inspects bucket shapes. Nothing else was
   changed. *)

(* Stand-in for deep_fibers.ml:174-182. *)
type answer = Astub

(* `Task` (`:104`), `Bucket` (`:110`), `Dispatcher` (`:117`). *)
type task = Tstart of int | Tresume of int * int * answer
type bucket = { priority : int; mutable tasks : task list }
type dispatcher = { mutable buckets : bucket list; mutable armed : bool }

module Dispatcher = struct
  let empty () = { buckets = []; armed = false }

  (* `Scheduler.ts:105-131`: ascending priority, FIFO within a bucket. *)
  let rec insert priority task = function
    | [] -> [ { priority; tasks = [ task ] } ]
    | b :: rest ->
      if b.priority = priority then (
        b.tasks <- b.tasks @ [ task ];
        b :: rest)
      else if priority < b.priority then { priority; tasks = [ task ] } :: b :: rest
      else b :: insert priority task rest

  (* enqueue plus arming on the first task (`Scheduler.ts:207-212`). *)
  let enqueue d priority task =
    d.buckets <- insert priority task d.buckets;
    d.armed <- true

  (* `runTasks` drains the snapshot once (`Scheduler.ts:225-233`): a task enqueued during
     the drain waits for the next host task. *)
  let drain d =
    let tasks = List.concat_map (fun b -> b.tasks) d.buckets in
    d.buckets <- [];
    d.armed <- false;
    tasks
end
