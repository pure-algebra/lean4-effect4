(* Round three: witnesses for the `WithFiberAction` arms that no committed golden reaches.

   There is no Lean golden for these, so the reference is rc.112: `extra_rc112.mjs` runs the
   same five programs over `effect@4.0.0-rc.112` and prints the same rows. Three programs are
   marked avatar-only in the report, and say why:
     `snapshotAwaitNewChildren` -- rc.112 fuses the two halves into `Effect.awaitAllChildren`
       and exposes no unfused surface (the REFUSAL `git:c407ab7:harness/trace/fibers-tail.ts:33-35`
       already records), so only the outcome is comparable;
     `refusesUnimplementedArm` -- it is a refusal by construction;
     `awaitAllFailFast` -- rc.112 reaches the arm only inside `Effect.all`/`forEach` with
       concurrency (`Layer.ts:1597-1598`), which `extra_rc112.mjs` does not spell (added by
       the drift re-diff of 2026-09-04).

   No decision tape: the handover is an explicit `yield` service row, which both faces
   spell as one primitive (`Effect.yieldNow`, `internal/effect.ts:982-994`). *)

open Deep_fibers

let handle = function Vhandle h -> h | _ -> failwith "not a handle"
let fork code = Effect.perform (Op_fork (code, false))
(* The handover as a service row. `Prim.yieldNowWith` is a machine primitive, not a family
   operation, so the two rows are pushed here -- exactly where `traceService` pushes them:
   `op` at the call, `answer` when the effect completes, which for a yield is after the
   fiber has been resumed. *)
let yield () =
  push_row (Rop ("yield", Vunit));
  ignore (Effect.perform (Op_yield_now 0));
  push_row (Ranswer ("yield", Vunit))
let await_all hs = Effect.perform (Op_await_all (List.map handle hs))
let interrupt_all hs = Effect.perform (Op_interrupt_all (List.map handle hs))
let children_snapshot () = Effect.perform (Op_snapshot_children ())
let await_children s = ignore (Effect.perform (Op_await_new_children s))
let started () = Effect.perform (Op_started ())
let cleanups () = Effect.perform (Op_cleanups ())

(* `WithFiberAction.awaitAll`: a countdown over two children, answered as their exits. *)
let await_all_two () =
  let a = fork 0 in
  let b = fork 1 in
  await_all [ a; b ]

(* `WithFiberAction.interruptAll`: record on every target first, then await them all. The
   explicit yield gives both children the processor, so both are parked when the interrupt
   is recorded and both run their finalizers. *)
let interrupt_all_two () =
  let a = fork 4 in
  let b = fork 4 in
  yield ();
  let s = started () in
  ignore (interrupt_all [ a; b ]);
  ignore (cleanups ());
  s

(* M2: a child masked across a yield keeps running past a recorded interrupt, and takes it
   when it restores interruptibility. Body 5 pushes `started 6` after the yield; without the
   mask the interrupt would land at the yield park and 6 would never be pushed. *)
let masked_yield_keeps_running () =
  let a = fork 5 in
  yield ();
  ignore (interrupt_all [ a ]);
  let s = started () in
  ignore (cleanups ());
  s

(* `snapshotChildren` and `awaitNewChildren`, the two halves rc.112 fuses. *)
let snapshot_await_new_children () =
  let _a = fork 0 in
  let s = children_snapshot () in
  let _b = fork 1 in
  await_children s;
  started ()

(* M1: a sibling completes a Deferred the parent is parked on. `Prim.async` registers the
   waiter, the completing `sync` queues it into `dueResumes`, and `Cmd.drainDue` resumes the
   parent synchronously inside the child's own completion. *)
let sibling_completes_deferred () =
  let d = Store_fixtures.def_make () in
  let _c = fork 6 in
  Store_fixtures.def_await_value d

(* `WithFiberAction.refuse` (S3 §5.2): every arm this pass does not implement dies visibly. *)
let refuses_unimplemented_arm () =
  let _a = fork 0 in
  Effect.perform (Op_refuse "raceAll")

(* `WithFiberAction.awaitAllFailFast` (`Fibers.lean:948-950`; the drift re-diff of
   2026-09-04): a countdown over a failing child (body 2) and a never-finishing one (body 4),
   both deferred-started, so the awaiter parks on the first. When 2 fails, the first failing
   exit the countdown observes interrupts the target not yet visited -- 4, still unstarted --
   with the awaiter's id (`Pending.failFast`, `Fibers.lean:83-85`, `:1065-1071`), and the
   countdown still waits for it: the answer is the exits in input order, `[failure 1;
   interrupted]`, and 4's body never runs (`started` is `[2]`). Avatar-only, like
   `refusesUnimplementedArm`: rc.112 reaches the arm only through `Effect.all`/`forEach` with
   concurrency (`Layer.ts:1597-1598`), which `extra_rc112.mjs` does not spell, and
   `build-avatar.sh`'s `extra_programs` list does not name it; the machine trace
   (`EFFECT4_EVENTS=1`) is the evidence -- `interruptRecorded 0 2` right after
   `exited 1 {"failure":1}`. Tape: `0:0,1:0`. *)
let await_all_fail_fast () =
  let a = fork 2 in
  let b = fork 4 in
  (* the Lean-alphabet effect takes fiber ids, not wire handles (as `arm_await_all` maps) *)
  let fid f = handle_target "fiber" (handle f) in
  let exits = Effect.perform (Op_await_fibers_fail_fast [ fid a; fid b ]) in
  let s = started () in
  Vpair
    ( s,
      Vlist
        (List.map
           (function
             | Esuccess v -> Vsome v
             | Efailure c -> (
               match cause_fail_of c with
               | Some e -> Vpair (Vbool false, Vnat e)
               | None -> if cause_has_interrupt c then Vstring "interrupted" else Vnone))
           exits) )

let programs : (string * (unit -> value)) list =
  [ ("awaitAllTwo", await_all_two);
    ("interruptAllTwo", interrupt_all_two);
    ("maskedYieldKeepsRunning", masked_yield_keeps_running);
    ("snapshotAwaitNewChildren", snapshot_await_new_children);
    ("siblingCompletesDeferred", sibling_completes_deferred);
    ("refusesUnimplementedArm", refuses_unimplemented_arm);
    ("awaitAllFailFast", await_all_fail_fast) ]
