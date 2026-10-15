(* Standalone finite probes. Depends on OCaml 5.1.1 and Eio 1.2.
   Properties tested here: one-shot continuation use, explicit unwinding,
   cancellation cleanup, release ordering, reply/apply separation, and domain ownership.
   This is host evidence, not a test of the generated Effect4 machine. *)

let check name condition =
  if not condition then failwith ("FAILED: " ^ name);
  Printf.printf "PASS %s\n%!" name

type _ Effect.t += Park : unit Effect.t

let raw_effect_probe () =
  let finalizers = ref 0 in
  let saved : (unit, unit) Effect.Deep.continuation option ref = ref None in
  Effect.Deep.try_with
    (fun () -> Fun.protect
       ~finally:(fun () -> incr finalizers)
       (fun () -> Effect.perform Park))
    ()
    { effc = (fun (type a) (effect : a Effect.t) -> match effect with
        | Park -> Some (fun (k : (a, unit) Effect.Deep.continuation) -> saved := Some k)
        | _ -> None) };
  check "suspended continuation has not run finalizer" (!finalizers = 0);
  let k = Option.get !saved in
  (try Effect.Deep.discontinue k Exit with Exit -> ());
  check "explicit discontinue runs finalizer once" (!finalizers = 1);
  let second_use_refused =
    try Effect.Deep.continue k (); false with Effect.Continuation_already_resumed -> true
  in
  check "second continuation use is refused" second_use_refused

let eio_probes env =
  let p, resolver = Eio.Promise.create () in
  Eio.Promise.resolve resolver 7;
  check "promise first result" (Eio.Promise.await p = 7);
  let duplicate_refused =
    try Eio.Promise.resolve resolver 8; false with Invalid_argument _ -> true
  in
  check "promise duplicate resolution is refused" duplicate_refused;

  let release_order = ref [] in
  Eio.Switch.run (fun sw ->
    Eio.Switch.on_release sw (fun () -> release_order := !release_order @ [1]);
    Eio.Switch.on_release sw (fun () -> release_order := !release_order @ [2]));
  check "switch releases in reverse registration order" (!release_order = [2; 1]);

  let host_state = ref 0 and cleanup = ref 0 in
  let started, mark_started = Eio.Promise.create () in
  let cancellation_observed = ref false in
  (try Eio.Switch.run (fun sw ->
     Eio.Fiber.fork ~sw (fun () ->
       Fun.protect
         ~finally:(fun () -> Eio.Cancel.protect (fun () ->
           Eio.Fiber.yield (); incr cleanup))
         (fun () -> host_state := 9;
           Eio.Promise.resolve mark_started ();
           Eio.Fiber.await_cancel ()));
     Eio.Promise.await started;
     Eio.Switch.fail sw Exit)
   with Exit -> cancellation_observed := true);
  check "switch cancellation is observed" !cancellation_observed;
  check "state before cancellation remains" (!host_state = 9);
  check "protected cleanup yields then finishes once" (!cleanup = 1);

  (* These callbacks mimic receipt and application, without calling Effect4.
     The gate determines completion order, rather than a timing assumption. *)
  let received = ref [] and applied = ref [] in
  Eio.Switch.run (fun sw ->
    let gate, open_gate = Eio.Promise.create () in
    let a = Eio.Fiber.fork_promise ~sw (fun () ->
      Eio.Promise.await gate;
      received := !received @ ["A"];
      10) in
    let b = Eio.Fiber.fork_promise ~sw (fun () ->
      received := !received @ ["B"];
      Eio.Promise.resolve open_gate ();
      20) in
    let vb = Eio.Promise.await_exn b in
    let va = Eio.Promise.await_exn a in
    check "receipt follows chosen host completion order" (!received = ["B"; "A"]);
    check "receipt does not apply either reply" (!applied = []);
    applied := ["A", va; "B", vb]);
  check "application order can differ from receipt order"
    (!applied = ["A", 10; "B", 20]);

  let compensated = ref 0 and acquired = ref false in
  let got, signal_got = Eio.Promise.create () in
  (try Eio.Switch.run (fun sw ->
     Eio.Fiber.fork ~sw (fun () ->
       Fun.protect
         ~finally:(fun () -> Eio.Cancel.protect (fun () ->
           if !acquired then (incr compensated; acquired := false)))
         (fun () -> acquired := true;
           Eio.Promise.resolve signal_got ();
           Eio.Fiber.await_cancel ()));
     Eio.Promise.await got;
     Eio.Switch.fail sw Exit)
   with Exit -> ());
  check "cancelled untransferred acquisition is compensated once"
    (!compensated = 1 && not !acquired);

  Eio.Switch.run (fun sw ->
    let refused = Domain.join (Domain.spawn (fun () ->
      try Eio.Fiber.fork ~sw (fun () -> ()); false
      with Invalid_argument message ->
        message = "Switch accessed from wrong domain!")) in
    check "fork through a foreign-domain switch is refused" refused);

  Eio.Switch.run (fun sw ->
    let gate, open_gate = Eio.Promise.create () in
    let events = ref [] in
    let child = Eio.Fiber.fork_promise ~sw (fun () ->
      Eio.Promise.await gate;
      events := !events @ ["woken"]) in
    Eio.Promise.resolve open_gate ();
    let sum = ref 0 in
    for i = 1 to 10000 do sum := !sum + i done;
    events := !events @ ["cpu-finished"];
    Eio.Promise.await_exn child;
    check "ready fiber waits through finite non-yielding CPU segment"
      (!sum = 50005000 && !events = ["cpu-finished"; "woken"]));

  let escaped_file = Eio.Switch.run (fun sw ->
    Eio.Path.open_in ~sw Eio.Path.(Eio.Stdenv.cwd env / "input.txt")) in
  let closed_refused =
    try ignore (Eio.Flow.single_read escaped_file (Cstruct.create 1)); false
    with Invalid_argument _ -> true
  in
  check "escaped resource keeps its OCaml type but refuses use after close" closed_refused;

  Eio.Switch.run (fun sw ->
    let pool = Eio.Executor_pool.create ~sw ~domain_count:2
      (Eio.Stdenv.domain_mgr env) in
    let executions = Atomic.make 0 in
    let submit x = Eio.Executor_pool.submit_fork ~sw pool ~weight:1.0 (fun () ->
      ignore (Atomic.fetch_and_add executions 1);
      x * x) in
    let a = submit 3 and b = submit 4 in
    check "pool returns typed results" (Eio.Promise.await_exn a = 9 && Eio.Promise.await_exn b = 16);
    check "finite pool jobs execute once" (Atomic.get executions = 2))

let () =
  raw_effect_probe ();
  Eio_main.run eio_probes;
  print_endline "ALL FINITE PROBES PASSED"
