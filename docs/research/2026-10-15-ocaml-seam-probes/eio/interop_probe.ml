(* Standalone host interoperability probes, using existing runtimes.
   Tested: one structured job client on three Picos schedulers, and
   a domain-local-await wake channel inside Eio and on a plain domain.
   No Effect4 machine or custom scheduler is involved. *)

let check name value =
  if not value then failwith ("FAILED: " ^ name);
  Printf.printf "PASS %s\n%!" name

let structured_jobs () =
  let open Picos_std_structured in
  let starts = Atomic.make 0 and releases = Atomic.make 0 in
  let answer = Flock.join_after (fun () ->
    let job x = Flock.fork_as_promise (fun () ->
      ignore (Atomic.fetch_and_add starts 1);
      Fun.protect
        ~finally:(fun () -> ignore (Atomic.fetch_and_add releases 1))
        (fun () -> Control.yield (); x * x)) in
    let a = job 3 and b = job 4 in
    Promise.await a + Promise.await b) in
  answer, Atomic.get starts, Atomic.get releases

let check_jobs name run =
  check name (run structured_jobs = (25, 2, 2))

(* A foreign producer publishes copied bytes and only then signals readiness.
   This host channel uses the installed scheduler's wake mechanism. *)
let foreign_completion () =
  let trigger = Domain_local_await.prepare_for_await () in
  let result = Atomic.make None in
  let worker = Domain.spawn (fun () ->
    Atomic.set result (Some (Bytes.of_string "ready"));
    trigger.release ();
    trigger.release ()) in
  trigger.await ();
  Domain.join worker;
  Option.map Bytes.to_string (Atomic.get result)

let () =
  Picos_io_select.configure ();
  check_jobs "same job client on Picos FIFO"
    (fun main -> Picos_mux_fifo.run main);
  check_jobs "same job client on Picos thread scheduler"
    (fun main -> Picos_mux_thread.run main);
  check_jobs "same job client on Picos multidomain scheduler"
    (fun main -> Picos_mux_multififo.run_on ~n_domains:2 main);
  check "domain-local-await receives copied completion on plain domain"
    (foreign_completion () = Some "ready");
  Eio_main.run (fun _ ->
    check "same domain-local-await client receives completion inside Eio"
      (foreign_completion () = Some "ready"));
  print_endline "ALL INTEROPERABILITY PROBES PASSED"
