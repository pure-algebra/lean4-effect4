(* e4_host.ml — the domains: N workers, their inboxes and rings, the router, quiescence.

   What it is: the process-level assembly. `start` initializes the Lean runtime once on
   the main domain, creates one port (inbox) and one event ring per worker domain, spawns
   the domains running `E4_worker.run`, and builds the router over the ports. Event rows
   go from a worker into ITS domain's ring (single writer, G1); the main domain reads the
   rings and merges by sequence number. `run_until_quiescent` waits for the pending count
   to reach zero; `shutdown` stops the workers and joins the domains.
   Depends on: everything below it (E4_bridge … E4_router).

   Properties:
     H1  The Lean runtime is initialized exactly once, on the main domain, before any
         worker domain exists; each worker initializes its own Lean thread state first
         thing (C4). [by construction]
     H2  A ring is written only by the worker of its domain: `on_events` is called on the
         stepping domain and appends to `rings.(domain)` (G1 checks it). [by construction;
         tested: host-four-machines]
     H3  `run_until_quiescent` returns when nothing is pending anywhere (Q2): every
         accepted decision applied, every load and inspect answered, every consequence of
         a finish hook already accepted. [by construction (W6)]
     H4  Finish hooks run on the finishing machine's domain and may `send` (the outward
         message of the architecture note): the message is accepted before the finishing
         step leaves the pending count. [by construction; tested: host-cross-machine]
     H5  `events` is the merge of the rings in sequence order, stable within a step, so
         each machine's rows appear in its application order (R1). [by construction;
         tested: host-four-machines] *)

type config = { domains : int; mailbox_bound : int; ring_capacity : int; batch : int }

let default_config = { domains = 2; mailbox_bound = 1024; ring_capacity = 1 lsl 16; batch = 8 }

type t = {
  config : config;
  ports : E4_worker.port array;
  rings : E4_ring.t array;
  pending : E4_quiescence.t;
  router : E4_router.t;
  mutable workers : unit Domain.t array;
  subs_mu : Mutex.t;
  mutable finished_subs : (int -> unit) list;
  refusals : int Atomic.t;
  mutable stopped : bool;
}

let start config =
  if config.domains < 1 then invalid_arg "E4_host.start: at least one domain";
  E4_bridge.init ();
  let pending = E4_quiescence.create () in
  let ports = Array.init config.domains (fun index -> { E4_worker.index; inbox = E4_inbox.create () }) in
  let rings = Array.init config.domains (fun domain -> E4_ring.create ~domain ~capacity:config.ring_capacity) in
  let router = E4_router.create ~ports ~pending ~mailbox_bound:config.mailbox_bound in
  let host =
    {
      config;
      ports;
      rings;
      pending;
      router;
      workers = [||];
      subs_mu = Mutex.create ();
      finished_subs = [];
      refusals = Atomic.make 0;
      stopped = false;
    }
  in
  let cfg =
    {
      E4_worker.batch = config.batch;
      stamp = E4_router.stamp router;
      pending;
      on_events =
        (fun ~domain ~machine ~seq ~decision rows ->
          let decision = E4_bridge.to_wire decision in
          List.iter
            (fun row -> E4_ring.append rings.(domain) { E4_ring.domain; machine; seq; decision; row })
            rows);
      on_finished =
        (fun ~domain:_ ~machine ->
          let fs = Mutex.protect host.subs_mu (fun () -> host.finished_subs) in
          List.iter (fun f -> f machine) fs);
      on_refused = (fun ~domain:_ ~machine:_ ~owner:_ -> Atomic.incr host.refusals);
    }
  in
  host.workers <- Array.map (fun port -> Domain.spawn (fun () -> E4_worker.run cfg port)) ports;
  host

(* A hook run on the finishing machine's domain, with its id (H4). *)
let subscribe_finished host f =
  Mutex.protect host.subs_mu (fun () -> host.finished_subs <- host.finished_subs @ [ f ])

let spawn ?domain host ~program ~fuel = E4_router.spawn ?domain host.router ~program ~fuel
let send host id decision = E4_router.send host.router id decision
let inspect ?snapshot host id = E4_router.inspect ?snapshot host.router id
let machines host = E4_router.machines host.router
let domain_of host id = E4_router.domain_of host.router id
let pending host = host.pending
let refusals host = Atomic.get host.refusals
let domains host = host.config.domains
let last_seq host = E4_router.last_seq host.router

let run_until_quiescent ?timeout host =
  match timeout with
  | None ->
      E4_quiescence.wait_zero host.pending;
      true
  | Some seconds -> E4_quiescence.wait_zero_for host.pending ~seconds

let ring_read host ~domain ~cursor = E4_ring.read host.rings.(domain) ~cursor

(* The merged log: every ring from its oldest retained entry, ordered by sequence number,
   stable within a step (H5); the flag says whether any ring overflowed. *)
let events host =
  let reads = Array.to_list (Array.map (fun r -> E4_ring.read r ~cursor:0) host.rings) in
  let gap = List.exists (fun (r : E4_ring.read) -> r.gap) reads in
  let entries = List.concat_map (fun (r : E4_ring.read) -> r.entries) reads in
  (List.stable_sort (fun (a : E4_ring.entry) (b : E4_ring.entry) -> Int.compare a.seq b.seq) entries, gap)

let shutdown host =
  if not host.stopped then begin
    host.stopped <- true;
    E4_router.stop host.router;
    Array.iter Domain.join host.workers
  end
