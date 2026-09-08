(* e4_sched.ml — the host scheduler: machine -> domain, run queue, wake, quiescence.

   Re-homed from ocaml/link/e4_worker.ml, ocaml/link/e4_router.ml and ocaml/link/e4_host.ml
   at 7d53312; E4_bridge replaced by the engine record; changes:
     - the three files become one module, as the design's §1.2.1 disposition table says
       ("re-homed ... folded into e4_sched");
     - every `E4_bridge.<f>` call becomes a field of the `engine` record supplied at `start`,
       so this module links no Lean and no generated code;
     - `E4_worker.slot` gains a `fire : int option` tag. link matched `E4_bridge.Fire owner`
       to clear the queued-fire mark; a polymorphic decision cannot be matched, so the mark
       travels with the slot the rule pushed. Same behaviour, one word wider;
     - `E4_router.spawn`'s unknown-program `Invalid_argument` becomes `Error
       (`Unknown_program p)` (S5), and `spawn`'s `Stopped` likewise;
     - added: the bounded spin-then-block inbox read (survey #27, `config.spin_budget`), the
       admission predicate (#23, `admit`), the park triggers (#9, S4), `abandon` as a control
       message run on the owning domain (S3), and `shutdown` as E4_shutdown's four-hook DAG
       instead of `stop` + `join`;
     - `E4_worker.status` loses its Lean `fibers` field and gains `status_answer`,
       `snapshot` (a string, not a Lean value) and `abandoned`.

   The property list W1-W6 / R1-R4 / H1-H5 / S1-S6, and the seven deviations from the
   design's .mli text, are stated at the head of e4_sched.mli.

   THE MEMORY RULE, restated because it is the one rule a later edit can break silently: a
   machine's engine value is created (`Load`), stepped and released on its owning domain and
   never leaves it. Only strings and ints cross domains -- decisions in through the mailbox,
   event rows and status records out. The worker asserts `m.m_owner = domain` before every
   touch of a session (Eio's `check_our_domain`, survey §8.2), so the rule is checked and
   not merely intended. *)

type machine_id = int
type domain_id = int
type answer = Finished | Suspended | Refused | Delay

type ('m, 'd) engine = {
  init : unit -> unit;
  thread_init : unit -> unit;
  thread_finalize : unit -> unit;
  programs : unit -> string list;
  load : program:string -> fuel:int -> 'm;
  step : 'm -> fuel:int -> 'd -> 'm;
  release : 'm -> unit;
  finished : 'm -> bool;
  answer : 'm -> answer;
  armed : 'm -> int list;
  fire_of : int -> 'd;
  trace_len : 'm -> int;
  rows : 'm -> cursor:int -> string list;
  to_wire : 'd -> string;
  snapshot : 'm -> string;
  abandon : 'm E4_abandon.driver;
}

type config = {
  domains : int;
  mailbox_bound : int;
  ring_capacity : int;
  batch : int;
  spin_budget : int;
  finalizer_fuel : int;
  checkpoint_every : int;
  minor_heap_words : int;
}

(* Named constants, never `max_int` (trap #17), and every one of them documented in the
   .mli's `config_of_env`. *)
let default_domains = 2
let default_mailbox_bound = 1024
let default_ring_capacity = 1 lsl 16
let default_batch = 8
let default_spin_budget = 32
let default_checkpoint_every = 1024
let default_minor_heap_words = 1 lsl 21

let default_config =
  {
    domains = default_domains;
    mailbox_bound = default_mailbox_bound;
    ring_capacity = default_ring_capacity;
    batch = default_batch;
    spin_budget = default_spin_budget;
    finalizer_fuel = E4_abandon.default_finalizer_fuel;
    checkpoint_every = default_checkpoint_every;
    minor_heap_words = default_minor_heap_words;
  }

let env_int name default =
  match Sys.getenv_opt name with
  | None -> default
  | Some s -> ( match int_of_string_opt (String.trim s) with Some n -> n | None -> default)

let config_of_env () =
  {
    domains = env_int "E4_DOMAINS" default_config.domains;
    mailbox_bound = env_int "E4_MAILBOX_BOUND" default_config.mailbox_bound;
    ring_capacity = env_int "E4_RING_CAPACITY" default_config.ring_capacity;
    batch = env_int "E4_BATCH" default_config.batch;
    spin_budget = env_int "E4_SPIN_BUDGET" default_config.spin_budget;
    finalizer_fuel = env_int "E4_FINALIZER_FUEL" default_config.finalizer_fuel;
    checkpoint_every = env_int "E4_CHECKPOINT_EVERY" default_config.checkpoint_every;
    minor_heap_words = env_int "E4_MINOR_HEAP_WORDS" default_config.minor_heap_words;
  }

let describe_config c =
  Printf.sprintf
    "E4_sched config: domains=%d mailbox_bound=%d ring_capacity=%d batch=%d spin_budget=%d \
     finalizer_fuel=%d checkpoint_every=%d minor_heap_words=%d"
    c.domains c.mailbox_bound c.ring_capacity c.batch c.spin_budget c.finalizer_fuel
    c.checkpoint_every c.minor_heap_words

type status = {
  id : machine_id;
  domain : domain_id;
  program : string;
  fuel : int;
  steps : int;
  cursor : int;
  finished : bool;
  status_answer : answer;
  armed : int list;
  trace_len : int;
  snapshot : string option;
  abandoned : E4_abandon.report option;
}

(* ---- what crosses a domain boundary: ints, strings, and the mailbox handle ---- *)

type 'd slot = { seq : int; decision : 'd; fire : int option }

type 'd control =
  | Load of { id : int; program : string; fuel : int; mailbox : 'd slot E4_mailbox.t }
  | Inspect of { id : int; want_snapshot : bool; reply : status option E4_reply.t }
  | Abandon_req of {
      id : int;
      reason : string;
      budget : E4_abandon.budget;
      reply : E4_abandon.report option E4_reply.t;
    }
  | Stop

type 'd wake = Control of 'd control | Runnable of int
type 'd port = { index : int; inbox : 'd wake E4_inbox.t }
(* The router's row for a machine: where it lives and how to reach it. The program and the
   fuel are the OWNING domain's business (they live in the worker's `machine` record), so
   they are not duplicated here -- `inspect` reads them from the owner. *)
type 'd entry = { e_domain : int; e_mailbox : 'd slot E4_mailbox.t }

(* The worker's own view of a machine. Reachable only from the owning domain's table: this
   record is THE MEMORY RULE's boundary, and nothing here ever leaves the domain. *)
type ('m, 'd) machine = {
  m_id : int;
  m_owner : int;
  m_program : string;
  m_fuel : int;
  mutable session : 'm;
  m_mailbox : 'd slot E4_mailbox.t;
  mutable cursor : int;
  mutable steps : int;
  mutable m_finished : bool;
  mutable m_abandoned : E4_abandon.report option;
  queued_fires : (int, unit) Hashtbl.t; (* owners with a fire already in the mailbox *)
  mutable fire_refused : bool; (* the rule was refused during this batch: retry after it *)
}

type ('m, 'd) t = {
  eng : ('m, 'd) engine;
  cfg : config;
  progs : string list;
  ports : 'd port array;
  rings : E4_ring.t array;
  quiescence : E4_quiescence.t;
  mu : Mutex.t;
  table : (machine_id, 'd entry) Hashtbl.t;
  mutable next_id : int;
  mutable next_domain : int;
  mutable stopped : bool;
  seq : int Atomic.t;
  refused : int Atomic.t;
  subs_mu : Mutex.t;
  mutable finished_subs : (machine_id -> unit) list;
  mutable workers : unit Domain.t array;
  trig_mu : Mutex.t;
  triggers : (int * int * int, E4_trigger.t) Hashtbl.t;
  sd_mu : Mutex.t;
  mutable sd_report : E4_shutdown.report option;
}

(* ---- the stamped, counted push (M5, Q1, R1) ---- *)

(* The sequence number and the quiescence entry are taken under the mailbox lock, only if
   the push is accepted. Returns the sequence number. *)
let enqueue t ?fire mailbox decision =
  let seq = ref (-1) in
  match
    E4_mailbox.push_with mailbox (fun () ->
        E4_quiescence.enter t.quiescence;
        let s = Atomic.fetch_and_add t.seq 1 + 1 in
        seq := s;
        { seq = s; decision; fire })
  with
  | Ok () -> Ok !seq
  | Error `Full -> Error `Full

(* ---- the worker loop (W1-W6) ---- *)

let event_loop_rule t m =
  List.iter
    (fun owner ->
      if not (Hashtbl.mem m.queued_fires owner) then
        match enqueue t ~fire:owner m.m_mailbox (t.eng.fire_of owner) with
        | Ok _ -> Hashtbl.replace m.queued_fires owner ()
        | Error `Full ->
            m.fire_refused <- true;
            Atomic.incr t.refused)
    (t.eng.armed m.session)

(* W4: the rows since the cursor, once, in trace order; the cursor then IS `trace_len`. The
   decision's wire form is computed only when there are rows to tag with it. *)
let emit_rows t ~domain m ~seq ~wire =
  let len = t.eng.trace_len m.session in
  if len > m.cursor then begin
    let rows = t.eng.rows m.session ~cursor:m.cursor in
    m.cursor <- len;
    let w = wire () in
    List.iter
      (fun row -> E4_ring.append t.rings.(domain) { E4_ring.domain; machine = m.m_id; seq; decision = w; row })
      rows
  end

let apply t ~domain m { seq; decision; fire } =
  assert (m.m_owner = domain);
  (match fire with Some owner -> Hashtbl.remove m.queued_fires owner | None -> ());
  let next = t.eng.step m.session ~fuel:m.m_fuel decision in
  t.eng.release m.session;
  m.session <- next;
  m.steps <- m.steps + 1;
  emit_rows t ~domain m ~seq ~wire:(fun () -> t.eng.to_wire decision);
  event_loop_rule t m;
  if (not m.m_finished) && t.eng.finished next then begin
    m.m_finished <- true;
    let fs = Mutex.protect t.subs_mu (fun () -> t.finished_subs) in
    List.iter (fun f -> f m.m_id) fs
  end;
  E4_quiescence.leave t.quiescence

let runnable t ~domain table id =
  match Hashtbl.find_opt table id with
  | None -> () (* W5 says this cannot happen; a wake for an unknown machine is a no-op *)
  | Some m -> (
      match E4_mailbox.pop_batch m.m_mailbox ~max:t.cfg.batch with
      | [] -> ()
      | batch ->
          List.iter (apply t ~domain m) batch;
          if m.fire_refused then begin
            m.fire_refused <- false;
            event_loop_rule t m
          end)

let status_of t ~domain ~want_snapshot m =
  assert (m.m_owner = domain);
  ({
     id = m.m_id;
     domain;
     program = m.m_program;
     fuel = m.m_fuel;
     steps = m.steps;
     cursor = m.cursor;
     finished = t.eng.finished m.session;
     status_answer = t.eng.answer m.session;
     armed = t.eng.armed m.session;
     trace_len = t.eng.trace_len m.session;
     snapshot = (if want_snapshot then Some (t.eng.snapshot m.session) else None);
     abandoned = m.m_abandoned;
   }
    : status)

(* S3: the abandon pass runs HERE, on the machine's own domain, never in the caller's. *)
let abandon_here t ~domain table id ~reason ~budget =
  match Hashtbl.find_opt table id with
  | None -> None
  | Some m -> (
      assert (m.m_owner = domain);
      match m.m_abandoned with
      | Some r -> Some r (* AB5 *)
      | None ->
          let next, report = E4_abandon.run t.eng.abandon m.session ~reason ~budget in
          t.eng.release m.session;
          m.session <- next;
          m.m_abandoned <- Some report;
          let seq = Atomic.fetch_and_add t.seq 1 + 1 in
          emit_rows t ~domain m ~seq ~wire:(fun () -> "abandon:" ^ reason);
          Some report)

let control t ~domain table = function
  | Load { id; program; fuel; mailbox } ->
      Hashtbl.replace table id
        {
          m_id = id;
          m_owner = domain;
          m_program = program;
          m_fuel = fuel;
          session = t.eng.load ~program ~fuel;
          m_mailbox = mailbox;
          cursor = 0;
          steps = 0;
          m_finished = false;
          m_abandoned = None;
          queued_fires = Hashtbl.create 4;
          fire_refused = false;
        };
      E4_quiescence.leave t.quiescence
  | Inspect { id; want_snapshot; reply } ->
      E4_reply.fill reply (Option.map (status_of t ~domain ~want_snapshot) (Hashtbl.find_opt table id));
      E4_quiescence.leave t.quiescence
  | Abandon_req { id; reason; budget; reply } ->
      E4_reply.fill reply (abandon_here t ~domain table id ~reason ~budget);
      E4_quiescence.leave t.quiescence
  | Stop -> ()

(* Borrow #27: a FIXED spin budget, then block. Spinning changes WHEN a wake is seen, never
   WHICH wake is seen, so it cannot reach a decision. Never adaptive. *)
let pop_wake t (port : 'd port) =
  if t.cfg.spin_budget <= 0 then E4_inbox.pop port.inbox
  else
    let rec spin n =
      if n <= 0 then E4_inbox.pop port.inbox
      else
        match E4_inbox.pop_opt port.inbox with
        | Some w -> Some w
        | None ->
            Domain.cpu_relax ();
            spin (n - 1)
    in
    spin t.cfg.spin_budget

(* Returns after `Stop` (or a closed inbox), having released every machine on this domain
   and finalized the engine's thread state. *)
let worker t (port : 'd port) =
  let domain = port.index in
  t.eng.thread_init ();
  let table : (int, ('m, 'd) machine) Hashtbl.t = Hashtbl.create 64 in
  let rec loop () =
    match pop_wake t port with
    | None | Some (Control Stop) -> ()
    | Some (Control c) ->
        control t ~domain table c;
        loop ()
    | Some (Runnable id) ->
        runnable t ~domain table id;
        loop ()
  in
  Fun.protect
    ~finally:(fun () ->
      Hashtbl.iter (fun _ m -> t.eng.release m.session) table;
      Hashtbl.reset table;
      t.eng.thread_finalize ())
    (fun () ->
      try loop ()
      with e ->
        Printf.eprintf "E4_sched: domain %d died: %s\n%!" domain (Printexc.to_string e);
        raise e)

(* ---- the host (H1-H5) ---- *)

let start eng cfg =
  if cfg.domains < 1 then invalid_arg "E4_sched.start: at least one domain";
  if cfg.mailbox_bound < 1 then invalid_arg "E4_sched.start: mailbox_bound must be at least 1";
  if cfg.ring_capacity < 1 then invalid_arg "E4_sched.start: ring_capacity must be at least 1";
  if cfg.batch < 1 then invalid_arg "E4_sched.start: batch must be at least 1";
  if cfg.spin_budget < 0 then invalid_arg "E4_sched.start: negative spin_budget";
  if cfg.finalizer_fuel < 0 then invalid_arg "E4_sched.start: negative finalizer_fuel";
  if cfg.checkpoint_every < 0 then invalid_arg "E4_sched.start: negative checkpoint_every";
  if cfg.minor_heap_words > 0 then Gc.set { (Gc.get ()) with minor_heap_size = cfg.minor_heap_words };
  if Sys.getenv_opt "E4_LOG_CONFIG" <> None then prerr_endline (describe_config cfg);
  eng.init ();
  let t =
    {
      eng;
      cfg;
      progs = eng.programs ();
      ports = Array.init cfg.domains (fun index -> { index; inbox = E4_inbox.create () });
      rings = Array.init cfg.domains (fun domain -> E4_ring.create ~domain ~capacity:cfg.ring_capacity);
      quiescence = E4_quiescence.create ();
      mu = Mutex.create ();
      table = Hashtbl.create 64;
      next_id = 0;
      next_domain = 0;
      stopped = false;
      seq = Atomic.make 0;
      refused = Atomic.make 0;
      subs_mu = Mutex.create ();
      finished_subs = [];
      workers = [||];
      trig_mu = Mutex.create ();
      triggers = Hashtbl.create 64;
      sd_mu = Mutex.create ();
      sd_report = None;
    }
  in
  t.workers <- Array.map (fun port -> Domain.spawn (fun () -> worker t port)) t.ports;
  t

let config t = t.cfg
let domains t = Array.length t.ports
let last_seq t = Atomic.get t.seq
let refusals t = Atomic.get t.refused
let pending t = E4_quiescence.outstanding t.quiescence

let lookup t id =
  Mutex.protect t.mu (fun () ->
      if t.stopped then Error `Stopped
      else match Hashtbl.find_opt t.table id with None -> Error `Unknown | Some e -> Ok e)

let spawn ?domain t ~program ~fuel =
  if fuel < 0 then invalid_arg "E4_sched.spawn: negative fuel";
  if not (List.mem program t.progs) then Error (`Unknown_program program)
  else
    Mutex.protect t.mu (fun () ->
        if t.stopped then Error `Stopped
        else begin
          let n = Array.length t.ports in
          let d =
            match domain with
            | Some d -> ((d mod n) + n) mod n
            | None ->
                let d = t.next_domain in
                t.next_domain <- (d + 1) mod n;
                d
          in
          let id = t.next_id in
          t.next_id <- id + 1;
          let port = t.ports.(d) in
          let mailbox =
            E4_mailbox.create ~bound:t.cfg.mailbox_bound
              ~wake:(fun () -> ignore (E4_inbox.push port.inbox (Runnable id)))
              ()
          in
          Hashtbl.replace t.table id { e_domain = d; e_mailbox = mailbox };
          (* R4: `Load` is in the owner's inbox before the id is handed out. *)
          E4_quiescence.enter t.quiescence;
          ignore (E4_inbox.push port.inbox (Control (Load { id; program; fuel; mailbox })));
          Ok id
        end)

let send t id decision =
  match lookup t id with
  | Error (`Stopped | `Unknown) as e -> e
  | Ok e -> ( match enqueue t e.e_mailbox decision with Ok seq -> Ok seq | Error `Full -> Error `Full)

let send_many t id decisions =
  match lookup t id with
  | Error ((`Stopped | `Unknown) as e) -> Error e
  | Ok e ->
      let rec go acc n = function
        | [] -> Ok (List.rev acc)
        | d :: rest -> (
            match enqueue t e.e_mailbox d with
            | Ok s -> go (s :: acc) (n + 1) rest
            | Error `Full -> Error (`Full n))
      in
      go [] 0 decisions

let admit t id =
  match lookup t id with
  | Error _ -> E4_admit.None_now
  | Ok e ->
      E4_admit.of_state
        ~mailbox_len:(E4_mailbox.length e.e_mailbox)
        ~mailbox_bound:t.cfg.mailbox_bound ~in_flight:(pending t)

let domain_of t id = match lookup t id with Ok e -> Some e.e_domain | Error _ -> None

let machines t =
  Mutex.protect t.mu (fun () -> List.sort compare (Hashtbl.fold (fun id _ acc -> id :: acc) t.table []))

let run_until_quiescent ?timeout t =
  match timeout with
  | None ->
      E4_quiescence.wait_zero t.quiescence;
      true
  | Some seconds -> E4_quiescence.wait_zero_for t.quiescence ~seconds

let inspect ?(snapshot = false) t id =
  match lookup t id with
  | Error _ -> None
  | Ok e ->
      let reply = E4_reply.create () in
      E4_quiescence.enter t.quiescence;
      if E4_inbox.push t.ports.(e.e_domain).inbox (Control (Inspect { id; want_snapshot = snapshot; reply }))
      then E4_reply.await reply
      else begin
        E4_quiescence.leave t.quiescence;
        None
      end

let subscribe_finished t f = Mutex.protect t.subs_mu (fun () -> t.finished_subs <- t.finished_subs @ [ f ])
let ring_read t ~domain ~cursor = E4_ring.read t.rings.(domain) ~cursor

(* The merged rings: every ring from its oldest retained entry, ordered by sequence number,
   stable within a step (H5); the flag says whether any ring overflowed (S6). *)
let events t =
  let reads = Array.to_list (Array.map (fun r -> E4_ring.read r ~cursor:0) t.rings) in
  let gap = List.exists (fun (r : E4_ring.read) -> r.gap) reads in
  let entries = List.concat_map (fun (r : E4_ring.read) -> r.entries) reads in
  ( List.stable_sort (fun (a : E4_ring.entry) (b : E4_ring.entry) -> Int.compare a.seq b.seq) entries,
    gap )

(* ---- S4: the park triggers ---- *)

let trigger t id ~fiber ~token =
  let key = (id, fiber, token) in
  Mutex.protect t.trig_mu (fun () ->
      match Hashtbl.find_opt t.triggers key with
      | Some tr -> tr
      | None ->
          let tr = E4_trigger.create () in
          Hashtbl.replace t.triggers key tr;
          tr)

let signal_once t tr decision =
  let outcome = ref (Error `Already) in
  (match E4_trigger.state tr with
  | E4_trigger.Initial -> outcome := Error `Not_awaited
  | E4_trigger.Signaled -> outcome := Error `Already
  | E4_trigger.Awaiting _ -> ());
  E4_trigger.signal tr ~post:(fun (a : E4_trigger.addr) -> outcome := send t a.machine decision);
  !outcome

(* ---- S3: abandon, as a message to the owning domain ---- *)

let abandon_budget t =
  { E4_abandon.finalizer_fuel = t.cfg.finalizer_fuel; max_scopes = E4_abandon.default_max_scopes }

let abandon t id ~reason ~budget =
  match lookup t id with
  | Error ((`Stopped | `Unknown) as e) -> Error e
  | Ok entry ->
      let reply = E4_reply.create () in
      E4_quiescence.enter t.quiescence;
      if E4_inbox.push t.ports.(entry.e_domain).inbox (Control (Abandon_req { id; reason; budget; reply }))
      then (match E4_reply.await reply with Some r -> Ok r | None -> Error `Unknown)
      else begin
        E4_quiescence.leave t.quiescence;
        Error `Stopped
      end

(* ---- the ordered shutdown (SD1-SD6) ---- *)

(* Four hooks with `after` edges, so the order is the one written here and not the one
   registration happens to give: seal the router, drain to quiescence, stop the workers,
   join the domains. Reverse registration alone would run them backwards. *)
let shutdown ?(deadline = E4_shutdown.no_deadline) t =
  let claim = Mutex.protect t.sd_mu (fun () -> t.sd_report) in
  match claim with
  | Some r -> r
  | None ->
      let reg = E4_shutdown.Registry.create () in
      let seal =
        E4_shutdown.Registry.register reg ~loc:__LOC__ ~name:"seal-router" (fun () ->
            Mutex.protect t.mu (fun () -> t.stopped <- true))
      in
      let drain =
        E4_shutdown.Registry.register reg ~after:[ seal ] ~loc:__LOC__ ~name:"drain-machines" (fun () ->
            if deadline = E4_shutdown.no_deadline then E4_quiescence.wait_zero t.quiescence
            else
              ignore
                (E4_quiescence.wait_zero_for t.quiescence
                   ~seconds:(Float.max 0.0 (deadline -. Unix.gettimeofday ()))))
      in
      let stop =
        E4_shutdown.Registry.register reg ~after:[ drain ] ~loc:__LOC__ ~name:"stop-workers" (fun () ->
            Array.iter
              (fun (p : 'd port) ->
                ignore (E4_inbox.push p.inbox (Control Stop));
                E4_inbox.close p.inbox)
              t.ports)
      in
      let _join =
        E4_shutdown.Registry.register reg ~after:[ stop ] ~loc:__LOC__ ~name:"join-domains" (fun () ->
            Array.iter Domain.join t.workers)
      in
      let r = E4_shutdown.Registry.run reg ~deadline in
      Mutex.protect t.sd_mu (fun () ->
          match t.sd_report with
          | Some existing -> existing
          | None ->
              t.sd_report <- Some r;
              r)
