(* e4_worker.ml — one domain's worker: the machines it owns, and the step loop.

   What it is: the loop that runs on a worker domain. It owns a table of machines
   (id -> session, mailbox, event cursor, step count), takes wake-ups and control
   messages from its inbox, pops at most `batch` decisions from a woken machine's mailbox
   and applies each with `E4_bridge.step` at the machine's fuel. After each step it reads
   the new event rows since the cursor and hands them to `on_events`, reads `armed` and
   self-enqueues `Fire owner` for each armed owner without a fire already queued (the
   host event-loop rule: setImmediate FIFO, R2-15), and reports `finished`.
   Depends on: E4_bridge, E4_mailbox, E4_inbox, E4_reply, E4_quiescence.

   THE MEMORY RULE: a machine's Lean value is created (`Load`), stepped and released on
   this domain and never leaves it. Only strings and ints cross domains: decisions in
   (the mailbox), event rows, fiber lines and status records out. [by construction: the
   session is reachable only from this domain's table; `Inspect` answers with parsed
   strings; every old value is released here, right after the step that replaced it.]

   Properties:
     W1  At most one step in flight per machine. [by construction: one machine has one
         owner domain, one worker loop, and the loop is sequential]
     W2  A step runs to completion under fuel `F` (the machine's fuel, fixed at spawn);
         `E4_bridge.step` is total: fuel exhaustion leaves the machine at a frontier, and
         the decision that reached it has been applied — never lost, never re-applied.
         [by construction: a decision is popped only to be applied, once (M3)]
     W3  The event-loop rule: after every step, each armed owner has exactly one `Fire`
         queued behind the decisions already in the mailbox; a refusal (mailbox full) is
         reported and retried after the batch (the pop just made room), so an armed
         dispatcher is fired eventually as long as the machine is woken. [by construction;
         tested: host-four-machines (every machine finishes with Evaluate + Flush only, the
         fires coming from the rule)]
     W4  Event rows are handed out exactly once, in trace order: the cursor advances to
         `trace_len` after each read. [by construction (B6); tested: host-four-machines]
     W5  `Load` precedes every wake for the same machine in the inbox, so a woken machine
         is always in the table: the router pushes `Load` before it returns the id, and a
         wake exists only after a push into the mailbox, which needs the id. [by
         construction (I1 FIFO)]
     W6  Quiescence accounting: `leave` is called once per applied decision, after its
         events, fires and finish hook, so the count cannot reach zero while a
         consequence of the step is still pending. [by construction] *)

type slot = { seq : int; decision : E4_bridge.decision }

type status = {
  id : int;
  domain : int;
  program : string;
  fuel : int;
  steps : int;
  cursor : int;
  finished : bool;
  armed : int list;
  trace_len : int;
  fibers : E4_bridge.fiber list;
  snapshot : string option;
}

type control =
  | Load of { id : int; program : string; fuel : int; mailbox : slot E4_mailbox.t }
  | Inspect of { id : int; snapshot : bool; reply : status option E4_reply.t }
  | Shutdown

type wake = Control of control | Runnable of int

type port = { index : int; inbox : wake E4_inbox.t }

type config = {
  batch : int;
  stamp : unit -> int;
  pending : E4_quiescence.t;
  on_events : domain:int -> machine:int -> seq:int -> decision:E4_bridge.decision -> string list -> unit;
  on_finished : domain:int -> machine:int -> unit;
  on_refused : domain:int -> machine:int -> owner:int -> unit;
}

type machine = {
  m_id : int;
  m_program : string;
  m_fuel : int;
  mutable session : E4_bridge.t;
  mailbox : slot E4_mailbox.t;
  mutable cursor : int;
  mutable steps : int;
  mutable finished : bool;
  queued_fires : (int, unit) Hashtbl.t; (* owners with a Fire in the mailbox *)
  mutable fire_refused : bool; (* the rule was refused during this batch: retry after it *)
}

(* A stamped, counted push: the sequence number and the quiescence entry are taken under
   the mailbox lock, only if the push is accepted (M5, Q1). Returns the sequence number. *)
let enqueue ~pending ~stamp mailbox decision =
  let seq = ref (-1) in
  match
    E4_mailbox.push_with mailbox (fun () ->
        E4_quiescence.enter pending;
        let s = stamp () in
        seq := s;
        { seq = s; decision })
  with
  | Ok () -> Ok !seq
  | Error `Full -> Error `Full

let event_loop_rule cfg ~domain m =
  List.iter
    (fun owner ->
      if not (Hashtbl.mem m.queued_fires owner) then
        match enqueue ~pending:cfg.pending ~stamp:cfg.stamp m.mailbox (E4_bridge.Fire owner) with
        | Ok _ -> Hashtbl.replace m.queued_fires owner ()
        | Error `Full ->
            m.fire_refused <- true;
            cfg.on_refused ~domain ~machine:m.m_id ~owner)
    (E4_bridge.armed m.session)

let apply cfg ~domain m { seq; decision } =
  (match decision with E4_bridge.Fire owner -> Hashtbl.remove m.queued_fires owner | _ -> ());
  let next = E4_bridge.step m.session ~fuel:m.m_fuel decision in
  E4_bridge.release m.session;
  m.session <- next;
  m.steps <- m.steps + 1;
  let len = E4_bridge.trace_len next in
  if len > m.cursor then begin
    let rows = E4_bridge.events next ~cursor:m.cursor in
    m.cursor <- len;
    cfg.on_events ~domain ~machine:m.m_id ~seq ~decision rows
  end;
  event_loop_rule cfg ~domain m;
  if (not m.finished) && E4_bridge.finished next then begin
    m.finished <- true;
    cfg.on_finished ~domain ~machine:m.m_id
  end;
  E4_quiescence.leave cfg.pending

let runnable cfg ~domain table id =
  match Hashtbl.find_opt table id with
  | None -> () (* W5 says this cannot happen; a wake for an unknown machine is a no-op *)
  | Some m -> (
      match E4_mailbox.pop_batch m.mailbox ~max:cfg.batch with
      | [] -> ()
      | batch ->
          List.iter (apply cfg ~domain m) batch;
          if m.fire_refused then begin
            m.fire_refused <- false;
            event_loop_rule cfg ~domain m
          end)

let status_of ~domain ~snapshot m =
  let s = m.session in
  {
    id = m.m_id;
    domain;
    program = m.m_program;
    fuel = m.m_fuel;
    steps = m.steps;
    cursor = m.cursor;
    finished = E4_bridge.finished s;
    armed = E4_bridge.armed s;
    trace_len = E4_bridge.trace_len s;
    fibers = E4_bridge.fibers s;
    snapshot = (if snapshot then Some (E4_bridge.snapshot s) else None);
  }

let control cfg ~domain table = function
  | Load { id; program; fuel; mailbox } ->
      let session = E4_bridge.load ~program ~fuel in
      Hashtbl.replace table id
        {
          m_id = id;
          m_program = program;
          m_fuel = fuel;
          session;
          mailbox;
          cursor = 0;
          steps = 0;
          finished = false;
          queued_fires = Hashtbl.create 4;
          fire_refused = false;
        };
      E4_quiescence.leave cfg.pending
  | Inspect { id; snapshot; reply } ->
      E4_reply.fill reply (Option.map (status_of ~domain ~snapshot) (Hashtbl.find_opt table id));
      E4_quiescence.leave cfg.pending
  | Shutdown -> ()

(* The loop. Returns after `Shutdown` (or a closed inbox), having released every machine
   on this domain and finalized the Lean thread state. *)
let run cfg port =
  let domain = port.index in
  E4_bridge.thread_init ();
  let table : (int, machine) Hashtbl.t = Hashtbl.create 64 in
  let rec loop () =
    match E4_inbox.pop port.inbox with
    | None | Some (Control Shutdown) -> ()
    | Some (Control c) ->
        control cfg ~domain table c;
        loop ()
    | Some (Runnable id) ->
        runnable cfg ~domain table id;
        loop ()
  in
  Fun.protect
    ~finally:(fun () ->
      Hashtbl.iter (fun _ m -> E4_bridge.release m.session) table;
      Hashtbl.reset table;
      E4_bridge.thread_finalize ())
    (fun () ->
      try loop ()
      with e ->
        Printf.eprintf "E4_worker: domain %d died: %s\n%!" domain (Printexc.to_string e);
        raise e)
