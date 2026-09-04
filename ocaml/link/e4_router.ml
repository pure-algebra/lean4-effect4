(* e4_router.ml — machine id -> owning domain; spawn, send, inspect.

   What it is: the table from machine id to (domain, mailbox), the global sequence
   counter, and the three requests that cross it. `spawn` picks a domain (round-robin, or
   the caller's choice) and asks that domain's worker to load the program — the load
   happens ON the owning domain, through a control message, never here. `send` stamps the
   decision with the global sequence number and pushes it into the machine's mailbox.
   `inspect` asks the owner for a status record and waits for the reply.
   Depends on: E4_bridge (program names), E4_mailbox, E4_inbox, E4_reply, E4_quiescence,
   E4_worker (the port and control types).

   Properties:
     R1  Cross-machine order is the global sequence number, stamped at send under the
         target mailbox's lock (M5): per mailbox, the stamps are strictly increasing in
         FIFO order; across mailboxes, the stamps are one total order that every machine's
         application order respects. [by construction; tested: host-four-machines]
     R2  A message to an unknown machine is a refusal (`Error `Unknown`), a message after
         `stop` is a refusal (`Error `Stopped`), a full mailbox is a refusal
         (`Error `Full`, M2); never a silent drop. [by construction; tested:
         host-refusals]
     R3  `spawn` of a program the Lean table does not have raises `Invalid_argument`
         (the Lean side would silently load `p42`). [by construction; tested:
         host-refusals]
     R4  `spawn` returns only after `Load` is in the owner's inbox, so any later send to
         the id is ordered after it (W5). [by construction] *)

type machine_id = int

type entry = { domain : int; program : string; fuel : int; mailbox : E4_worker.slot E4_mailbox.t }

type t = {
  ports : E4_worker.port array;
  pending : E4_quiescence.t;
  mailbox_bound : int;
  programs : string list;
  mu : Mutex.t;
  table : (machine_id, entry) Hashtbl.t;
  mutable next_id : int;
  mutable next_domain : int;
  mutable stopped : bool;
  seq : int Atomic.t;
}

let create ~ports ~pending ~mailbox_bound =
  if Array.length ports = 0 then invalid_arg "E4_router.create: no ports";
  {
    ports;
    pending;
    mailbox_bound;
    programs = E4_bridge.program_names ();
    mu = Mutex.create ();
    table = Hashtbl.create 64;
    next_id = 0;
    next_domain = 0;
    stopped = false;
    seq = Atomic.make 0;
  }

(* The global sequence: 1, 2, 3, … *)
let stamp t () = Atomic.fetch_and_add t.seq 1 + 1
let last_seq t = Atomic.get t.seq
let domains t = Array.length t.ports
let programs t = t.programs

let spawn ?domain t ~program ~fuel =
  if not (List.mem program t.programs) then
    invalid_arg ("E4_router.spawn: unknown program " ^ program);
  if fuel < 0 then invalid_arg "E4_router.spawn: negative fuel";
  Mutex.protect t.mu (fun () ->
      if t.stopped then invalid_arg "E4_router.spawn: stopped";
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
        E4_mailbox.create ~bound:t.mailbox_bound
          ~wake:(fun () -> ignore (E4_inbox.push port.inbox (E4_worker.Runnable id)))
          ()
      in
      Hashtbl.replace t.table id { domain = d; program; fuel; mailbox };
      E4_quiescence.enter t.pending;
      ignore (E4_inbox.push port.inbox (E4_worker.Control (E4_worker.Load { id; program; fuel; mailbox })));
      id)

let lookup t id =
  Mutex.protect t.mu (fun () ->
      if t.stopped then Error `Stopped
      else match Hashtbl.find_opt t.table id with None -> Error `Unknown | Some e -> Ok e)

let send t id decision =
  match lookup t id with
  | Error (`Stopped | `Unknown) as e -> e
  | Ok e -> (
      match E4_worker.enqueue ~pending:t.pending ~stamp:(stamp t) e.mailbox decision with
      | Ok seq -> Ok seq
      | Error `Full -> Error `Full)

let inspect ?(snapshot = false) t id =
  match lookup t id with
  | Error _ -> None
  | Ok e ->
      let reply = E4_reply.create () in
      E4_quiescence.enter t.pending;
      if
        E4_inbox.push t.ports.(e.domain).inbox
          (E4_worker.Control (E4_worker.Inspect { id; snapshot; reply }))
      then E4_reply.await reply
      else begin
        E4_quiescence.leave t.pending;
        None
      end

let domain_of t id = match lookup t id with Ok e -> Some e.domain | Error _ -> None
let entry t id = match lookup t id with Ok e -> Some e | Error _ -> None

let machines t =
  Mutex.protect t.mu (fun () -> List.sort compare (Hashtbl.fold (fun id _ acc -> id :: acc) t.table []))

(* Refuse every later send, and tell each worker to shut down. *)
let stop t =
  Mutex.protect t.mu (fun () ->
      t.stopped <- true;
      Array.iter
        (fun (p : E4_worker.port) ->
          ignore (E4_inbox.push p.inbox (E4_worker.Control E4_worker.Shutdown));
          E4_inbox.close p.inbox)
        t.ports)
