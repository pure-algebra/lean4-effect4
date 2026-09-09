(* e4_sched.mli — the host scheduler: machine -> domain, run queue, wake, quiescence.

   What it is: `git:14e6835:ocaml/link/e4_worker.ml`, `e4_router.ml` and `e4_host.ml` re-homed into one
   module at 7d53312; `E4_bridge` is replaced by the {!engine} record of functions, so this
   file names neither Lean nor the generated engine and links neither. One machine has
   exactly one owning domain and exactly one worker loop (W1); a machine's engine value is
   created, stepped and released on that domain and never leaves it (THE MEMORY RULE); only
   strings and ints cross.
   Depends on: E4_mailbox, E4_inbox, E4_ring, E4_quiescence, E4_reply, E4_trigger, E4_admit,
   E4_shutdown, E4_abandon.

   Properties (R1-R4, W1-W6, H1-H5 carried over from link/README.md and the file heads, plus
   S1-S6 of 2026-09-08-engine-a3-queue-query.md §1.2.2):

     W1  At most one step in flight per machine: one machine, one owner domain, one
         sequential worker loop. Checked, not merely intended (Eio's `check_our_domain`,
         survey §8.2): the worker asserts the machine's owner is its own domain at every
         entry point that touches a session.
         [by construction; tested: sched-four-machines, sched-memory-rule]
     W2  A step runs to completion under the machine's fuel; a decision is popped only to be
         applied, once -- never lost, never re-applied. [by construction (M3)]
     W3  The event-loop rule: after every step, each armed owner has exactly one `fire`
         queued behind the decisions already in the mailbox; a refusal (mailbox full) is
         counted and retried after the batch. [by construction; tested: sched-rule-alone]
     W4  Event rows are handed out exactly once, in trace order: the cursor advances to
         `trace_len` after each read. [by construction; tested: sched-four-machines]
     W5  `Load` precedes every wake for the same machine in the inbox, so a woken machine is
         always in the table. [by construction (I1 FIFO); tested: sched-four-machines]
     W6  Quiescence accounting: `leave` is called once per applied decision, after its
         events, fires and finish hook. [by construction; tested: sched-four-machines]
     R1  Cross-machine order is the global sequence number, stamped at send under the target
         mailbox's lock (M5): per mailbox strictly increasing in FIFO order, and across
         mailboxes one total order every machine's application order respects.
         [by construction; tested: sched-four-machines]
     R2  A message to an unknown machine, to a stopped host, or into a full mailbox is a
         REFUSAL, never a silent drop. [by construction; tested: sched-refusals]
     R3  `spawn` of a program the engine does not have is a refusal. S5 moves it from
         link's `Invalid_argument` to the `result` side, because a caller can enumerate
         program names. [by construction; tested: sched-refusals]
     R4  `spawn` returns only after `Load` is in the owner's inbox, so any later send to the
         id is ordered after it (W5). [by construction]
     H1  `engine.init` runs exactly once, on the main domain, before any worker domain
         exists; each worker runs `engine.thread_init` first thing. [by construction]
     H2  A ring is written only by the worker of its domain (G1 checks it).
         [by construction; tested: sched-four-machines]
     H3  `run_until_quiescent` returns when nothing is pending anywhere (Q2).
         [by construction (W6); tested: sched-four-machines]
     H4  Finish hooks run on the finishing machine's domain and may `send`; the message is
         accepted before the finishing step leaves the pending count.
         [by construction; tested: sched-cross-machine]
     H5  `events` is the merge of the rings in sequence order, stable within a step.
         [by construction; tested: sched-four-machines]
     S1  Placement is unobservable. `spawn` picks a domain round-robin; nothing a machine can
         read depends on which domain it landed on. Consequence: there is NO `current_domain`
         row and none may be added -- refusal row A3-SCHED-DOMAIN-ROW (Q-A3-6, trap #14).
         [by construction; tested: sched-placement]
     S2  Admission before pop. {!admit} is a pure function of the saved host state, consulted
         BEFORE `pop_batch`, not discovered as a refusal after a push (survey #23). A
         refusal is a decision, so it must not be timing-dependent: an atomic length hint for
         lock-free fast refusal is explicitly rejected (survey §4.6).
         [by construction; tested: sched-admit]
     S3  Cross-domain cancellation is a MESSAGE, never a call: {!abandon} posts into the
         owner's inbox and the owner runs it, on the machine's own domain (Eio and Miou
         converge on this independently). [by construction; tested: abandon-accounts]
     S4  A wake is one-shot per drain cycle (M4) and a signal that races another signal posts
         at most one row (E4_trigger's three-state CAS): a foreign domain signalling twice
         cannot make the tape diverge on replay.
         [by construction; tested: sched-trigger-once]
     S5  Refuse, never drop, at every boundary: `Unknown` / `Stopped` / `Full` as a
         `result`; a violated precondition (a negative fuel, a zero domain count) is an
         exception (Mirage's rule, survey §7). [by construction; tested: sched-refusals]
     S6  Two objects, two names: the per-domain RING is observation and may drop-with-gap
         (G2); the LOG is the receipt and is complete. Never conflate them (trap #15).

   DEVIATIONS FROM THE DESIGN'S .mli TEXT (§1.2.2), each additive and each named here so
   lane D reads one contract and not two:
     (a) `engine` gains `answer` (the four-way alphabet of survey #1, Riot's `proc_state`),
         `snapshot` (what link's `Inspect ~snapshot:true` returned) and `abandon` (the
         `E4_abandon.driver`, without which {!abandon}'s signature -- which takes no driver
         -- cannot be honoured). Nothing was removed.
     (b) `inspect`, `status`, `last_seq` and `refusals` are added: they are link's
         `E4_router.inspect` / `E4_worker.status` / `last_seq` / `E4_host.refusals`, and the
         re-homed property tests are written against them.
     (c) `trigger` and `signal_once` are added: S4 is a law of this file and the design
         lists `E4_trigger` among its dependencies, but §1.2.2 gives no entry point that
         reaches it.
     (d) `send_many`'s "one lock acquisition" is not achieved: `E4_mailbox` (lane Q4,
         unchanged) exposes no batch push, so the pushes are sequential. The RESULT contract
         is honoured exactly -- `Full n` means the first [n] were accepted -- and the
         refusal row for the missing primitive is A3-SCHED-SEND-MANY-LOCK.
     (e) `config.ring_capacity` is documented in §1.2.2 as a power of two for masked
         indexing (#28); `E4_ring` as landed by lane Q4 indexes with `mod`, so this module
         requires only `capacity >= 1` and does not enforce a power of two. Refusal row
         A3-SCHED-RING-MASK.
     (f) `shutdown`'s `?deadline` is an ABSOLUTE instant on `Unix.gettimeofday`'s scale, as
         `E4_shutdown.run ~deadline` is; `run_until_quiescent`'s `?timeout` stays a
         DURATION, as link had it. Two words, two meanings, both documented.
     (g) `_ t` in §1.2.2's text is written `(_, _) t` here: the type has two parameters, so
         the design's one-parameter application does not elaborate. A transcription fix, not
         a design change. *)

type machine_id = int
type domain_id = int

type answer = Finished | Suspended | Refused | Delay
(** The step answer alphabet (survey #1, Riot `proc_state.mli`; proposal 11). `Delay` means
    "not ready, re-present the same row, consume nothing" (DL1) and is a STORE answer, not a
    decision (DL2), so it never reaches the tape. *)

type ('m, 'd) engine = {
  init : unit -> unit;  (** once, on the main domain (H1) *)
  thread_init : unit -> unit;  (** first thing on each worker *)
  thread_finalize : unit -> unit;
  programs : unit -> string list;
  load : program:string -> fuel:int -> 'm;
  step : 'm -> fuel:int -> 'd -> 'm;
  release : 'm -> unit;
  finished : 'm -> bool;
  answer : 'm -> answer;
  armed : 'm -> int list;  (** the armed dispatchers (R2-15) *)
  fire_of : int -> 'd;  (** the `fire owner` decision *)
  trace_len : 'm -> int;
  rows : 'm -> cursor:int -> string list;  (** the log rows since the cursor *)
  to_wire : 'd -> string;
  snapshot : 'm -> string;
  abandon : 'm E4_abandon.driver;
}
(** A record of functions, not a functor: one machine over one carrier is the case RWO says
    dictionary passing handles well, and packages-plan §4.4 forbids functors beyond what
    `Ml.Syntax` spells (survey §7). Nothing in this record names Lean, `ocaml/gen` or
    `ocaml/link`; the same scheduler drives any of them. *)

type config = {
  domains : int;
  mailbox_bound : int;  (** M2's bound; a refusal, never a drop *)
  ring_capacity : int;  (** see deviation (e) *)
  batch : int;  (** pop_batch size: the lock is taken once per batch *)
  spin_budget : int;
      (** #27: FIXED, never adaptive -- an adaptive budget would be timing-dependent,
          harmless here only because spinning changes WHEN, never WHICH. The worker tries
          this many non-blocking inbox reads before it blocks on the condition variable. *)
  finalizer_fuel : int;  (** D-A3-9: the abandon budget's per-scope fuel *)
  checkpoint_every : int;  (** D-A3-7: the replay_steps retention knob (carried, not used here) *)
  minor_heap_words : int;  (** raised well above the 256k default; survey §6 D *)
}

val default_config : config

val config_of_env : unit -> config
(** Octez's `Env` pattern (survey §6): every knob from one env-var record with documented
    defaults, logged at boot, so an operator tunes without a rebuild. The variables are
    [E4_DOMAINS], [E4_MAILBOX_BOUND], [E4_RING_CAPACITY], [E4_BATCH], [E4_SPIN_BUDGET],
    [E4_FINALIZER_FUEL], [E4_CHECKPOINT_EVERY], [E4_MINOR_HEAP_WORDS]; an unset or
    unparseable variable keeps {!default_config}'s value. Every value that reaches a
    decision is on the tape; nothing here does. *)

val describe_config : config -> string
(** The one line {!start} logs at boot when [E4_LOG_CONFIG] is set. *)

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
(** What `inspect` answers with: link's `E4_worker.status` without its Lean fiber list.
    Built on the owning domain and carrying only ints and strings (THE MEMORY RULE). *)

type ('m, 'd) t

val start : ('m, 'd) engine -> config -> ('m, 'd) t
(** H1. Spawns [config.domains] worker domains and returns once each has been created.
    @raise Invalid_argument if any of [domains], [mailbox_bound], [ring_capacity], [batch]
    is below 1, or if [spin_budget], [finalizer_fuel] or [checkpoint_every] is negative. *)

val config : ('m, 'd) t -> config
val domains : (_, _) t -> int

val spawn :
  ?domain:domain_id ->
  ('m, 'd) t ->
  program:string ->
  fuel:int ->
  (machine_id, [ `Unknown_program of string | `Stopped ]) result
(** S1, S5, R4: returns only after `Load` is in the owner's inbox, so any later send to the
    id is ordered after it. Without [?domain] the placement is round-robin and unobservable.
    @raise Invalid_argument if [fuel] is negative. *)

val send : ('m, 'd) t -> machine_id -> 'd -> (int, [ `Unknown | `Stopped | `Full ]) result
(** R1: the answer is the global sequence number, stamped under the target mailbox's lock,
    so per mailbox the stamps are strictly increasing in FIFO order and across mailboxes
    they are one total order every machine's application order respects. S5. *)

val send_many :
  ('m, 'd) t -> machine_id -> 'd list -> (int list, [ `Unknown | `Stopped | `Full of int ]) result
(** [`Full n] means the first [n] were accepted and the rest refused, so the caller never
    has to reconstruct a partial push. See deviation (d). *)

val admit : ('m, 'd) t -> machine_id -> E4_admit.t
(** S2. A pure function of saved host state: the target's mailbox length, the mailbox bound
    and the pending count. An unknown or stopped machine admits nothing. *)

val domain_of : (_, _) t -> machine_id -> domain_id option
val machines : (_, _) t -> machine_id list

val pending : (_, _) t -> int
(** The quiescence count: accepted-but-not-yet-applied work. Q1. *)

val last_seq : (_, _) t -> int
(** The last global sequence number stamped. R1. *)

val refusals : (_, _) t -> int
(** How many times the event-loop rule was refused at a full mailbox (W3). *)

val run_until_quiescent : ?timeout:float -> (_, _) t -> bool
(** H3, Q2, Q3. The timeout is a DURATION in seconds and a HOST deadline: a parked run
    spends no budget, and the value never reaches a decision. *)

val inspect : ?snapshot:bool -> ('m, 'd) t -> machine_id -> status option
(** Asks the owning domain for a status record and waits for the reply. Deviation (b). *)

val ring_read : (_, _) t -> domain:domain_id -> cursor:int -> E4_ring.read
val events : (_, _) t -> E4_ring.entry list * bool
(** H5: the merge of the rings in sequence order, stable within a step. The bool is "some
    ring overflowed": observation, not the receipt (S6). *)

val subscribe_finished : (_, _) t -> (machine_id -> unit) -> unit
(** H4: hooks run on the finishing machine's domain and may `send`; the message is accepted
    before the finishing step leaves the pending count. *)

val trigger : (_, _) t -> machine_id -> fiber:int -> token:int -> E4_trigger.t
(** S4, deviation (c). The one-shot trigger of one park, created on first ask and returned
    unchanged after: two domains that look up the same (machine, fiber, token) get the same
    trigger, which is what makes {!signal_once} post once between them. *)

val signal_once :
  ('m, 'd) t ->
  E4_trigger.t ->
  'd ->
  (int, [ `Unknown | `Stopped | `Full | `Already | `Not_awaited ]) result
(** Signal a trigger: the CAS winner sends [decision] to the awaited machine and answers
    with its sequence number; a loser, or a second signal, answers [`Already]; a trigger
    nobody awaited answers [`Not_awaited] and posts nothing (TR1, TR3). *)

val abandon :
  ('m, 'd) t ->
  machine_id ->
  reason:string ->
  budget:E4_abandon.budget ->
  (E4_abandon.report, [ `Unknown | `Stopped ]) result
(** S3, AB1-AB5. Posted into the owner's inbox and run there; the caller blocks on a reply
    cell. AB5: a second call on an abandoned machine returns the first report and runs no
    second pass. *)

val abandon_budget : (_, _) t -> E4_abandon.budget
(** The budget {!config}'s `finalizer_fuel` names, with `E4_abandon.default_max_scopes`. *)

val shutdown : ?deadline:float -> (_, _) t -> E4_shutdown.report
(** The ordered clean-up DAG, not `stop` + `join`: seal the router, drain to quiescence,
    stop the workers, join the domains -- four hooks with `after` edges, so SD2's order is
    the one written down and not the one registration happens to give. The report's
    `exit_code` is E4_shutdown's contract. SD6: a second call returns the first report.
    [?deadline] is an ABSOLUTE instant (deviation (f)); the default is no deadline. *)
