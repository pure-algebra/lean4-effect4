(* The daemon's own service alphabet.

   The estate describes a host boundary as a family of operations with an `OpSpec` row each
   (`git:c407ab7:Effect4/Target/TypeScript/ScriptFlow.lean:39`: `name`, `kind`, `requestTy`, `answerTy`,
   `errorTy`, `params`). The daemon *is* a host boundary, so its request set is written in
   that shape and not in prose: `families` answers the five service families in `OpSpec`
   rows, and `schema` answers the daemon's own requests in the same rows, so a caller reads
   one alphabet for the programs and one for the protocol.

   `kind` is `family` for every row: each is a traced operation of the daemon's own family.
   The type spellings are TypeScript, as `OpSpec` requires -- the wire is JSON and TypeScript
   is what the estate's other alphabets spell JSON shapes in.

   This is the table `README.md` §5 documents; when the swap to derived carriers lands
   (`docs/research/2026-09-04-ocaml-packages-plan.md` §2) the rows come from the request
   variant's `Variants.to_rank` and the reply record's `Fields.names` instead of from here. *)

open E4d_json

type row = {
  name : string;
  request_ty : string;
  answer_ty : string;
  error_ty : string;
  params : (string * string) list;
}

let program_params =
  [ ("source", "\"fixture\" | \"corpus\" | \"golden\" | \"id\"");
    ("family", "string?");
    ("program", "string?");
    ("programId", "string?");
    ("text", "string?");
    ("tape", "string?") ]

let bound_params =
  [ ("fuel", "number?"); ("rounds", "number?"); ("maxOps", "number?") ]

let mask_params = [ ("masks", "ReadonlyArray<string>?"); ("masksText", "string?") ]

let rows : row list =
  [ { name = "ping"; request_ty = "void"; answer_ty = "{ pong: true }"; error_ty = "never";
      params = [] };
    { name = "version"; request_ty = "void";
      answer_ty =
        "{ protocol: string; host: string; ocaml: string; pin: { effects: string }; \
         inputs: ReadonlyArray<{ path: string; sha256: string }>; requests: \
         ReadonlyArray<string> }";
      error_ty = "never"; params = [] };
    { name = "pins"; request_ty = "void"; answer_ty = "the `version` answer"; error_ty = "never";
      params = [] };
    { name = "schema"; request_ty = "void";
      answer_ty = "{ requests: ReadonlyArray<OpSpec>; properties: ReadonlyArray<Property> }";
      error_ty = "never"; params = [] };
    { name = "families"; request_ty = "void";
      answer_ty =
        "{ families: ReadonlyArray<{ family: string; source: string; programs: \
         ReadonlyArray<string>; operations: ReadonlyArray<OpSpec> }> }";
      error_ty = "never"; params = [] };
    { name = "masks"; request_ty = "void";
      answer_ty = "{ masks: ReadonlyArray<{ name: string; keeps: Record<string, boolean> }> }";
      error_ty = "never"; params = [] };
    { name = "programs"; request_ty = "void";
      answer_ty = "{ fixtures: ReadonlyArray<{ family: string; programs: ReadonlyArray<string> }>; \
                   corpus: ReadonlyArray<string> }";
      error_ty = "never"; params = [] };
    { name = "load"; request_ty = "ProgramRef";
      answer_ty = "{ programId: string; program: string; family: string; tape: string }";
      error_ty = "\"unknown-program\" | \"unknown-source\" | \"no-text\""; params = program_params };
    { name = "inspect"; request_ty = "ProgramRef";
      answer_ty = "{ inspect: { operations: ReadonlyArray<OpSpec>; alphabet: Alphabet; roots: \
                   ReadonlyArray<Root>; main?: ReadonlyArray<Step> } }";
      error_ty = "\"unknown-program\""; params = program_params };
    { name = "run"; request_ty = "ProgramRef & Bounds & Masks & { expect?: Rows; chunk?: number }";
      answer_ty = "{ rows: Rows; projections: ReadonlyArray<Projection>; outcome: Outcome; \
                   events: ReadonlyArray<RunEvent>; tsv: string; verdicts?: \
                   ReadonlyArray<Verdict>; stream?: StreamHead }";
      error_ty = "\"unknown-program\" | \"avatar-failure\" | \"stream-too-large\"";
      params = program_params @ bound_params @ mask_params
               @ [ ("expect", "string | ReadonlyArray<string> | undefined");
                   ("chunk", "number?") ] };
    { name = "step"; request_ty = "ProgramRef & Bounds";
      answer_ty = "{ machine: RunMachine; rowsSoFar: Rows; events: ReadonlyArray<RunEvent>; \
                   outcome: Outcome; complete: boolean }";
      error_ty = "\"unknown-program\" | \"avatar-failure\""; params = program_params @ bound_params };
    { name = "diff"; request_ty = "{ left: Rows; right: Rows } & Masks & { program?: string }";
      answer_ty = "{ verdicts: ReadonlyArray<Verdict>; agree: boolean; classified: Classified | null }";
      error_ty = "\"bad-diff\" | \"unknown-mask\"";
      params = [ ("left", "string | ReadonlyArray<string>");
                 ("right", "string | ReadonlyArray<string>");
                 ("program", "string?"); ("knownText", "string?") ] @ mask_params };
    { name = "explain"; request_ty = "ProgramRef & Bounds";
      answer_ty = "{ rows: ReadonlyArray<{ index: number; row: string; arms: \
                   ReadonlyArray<Arm>; events: ReadonlyArray<RunEvent> }>; granularity: \
                   \"flush-round\" | \"drive-command\" | \"coarse\"; buckets: number }";
      error_ty = "\"unknown-program\""; params = program_params @ bound_params };
    { name = "why"; request_ty = "ProgramRef & Masks & { reference: Rows }";
      answer_ty = "{ why: { diverges: boolean; mask?: string; rowIndex?: number; expected?: \
                   string; actual?: string; eventsUpToDifference: ReadonlyArray<RunEvent>; \
                   arms: ReadonlyArray<Arm>; classified: Classified | null } }";
      error_ty = "\"no-reference\" | \"unknown-program\"";
      params = program_params @ mask_params @ [ ("reference", "string | ReadonlyArray<string>") ] };
    { name = "reachable"; request_ty = "ProgramRef & Bounds";
      answer_ty = "{ reachable: { fibers: ReadonlyArray<ReachableFiber>; resumable: \
                   ReadonlyArray<number>; armed: ReadonlyArray<number>; observersPending: \
                   ReadonlyArray<PendingObserver>; finished: boolean } }";
      error_ty = "\"unknown-program\""; params = program_params @ bound_params };
    { name = "budget"; request_ty = "ProgramRef & Bounds";
      answer_ty = "{ budget: { maxOpsBeforeYield: number | null; yields: number; injections: \
                   ReadonlyArray<{ fiber: number; opCount: number }>; perFiber: \
                   ReadonlyArray<FiberBudget> } }";
      error_ty = "\"unknown-program\""; params = program_params @ bound_params };
    { name = "pull"; request_ty = "{ stream: string; cursor: number }";
      answer_ty = "{ stream: string; cursor: number; items: ReadonlyArray<unknown>; more: \
                   boolean; next: number | null; terminal?: unknown }";
      error_ty = "\"unknown-stream\" | \"out-of-order-pull\" | \"chunk-already-delivered\"";
      params = [ ("stream", "string"); ("cursor", "number") ] };
    { name = "streams"; request_ty = "void";
      answer_ty = "{ streams: ReadonlyArray<StreamHead>; open: number; max: number }";
      error_ty = "never"; params = [] };
    { name = "reset"; request_ty = "void"; answer_ty = "{ reset: true }"; error_ty = "never";
      params = [] } ]

let names = List.map (fun r -> r.name) rows

let json_of_row (r : row) : E4d_json.t =
  Obj
    [ ("name", Str r.name);
      ("kind", Str "family");
      ("requestTy", Str r.request_ty);
      ("answerTy", Str r.answer_ty);
      ("errorTy", Str r.error_ty);
      ( "params",
        List
          (List.map
             (fun (binder, ty) -> E4d_json.Obj [ ("binder", Str binder); ("type", Str ty) ])
             r.params) );
      ("arity", Int (max 1 (List.length r.params))) ]

let json : E4d_json.t = List (List.map json_of_row rows)

(* ------------------------------------------------------------ the stated behaviour

   README §0. Each row is one property, how it holds -- `by construction` or `tested` -- and
   the shape of the Lean theorem W4 would state over the same carrier. `schema` answers these
   next to the operation rows, so a caller reads the guarantees off the daemon rather than
   off the prose. *)

type property = { code : string; statement : string; how : string; theorem : string }

let properties : property list =
  [ { code = "W1";
      statement =
        "Every request may carry an `id`. A reply carries the same `id` back.";
      how = "by construction (E4d_protocol.request/response)";
      theorem = "forall q, (step s q).reply.id = q.id" };
    { code = "W2";
      statement =
        "At-least-once delivery is safe: a request replayed with the same non-null `id` \
         returns the recorded reply and leaves the session unchanged.";
      how = "by construction (the session's reply journal), tested (duplicate-request)";
      theorem =
        "forall s q, q.id <> Null -> let (s1, r1) = step s q in let (s2, r2) = step s1 q in \
         s2 = s1 /\\ r2 = r1" };
    { code = "W3";
      statement =
        "Replies are in request order, one per request, per session.";
      how = "by construction (E4d_server_loop.pump is a fold over the input lines)";
      theorem = "pump is List.foldl step: the i-th reply is the i-th request's" };
    { code = "W4";
      statement =
        "At most one request is in flight per session. The bound is 1: the loop reads a \
         request, answers it, and only then reads the next.";
      how = "by construction (E4d_server_loop.pump; the TCP listener accepts one connection \
             at a time)";
      theorem = "no interleaving to state" };
    { code = "W5";
      statement =
        "The reply journal is bounded: the last 64 answered ids per session. A replay older \
         than that is answered afresh, which is safe for every request but `load` (which \
         mints a new id).";
      how = "by construction (journal_bound), tested (journal-eviction)";
      theorem = "|journal s| <= 64" };
    { code = "R1";
      statement =
        "`run` is deterministic in (program, tape, maxOps, fuel, rounds): the same request \
         twice gives byte-identical rows, events and outcome. There is no clock, no \
         randomness and no ambient state -- the avatar's module-level state is reset at the \
         head of every run.";
      how = "by construction (E4d_reset.all before every run), tested (determinism, \
             hosts-agree, batch-state-is-reset)";
      theorem = "run p t b = run p t b" };
    { code = "R2";
      statement =
        "`step` snapshots are prefix-closed in `rounds`: the rows of a run at `r` rounds are \
         a prefix of the rows at `r+1`. They are NOT prefix-closed in `fuel`.";
      how = "tested (prefix-closed-in-rounds), and the counterexample for fuel is recorded \
             (parentInterruptDuringChildWait: 14 rows at fuel 3, 11 at fuel 4)";
      theorem = "rows (step p (rounds r)) <+: rows (step p (rounds (r+1)))" };
    { code = "R3";
      statement =
        "A `run` answer and a `step` answer at full bounds agree on the rows the run \
         produced, up to the terminal row `run` appends.";
      how = "by construction (both call the same `execute`), tested (step-complete-flag)";
      theorem = "rows (run p) = rows (step p full) ++ [terminal p]" };
    { code = "S1";
      statement = "A stream's chunks are delivered in index order and in no other (FIFO).";
      how = "by construction (E4d_stream.pull accepts only cursor = delivered), tested \
             (out-of-order-pull)";
      theorem = "pull s c = (s', Chunk _) -> c = s.delivered /\\ s'.delivered = c + 1" };
    { code = "S2";
      statement = "No chunk is delivered twice on the same stream (at most once).";
      how = "by construction (delivered only increases), tested (chunk-already-delivered)";
      theorem = "delivered is monotone, and pull refuses c < delivered" };
    { code = "S3";
      statement =
        "A stream's buffer is bounded: a reply of more than 100000 items is refused with \
         `stream-too-large` rather than truncated, and a session holds at most 8 open \
         streams.";
      how = "by construction (max_stream_items, max_open_streams), tested (stream-too-large, \
             too-many-streams)";
      theorem = "|s.chunks| * s.chunk_size <= max_stream_items /\\ |session.streams| <= 8" };
    { code = "S4";
      statement =
        "Back-pressure: nothing is produced until it is pulled. The chunks are cut once when \
         the stream is opened and `pull` reads; a client that stops pulling costs one \
         stream's storage and no further work.";
      how = "by construction (E4d_stream is data; pull is a total function)";
      theorem = "pull is pure: no effect on anything but the stream's cursor" };
    { code = "S5";
      statement =
        "Every stream ends explicitly: the item after the last chunk is a `Halt` carrying \
         the reply's terminal value, or a `Fail` carrying the reason. A stream never simply \
         ends.";
      how = "by construction (E4d_stream.pull is total), tested (stream-terminator)";
      theorem = "forall c >= |s.chunks|, snd (pull s c) = Halt _" } ]

let json_of_property (p : property) : E4d_json.t =
  Obj
    [ ("code", Str p.code);
      ("statement", Str p.statement);
      ("how", Str p.how);
      ("theoremShape", Str p.theorem) ]

let properties_json : E4d_json.t = List (List.map json_of_property properties)
