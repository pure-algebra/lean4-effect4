(* E4_cas — the on-disk content-addressed store.  See e4_cas.mli for what it is, the laws it
   holds itself to, and the deviations from docs/research/2026-09-08-engine-a2-persistence.md
   §1.8.

   The file is in eight parts:
     1. the view: a pack reader, the index, the watermark, the control payload, the staging table
     2. the types and their words
     3. lookups: resident bytes, kind, node, the insertion order
     4. admission: the stages in Lean's order, then the edges
     5. put, commit, the roots
     6. words: wf, closure, apply
     7. verify: its own scan, no index, no trusted digest
     8. opening, recovery, closing *)

open Effect4_engine

let host_limit_why = "a frame length at or above 2^62 (amendment M9)"

(* ============================================================ 1. the view *)

type counters = { mutable commits : int; mutable fsyncs : int; mutable conflicts : int }

(* A record staged by `put` and not yet written: its bytes answer every lookup, and its place
   joins the index at `commit`, because `E4_index.find` CONFIRMS at the record (IX1) and there
   is nothing at that place to confirm against until the write(2) has happened. *)
type staged = { st_bytes : string; st_seg : int; st_off : int; st_kind : E4_kind.t }

(* The by-Cid index (A2 §2.4 lists `byCid` as "a cache with a rebuild"; D5 said so and did not
   build one).  A `Cid` is the digest of a node's PAYLOAD (amendment M6) and the address is the
   digest of its whole bytes, so neither the pack's record header nor `E4_index` carries it:
   answering `by_cid` means hashing payloads.  It used to hash EVERY resident payload on every
   call -- O(store bytes) per call, which is lane P6's finding F6: `pin_all` at every
   checkpoint was one pass over the whole store per publish.  This table pays that hash ONCE
   per node over the life of the view and then answers in O(matches).

   Two halves, because the store has two: `c_tbl` covers the durable records up to `c_end` and
   is extended by one pass over what the last call did not see; `c_stbl` covers the records
   `put` has staged and `commit` has not yet promoted, and is folded from `v_order` (which
   `put` prepends to and `promote_staged` empties, at which point the durable walk picks the
   same records up).  Both hold their filings in write order reversed, so `by_cid_any` answers
   `durable @ staged` in insertion order -- exactly what the `nodes` scan answered. *)
type cidmap = {
  c_tbl : (string, (E4_kind.t * E4_addr.Addr.t) list ref) Hashtbl.t;
  mutable c_end : int * int; (* the durable watermark this table covers *)
  c_stbl : (string, (E4_kind.t * E4_addr.Addr.t) list ref) Hashtbl.t;
  mutable c_staged_n : int; (* how many entries of `v_order` are already folded in *)
}

type view = {
  v_dir : string;
  mutable v_reader : E4_pack.reader;
  v_slots : int;
  mutable v_index : E4_index.t option; (* None: dropped; the next query rebuilds it *)
  mutable v_cids : cidmap option; (* None: not built yet, or dropped; see `cid_map` *)
  mutable v_end : int * int; (* what this view indexes: the durable watermark *)
  v_staged : (string, staged) Hashtbl.t; (* address bytes -> the record put staged *)
  mutable v_order : string list; (* reversed: the staged addresses, in put order *)
  mutable v_control : E4_control.t;
  v_counters : counters;
  mutable v_closed : bool;
}

type ro = view

(* ============================================================ 2. the types *)

type outcome = Fresh | Duplicate | Conflict of E4_node.t

type admission =
  | Oversize
  | Host_limit of string
  | Bad_version of int
  | Malformed_ref
  | Handle_in_content
  | Dangling of E4_addr.Addr.t
  | Wrong_kind of { at : E4_addr.Addr.t; expected : E4_kind.t; actual : E4_kind.t }

type verify_error =
  | Digest_mismatch of E4_addr.Addr.t
  | Undecodable of E4_addr.Addr.t
  | Verify_malformed_ref of E4_addr.Addr.t
  | Verify_dangling of { node : E4_addr.Addr.t; missing : E4_addr.Addr.t }
  | Verify_wrong_kind of {
      node : E4_addr.Addr.t;
      ref_ : E4_addr.Addr.t;
      expected : E4_kind.t;
      actual : E4_kind.t;
    }
  | Root_unresolved of string

exception Locked of string
exception Store_error of string

type open_opts = { seg_max : int; index_slots : int; verify_on_open : bool }

let default_opts =
  { seg_max = E4_pack.default_seg_max; index_slots = 1 lsl 12; verify_on_open = false }

type recovery_stop =
  | Clean
  | Torn of E4_pack.scan_stop
  | Refused of { seg : int; off : int; addr : E4_addr.Addr.t; why : admission }

type recovery = {
  from : int * int;
  admitted : int;
  duplicates : int;
  ends_at : int * int;
  stop : recovery_stop;
  pack : E4_pack.recovery;
}

type t = {
  w_pack : E4_pack.t;
  w_view : view;
  w_recovery : recovery;
  w_blocked : string option; (* an unadmitted tail: no growth until an operator acts *)
  mutable w_closed : bool;
}

type binding = { addr : E4_addr.Addr.t; node : E4_node.t }

type word_error =
  | Refused_by of admission
  | Word_conflict of { at : E4_addr.Addr.t; occupant : E4_node.t }

type stats = {
  nodes : int;
  bytes : int;
  index_slots : int;
  index_bytes : int;
  commits : int;
  fsyncs : int;
  conflicts : int;
}

let outcome_word = function
  | Fresh -> "fresh"
  | Duplicate -> "duplicate"
  | Conflict _ -> "conflict"

let admission_word = function
  | Oversize -> "oversize"
  | Host_limit why -> "hostLimit " ^ why
  | Bad_version _ -> "badVersion"
  | Malformed_ref -> "malformedRef"
  | Handle_in_content -> "handleInContent"
  | Dangling a -> "dangling " ^ E4_addr.Addr.hex a
  | Wrong_kind _ -> "wrongKind"

let verify_error_word = function
  | Digest_mismatch _ -> "digestMismatch"
  | Undecodable _ -> "undecodable"
  | Verify_malformed_ref _ -> "malformedRef"
  | Verify_dangling { missing; _ } -> "dangling " ^ E4_addr.Addr.hex missing
  | Verify_wrong_kind _ -> "wrongKind"
  | Root_unresolved name -> "rootUnresolved " ^ name

let recovery_stop_word = function
  | Clean -> "clean"
  | Torn s -> "torn " ^ E4_pack.scan_stop_to_string s
  | Refused { seg; off; addr; why } ->
    Printf.sprintf "refused seg=%d off=%d %s %s" seg off (E4_addr.Addr.hex addr)
      (admission_word why)

(* ---- positions ---- *)

let pos_lt (s1, o1) (s2, o2) = s1 < s2 || (s1 = s2 && o1 < o2)
let record_end (seg, off) len = (seg, off + E4_pack.record_overhead + len)
let index_path ~dir = Filename.concat (Filename.concat dir "index") "000000.idx"

let rec mkdir_p d =
  if d <> "" && d <> "/" && d <> Filename.dirname d && not (Sys.file_exists d) then begin
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

(* ============================================================ 3. lookups *)

let key_of (a : E4_addr.Addr.t) = E4_addr.Addr.bytes a
let control_path ~dir = E4_control.control_path ~dir

(* Walk the pack's records from [from] up to (but not including) [upto], in write order.  The
   payload is not read: this is the 41-byte header scan (E4_pack PK4). *)
let walk_records view ~from ~upto ~f =
  let stop = ref E4_pack.Eof in
  let seq = E4_pack.scan_seq ~verify:false view.v_reader ~from in
  (try
     Seq.iter
       (fun s ->
         match s with
         | E4_pack.Stopped st ->
           stop := st;
           raise Exit
         | E4_pack.Scanned (pos, r) ->
           if not (pos_lt pos upto) then raise Exit;
           f pos r)
       seq
   with Exit -> ());
  !stop

(* The kind is the second byte of `node_bytes`, so it is not in the 41-byte header: filling
   `E4_index.entry.kind` costs a record read (lane P2's D5, `kind_at_default`).  Lane P4 holds
   the mmap and has no cheaper probe than that read, so the default is what is used and the
   cost is reported rather than hidden. *)
let rebuild_index view =
  let idx = E4_index.with_capacity ~capacity:(max 16 view.v_slots) in
  let start = E4_index.from_start in
  if pos_lt start view.v_end then
    ignore
      (walk_records view ~from:start ~upto:view.v_end ~f:(fun (seg, off) r ->
           match E4_index.kind_at_default view.v_reader ~seg ~off with
           | Some kind -> E4_index.add idx r.E4_pack.r_addr { E4_index.seg; off; kind }
           | None -> ()));
  view.v_index <- Some idx;
  idx

let index view = match view.v_index with Some i -> i | None -> rebuild_index view
let drop_index view = view.v_index <- None

(* ---- the by-Cid index: the two halves, and the one function that brings them up to date ---- *)

let cid_add tbl key entry =
  match Hashtbl.find_opt tbl key with
  | Some l -> l := entry :: !l
  | None -> Hashtbl.replace tbl key (ref [ entry ])

let cid_find tbl key = match Hashtbl.find_opt tbl key with Some l -> List.rev !l | None -> []

let new_cidmap () =
  { c_tbl = Hashtbl.create 1024;
    c_end = E4_index.from_start;
    c_stbl = Hashtbl.create 16;
    c_staged_n = 0 }

let reset_staged_cids view =
  match view.v_cids with
  | None -> ()
  | Some m ->
    Hashtbl.reset m.c_stbl;
    m.c_staged_n <- 0

let drop_cids view = view.v_cids <- None

(* Bring the by-Cid index up to the watermark and to the staged set, and answer it.  The
   durable half is extended by ONE pass over the records the last call did not see; a watermark
   that went BACKWARDS (a truncating recovery) is not extendable and the map is thrown away.
   The staged half is folded from the front of `v_order`, which holds the staged addresses
   newest first. *)
let cid_map view =
  let m =
    match view.v_cids with
    | Some m when not (pos_lt view.v_end m.c_end) -> m
    | _ ->
      let m = new_cidmap () in
      view.v_cids <- Some m;
      m
  in
  if pos_lt m.c_end view.v_end then begin
    ignore
      (walk_records view ~from:m.c_end ~upto:view.v_end ~f:(fun (seg, off) r ->
           match E4_pack.read_at view.v_reader ~seg ~off with
           | None -> ()
           | Some (_, bytes) -> (
             match E4_node.decode bytes with
             | Error _ -> ()
             | Ok n ->
               cid_add m.c_tbl (E4_sha256.digest n.E4_node.payload)
                 (n.E4_node.kind, r.E4_pack.r_addr))));
    m.c_end <- view.v_end
  end;
  let staged = Hashtbl.length view.v_staged in
  if staged < m.c_staged_n then begin
    Hashtbl.reset m.c_stbl;
    m.c_staged_n <- 0
  end;
  if staged > m.c_staged_n then begin
    (* the first `staged - c_staged_n` of `v_order` are the new ones, newest first, so taking
       them from the front and consing puts them back in PUT order *)
    let rec take k l acc =
      if k <= 0 then acc else match l with [] -> acc | x :: r -> take (k - 1) r (x :: acc)
    in
    List.iter
      (fun key ->
        match Hashtbl.find_opt view.v_staged key with
        | None -> ()
        | Some s -> (
          match E4_node.decode s.st_bytes with
          | Error _ -> ()
          | Ok n ->
            cid_add m.c_stbl (E4_sha256.digest n.E4_node.payload)
              (n.E4_node.kind, E4_addr.Addr.of_digest key)))
      (take (staged - m.c_staged_n) view.v_order []);
    m.c_staged_n <- staged
  end;
  m
let index_count view = E4_index.count (index view)
let count view = E4_index.count (index view) + Hashtbl.length view.v_staged

let find_entry view a = E4_index.find_in view.v_reader (index view) a

let resident_bytes view (a : E4_addr.Addr.t) =
  match Hashtbl.find_opt view.v_staged (key_of a) with
  | Some s -> Some s.st_bytes
  | None -> (
    match find_entry view a with
    | None -> None
    | Some e -> (
      match E4_pack.read_at view.v_reader ~seg:e.E4_index.seg ~off:e.E4_index.off with
      | Some (recorded, bytes) when E4_addr.Addr.equal recorded a -> Some bytes
      | _ -> None))

let get_kind view a =
  match Hashtbl.find_opt view.v_staged (key_of a) with
  | Some s -> Some s.st_kind
  | None -> ( match find_entry view a with None -> None | Some e -> Some e.E4_index.kind)

let get_bytes view a = resident_bytes view a

let get_node view a =
  match resident_bytes view a with
  | None -> None
  | Some bytes -> ( match E4_node.decode bytes with Ok n -> Some n | Error _ -> None)

let mem view a =
  Hashtbl.mem view.v_staged (key_of a) || E4_index.mem_in view.v_reader (index view) a

let resolves view (r : E4_addr.Ref.t) =
  match get_kind view r.E4_addr.Ref.addr with
  | Some k -> E4_kind.equal k r.E4_addr.Ref.kind
  | None -> false

(* `Store.nodes` (Store.lean:73-75): insertion order, which is the pack's write order.  It is
   read back from the pack rather than held in memory — the index is off-heap on purpose and a
   list of every address would put it back on the heap. *)
let addresses view =
  let acc = ref [] in
  let start = E4_index.from_start in
  if pos_lt start view.v_end then
    ignore (walk_records view ~from:start ~upto:view.v_end ~f:(fun _ r -> acc := r.E4_pack.r_addr :: !acc));
  let staged = List.rev_map (fun k -> E4_addr.Addr.of_digest k) view.v_order in
  List.rev_append !acc (List.rev staged)

let nodes view =
  List.filter_map
    (fun a -> match get_node view a with Some n -> Some (a, n) | None -> None)
    (addresses view)

(* ============================================================ 4. admission *)

(* CS2 / L-CAS-4.  The stages that are functions of the node alone, in Lean's order
   (Store.lean:262-276), with amendment M2's handle test at A2 owner question OQ4's default
   position — after `malformedRef`, before the edges.  Moving it is moving one element of this
   list, and `E4_node.check_pure` (lane P0's ND10) is the same order stated once more. *)
type stage = St_bad_version | St_malformed_ref | St_handle_in_content

let admission_stages = [ St_bad_version; St_malformed_ref; St_handle_in_content ]

(* `Oversize` is not in the list because it cannot move: `malformedRef` and the handle test
   are defined only on a payload that parses (lane P0's D3), and Lean tests `payload.WF`
   first for the same reason (Store.lean:263).  The three that CAN move are the list, and
   moving amendment M2's handle test — A2 owner question OQ4 — is moving one element of it. *)
let stage_refusal (n : E4_node.t) (sc : E4_node.scan) = function
  | St_bad_version -> if n.E4_node.version <> 0 then Some (Bad_version n.E4_node.version) else None
  | St_malformed_ref -> if sc.E4_node.malformed then Some Malformed_ref else None
  | St_handle_in_content ->
    if E4_kind.is_content n.E4_node.kind && sc.E4_node.handles <> [] then Some Handle_in_content
    else None

let check_pure (n : E4_node.t) =
  (* ONE traversal of the payload for all three tests: `payload_ok`, `malformed_ref` and
     `handles` are the same walk, and the put path is hot. *)
  match E4_node.scan_payload n.E4_node.payload with
  | Error E4_node.Host_limit -> Error (Host_limit host_limit_why)
  | Error _ -> Error Oversize
  | Ok sc ->
    let rec go = function
      | [] -> Ok ()
      | s :: rest -> ( match stage_refusal n sc s with Some a -> Error a | None -> go rest)
    in
    go admission_stages

(* `Store.checkAll` (Store.lean:192-198) over `Node.checkedEdges` (:297): in order, spec edge
   first, the genesis exempt from it and nothing else. *)
let check_edges view (n : E4_node.t) =
  let rec go = function
    | [] -> Ok ()
    | (e : E4_addr.Ref.t) :: rest -> (
      match get_kind view e.E4_addr.Ref.addr with
      | None -> Error (Dangling e.E4_addr.Ref.addr)
      | Some k ->
        if E4_kind.equal k e.E4_addr.Ref.kind then go rest
        else Error (Wrong_kind { at = e.E4_addr.Ref.addr; expected = e.E4_addr.Ref.kind; actual = k }))
  in
  go (E4_node.checked_edges n)

let admissible view n = match check_pure n with Error a -> Error a | Ok () -> check_edges view n

(* ============================================================ 5. put, commit, roots *)

let ensure_open t =
  if t.w_closed then invalid_arg "E4_cas: the writer is closed";
  match t.w_blocked with Some why -> raise (Store_error why) | None -> ()

let occupant_node bytes =
  match E4_node.decode bytes with
  | Ok n -> n
  | Error _ ->
    (* A resident record whose bytes do not decode can only be a forged one: this module never
       files such a record.  It is still exhibited, leniently, rather than hidden. *)
    if String.length bytes >= 34 then (
      match E4_kind.of_byte (Char.code bytes.[1]) with
      | Some kind ->
        { E4_node.version = Char.code bytes.[0];
          kind;
          spec = String.sub bytes 2 32;
          payload = String.sub bytes 34 (String.length bytes - 34) }
      | None ->
        raise (Store_error "the occupant's kind byte is not registered; it cannot be exhibited"))
    else raise (Store_error "the occupant is shorter than a node header")

let put t (n : E4_node.t) =
  ensure_open t;
  let view = t.w_view in
  match admissible view n with
  | Error a -> Error a
  | Ok () -> (
    let bytes = E4_node.encode n in
    let addr = E4_addr.Addr.of_digest (E4_sha256.digest bytes) in
    match resident_bytes view addr with
    | Some resident when String.equal resident bytes -> Ok (Duplicate, addr)
    | Some resident ->
      view.v_counters.conflicts <- view.v_counters.conflicts + 1;
      Ok (Conflict (occupant_node resident), addr)
    | None ->
      let seg, off = E4_pack.stage t.w_pack ~addr ~node_bytes:bytes in
      let key = key_of addr in
      Hashtbl.replace view.v_staged key
        { st_bytes = bytes; st_seg = seg; st_off = off; st_kind = n.E4_node.kind };
      view.v_order <- key :: view.v_order;
      Ok (Fresh, addr))

let put_bytes t bytes =
  match E4_node.decode bytes with
  | Ok n -> put t n
  | Error (E4_node.Bad_version b) -> Error (Bad_version b)
  | Error E4_node.Host_limit -> Error (Host_limit host_limit_why)
  | Error _ -> Error Oversize

let promote_staged view =
  if Hashtbl.length view.v_staged > 0 then begin
    let idx = index view in
    Hashtbl.iter
      (fun key s ->
        E4_index.add idx (E4_addr.Addr.of_digest key)
          { E4_index.seg = s.st_seg; off = s.st_off; kind = s.st_kind })
      view.v_staged;
    Hashtbl.reset view.v_staged;
    view.v_order <- []
  end;
  (* The staged half of the by-Cid index is now below the watermark `commit` is about to
     advance, so the durable walk will re-derive it; keeping it would double every filing. *)
  reset_staged_cids view

(* A reader caches each segment's size at the moment it maps it and only re-stats when a walk
   is about to run off the end (e4_pack.ml:170-186).  A record committed after that moment
   lives past the cached size, so a read AT its offset — which is what `E4_index.find`'s
   confirmation does — would be `Short` rather than the record.  The watermark moving is
   exactly when that can happen, so the reader is replaced there.  Segments are mapped lazily,
   so a replacement costs one mmap per segment actually touched afterwards. *)
let refresh_reader view =
  let old = view.v_reader in
  view.v_reader <- E4_pack.open_reader ~dir:view.v_dir;
  E4_pack.close_reader old

let write_control view =
  E4_control.commit ~path:(control_path ~dir:view.v_dir) view.v_control;
  view.v_counters.fsyncs <- view.v_counters.fsyncs + 1;
  view.v_counters.commits <- view.v_counters.commits + 1

(* CS5: one write(2) and one fsync(2) per touched pack segment, then the control file's
   watermark by tmp+rename+fsync.  The group commit and the watermark advance are one step:
   nothing between them can leave a durable record below an unadvanced watermark that a later
   open would have to re-admit, and nothing can advance the watermark over bytes that are not
   yet durable. *)
let commit t =
  ensure_open t;
  let view = t.w_view in
  let staged = E4_pack.staged_count t.w_pack in
  E4_pack.sync t.w_pack;
  if staged > 0 then view.v_counters.fsyncs <- view.v_counters.fsyncs + 1;
  promote_staged view;
  let pe = E4_pack.pack_end t.w_pack in
  if pe <> view.v_end then refresh_reader view;
  view.v_end <- pe;
  if E4_control.pack_end view.v_control <> pe then begin
    view.v_control <- E4_control.set_pack_end view.v_control pe;
    write_control view
  end

let root view name = E4_control.root view.v_control name
let roots view = E4_control.roots view.v_control
let next_version view name = E4_control.next_version view.v_control name
let generation view = E4_control.generation view.v_control
let dir t = t.w_view.v_dir
let read_only t = t.w_view

let advance_root t ?prev (r : E4_control.root) =
  ensure_open t;
  commit t;
  let view = t.w_view in
  let resolve a = get_kind view a in
  match E4_control.advance_root view.v_control ~resolve ?prev r with
  | Error e -> Error e
  | Ok payload ->
    view.v_control <- payload;
    write_control view;
    Ok ()

(* ============================================================ 6. words *)

(* `Binding.admissibleAfter` (src/Effect4/Store/Word.lean:59-63) with the bindings before it
   carried as a digest -> kind table. *)
let admissible_after (seen : (string, E4_kind.t) Hashtbl.t) (b : binding) =
  let n = b.node in
  let key = key_of b.addr in
  n.E4_node.version = 0
  && E4_node.payload_ok n.E4_node.payload = Ok ()
  && (not (E4_node.malformed_ref n))
  && String.equal (E4_sha256.digest (E4_node.encode n)) key
  && (not (Hashtbl.mem seen key))
  && List.for_all
       (fun (e : E4_addr.Ref.t) ->
         match Hashtbl.find_opt seen (key_of e.E4_addr.Ref.addr) with
         | Some k -> E4_kind.equal k e.E4_addr.Ref.kind
         | None -> false)
       (E4_node.checked_edges n)

let word_wf w =
  let seen = Hashtbl.create 64 in
  List.for_all
    (fun b ->
      if admissible_after seen b then begin
        Hashtbl.replace seen (key_of b.addr) b.node.E4_node.kind;
        true
      end
      else false)
    w

(* `closureGo` / `Store.closure` (Word.lean:334-346), transcribed: skip what is already
   emitted, walk the checked edges with one unit of fuel less, then emit under `emit`'s guard.
   `seen` is exactly the accumulator's digests, so the guard is `emit`'s. *)
let closure view (r : E4_addr.Ref.t) =
  let fuel0 = count view in
  let seen : (string, E4_kind.t) Hashtbl.t = Hashtbl.create 64 in
  let acc = ref [] in
  let rec go fuel (a : E4_addr.Addr.t) =
    if fuel <= 0 then ()
    else if Hashtbl.mem seen (key_of a) then ()
    else
      match get_node view a with
      | None -> ()
      | Some n ->
        List.iter (fun (e : E4_addr.Ref.t) -> go (fuel - 1) e.E4_addr.Ref.addr) (E4_node.checked_edges n);
        let b = { addr = a; node = n } in
        if admissible_after seen b then begin
          acc := b :: !acc;
          Hashtbl.replace seen (key_of a) n.E4_node.kind
        end
  in
  go fuel0 r.E4_addr.Ref.addr;
  List.rev !acc

let apply_word t w =
  let rec go = function
    | [] -> Ok ()
    | b :: rest -> (
      match put t b.node with
      | Error a -> Error (Refused_by a)
      | Ok (Conflict m, at) -> Error (Word_conflict { at; occupant = m })
      | Ok ((Fresh | Duplicate), _) -> go rest)
  in
  go w

(* ============================================================ 7. verify *)

(* CS7 / L-CAS-6.  `verify` builds its own table by scanning the pack — it never consults the
   index — and it never trusts a record's recorded digest: every record is re-hashed. *)
let verify view =
  let start = E4_index.from_start in
  let order = ref [] in
  let tbl : (string, int * int) Hashtbl.t = Hashtbl.create 256 in
  if pos_lt start view.v_end then
    ignore
      (walk_records view ~from:start ~upto:view.v_end ~f:(fun (seg, off) r ->
           let key = key_of r.E4_pack.r_addr in
           order := (key, (seg, off)) :: !order;
           if not (Hashtbl.mem tbl key) then Hashtbl.replace tbl key (seg, off)));
  let order = List.rev !order in
  let kinds : (string, E4_kind.t) Hashtbl.t = Hashtbl.create 256 in
  let read_bytes (seg, off) =
    match E4_pack.read_at view.v_reader ~seg ~off with Some (_, b) -> Some b | None -> None
  in
  let kind_at key =
    match Hashtbl.find_opt kinds key with
    | Some k -> Some k
    | None -> (
      match Hashtbl.find_opt tbl key with
      | None -> None
      | Some pos -> (
        match read_bytes pos with
        | None -> None
        | Some bytes -> (
          match E4_node.decode bytes with
          | Error _ -> None
          | Ok n ->
            Hashtbl.replace kinds key n.E4_node.kind;
            Some n.E4_node.kind)))
  in
  let edges_of a n =
    let rec go = function
      | [] -> Ok ()
      | (e : E4_addr.Ref.t) :: rest -> (
        match kind_at (key_of e.E4_addr.Ref.addr) with
        | None -> Error (Verify_dangling { node = a; missing = e.E4_addr.Ref.addr })
        | Some k ->
          if E4_kind.equal k e.E4_addr.Ref.kind then go rest
          else
            Error
              (Verify_wrong_kind
                 { node = a; ref_ = e.E4_addr.Ref.addr; expected = e.E4_addr.Ref.kind; actual = k }))
    in
    go (E4_node.checked_edges n)
  in
  (* `Store.verifyNode` (Word.lean:749-755), in `verifyNodes`' order. *)
  let verify_one key pos =
    let a = E4_addr.Addr.of_digest key in
    match read_bytes pos with
    | None -> Error (Undecodable a)
    | Some bytes ->
      if not (String.equal (E4_sha256.digest bytes) key) then Error (Digest_mismatch a)
      else (
        match E4_node.decode bytes with
        | Error _ -> Error (Undecodable a)
        | Ok n -> if E4_node.malformed_ref n then Error (Verify_malformed_ref a) else edges_of a n)
  in
  let rec nodes_pass = function
    | [] -> Ok ()
    | (key, pos) :: rest -> ( match verify_one key pos with Ok () -> nodes_pass rest | e -> e)
  in
  let rec roots_pass = function
    | [] -> Ok ()
    | (r : E4_control.root) :: rest -> (
      match kind_at (key_of r.E4_control.digest) with
      | Some k when E4_kind.equal k r.E4_control.kind -> roots_pass rest
      | _ -> Error (Root_unresolved r.E4_control.name))
  in
  match nodes_pass order with Error e -> Error e | Ok () -> roots_pass (E4_control.roots view.v_control)

let verify_node view a =
  match resident_bytes view a with
  | None -> Error (Verify_dangling { node = a; missing = a })
  | Some bytes ->
    if not (String.equal (E4_sha256.digest bytes) (key_of a)) then Error (Digest_mismatch a)
    else (
      match E4_node.decode bytes with
      | Error _ -> Error (Undecodable a)
      | Ok n ->
        if E4_node.malformed_ref n then Error (Verify_malformed_ref a)
        else
          let rec go = function
            | [] -> Ok ()
            | (e : E4_addr.Ref.t) :: rest -> (
              match get_kind view e.E4_addr.Ref.addr with
              | None -> Error (Verify_dangling { node = a; missing = e.E4_addr.Ref.addr })
              | Some k ->
                if E4_kind.equal k e.E4_addr.Ref.kind then go rest
                else
                  Error
                    (Verify_wrong_kind
                       { node = a; ref_ = e.E4_addr.Ref.addr; expected = e.E4_addr.Ref.kind; actual = k }))
          in
          go (E4_node.checked_edges n))

let closed view =
  List.for_all
    (fun (_, n) -> List.for_all (fun e -> resolves view e) (E4_node.checked_edges n))
    (nodes view)

(* ============================================================ queries that are not edges *)

(* Insertion order, and the same answer the `nodes` scan gave: durable filings in write order,
   then the staged ones in put order.  O(matches) once the index is warm (lane P6 finding F6;
   the numbers are in 2026-09-08-engine-lane-w-delivery.md item 4). *)
let by_cid_any view (c : E4_addr.Cid.t) =
  let m = cid_map view in
  let want = E4_addr.Addr.bytes c in
  cid_find m.c_tbl want @ cid_find m.c_stbl want

let by_cid view k c =
  List.filter_map (fun (k', a) -> if E4_kind.equal k k' then Some a else None) (by_cid_any view c)

let reachable view (a : E4_addr.Addr.t) =
  let want = key_of a in
  let seen = Hashtbl.create 64 in
  let rec go (d : E4_addr.Addr.t) =
    let key = key_of d in
    if Hashtbl.mem seen key then false
    else begin
      Hashtbl.replace seen key ();
      String.equal key want
      ||
      match get_node view d with
      | None -> false
      | Some n -> List.exists (fun (e : E4_addr.Ref.t) -> go e.E4_addr.Ref.addr) (E4_node.checked_edges n)
    end
  in
  List.exists (fun (r : E4_control.root) -> go r.E4_control.digest) (roots view)

(* ---- the pins (amendment M1; D8) ---- *)

let pin t ~name kind (c : E4_addr.Cid.t) =
  ensure_open t;
  let view = t.w_view in
  match by_cid view kind c with
  | [] -> Error (E4_control.Dangling c)
  | a :: _ ->
    let name = E4_control.normalise_name name in
    advance_root t
      { E4_control.name; root_kind = E4_control.Pin; kind; digest = a; version = next_version view name }

let pin_all t ~job cids =
  ensure_open t;
  let view = t.w_view in
  let job_hex = E4_addr.Addr.hex job in
  let plans = List.map (fun c -> (c, by_cid_any view c)) cids in
  (* M1: refuse the whole publish before minting anything when some Cid has no filing. *)
  match List.find_opt (fun (_, filings) -> filings = []) plans with
  | Some (c, _) -> Error (E4_control.Dangling c)
  | None ->
    let rec mint = function
      | [] -> Ok ()
      | (c, filings) :: rest -> (
        let cid_hex = E4_addr.Addr.hex c in
        let rec one i = function
          | [] -> Ok ()
          | (kind, a) :: more -> (
            let name =
              E4_control.normalise_name
                (if i = 1 then Printf.sprintf "runs/%s/pin/%s" job_hex cid_hex
                 else Printf.sprintf "runs/%s/pin/%s/%d" job_hex cid_hex i)
            in
            match
              advance_root t
                { E4_control.name;
                  root_kind = E4_control.Pin;
                  kind;
                  digest = a;
                  version = next_version view name }
            with
            | Error e -> Error e
            | Ok () -> one (i + 1) more)
        in
        match one 1 filings with Error e -> Error e | Ok () -> mint rest)
    in
    mint plans

(* ============================================================ 8. opening *)

let stats view =
  let idx = index view in
  let bytes =
    List.fold_left
      (fun acc s ->
        match
          try Some (Unix.stat (E4_pack.seg_path ~dir:view.v_dir s)).Unix.st_size
          with Unix.Unix_error _ -> None
        with
        | Some n -> acc + n
        | None -> acc)
      0
      (E4_pack.segments view.v_reader)
  in
  { nodes = E4_index.count idx + Hashtbl.length view.v_staged;
    bytes;
    index_slots = E4_index.slots idx;
    index_bytes = E4_index.bytes idx;
    commits = view.v_counters.commits;
    fsyncs = view.v_counters.fsyncs;
    conflicts = view.v_counters.conflicts }

let read_control ~dir =
  match E4_control.read ~path:(control_path ~dir) with
  | Ok p -> Some p
  | Error E4_control.Missing -> None
  | Error e -> raise (Store_error ("control: " ^ E4_control.open_error_word e))

(* The watermark a control file names, made safe to scan from: never below a segment's head,
   never past a segment's end, and never into a segment that is not there.  Crash family
   X4(b) — "pack_end names bytes that are not there" — lands here and falls back to a full
   re-admission from the first record. *)
let clamp_watermark ~dir (seg, off) =
  let start = E4_index.from_start in
  if seg < 0 || off < E4_pack.head_length then start
  else
    match
      try Some (Unix.stat (E4_pack.seg_path ~dir seg)).Unix.st_size with Unix.Unix_error _ -> None
    with
    | Some size when off <= size -> (seg, off)
    | _ -> start

let make_view ~dir ~slots ~control ~upto =
  { v_dir = dir;
    v_reader = E4_pack.open_reader ~dir;
    v_slots = slots;
    v_index = None;
    v_cids = None;
    v_end = upto;
    v_staged = Hashtbl.create 64;
    v_order = [];
    v_control = control;
    v_counters = { commits = 0; fsyncs = 0; conflicts = 0 };
    v_closed = false }

let open_ro ~dir =
  let control = match read_control ~dir with Some p -> p | None -> E4_control.initial in
  let upto = clamp_watermark ~dir (E4_control.pack_end control) in
  make_view ~dir ~slots:default_opts.index_slots ~control ~upto

let reopen_ro view =
  let control = match read_control ~dir:view.v_dir with Some p -> p | None -> E4_control.initial in
  let upto = clamp_watermark ~dir:view.v_dir (E4_control.pack_end control) in
  view.v_control <- control;
  if view.v_end <> upto then refresh_reader view;
  if pos_lt view.v_end upto then begin
    (match view.v_index with
     | None -> ()
     | Some idx ->
       ignore
         (walk_records view ~from:view.v_end ~upto ~f:(fun (seg, off) r ->
              match E4_index.kind_at_default view.v_reader ~seg ~off with
              | Some kind -> E4_index.add idx r.E4_pack.r_addr { E4_index.seg; off; kind }
              | None -> ())));
    view.v_end <- upto
  end
  else if pos_lt upto view.v_end then begin
    view.v_end <- upto;
    view.v_index <- None;
    (* the watermark went backwards, so the by-Cid index names records this view can no longer
       see: it is not extendable and is dropped, exactly as the node index is *)
    drop_cids view
  end;
  view

let close_ro view =
  if not view.v_closed then begin
    view.v_closed <- true;
    E4_pack.close_reader view.v_reader
  end

let close t =
  if not t.w_closed then begin
    t.w_closed <- true;
    (* The index snapshot is a cache: saving it is best-effort and losing it costs a rebuild
       (L-IDX-0, crash family X3). *)
    (match t.w_view.v_index with
     | Some idx when t.w_blocked = None -> (
       try E4_index.save ~path:(index_path ~dir:t.w_view.v_dir) idx ~covers:t.w_view.v_end
       with Sys_error _ | Unix.Unix_error _ -> ())
     | _ -> ());
    (try E4_pack.close t.w_pack with Invalid_argument _ -> ());
    close_ro t.w_view
  end

(* CS6 / L-CAS-8: re-admit the tail past the control file's `pack_end`, children first, in
   write order, and stop at the first record that fails CRC, digest or admission.  The pack's
   own scan (E4_pack PK7, ~verify:true) has already refused and truncated a torn or corrupt
   record; what is left for this pass is the STORE's admission. *)
let readmit_tail view ~from ~pack_recovery =
  let admitted = ref 0 and duplicates = ref 0 in
  let ends_at = ref from in
  let stop = ref Clean in
  let idx = index view in
  let seq = E4_pack.scan_seq ~verify:false view.v_reader ~from in
  (try
     Seq.iter
       (fun s ->
         match s with
         | E4_pack.Stopped E4_pack.Eof -> raise Exit
         | E4_pack.Stopped st ->
           stop := Torn st;
           raise Exit
         | E4_pack.Scanned ((seg, off), r) -> (
           let a = r.E4_pack.r_addr in
           match E4_pack.read_at view.v_reader ~seg ~off with
           | None ->
             stop := Torn (E4_pack.Bad_crc { seg; off });
             raise Exit
           | Some (_, bytes) ->
             if not (String.equal (E4_sha256.digest bytes) (key_of a)) then begin
               stop := Torn (E4_pack.Bad_digest { seg; off });
               raise Exit
             end
             else (
               match E4_node.decode bytes with
               | Error E4_node.Host_limit ->
                 stop := Refused { seg; off; addr = a; why = Host_limit host_limit_why };
                 raise Exit
               | Error (E4_node.Bad_version b) ->
                 stop := Refused { seg; off; addr = a; why = Bad_version b };
                 raise Exit
               | Error _ ->
                 stop := Refused { seg; off; addr = a; why = Oversize };
                 raise Exit
               | Ok n -> (
                 match admissible view n with
                 | Error why ->
                   stop := Refused { seg; off; addr = a; why };
                   raise Exit
                 | Ok () ->
                   if E4_index.mem_in view.v_reader idx a then incr duplicates
                   else begin
                     E4_index.add idx a { E4_index.seg; off; kind = n.E4_node.kind };
                     incr admitted
                   end;
                   ends_at := record_end (seg, off) r.E4_pack.r_len))))
       seq
   with Exit -> ());
  { from; admitted = !admitted; duplicates = !duplicates; ends_at = !ends_at; stop = !stop;
    pack = pack_recovery }

let open_rw ~dir opts =
  mkdir_p dir;
  mkdir_p (Filename.concat dir "index");
  E4_control.cleanup ~dir;
  let control = match read_control ~dir with Some p -> p | None -> E4_control.initial in
  let want = clamp_watermark ~dir (E4_control.pack_end control) in
  let pack =
    try E4_pack.open_at ~from:want ~verify:true ~truncate:true ~dir ~seg_max:opts.seg_max ()
    with
    | E4_pack.Locked d -> raise (Locked d)
    | E4_pack.Bad_pack why -> raise (Store_error ("pack: " ^ why))
  in
  let view = make_view ~dir ~slots:opts.index_slots ~control ~upto:want in
  (* Everything below the watermark was admitted when it was written and the control commit is
     the proof; the index over it is a cache with a rebuild (L-IDX-0), so a valid snapshot is
     loaded and anything else is rebuilt from the pack. *)
  (match
     try E4_index.load_at ~path:(index_path ~dir) ~pack_end:want with
     | Sys_error _ | Unix.Unix_error _ -> Error E4_index.No_file
   with
  | Ok idx -> view.v_index <- Some idx
  | Error _ -> ignore (rebuild_index view));
  let pack_recovery = E4_pack.recovery pack in
  let rec_ = readmit_tail view ~from:want ~pack_recovery in
  view.v_end <- rec_.ends_at;
  let blocked =
    match rec_.stop with
    | Refused { seg; off; addr; why } ->
      Some
        (Printf.sprintf
           "the pack holds an unadmitted record at seg=%d off=%d (%s): %s.  The store is open \
            for reading; it refuses to grow until an operator acts (e4_cas.mli D6)."
           seg off (E4_addr.Addr.hex addr) (admission_word why))
    | Clean | Torn _ -> None
  in
  if E4_control.pack_end view.v_control <> rec_.ends_at then begin
    view.v_control <- E4_control.set_pack_end view.v_control rec_.ends_at;
    write_control view
  end;
  let t = { w_pack = pack; w_view = view; w_recovery = rec_; w_blocked = blocked; w_closed = false } in
  if opts.verify_on_open then (
    match verify view with
    | Ok () -> ()
    | Error e ->
      close t;
      raise (Store_error ("verify: " ^ verify_error_word e)));
  t

let recovery t = t.w_recovery
