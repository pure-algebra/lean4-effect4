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
     7. verify: one address, by the steps of the checked image
     8. opening, recovery, closing *)

(* ============================================================ 1. the view *)

type counters =
  { mutable commits : int
  ; mutable fsyncs : int
  ; mutable conflicts : int
  }

(* A record staged by `put` and not yet written: its bytes answer every lookup, and its place
   joins the index at `commit`, because `E4_index.find` CONFIRMS at the record (IX1) and there
   is nothing at that place to confirm against until the write(2) has happened. *)
type staged =
  { st_bytes : string
  ; st_seg : int
  ; st_off : int
  ; st_kind : E4_kind.t
  }

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
type cidmap =
  { c_tbl : (string, (E4_kind.t * E4_addr.Addr.t) list ref) Hashtbl.t
  ; mutable c_end : int * int (* the durable watermark this table covers *)
  ; c_stbl : (string, (E4_kind.t * E4_addr.Addr.t) list ref) Hashtbl.t
  ; mutable c_staged_n : int (* how many entries of `v_order` are already folded in *)
  }

(* The by-query table of results (seams ST3): which resident result nodes answer each designated
   query, for the result rule (`resultFault`, Store (src/Effect4/Store/Domain/Store.lean)).  It
   has the by-Cid index's two halves: `r_tbl` covers the durable records up to `r_end` and is
   extended by one pass over what the last call did not see, reading only records the index
   files at kind `result`; `v_rstaged` holds the staged results, filed at staging and emptied at
   promotion, when the durable pass picks them up.  Both answer in insertion order. *)
type resultmap =
  { r_tbl : (string, E4_addr.Addr.t list ref) Hashtbl.t
  ; mutable r_end : int * int (* the durable watermark this table covers *)
  }

type view =
  { v_dir : string
  ; mutable v_reader : E4_pack.reader
  ; v_slots : int
  ; mutable v_index : E4_index.t option (* None: dropped; the next query rebuilds it *)
  ; mutable v_cids : cidmap option (* None: not built yet, or dropped; see `cid_map` *)
  ; mutable v_results : resultmap option
    (* None: not built yet, or dropped; see `result_map` *)
  ; mutable v_end : int * int (* what this view indexes: the durable watermark *)
  ; v_staged : (string, staged) Hashtbl.t (* address bytes -> the record put staged *)
  ; v_rstaged : (string, E4_addr.Addr.t list ref) Hashtbl.t
    (* query bytes -> staged results *)
  ; mutable v_order : string list (* reversed: the staged addresses, in put order *)
  ; mutable v_control : E4_control.t
  ; v_counters : counters
  ; mutable v_closed : bool
  }

type ro = view

(* ============================================================ 2. the types *)

type outcome =
  | Fresh
  | Duplicate
  | Conflict of E4_node.t
  | Corrupt of E4_addr.Addr.t

type admission = E4_admission.t =
  | Model of E4_admission.model
  | Capacity of string
  | Fault of E4_fault.t

exception Locked of string
exception Store_error of string

type open_opts =
  { seg_max : int
  ; index_slots : int
  }

let default_opts = { seg_max = E4_pack.default_seg_max; index_slots = 1 lsl 12 }

type recovery_stop =
  | Clean
  | Torn of E4_pack.scan_stop
  | Refused of
      { seg : int
      ; off : int
      ; addr : E4_addr.Addr.t
      ; why : admission
      }

type recovery =
  { from : int * int
  ; admitted : int
  ; duplicates : int
  ; ends_at : int * int
  ; stop : recovery_stop
  ; pack : E4_pack.recovery
  }

type t =
  { w_pack : E4_pack.t
  ; w_view : view
  ; w_recovery : recovery
  ; w_blocked : string option (* an unadmitted tail: no growth until an operator acts *)
  ; mutable w_closed : bool
  }

type binding =
  { addr : E4_addr.Addr.t
  ; node : E4_node.t
  }

type word_error =
  | Refused_by of admission
  | Word_conflict of
      { at : E4_addr.Addr.t
      ; occupant : E4_node.t
      }
  | Word_corrupt of E4_addr.Addr.t

type stats =
  { nodes : int
  ; bytes : int
  ; index_slots : int
  ; index_bytes : int
  ; commits : int
  ; fsyncs : int
  ; conflicts : int
  }

let outcome_word = function
  | Fresh -> "fresh"
  | Duplicate -> "duplicate"
  | Conflict _ -> "conflict"
  | Corrupt _ -> "corrupt"
;;

let admission_word = function
  | Model model ->
    (match model with
     | E4_admission.Oversize -> "oversize"
     | E4_admission.Unknown_tag tag -> "unknownTag " ^ string_of_int tag
     | E4_admission.Bad_version -> "badVersion"
     | E4_admission.Malformed_ref -> "malformedRef"
     | E4_admission.Handle_in_content -> "handleInContent"
     | E4_admission.Dangling addr -> "dangling " ^ E4_addr.Addr.hex addr
     | E4_admission.Wrong_kind _ -> "wrongKind"
     | E4_admission.Short_spec -> "shortSpec"
     | E4_admission.Unregistered_kind byte -> "unregisteredKind " ^ string_of_int byte
     | E4_admission.Bad_frame -> "badFrame"
     | E4_admission.Trailing -> "trailing"
     | E4_admission.Conflict _ -> "conflict"
     | E4_admission.Bad_envelope -> "badEnvelope"
     | E4_admission.Poisoned (query, first, second) ->
       "poisoned "
       ^ E4_addr.Addr.hex query
       ^ " "
       ^ E4_addr.Addr.hex first
       ^ " "
       ^ E4_addr.Addr.hex second)
  | Capacity reason -> "capacity " ^ reason
  | Fault fault -> E4_fault.word fault
;;

let recovery_stop_word = function
  | Clean -> "clean"
  | Torn s -> "torn " ^ E4_pack.scan_stop_to_string s
  | Refused { seg; off; addr; why } ->
    Printf.sprintf
      "refused seg=%d off=%d %s %s"
      seg
      off
      (E4_addr.Addr.hex addr)
      (admission_word why)
;;

(* ---- positions ---- *)

let pos_lt a b = E4_pack.compare_position a b < 0
let record_end (seg, off) len = seg, off + E4_pack.record_overhead + len
let index_path ~dir = Filename.concat (Filename.concat dir "index") "000000.idx"

let rec mkdir_p d =
  if d <> "" && d <> "/" && d <> Filename.dirname d && not (Sys.file_exists d)
  then (
    mkdir_p (Filename.dirname d);
    try Unix.mkdir d 0o755 with
    | Unix.Unix_error (Unix.EEXIST, _, _) -> ())
;;

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
   with
   | Exit -> ());
  !stop
;;

(* The kind is the second byte of `node_bytes`, so it is not in the 41-byte header: filling
   `E4_index.entry.kind` costs a record read (lane P2's D5, `kind_at_default`).  Lane P4 holds
   the mmap and has no cheaper probe than that read, so the default is what is used and the
   cost is reported rather than hidden. *)
let rebuild_index view =
  let idx = E4_index.with_capacity ~capacity:(max 16 view.v_slots) in
  let start = E4_index.from_start in
  if pos_lt start view.v_end
  then
    ignore
      (walk_records view ~from:start ~upto:view.v_end ~f:(fun (seg, off) r ->
         match E4_index.kind_at_default view.v_reader ~seg ~off with
         | Some kind -> E4_index.add idx r.E4_pack.r_addr { E4_index.seg; off; kind }
         | None -> ()));
  view.v_index <- Some idx;
  idx
;;

let index view =
  match view.v_index with
  | Some i -> i
  | None -> rebuild_index view
;;

let drop_index view = view.v_index <- None

(* ---- the by-Cid index: the two halves, and the one function that brings them up to date ---- *)

let cid_add (tbl : (string, _ list ref) Hashtbl.t) key entry =
  match Hashtbl.find_opt tbl key with
  | Some l -> l := entry :: !l
  | None -> Hashtbl.replace tbl key (ref [ entry ])
;;

let cid_find (tbl : (string, _ list ref) Hashtbl.t) key =
  match Hashtbl.find_opt tbl key with
  | Some l -> List.rev !l
  | None -> []
;;

let new_cidmap () =
  { c_tbl = Hashtbl.create 1024
  ; c_end = E4_index.from_start
  ; c_stbl = Hashtbl.create 16
  ; c_staged_n = 0
  }
;;

let reset_staged_cids view =
  match view.v_cids with
  | None -> ()
  | Some m ->
    Hashtbl.reset m.c_stbl;
    m.c_staged_n <- 0
;;

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
  if pos_lt m.c_end view.v_end
  then (
    ignore
      (walk_records view ~from:m.c_end ~upto:view.v_end ~f:(fun (seg, off) r ->
         match E4_pack.read_at view.v_reader ~seg ~off with
         | None -> ()
         | Some (_, bytes) ->
           (match E4_node.decode bytes with
            | Error _ -> ()
            | Ok n ->
              cid_add
                m.c_tbl
                (E4_sha256.digest n.E4_node.payload)
                (n.E4_node.kind, r.E4_pack.r_addr))));
    m.c_end <- view.v_end);
  let staged = Hashtbl.length view.v_staged in
  if staged < m.c_staged_n
  then (
    Hashtbl.reset m.c_stbl;
    m.c_staged_n <- 0);
  if staged > m.c_staged_n
  then (
    (* the first `staged - c_staged_n` of `v_order` are the new ones, newest first, so taking
       them from the front and consing puts them back in PUT order *)
    let rec take k l acc =
      if k <= 0
      then acc
      else (
        match l with
        | [] -> acc
        | x :: r -> take (k - 1) r (x :: acc))
    in
    List.iter
      (fun key ->
         match Hashtbl.find_opt view.v_staged key with
         | None -> ()
         | Some s ->
           (match E4_node.decode s.st_bytes with
            | Error _ -> ()
            | Ok n ->
              cid_add
                m.c_stbl
                (E4_sha256.digest n.E4_node.payload)
                (n.E4_node.kind, E4_addr.Addr.of_digest key)))
      (take (staged - m.c_staged_n) view.v_order []);
    m.c_staged_n <- staged);
  m
;;

let index_count view = E4_index.count (index view)
let count view = E4_index.count (index view) + Hashtbl.length view.v_staged
let find_entry view a = E4_index.find_in view.v_reader (index view) a

let resident_bytes view (a : E4_addr.Addr.t) =
  match Hashtbl.find_opt view.v_staged (key_of a) with
  | Some s -> Some s.st_bytes
  | None ->
    (match find_entry view a with
     | None -> None
     | Some e ->
       (match E4_pack.read_at view.v_reader ~seg:e.E4_index.seg ~off:e.E4_index.off with
        | Some (recorded, bytes) when E4_addr.Addr.equal recorded a -> Some bytes
        | _ -> None))
;;

let get_kind view a =
  match Hashtbl.find_opt view.v_staged (key_of a) with
  | Some s -> Some s.st_kind
  | None ->
    (match find_entry view a with
     | None -> None
     | Some e -> Some e.E4_index.kind)
;;

let get_bytes view a = resident_bytes view a

let get_node view a =
  match resident_bytes view a with
  | None -> None
  | Some bytes ->
    (match E4_node.decode bytes with
     | Ok n -> Some n
     | Error _ -> None)
;;

let mem view a =
  Hashtbl.mem view.v_staged (key_of a) || E4_index.mem_in view.v_reader (index view) a
;;

let resolves view (r : E4_addr.Ref.t) =
  match get_kind view r.E4_addr.Ref.addr with
  | Some k -> E4_kind.equal k r.E4_addr.Ref.kind
  | None -> false
;;

(* `Store.nodes` (Store (src/Effect4/Store/Domain/Store.lean)): insertion order, which is the pack's write order.  It is
   read back from the pack rather than held in memory — the index is off-heap on purpose and a
   list of every address would put it back on the heap. *)
let addresses view =
  let acc = ref [] in
  let start = E4_index.from_start in
  if pos_lt start view.v_end
  then
    ignore
      (walk_records view ~from:start ~upto:view.v_end ~f:(fun _ r ->
         acc := r.E4_pack.r_addr :: !acc));
  let staged = List.rev_map (fun k -> E4_addr.Addr.of_digest k) view.v_order in
  List.rev_append !acc (List.rev staged)
;;

let nodes view =
  List.filter_map
    (fun a ->
       match get_node view a with
       | Some n -> Some (a, n)
       | None -> None)
    (addresses view)
;;

(* `Node.resultQuery?` (Node.resultQuery? (src/Effect4/Store/Domain/Action.lean)): a result
   node's designated query, read as the common envelope `ctor 0 [nat 0, ref query q, output]` at
   node version 0 and the common specification (`E4_result`, generated); None for every other
   node.  It names the query field, never a reference inside the output. *)
let result_query (n : E4_node.t) =
  let s = n.E4_node.payload in
  let len = String.length s in
  if
    not
      (E4_kind.equal n.E4_node.kind E4_kind.Result
       && n.E4_node.version = 0
       && String.equal n.E4_node.spec E4_result.spec)
  then None
  else (
    match Eff_frame.read_ctor s 0 len with
    | Some (0, start, limit, ending) when ending = len ->
      (match Eff_frame.decode_nat s start limit with
       | Some (version, after) when version = E4_result.envelope_version ->
         (match Eff_frame.decode_ref s after limit with
          | Some ((kind, digest), next)
            when kind = E4_kind.byte E4_kind.Query && String.length digest = 32 ->
            (match Eff_frame.read_frame s next limit with
             | Some (_, _, _, finish) when finish = limit ->
               Some (E4_addr.Addr.of_digest digest)
             | _ -> None)
          | _ -> None)
       | _ -> None)
    | _ -> None)
;;

let stage_result view (address : E4_addr.Addr.t) (n : E4_node.t) =
  match result_query n with
  | Some query -> cid_add view.v_rstaged (key_of query) address
  | None -> ()
;;

(* Bring the by-query table up to the watermark and answer it; a watermark that went backwards
   drops it, as it drops the by-Cid index. *)
let result_map view =
  let m =
    match view.v_results with
    | Some m when not (pos_lt view.v_end m.r_end) -> m
    | _ ->
      let m = { r_tbl = Hashtbl.create 64; r_end = E4_index.from_start } in
      view.v_results <- Some m;
      m
  in
  if pos_lt m.r_end view.v_end
  then (
    ignore
      (walk_records view ~from:m.r_end ~upto:view.v_end ~f:(fun (seg, off) r ->
         match E4_index.kind_at_default view.v_reader ~seg ~off with
         | Some kind when E4_kind.equal kind E4_kind.Result ->
           (match E4_pack.read_at view.v_reader ~seg ~off with
            | None -> ()
            | Some (_, bytes) ->
              (match E4_node.decode bytes with
               | Error _ -> ()
               | Ok n ->
                 (match result_query n with
                  | Some query -> cid_add m.r_tbl (key_of query) r.E4_pack.r_addr
                  | None -> ())))
         | _ -> ()));
    m.r_end <- view.v_end);
  m
;;

(* `resultFault` (resultFault (src/Effect4/Store/Domain/Store.lean)): a result reads as the
   envelope, and no resident result answers its query with another node.  The first such
   resident is named, with the query and the refused node's own address. *)
let check_result view (n : E4_node.t) =
  if not (E4_kind.equal n.E4_node.kind E4_kind.Result)
  then Ok ()
  else (
    match result_query n with
    | None -> Error (Model E4_admission.Bad_envelope)
    | Some query ->
      let key = key_of query in
      let bytes = E4_node.encode n in
      let differs a =
        match resident_bytes view a with
        | Some b -> not (String.equal b bytes)
        | None -> false
      in
      (match
         List.find_opt
           differs
           (cid_find (result_map view).r_tbl key @ cid_find view.v_rstaged key)
       with
       | Some first ->
         Error (Model (E4_admission.Poisoned (query, first, E4_node.address n)))
       | None -> Ok ()))
;;

(* ============================================================ 4. admission *)

(* CS2 / L-CAS-4.  The stages that are functions of the node alone, in Lean's order
   (Store.putNode (src/Effect4/Store/Domain/Store.lean)), with amendment M2's handle test at A2 owner question OQ4's default
   position — after `malformedRef`, before the edges.  Moving it is moving one element of this
   list, and `E4_node.check_pure` (lane P0's ND10) is the same order stated once more. *)
type stage =
  | St_bad_version
  | St_malformed_ref
  | St_handle_in_content

let admission_stages = [ St_bad_version; St_malformed_ref; St_handle_in_content ]

(* `Oversize` is not in the list because it cannot move: `malformedRef` and the handle test
   are defined only on a payload that parses (lane P0's D3), and Lean tests `payload.WF`
   first for the same reason (Store.putNode (src/Effect4/Store/Domain/Store.lean)).  The three that CAN move are the list, and
   moving amendment M2's handle test — A2 owner question OQ4 — is moving one element of it. *)
let stage_refusal (n : E4_node.t) (sc : E4_node.scan) = function
  | St_bad_version ->
    if n.E4_node.version <> 0 then Some (Model E4_admission.Bad_version) else None
  | St_malformed_ref ->
    if sc.E4_node.malformed then Some (Model E4_admission.Malformed_ref) else None
  | St_handle_in_content ->
    if E4_kind.is_content n.E4_node.kind && not (List.is_empty sc.E4_node.handles)
    then Some (Model E4_admission.Handle_in_content)
    else None
;;

let check_pure (n : E4_node.t) =
  (* ONE traversal of the payload for all three tests: `payload_ok`, `malformed_ref` and
     `handles` are the same walk, and the put path is hot. *)
  match E4_node.scan_payload n.E4_node.payload with
  | Error why -> Error (E4_admission.of_decode why)
  | Ok sc ->
    let rec go = function
      | [] -> Ok ()
      | s :: rest ->
        (match stage_refusal n sc s with
         | Some a -> Error a
         | None -> go rest)
    in
    go admission_stages
;;

(* `Store.checkAll` (src/Effect4/Store/Domain/Store.lean) over
   `Node.checkedEdges` (src/Effect4/Store/Domain/Node.lean): in order, spec edge
   first, the genesis exempt from it and nothing else. *)
let check_edges view (n : E4_node.t) =
  let rec go = function
    | [] -> Ok ()
    | (e : E4_addr.Ref.t) :: rest ->
      (match get_kind view e.E4_addr.Ref.addr with
       | None -> Error (Model (E4_admission.Dangling e.E4_addr.Ref.addr))
       | Some k ->
         if E4_kind.equal k e.E4_addr.Ref.kind
         then go rest
         else
           Error
             (Model (E4_admission.Wrong_kind (e.E4_addr.Ref.addr, e.E4_addr.Ref.kind, k))))
  in
  go (E4_node.checked_edges n)
;;

let admissible view n =
  match check_pure n with
  | Error a -> Error a
  | Ok () ->
    (match check_edges view n with
     | Error a -> Error a
     | Ok () -> check_result view n)
;;

(* A snapshot contains values only: no mutable view, index, or pack handle. *)
type image =
  { image_nodes : (E4_addr.Addr.t * string) list
  ; image_roots : E4_control.root list
  ; image_boundary : int * int
  }

let empty_admission_view view =
  { view with
    v_index = Some (E4_index.create ~slots:8)
  ; v_cids = None
  ; v_results = None
  ; v_end = E4_index.from_start
  ; v_staged = Hashtbl.create 16
  ; v_rstaged = Hashtbl.create 16
  ; v_order = []
  ; v_control = E4_control.initial
  }
;;

let checked_image view =
  let shadow = empty_admission_view view in
  let bytes = ref []
  and ending = ref E4_index.from_start in
  let exception Refused_image of admission in
  let refuse why = raise (Refused_image why) in
  let record_fault (seg, off) reason = Fault (E4_fault.Record { seg; off; reason }) in
  try
    let stop =
      if not (pos_lt E4_index.from_start view.v_end)
      then E4_pack.Eof
      else
        walk_records
          view
          ~from:E4_index.from_start
          ~upto:view.v_end
          ~f:(fun ((seg, off) as position) record ->
            let address = record.E4_pack.r_addr in
            let raw =
              match E4_pack.read_at view.v_reader ~seg ~off with
              | None -> refuse (record_fault position "record checksum or framing")
              | Some (_, raw) -> raw
            in
            if not (String.equal (E4_sha256.digest raw) (key_of address))
            then refuse (Fault (E4_fault.Corrupt address));
            let node =
              match E4_node.decode raw with
              | Error why -> refuse (E4_admission.of_decode why)
              | Ok node -> node
            in
            (match admissible shadow node with
             | Error why -> refuse why
             | Ok () -> ());
            (match Hashtbl.find_opt shadow.v_staged (key_of address) with
             | Some old when not (String.equal old.st_bytes raw) ->
               (match E4_node.decode old.st_bytes with
                | Ok occupant ->
                  refuse (Model (E4_admission.Conflict (address, occupant)))
                | Error why -> refuse (E4_admission.of_decode why))
             | Some _ -> ()
             | None ->
               Hashtbl.add
                 shadow.v_staged
                 (key_of address)
                 { st_bytes = raw
                 ; st_seg = seg
                 ; st_off = off
                 ; st_kind = node.E4_node.kind
                 };
               stage_result shadow address node);
            bytes := (address, String.sub raw 0 (String.length raw)) :: !bytes;
            ending := record_end position record.E4_pack.r_len)
    in
    if not (E4_pack.equal_position !ending view.v_end)
    then
      refuse
        (record_fault !ending ("durable boundary: " ^ E4_pack.scan_stop_to_string stop));
    let rec roots names = function
      | [] -> ()
      | (root : E4_control.root) :: rest ->
        if List.exists (String.equal root.name) names
        then
          refuse (Fault (E4_fault.Root { name = root.name; reason = "duplicate name" }));
        (match get_kind shadow root.head.digest with
         | None ->
           refuse
             (Fault
                (E4_fault.Root
                   { name = root.name; reason = "target absent from durable image" }))
         | Some kind when not (E4_kind.equal kind root.kind) ->
           refuse (Fault (E4_fault.Root { name = root.name; reason = "target kind" }))
         | Some _ -> ());
        roots (root.name :: names) rest
    in
    let image_roots = E4_control.roots view.v_control in
    roots [] image_roots;
    Ok { image_nodes = List.rev !bytes; image_roots; image_boundary = view.v_end }
  with
  | Refused_image why -> Error why
;;

(* ============================================================ 5. put, commit, roots *)

let ensure_open t =
  if t.w_closed then invalid_arg "E4_cas: the writer is closed";
  match t.w_blocked with
  | Some why -> raise (Store_error why)
  | None -> ()
;;

let occupant_node bytes =
  match E4_node.decode bytes with
  | Ok n -> n
  | Error _ ->
    (* A resident record whose bytes do not decode can only be a forged one: this module never
       files such a record.  It is still exhibited, leniently, rather than hidden. *)
    if String.length bytes >= 34
    then (
      match E4_kind.of_byte (Char.code bytes.[1]) with
      | Some kind ->
        { E4_node.version = Char.code bytes.[0]
        ; kind
        ; spec = String.sub bytes 2 32
        ; payload = String.sub bytes 34 (String.length bytes - 34)
        }
      | None ->
        raise
          (Store_error
             "the occupant's kind byte is not registered; it cannot be exhibited"))
    else raise (Store_error "the occupant is shorter than a node header")
;;

let put_admitted t (n : E4_node.t) =
  ensure_open t;
  let view = t.w_view in
  match admissible view n with
  | Error a -> Error a
  | Ok () ->
    let bytes = E4_node.encode n in
    let addr = E4_addr.Addr.of_digest (E4_sha256.digest bytes) in
    (match resident_bytes view addr with
     | Some resident when String.equal resident bytes -> Ok (Duplicate, addr)
     | Some resident ->
       (* The occupant is re-hashed: bytes that do not hash to their address are a corrupt
         record, bytes that do are an exhibited collision. Either way nothing changes. *)
       if String.equal (E4_sha256.digest resident) (E4_addr.Addr.bytes addr)
       then (
         view.v_counters.conflicts <- view.v_counters.conflicts + 1;
         Ok (Conflict (occupant_node resident), addr))
       else Ok (Corrupt addr, addr)
     | None ->
       let seg, off = E4_pack.stage t.w_pack ~addr ~node_bytes:bytes in
       let key = key_of addr in
       Hashtbl.replace
         view.v_staged
         key
         { st_bytes = bytes; st_seg = seg; st_off = off; st_kind = n.E4_node.kind };
       stage_result view addr n;
       view.v_order <- key :: view.v_order;
       Ok (Fresh, addr))
;;

(* Both native entrances read the exact raw bytes before shared node admission. *)
let put_bytes t bytes =
  match E4_node.decode bytes with
  | Ok node -> put_admitted t node
  | Error why -> Error (E4_admission.of_decode why)
;;

let put t (node : E4_node.t) =
  if node.E4_node.version < 0 || node.E4_node.version > 255
  then Error (Capacity "node version is outside the byte domain")
  else put_bytes t (E4_node.encode node)
;;

let promote_staged view =
  if Hashtbl.length view.v_staged > 0
  then (
    let idx = index view in
    Hashtbl.iter
      (fun key s ->
         E4_index.add
           idx
           (E4_addr.Addr.of_digest key)
           { E4_index.seg = s.st_seg; off = s.st_off; kind = s.st_kind })
      view.v_staged;
    Hashtbl.reset view.v_staged;
    Hashtbl.reset view.v_rstaged;
    view.v_order <- []);
  (* The staged half of the by-Cid index is now below the watermark `commit` is about to
     advance, so the durable walk will re-derive it; keeping it would double every filing. *)
  reset_staged_cids view
;;

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
;;

let write_control view =
  E4_control.commit ~path:(control_path ~dir:view.v_dir) view.v_control;
  view.v_counters.fsyncs <- view.v_counters.fsyncs + 1;
  view.v_counters.commits <- view.v_counters.commits + 1
;;

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
  if not (E4_pack.equal_position pe view.v_end) then refresh_reader view;
  view.v_end <- pe;
  if not (E4_pack.equal_position (E4_control.pack_end view.v_control) pe)
  then (
    view.v_control <- E4_control.set_pack_end view.v_control pe;
    write_control view)
;;

let root view name = E4_control.root view.v_control name
let roots view = E4_control.roots view.v_control
let generation view = E4_control.generation view.v_control
let dir t = t.w_view.v_dir
let read_only t = t.w_view

(* Designated parents match Node.designatedParent in the Lean model. *)
let designated_parent view address =
  match get_node view address with
  | None -> None
  | Some node ->
    let bytes = node.E4_node.payload in
    let finish expected parent after limit =
      match parent, Eff_frame.read_frame bytes after limit with
      | Some (kind, digest), Some (_, _, _, ending)
        when kind = E4_kind.byte expected && String.length digest = 32 && ending = limit
        -> Some (E4_addr.Addr.of_digest digest)
      | _ -> None
    in
    let rec skip_frames count pos limit =
      if count = 0
      then Some pos
      else (
        match Eff_frame.read_frame bytes pos limit with
        | Some (_, _, _, next) -> skip_frames (count - 1) next limit
        | None -> None)
    in
    (match Eff_frame.read_ctor bytes 0 (String.length bytes) with
     | Some (1, start, limit, ending)
       when E4_kind.equal node.E4_node.kind E4_kind.Entry && ending = String.length bytes
       ->
       (* a session entry's action (seams ST4): [parent, index, action, after] *)
       (match Eff_frame.decode_ref bytes start limit with
        | Some (parent, after) ->
          (match skip_frames 2 after limit with
           | Some next -> finish E4_kind.Entry (Some parent) next limit
           | None -> None)
        | None -> None)
     | Some (0, start, limit, ending)
       when E4_kind.equal node.E4_node.kind E4_kind.Tape && ending = String.length bytes
       ->
       (match Eff_frame.read_frame bytes start limit with
        | Some (_, _, _, next) ->
          (match Eff_frame.decode_option Eff_frame.decode_ref bytes next limit with
           | Some (parent, after) -> finish E4_kind.Tape parent after limit
           | None -> None)
        | None -> None)
     | Some (0, start, limit, ending)
       when E4_kind.equal node.E4_node.kind E4_kind.Checkpoint
            && ending = String.length bytes ->
       let rec skip count pos =
         if count = 0
         then Some pos
         else (
           match Eff_frame.read_frame bytes pos limit with
           | Some (_, _, _, next) -> skip (count - 1) next
           | None -> None)
       in
       (match skip 3 start with
        | None -> None
        | Some pos ->
          (match Eff_frame.decode_option Eff_frame.decode_ref bytes pos limit with
           | Some (Some (kind, digest), after)
             when kind = E4_kind.byte E4_kind.Checkpoint && String.length digest = 32 ->
             (match skip 3 after with
              | Some final when final = limit -> Some (E4_addr.Addr.of_digest digest)
              | _ -> None)
           | _ -> None))
     | _ -> None)
;;

let advance_root t (move : E4_control.move) =
  ensure_open t;
  commit t;
  let view = t.w_view in
  let resolve a = get_kind view a in
  match
    E4_control.advance_root view.v_control ~resolve ~parent:(designated_parent view) move
  with
  | Error e -> Error e
  | Ok payload ->
    view.v_control <- payload;
    write_control view;
    Ok ()
;;

let move_at_head view name policy (target : E4_control.target) =
  match root view name with
  | None -> E4_control.Create (name, policy, target)
  | Some old -> E4_control.Advance (name, old.E4_control.head, target)
;;

(* Transactions preflight entirely in a private value view before staging any bytes. *)
type transaction =
  { txn_nodes : string list
  ; txn_moves : E4_control.move list
  }

type node_outcome =
  | Fresh_node
  | Duplicate_node

type move_outcome =
  | Created of Z.t
  | Advanced of Z.t
  | Duplicate_move of Z.t

type receipt =
  { receipt_nodes : (E4_addr.Addr.t * node_outcome) list
  ; receipt_moves : move_outcome list
  }

type transaction_error =
  | Node_refused of
      { index : Z.t
      ; why : admission
      }
  | Move_refused of
      { name : string
      ; why : E4_control.root_error
      }
  | Host_refused of admission

type commit_point =
  | Before_write of int
  | After_write of int
  | After_sync
  | Before_publish
  | After_publish

type prepared =
  { prepared_fresh : (E4_addr.Addr.t * E4_node.t * string) list
  ; prepared_control : E4_control.t
  ; prepared_receipt : receipt
  }

let prepare_transaction view transaction =
  let shadow =
    { view with
      v_staged = Hashtbl.copy view.v_staged
    ; v_rstaged = Hashtbl.copy view.v_rstaged
    ; v_order = view.v_order
    }
  in
  let exception Refused_transaction of transaction_error in
  let refuse why = raise (Refused_transaction why) in
  try
    let fresh = ref [] in
    let outcomes =
      List.mapi
        (fun index raw ->
           let node =
             match E4_node.decode raw with
             | Error why ->
               refuse
                 (Node_refused
                    { index = Z.of_int index; why = E4_admission.of_decode why })
             | Ok node -> node
           in
           (match admissible shadow node with
            | Error why -> refuse (Node_refused { index = Z.of_int index; why })
            | Ok () -> ());
           let address = E4_addr.Addr.of_digest (E4_sha256.digest raw) in
           let outcome =
             match resident_bytes shadow address with
             | Some bytes when String.equal bytes raw -> Duplicate_node
             | Some bytes ->
               let why =
                 if not (String.equal (E4_sha256.digest bytes) (key_of address))
                 then Fault (E4_fault.Corrupt address)
                 else (
                   match E4_node.decode bytes with
                   | Error why -> E4_admission.of_decode why
                   | Ok occupant -> Model (E4_admission.Conflict (address, occupant)))
               in
               refuse (Node_refused { index = Z.of_int index; why })
             | None ->
               Hashtbl.add
                 shadow.v_staged
                 (key_of address)
                 { st_bytes = raw; st_seg = 0; st_off = 0; st_kind = node.E4_node.kind };
               stage_result shadow address node;
               fresh := (address, node, raw) :: !fresh;
               Fresh_node
           in
           address, outcome)
        transaction.txn_nodes
    in
    let moves =
      List.map
        (fun move ->
           let name =
             match move with
             | E4_control.Create (name, _, _) | E4_control.Advance (name, _, _) -> name
           in
           let before = root shadow name in
           match
             E4_control.advance_root
               shadow.v_control
               ~resolve:(get_kind shadow)
               ~parent:(designated_parent shadow)
               move
           with
           | Error why -> refuse (Move_refused { name; why })
           | Ok control ->
             shadow.v_control <- control;
             (match root shadow name, before with
              | Some next, None -> Created next.head.generation
              | Some next, Some previous
                when E4_control.head_equal next.head previous.head ->
                Duplicate_move next.head.generation
              | Some next, Some _ -> Advanced next.head.generation
              | None, _ ->
                refuse (Host_refused (Fault (E4_fault.Store "accepted move has no root")))))
        transaction.txn_moves
    in
    (try ignore (E4_control.encode shadow.v_control) with
     | Invalid_argument reason -> refuse (Host_refused (Capacity reason)));
    Ok
      { prepared_fresh = List.rev !fresh
      ; prepared_control = shadow.v_control
      ; prepared_receipt = { receipt_nodes = outcomes; receipt_moves = moves }
      }
  with
  | Refused_transaction why -> Error why
;;

(* The writer's records were admitted whole when it opened (E4_disk.open_ takes a checked image),
   and every later record is its own, admitted here under the pack lock. So a commit checks only its
   transaction: its cost is the transaction's, not the store's. *)
let commit_transaction ?hook writer transaction =
  ensure_open writer;
  let view = writer.w_view in
  match prepare_transaction view transaction with
  | Error why -> Error why
  | Ok prepared ->
    let call point =
      match hook with
      | None -> ()
      | Some callback -> callback point
    in
    List.iteri
      (fun index (address, node, raw) ->
         call (Before_write index);
         let seg, off = E4_pack.stage writer.w_pack ~addr:address ~node_bytes:raw in
         Hashtbl.replace
           view.v_staged
           (key_of address)
           { st_bytes = raw; st_seg = seg; st_off = off; st_kind = node.E4_node.kind };
         stage_result view address node;
         view.v_order <- key_of address :: view.v_order;
         (match hook with
          | None -> ()
          | Some _ -> E4_pack.flush writer.w_pack);
         call (After_write (index + 1)))
      prepared.prepared_fresh;
    E4_pack.sync writer.w_pack;
    call After_sync;
    promote_staged view;
    let ending = E4_pack.pack_end writer.w_pack in
    if not (E4_pack.equal_position ending view.v_end) then refresh_reader view;
    view.v_end <- ending;
    call Before_publish;
    view.v_control <- E4_control.set_pack_end prepared.prepared_control ending;
    write_control view;
    call After_publish;
    Ok prepared.prepared_receipt
;;

(* ============================================================ 6. words *)

(* `Binding.admissibleAfter` (Binding.admissibleAfter (src/Effect4/Store/Domain/Word.lean)) with the bindings before it
   carried as a digest -> kind table, and their results as a query -> node table: the result
   rule (`resultFault`) among the earlier bindings, and M2's handle test, as Lean's has them. *)
let admissible_after
      (seen : (string, E4_kind.t) Hashtbl.t)
      (results : (string, E4_node.t) Hashtbl.t)
      (b : binding)
  =
  let n = b.node in
  let key = key_of b.addr in
  n.E4_node.version = 0
  && Result.is_ok (E4_node.payload_ok n.E4_node.payload)
  && (not (E4_node.malformed_ref n))
  && (not (E4_node.handle_in_content n))
  && String.equal (E4_sha256.digest (E4_node.encode n)) key
  && (not (Hashtbl.mem seen key))
  && List.for_all
       (fun (e : E4_addr.Ref.t) ->
          match Hashtbl.find_opt seen (key_of e.E4_addr.Ref.addr) with
          | Some k -> E4_kind.equal k e.E4_addr.Ref.kind
          | None -> false)
       (E4_node.checked_edges n)
  && ((not (E4_kind.equal n.E4_node.kind E4_kind.Result))
      ||
      match result_query n with
      | None -> false
      | Some query ->
        (match Hashtbl.find_opt results (key_of query) with
         | Some earlier -> E4_node.equal earlier n
         | None -> true))
;;

let admit_binding seen results (b : binding) =
  Hashtbl.replace seen (key_of b.addr) b.node.E4_node.kind;
  match result_query b.node with
  | Some query when not (Hashtbl.mem results (key_of query)) ->
    Hashtbl.replace results (key_of query) b.node
  | _ -> ()
;;

let word_wf w =
  let seen = Hashtbl.create 64
  and results = Hashtbl.create 8 in
  List.for_all
    (fun b ->
       if admissible_after seen results b
       then (
         admit_binding seen results b;
         true)
       else false)
    w
;;

(* `closureGo` / `Store.closure` (Store.closure (src/Effect4/Store/Domain/Word.lean)), transcribed: skip what is already
   emitted, walk the checked edges with one unit of fuel less, then emit under `emit`'s guard.
   `seen` is exactly the accumulator's digests, so the guard is `emit`'s. *)
let closure view (r : E4_addr.Ref.t) =
  let fuel0 = count view in
  let seen : (string, E4_kind.t) Hashtbl.t = Hashtbl.create 64 in
  let results : (string, E4_node.t) Hashtbl.t = Hashtbl.create 8 in
  let acc = ref [] in
  let rec go fuel (a : E4_addr.Addr.t) =
    if fuel <= 0
    then ()
    else if Hashtbl.mem seen (key_of a)
    then ()
    else (
      match get_node view a with
      | None -> ()
      | Some n ->
        List.iter
          (fun (e : E4_addr.Ref.t) -> go (fuel - 1) e.E4_addr.Ref.addr)
          (E4_node.checked_edges n);
        let b = { addr = a; node = n } in
        if admissible_after seen results b
        then (
          acc := b :: !acc;
          admit_binding seen results b))
  in
  go fuel0 r.E4_addr.Ref.addr;
  List.rev !acc
;;

let apply_word t w =
  let rec go = function
    | [] -> Ok ()
    | b :: rest ->
      (match put t b.node with
       | Error a -> Error (Refused_by a)
       | Ok (Conflict m, at) -> Error (Word_conflict { at; occupant = m })
       | Ok (Corrupt at, _) -> Error (Word_corrupt at)
       | Ok ((Fresh | Duplicate), _) -> go rest)
  in
  go w
;;

(* ============================================================ 7. verify *)

(* CS7 / L-CAS-6: the store's verification is `checked_image` (section 4), the walk the checked
   open (`E4_disk.open_`) runs.  One address is checked by the steps that walk takes for each
   record: the resident bytes, their digest, `E4_node.decode`, then [admissible]. *)
let verify_node view a =
  match resident_bytes view a with
  | None -> Error (Model (E4_admission.Dangling a))
  | Some bytes ->
    if not (String.equal (E4_sha256.digest bytes) (key_of a))
    then Error (Fault (E4_fault.Corrupt a))
    else (
      match E4_node.decode bytes with
      | Error why -> Error (E4_admission.of_decode why)
      | Ok n -> admissible view n)
;;

let closed view =
  List.for_all
    (fun (_, n) -> List.for_all (fun e -> resolves view e) (E4_node.checked_edges n))
    (nodes view)
;;

(* ============================================================ queries that are not edges *)

(* Insertion order, and the same answer the `nodes` scan gave: durable filings in write order,
   then the staged ones in put order.  O(matches) once the index is warm (lane P6 finding F6;
   the numbers are in 2026-09-08-engine-lane-w-delivery.md item 4). *)
let by_cid_any view (c : E4_addr.Cid.t) =
  let m = cid_map view in
  let want = E4_addr.Addr.bytes c in
  cid_find m.c_tbl want @ cid_find m.c_stbl want
;;

let by_cid view k c =
  List.filter_map
    (fun (k', a) -> if E4_kind.equal k k' then Some a else None)
    (by_cid_any view c)
;;

let reachable view (a : E4_addr.Addr.t) =
  let want = key_of a in
  let seen = Hashtbl.create 64 in
  let rec go (d : E4_addr.Addr.t) =
    let key = key_of d in
    if Hashtbl.mem seen key
    then false
    else (
      Hashtbl.replace seen key ();
      String.equal key want
      ||
      match get_node view d with
      | None -> false
      | Some n ->
        List.exists
          (fun (e : E4_addr.Ref.t) -> go e.E4_addr.Ref.addr)
          (E4_node.checked_edges n))
  in
  List.exists (fun (r : E4_control.root) -> go r.E4_control.head.digest) (roots view)
;;

(* ---- the pins (amendment M1; D8) ---- *)

let pin t ~name kind (c : E4_addr.Cid.t) =
  ensure_open t;
  let view = t.w_view in
  match by_cid view kind c with
  | [] -> Error (E4_control.Dangling c)
  | a :: _ ->
    let name = E4_control.normalise_name name in
    advance_root t (move_at_head view name E4_control.Pin { E4_control.kind; digest = a })
;;

let pin_all t ~job cids =
  ensure_open t;
  let view = t.w_view in
  let job_hex = E4_addr.Addr.hex job in
  let plans = List.map (fun c -> c, by_cid_any view c) cids in
  (* M1: refuse the whole publish before minting anything when some Cid has no filing. *)
  match List.find_opt (fun (_, filings) -> List.is_empty filings) plans with
  | Some (c, _) -> Error (E4_control.Dangling c)
  | None ->
    let rec mint = function
      | [] -> Ok ()
      | (c, filings) :: rest ->
        let cid_hex = E4_addr.Addr.hex c in
        let rec one i = function
          | [] -> Ok ()
          | (kind, a) :: more ->
            let name =
              E4_control.normalise_name
                (if i = 1
                 then Printf.sprintf "runs/%s/pin/%s" job_hex cid_hex
                 else Printf.sprintf "runs/%s/pin/%s/%d" job_hex cid_hex i)
            in
            (match
               advance_root
                 t
                 (move_at_head view name E4_control.Pin { E4_control.kind; digest = a })
             with
             | Error e -> Error e
             | Ok () -> one (i + 1) more)
        in
        (match one 1 filings with
         | Error e -> Error e
         | Ok () -> mint rest)
    in
    mint plans
;;

(* ============================================================ 8. opening *)

let stats view =
  let idx = index view in
  let bytes =
    List.fold_left
      (fun acc s ->
         match
           try Some (Unix.stat (E4_pack.seg_path ~dir:view.v_dir s)).Unix.st_size with
           | Unix.Unix_error _ -> None
         with
         | Some n -> acc + n
         | None -> acc)
      0
      (E4_pack.segments view.v_reader)
  in
  { nodes = E4_index.count idx + Hashtbl.length view.v_staged
  ; bytes
  ; index_slots = E4_index.slots idx
  ; index_bytes = E4_index.bytes idx
  ; commits = view.v_counters.commits
  ; fsyncs = view.v_counters.fsyncs
  ; conflicts = view.v_counters.conflicts
  }
;;

let read_control ~dir =
  match E4_control.read ~path:(control_path ~dir) with
  | Ok p -> Some p
  | Error E4_control.Missing -> None
  | Error e -> raise (Store_error ("control: " ^ E4_control.open_error_word e))
;;

(* The watermark a control file names, made safe to scan from: never below a segment's head,
   never past a segment's end, and never into a segment that is not there.  Crash family
   X4(b) — "pack_end names bytes that are not there" — lands here and falls back to a full
   re-admission from the first record. *)
let clamp_watermark ~dir (seg, off) =
  let start = E4_index.from_start in
  if seg < 0 || off < E4_pack.head_length
  then start
  else (
    match
      try Some (Unix.stat (E4_pack.seg_path ~dir seg)).Unix.st_size with
      | Unix.Unix_error _ -> None
    with
    | Some size when off <= size -> seg, off
    | _ -> start)
;;

let make_view ~dir ~slots ~control ~upto =
  { v_dir = dir
  ; v_reader = E4_pack.open_reader ~dir
  ; v_slots = slots
  ; v_index = None
  ; v_cids = None
  ; v_results = None
  ; v_end = upto
  ; v_staged = Hashtbl.create 64
  ; v_rstaged = Hashtbl.create 16
  ; v_order = []
  ; v_control = control
  ; v_counters = { commits = 0; fsyncs = 0; conflicts = 0 }
  ; v_closed = false
  }
;;

let open_ro ~dir =
  let control =
    match read_control ~dir with
    | Some p -> p
    | None -> E4_control.initial
  in
  let upto = clamp_watermark ~dir (E4_control.pack_end control) in
  make_view ~dir ~slots:default_opts.index_slots ~control ~upto
;;

let reopen_ro view =
  let control =
    match read_control ~dir:view.v_dir with
    | Some p -> p
    | None -> E4_control.initial
  in
  let upto = clamp_watermark ~dir:view.v_dir (E4_control.pack_end control) in
  view.v_control <- control;
  if not (E4_pack.equal_position view.v_end upto) then refresh_reader view;
  if pos_lt view.v_end upto
  then (
    (match view.v_index with
     | None -> ()
     | Some idx ->
       ignore
         (walk_records view ~from:view.v_end ~upto ~f:(fun (seg, off) r ->
            match E4_index.kind_at_default view.v_reader ~seg ~off with
            | Some kind -> E4_index.add idx r.E4_pack.r_addr { E4_index.seg; off; kind }
            | None -> ())));
    view.v_end <- upto)
  else if pos_lt upto view.v_end
  then (
    view.v_end <- upto;
    view.v_index <- None;
    (* the watermark went backwards, so the by-Cid and by-query indexes name records this view
       can no longer see: they are not extendable and are dropped, exactly as the node index is *)
    drop_cids view;
    view.v_results <- None);
  view
;;

let close_ro view =
  if not view.v_closed
  then (
    view.v_closed <- true;
    E4_pack.close_reader view.v_reader)
;;

let close t =
  if not t.w_closed
  then (
    t.w_closed <- true;
    (* The index snapshot is a cache: saving it is best-effort and losing it costs a rebuild
       (L-IDX-0, crash family X3). *)
    (match t.w_view.v_index with
     | Some idx when Option.is_none t.w_blocked ->
       (try
          E4_index.save ~path:(index_path ~dir:t.w_view.v_dir) idx ~covers:t.w_view.v_end
        with
        | Sys_error _ | Unix.Unix_error _ -> ())
     | _ -> ());
    (try E4_pack.close t.w_pack with
     | Invalid_argument _ -> ());
    close_ro t.w_view)
;;

(* CS6 / L-CAS-8: re-admit the tail past the control file's `pack_end`, children first, in
   write order, and stop at the first record that fails CRC, digest or admission.  The pack's
   own scan (E4_pack PK7, ~verify:true) has already refused and truncated a torn or corrupt
   record; what is left for this pass is the STORE's admission. *)
let readmit_tail view ~from ~pack_recovery =
  let admitted = ref 0
  and duplicates = ref 0 in
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
          | E4_pack.Scanned ((seg, off), r) ->
            let a = r.E4_pack.r_addr in
            (match E4_pack.read_at view.v_reader ~seg ~off with
             | None ->
               stop := Torn (E4_pack.Bad_crc { seg; off });
               raise Exit
             | Some (_, bytes) ->
               if not (String.equal (E4_sha256.digest bytes) (key_of a))
               then (
                 stop := Torn (E4_pack.Bad_digest { seg; off });
                 raise Exit)
               else (
                 match E4_node.decode bytes with
                 | Error why ->
                   stop
                   := Refused { seg; off; addr = a; why = E4_admission.of_decode why };
                   raise Exit
                 | Ok n ->
                   (match admissible view n with
                    | Error why ->
                      stop := Refused { seg; off; addr = a; why };
                      raise Exit
                    | Ok () ->
                      if E4_index.mem_in view.v_reader idx a
                      then incr duplicates
                      else (
                        E4_index.add idx a { E4_index.seg; off; kind = n.E4_node.kind };
                        incr admitted);
                      ends_at := record_end (seg, off) r.E4_pack.r_len))))
       seq
   with
   | Exit -> ());
  { from
  ; admitted = !admitted
  ; duplicates = !duplicates
  ; ends_at = !ends_at
  ; stop = !stop
  ; pack = pack_recovery
  }
;;

let open_rw_exn ~dir opts =
  mkdir_p dir;
  (* The writer lock comes before any read or write of the store: a refused opener removes no
     live writer's control.tmp (K2) and reads no control file that a live writer may replace. *)
  let lock =
    match E4_lock.acquire ~dir with
    | Ok lock -> lock
    | Error d -> raise (Locked d)
  in
  let control, want =
    try
      mkdir_p (Filename.concat dir "index");
      E4_control.cleanup ~dir;
      let control =
        match read_control ~dir with
        | Some p -> p
        | None -> E4_control.initial
      in
      let published = E4_control.pack_end control in
      let want = clamp_watermark ~dir published in
      let empty_sentinel =
        E4_pack.equal_position published (0, 0)
        && List.is_empty (E4_control.roots control)
      in
      if (not (E4_pack.equal_position want published)) && not empty_sentinel
      then raise (Store_error "published durable boundary is outside the pack");
      control, want
    with
    | failure ->
      E4_lock.release lock;
      raise failure
  in
  let pack =
    E4_pack.open_at
      ~lock
      ~from:want
      ~verify:true
      ~truncate:true
      ~dir
      ~seg_max:opts.seg_max
      ()
  in
  let acquired_view = ref None in
  try
    let view = make_view ~dir ~slots:opts.index_slots ~control ~upto:want in
    acquired_view := Some view;
    (* The control boundary limits tail recovery. checked_image separately reads and admits
     every durable record before Disk exposes its value snapshot. The index is a cache. *)
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
             "the pack holds an unadmitted record at seg=%d off=%d (%s): %s.  The store \
              is open for reading; it refuses to grow until an operator acts (e4_cas.mli \
              D6)."
             seg
             off
             (E4_addr.Addr.hex addr)
             (admission_word why))
      | Clean | Torn _ -> None
    in
    if not (E4_pack.equal_position (E4_control.pack_end view.v_control) rec_.ends_at)
    then (
      view.v_control <- E4_control.set_pack_end view.v_control rec_.ends_at;
      write_control view);
    { w_pack = pack
    ; w_view = view
    ; w_recovery = rec_
    ; w_blocked = blocked
    ; w_closed = false
    }
  with
  | failure ->
    (match !acquired_view with
     | Some view -> close_ro view
     | None -> ());
    (try E4_pack.close pack with
     | Invalid_argument _ | Unix.Unix_error _ -> ());
    raise failure
;;

(* The disk opening boundary returns faults as values, including sealed damage. *)
let open_rw ~dir opts =
  try Ok (open_rw_exn ~dir opts) with
  | E4_pack.Damaged_sealed { seg; off; reason } ->
    Error
      (Fault
         (E4_fault.Sealed_segment
            { seg; off; reason = E4_pack.scan_stop_to_string reason }))
  | E4_pack.Bad_pack reason -> Error (Fault (E4_fault.Pack reason))
  | Locked directory | E4_pack.Locked directory ->
    Error (Fault (E4_fault.Locked directory))
  | Store_error reason -> Error (Fault (E4_fault.Store reason))
  | Invalid_argument reason -> Error (Capacity reason)
  | Sys_error reason -> Error (Fault (E4_fault.Io reason))
  | Unix.Unix_error (error, call, argument) ->
    Error (Fault (E4_fault.Io (call ^ " " ^ argument ^ ": " ^ Unix.error_message error)))
;;

let recovery t = t.w_recovery
