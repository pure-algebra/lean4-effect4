(* E4_checkpoint — see e4_checkpoint.mli for what this is, its two byte tables, the PENDING
   note about CAS commit 7, and its behaviours. *)

open Effect4_engine
(* E4_be, E4_sha256, E4_engine — the framing, the hash and the drive loop, all A1's. *)

(* ================================================================ the frame layer *)

(* Writing goes through E4_be and nothing else (brief §2.2: no second encoding is ever
   hashed).  Reading is one small length-directed walk; `Bad` is the only refusal and every
   entry point turns it into None or an error constructor. *)

exception Bad

let f_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let f_bytes b = E4_be.framed Eff_frame.tag_bytes b
let f_list xs = E4_be.framed Eff_frame.tag_list (String.concat "" xs)
let f_pair a b = E4_be.framed Eff_frame.tag_pair (a ^ b)
let f_none = E4_be.framed Eff_frame.tag_none ""
let f_some x = E4_be.framed Eff_frame.tag_some x
let f_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (f_nat i :: args))

let f_ref (r : E4_addr.Ref.t) =
  E4_be.framed Eff_frame.tag_ref
    (String.make 1 (Char.chr (E4_kind.byte r.E4_addr.Ref.kind))
    ^ E4_addr.Addr.bytes r.E4_addr.Ref.addr)

let f_opt_ref = function None -> f_none | Some r -> f_some (f_ref r)
let f_opt_bytes = function None -> f_none | Some b -> f_some (f_bytes b)

type cursor = { s : string; mutable pos : int; stop : int }

let cursor_of s pos stop = { s; pos; stop }
let at_end c = c.pos >= c.stop

let take c =
  match E4_be.read_frame c.s c.pos c.stop with
  | None -> raise Bad
  | Some (tag, ppos, pend, fend) ->
    c.pos <- fend;
    (tag, ppos, pend)

let expect tag c =
  let t, p, e = take c in
  if t <> tag then raise Bad else (p, e)

let rd_nat c =
  let p, e = expect Eff_frame.tag_nat c in
  match E4_be.nat_of_digits (String.sub c.s p (e - p)) with Some n -> n | None -> raise Bad

let rd_bytes c =
  let p, e = expect Eff_frame.tag_bytes c in
  String.sub c.s p (e - p)

let rd_ref c =
  let p, e = expect Eff_frame.tag_ref c in
  if e - p <> 33 then raise Bad
  else
    match E4_kind.of_byte (Char.code c.s.[p]) with
    | None -> raise Bad
    | Some kind -> (
      match E4_addr.Addr.of_digest_opt (String.sub c.s (p + 1) 32) with
      | None -> raise Bad
      | Some addr -> E4_addr.Ref.make kind addr)

let rd_ref_at kind c =
  let r = rd_ref c in
  if E4_kind.equal r.E4_addr.Ref.kind kind then r else raise Bad

let rd_opt inner c =
  let tag, p, e = take c in
  if tag = Eff_frame.tag_none then (if e <> p then raise Bad else None)
  else if tag = Eff_frame.tag_some then begin
    let sub = cursor_of c.s p e in
    let v = inner sub in
    if not (at_end sub) then raise Bad else Some v
  end
  else raise Bad

let rd_list inner c =
  let p, e = expect Eff_frame.tag_list c in
  let sub = cursor_of c.s p e in
  let acc = ref [] in
  while not (at_end sub) do
    acc := inner sub :: !acc
  done;
  List.rev !acc

let rd_ctor c =
  let p, e = expect Eff_frame.tag_ctor c in
  let sub = cursor_of c.s p e in
  let idx = rd_nat sub in
  (idx, sub)

let rd_pair fa fb c =
  let p, e = expect Eff_frame.tag_pair c in
  let sub = cursor_of c.s p e in
  let a = fa sub in
  let b = fb sub in
  if not (at_end sub) then raise Bad else (a, b)

let whole s f = try (let c = cursor_of s 0 (String.length s) in
                     let v = f c in
                     if at_end c then Some v else None)
               with Bad | Invalid_argument _ -> None

(* ================================================================ the node *)

type image =
  | Whole of string
  | Chunked of E4_addr.Ref.t list
  | Manifested of E4_addr.Ref.t

type t = {
  job : E4_addr.Ref.t;
  position : int;
  tape_prefix : E4_addr.Ref.t option;
  prev : E4_addr.Ref.t option;
  engine : E4_addr.Addr.t;
  image_length : int;
  image : image;
}

let f_image = function
  | Whole b -> f_ctor 0 [ f_bytes b ]
  | Chunked refs -> f_ctor 1 [ f_list (List.map f_ref refs) ]
  | Manifested r -> f_ctor 2 [ f_ref r ]

let encode (t : t) =
  f_ctor 0
    [ f_ref t.job;
      f_nat t.position;
      f_opt_ref t.tape_prefix;
      f_opt_ref t.prev;
      f_bytes (E4_addr.Addr.bytes t.engine);
      f_nat t.image_length;
      f_image t.image ]

let rd_image c =
  let idx, sub = rd_ctor c in
  let v =
    match idx with
    | 0 -> Whole (rd_bytes sub)
    | 1 -> Chunked (rd_list (rd_ref_at E4_kind.Chunk) sub)
    | 2 -> Manifested (rd_ref_at E4_kind.Manifest sub)
    | _ -> raise Bad
  in
  if not (at_end sub) then raise Bad else v

let decode bytes =
  whole bytes (fun c ->
      let idx, sub = rd_ctor c in
      if idx <> 0 then raise Bad;
      let job = rd_ref_at E4_kind.Job sub in
      let position = rd_nat sub in
      let tape_prefix = rd_opt (rd_ref_at E4_kind.Tape) sub in
      let prev = rd_opt (rd_ref_at E4_kind.Checkpoint) sub in
      let eng = rd_bytes sub in
      let engine = match E4_addr.Addr.of_digest_opt eng with Some a -> a | None -> raise Bad in
      let image_length = rd_nat sub in
      let image = rd_image sub in
      if not (at_end sub) then raise Bad;
      { job; position; tape_prefix; prev; engine; image_length; image })

let payload_of = encode
let t_of_payload = decode

let node ~spec t =
  E4_node.make ~version:0 ~kind:E4_kind.Checkpoint ~spec:(E4_addr.Addr.bytes spec)
    ~payload:(encode t)

(* ================================================================ the pending schema (D7) *)

let image_version = 0
let pending = true

let schema_payload =
  f_ctor 0
    [ f_bytes "e4.checkpoint";
      f_nat image_version;
      f_bytes "pending: the run-relative payload shapes are CAS commit 7's (A2 §5.2 R6)" ]

let schema_node =
  E4_node.make ~version:0 ~kind:E4_kind.Schema ~spec:E4_node.zero_digest ~payload:schema_payload

let schema_address = E4_node.address schema_node

let ensure_schema st =
  (match E4_cas.put st schema_node with
  | Ok _ -> ()
  | Error a ->
    raise
      (E4_cas.Store_error
         ("E4_checkpoint: the pending schema node was refused: " ^ E4_cas.admission_word a)));
  schema_address

(* ================================================================ the roots *)

let head_root_name job = Printf.sprintf "runs/%s/checkpoint" (E4_addr.Addr.hex job)

let pin_root_name ~job cid =
  Printf.sprintf "runs/%s/pin/%s" (E4_addr.Addr.hex job) (E4_addr.Addr.hex cid)

(* ================================================================ writing *)

type write_error =
  | Refused of E4_cas.admission
  | Chunk_refused of string
  | Root_refused of E4_control.root_error

let write_error_word = function
  | Refused a -> "refused " ^ E4_cas.admission_word a
  | Chunk_refused s -> "chunkRefused " ^ s
  | Root_refused e -> "rootRefused " ^ E4_control.root_error_word e

exception Write_refused of string

type written = {
  addr : E4_addr.Addr.t;
  chunks_cut : int;
  chunks_fresh : int;
  chunks_dup : int;
  manifest_nodes : int;
  manifest_fresh : int;
  manifest_dup : int;
  payload_bytes : int;
  image_bytes_written : int;
}

let mint_pin st ~job ~cid ~addr =
  let view = E4_cas.read_only st in
  let name = E4_control.normalise_name (pin_root_name ~job cid) in
  let version = E4_cas.next_version view name in
  E4_cas.advance_root st
    { E4_control.name;
      root_kind = E4_control.Pin;
      kind = E4_kind.Checkpoint;
      digest = addr;
      version }

let advance_head st ~job ~addr ~prev =
  let view = E4_cas.read_only st in
  let name = E4_control.normalise_name (head_root_name job) in
  let version = E4_cas.next_version view name in
  let prev_addr = match prev with Some a -> a | None -> E4_addr.Addr.zero in
  E4_cas.advance_root st ~prev:prev_addr
    { E4_control.name;
      root_kind = E4_control.Registry;
      kind = E4_kind.Checkpoint;
      digest = addr;
      version }

let write_counted st ~job ~position ~machine_image ~prev ?(params = E4_chunk.default)
    ?(threshold = E4_chunk.threshold) ?(manifest = true) ?tape_prefix ?(pin = true)
    ?(pin_via_cid = false) ?(head = true) () =
  let spec = ensure_schema st in
  let engine = E4_addr.Addr.of_digest (E4_sha256.digest machine_image) in
  let image_length = String.length machine_image in
  match
    if image_length < threshold then
      Ok (Whole machine_image, 0, 0, 0, 0, 0, 0)
    else
      try
        let refs, fresh, dup = E4_chunk.store_counted st ~spec params machine_image in
        let cut = List.length refs in
        if manifest then begin
          let root, mn, mf, md = E4_chunk.store_manifest_counted st ~spec refs in
          Ok (Manifested root, cut, fresh, dup, mn, mf, md)
        end
        else Ok (Chunked refs, cut, fresh, dup, 0, 0, 0)
      with E4_cas.Store_error why -> Error (Chunk_refused why)
  with
  | Error e -> Error e
  | Ok (image, chunks_cut, chunks_fresh, chunks_dup, manifest_nodes, manifest_fresh, manifest_dup)
    -> (
    let cp =
      { job = E4_addr.Ref.make E4_kind.Job job;
        position;
        tape_prefix = Option.map (E4_addr.Ref.make E4_kind.Tape) tape_prefix;
        prev = Option.map (E4_addr.Ref.make E4_kind.Checkpoint) prev;
        engine;
        image_length;
        image }
    in
    let payload = encode cp in
    match E4_cas.put st (node ~spec cp) with
    | Error a -> Error (Refused a)
    | Ok (_, addr) -> (
      (* the group commit: one write(2) and one fsync(2) for every node this checkpoint
         added, then the roots (E4_cas CS5, D7) *)
      E4_cas.commit st;
      let cid = E4_addr.Addr.of_digest (E4_sha256.digest payload) in
      let pinned =
        if not pin then Ok ()
        else if pin_via_cid then E4_cas.pin_all st ~job [ cid ]
        else mint_pin st ~job ~cid ~addr
      in
      match pinned with
      | Error e -> Error (Root_refused e)
      | Ok () -> (
        match if head then advance_head st ~job ~addr ~prev else Ok () with
        | Error e -> Error (Root_refused e)
        | Ok () ->
          Ok
            { addr;
              chunks_cut;
              chunks_fresh;
              chunks_dup;
              manifest_nodes;
              manifest_fresh;
              manifest_dup;
              payload_bytes = String.length payload;
              image_bytes_written = image_length })))

let write st ~job ~position ~machine_image ~prev ?params ?threshold ?manifest ?tape_prefix ?pin
    ?pin_via_cid ?head () =
  match
    write_counted st ~job ~position ~machine_image ~prev ?params ?threshold ?manifest
      ?tape_prefix ?pin ?pin_via_cid ?head ()
  with
  | Ok w -> Ok w.addr
  | Error e -> Error e

let write_exn st ~job ~position ~machine_image ~prev =
  match write st ~job ~position ~machine_image ~prev () with
  | Ok a -> a
  | Error e -> raise (Write_refused (write_error_word e))

(* ================================================================ reading *)

type read_error =
  | Absent of E4_addr.Addr.t
  | Not_a_checkpoint of E4_kind.t
  | Bad_payload
  | Missing_chunk
  | Image_mismatch of { expected : E4_addr.Addr.t; actual : E4_addr.Addr.t }
  | Length_mismatch of { expected : int; actual : int }

let read_error_word = function
  | Absent a -> "absent " ^ E4_addr.Addr.hex a
  | Not_a_checkpoint k -> "notACheckpoint " ^ E4_kind.name k
  | Bad_payload -> "badPayload"
  | Missing_chunk -> "missingChunk"
  | Image_mismatch { expected; actual } ->
    Printf.sprintf "imageMismatch expected=%s actual=%s" (E4_addr.Addr.hex expected)
      (E4_addr.Addr.hex actual)
  | Length_mismatch { expected; actual } ->
    Printf.sprintf "lengthMismatch expected=%d actual=%d" expected actual

let image_bytes ro (cp : t) =
  match cp.image with
  | Whole b -> Some b
  | Chunked refs -> E4_chunk.reassemble ro refs
  | Manifested r -> E4_chunk.reassemble_manifest ro r

let read ro addr =
  match E4_cas.get_node ro addr with
  | None -> Error (Absent addr)
  | Some n when not (E4_kind.equal n.E4_node.kind E4_kind.Checkpoint) ->
    Error (Not_a_checkpoint n.E4_node.kind)
  | Some n -> (
    match decode n.E4_node.payload with
    | None -> Error Bad_payload
    | Some cp -> (
      match image_bytes ro cp with
      | None -> Error Missing_chunk
      | Some img ->
        if String.length img <> cp.image_length then
          Error (Length_mismatch { expected = cp.image_length; actual = String.length img })
        else
          let d = E4_addr.Addr.of_digest (E4_sha256.digest img) in
          if not (E4_addr.Addr.equal d cp.engine) then
            Error (Image_mismatch { expected = cp.engine; actual = d })
          else Ok (cp, img)))

let read_parts ro addr =
  match read ro addr with
  | Error e -> Error e
  | Ok (cp, img) ->
    Ok
      ( cp.job.E4_addr.Ref.addr,
        cp.position,
        Option.map (fun (r : E4_addr.Ref.t) -> r.E4_addr.Ref.addr) cp.prev,
        img )

let head ro job =
  match E4_cas.root ro (E4_control.normalise_name (head_root_name job)) with
  | Some r -> Some r.E4_control.digest
  | None -> None

(* ================================================================ the chain (CP8) *)

type chain_error = Cycle of E4_addr.Addr.t | Unreadable of E4_addr.Addr.t * read_error

let chain_from ~prev_of start =
  let seen = Hashtbl.create 64 in
  let rec go a acc =
    let key = E4_addr.Addr.bytes a in
    if Hashtbl.mem seen key then Error (Cycle a)
    else begin
      Hashtbl.replace seen key ();
      match prev_of a with None -> Ok (List.rev (a :: acc)) | Some p -> go p (a :: acc)
    end
  in
  go start []

let chain ro start =
  let failed = ref None in
  let prev_of a =
    match read ro a with
    | Error e ->
      if !failed = None then failed := Some (a, e);
      None
    | Ok (cp, _) -> Option.map (fun (r : E4_addr.Ref.t) -> r.E4_addr.Ref.addr) cp.prev
  in
  match chain_from ~prev_of start with
  | Error e -> Error e
  | Ok l -> ( match !failed with Some (a, e) -> Error (Unreadable (a, e)) | None -> Ok l)

(* ================================================================ the closure (CP9, R8) *)

let closure_fold ro (root : E4_addr.Ref.t) ~init ~f =
  let seen = Hashtbl.create 1024 in
  let acc = ref init in
  let rec go (a : E4_addr.Addr.t) =
    let key = E4_addr.Addr.bytes a in
    if not (Hashtbl.mem seen key) then begin
      Hashtbl.replace seen key ();
      match E4_cas.get_node ro a with
      | None -> ()
      | Some n ->
        List.iter (fun (e : E4_addr.Ref.t) -> go e.E4_addr.Ref.addr) (E4_node.checked_edges n);
        acc := f !acc a n
    end
  in
  go root.E4_addr.Ref.addr;
  !acc

let closure_streaming ro root f = closure_fold ro root ~init:() ~f:(fun () a n -> f a n)

let closure_size ro root =
  closure_fold ro root ~init:(0, 0) ~f:(fun (n, b) _ node ->
      (n + 1, b + String.length (E4_node.encode node)))

(* ================================================================ ephemeral (CP10) *)

let ephemeral wal ~position = E4_wal.checkpoint_mark wal position

(* ================================================================ the machine image *)

type machine_image = {
  mi_version : int;
  mi_carriers : string;
  mi_fuel : int;
  mi_outcome : string;
  mi_answer : string;
  mi_fiber_count : int;
  mi_trace_length : int;
  mi_root_exit : string option;
  mi_exits : (int * string) list;
  mi_fiber_rows : (int * string) list;
  mi_trace_rows : string list;
  mi_refs : string list;
  mi_store_row : string;
}

let encode_image m =
  f_ctor 0
    [ f_nat m.mi_version;
      f_bytes m.mi_carriers;
      f_nat m.mi_fuel;
      f_bytes m.mi_outcome;
      f_bytes m.mi_answer;
      f_nat m.mi_fiber_count;
      f_nat m.mi_trace_length;
      f_opt_bytes m.mi_root_exit;
      f_list (List.map (fun (i, s) -> f_pair (f_nat i) (f_bytes s)) m.mi_exits);
      f_list (List.map (fun (i, s) -> f_pair (f_nat i) (f_bytes s)) m.mi_fiber_rows);
      f_list (List.map f_bytes m.mi_trace_rows);
      f_list (List.map f_bytes m.mi_refs);
      f_bytes m.mi_store_row ]

let machine_of_image bytes =
  whole bytes (fun c ->
      let idx, s = rd_ctor c in
      if idx <> 0 then raise Bad;
      let mi_version = rd_nat s in
      let mi_carriers = rd_bytes s in
      let mi_fuel = rd_nat s in
      let mi_outcome = rd_bytes s in
      let mi_answer = rd_bytes s in
      let mi_fiber_count = rd_nat s in
      let mi_trace_length = rd_nat s in
      let mi_root_exit = rd_opt rd_bytes s in
      let mi_exits = rd_list (rd_pair rd_nat rd_bytes) s in
      let mi_fiber_rows = rd_list (rd_pair rd_nat rd_bytes) s in
      let mi_trace_rows = rd_list rd_bytes s in
      let mi_refs = rd_list rd_bytes s in
      let mi_store_row = rd_bytes s in
      if not (at_end s) then raise Bad;
      { mi_version; mi_carriers; mi_fuel; mi_outcome; mi_answer; mi_fiber_count;
        mi_trace_length; mi_root_exit; mi_exits; mi_fiber_rows; mi_trace_rows; mi_refs;
        mi_store_row })

let show_frontier (fr : E4_engine.frontier) =
  Printf.sprintf "parked=[%s] armed=[%s] due=%d"
    (String.concat "," (List.map (fun (a, b) -> Printf.sprintf "%d:%d" a b) fr.E4_engine.parked))
    (String.concat "," (List.map string_of_int fr.E4_engine.armed))
    fr.E4_engine.due

let show_answer = function
  | E4_engine.Finished -> "finished"
  | E4_engine.Suspended fr -> "suspended " ^ show_frontier fr
  | E4_engine.Refused s -> "refused " ^ s
  | E4_engine.Delay fr -> "delay " ^ show_frontier fr

module Of_engine (En : E4_engine.ENGINE) = struct
  let state (t : En.t) =
    { mi_version = image_version;
      mi_carriers = En.carriers;
      mi_fuel = En.fuel t;
      mi_outcome = En.outcome t;
      mi_answer = show_answer (En.answer t);
      mi_fiber_count = En.fiber_count t;
      mi_trace_length = En.trace_length t;
      mi_root_exit = En.root_exit t;
      mi_exits = En.exits t;
      mi_fiber_rows = En.fiber_rows t;
      mi_trace_rows = En.trace_rows t;
      mi_refs = En.refs t;
      mi_store_row = En.store_row t }

  let image t = encode_image (state t)
end

module Fast_image = Of_engine (E4_engine.Fast)

let machine_state = Fast_image.state
let image_of_machine = Fast_image.image
