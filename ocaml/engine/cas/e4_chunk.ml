(* E4_chunk — see e4_chunk.mli for what this is, its byte grammar and its behaviours. *)

open Effect4_engine
(* E4_be, E4_sha256 — never a second framing writer and never a second hash (brief §2.2). *)

(* ---------------------------------------------------------------- the parameters *)

type params = { avg : int; min : int; max : int }

let window = 62
let mask62 = (1 lsl 62) - 1
let default = { avg = 16384; min = 4096; max = 65536 }
let threshold = 1 lsl 20

let is_pow2 n = n > 0 && n land (n - 1) = 0

let log2 n =
  let r = ref 0 and v = ref n in
  while !v > 1 do
    incr r;
    v := !v lsr 1
  done;
  !r

(* The cut mask sits at the TOP of the 62-bit word, not the bottom.  Bit j of h after the
   recurrence depends on the last j+1 bytes, so a mask over the low `bits` bits would make the
   cut a function of the last `bits` bytes ALONE — on data with a short period that is a few
   distinct windows and the candidate density has nothing to do with `avg`.  Measured on a
   period-90 synthetic image: a low mask at avg = 1024 cut every 292 bytes (min-forced) and a
   one-byte insertion re-phased the whole lattice.  At the top of the word every mask bit
   depends on 49..62 preceding bytes, which is the window CH6 cites. *)
let cut_mask_of p =
  let b = log2 p.avg in
  ((1 lsl b) - 1) lsl (62 - b)

let params_ok p =
  p.min > window && is_pow2 p.avg && p.min <= p.avg && p.avg <= p.max
  && p.max <= max_int / 2
  && log2 p.avg <= 30

let check_params p =
  if not (params_ok p) then
    invalid_arg
      (Printf.sprintf "E4_chunk: params avg=%d min=%d max=%d (need %d < min <= avg <= max, avg a power of two)"
         p.avg p.min p.max window)

(* The gear table.  Derived from the one hash this estate has, so the 256 constants are
   reproducible from the .mli's one line and are never typed out.  Seven bytes, not eight:
   eight would overflow a 63-bit int during the fold and the value would depend on
   Sys.int_size.  Built once, at module initialisation; it is read-only for ever after. *)
let gear : int array =
  let a = Array.make 256 0 in
  for i = 0 to 255 do
    let d = E4_sha256.digest ("e4.chunk.gear.v0:" ^ String.make 1 (Char.chr i)) in
    let v = ref 0 in
    for j = 0 to 6 do
      v := (!v lsl 8) lor Char.code (String.unsafe_get d j)
    done;
    a.(i) <- !v land mask62
  done;
  a

(* ---------------------------------------------------------------- cutting *)

let cut p s =
  check_params p;
  let n = String.length s in
  let cut_mask = cut_mask_of p in
  let out = ref [] in
  let start = ref 0 in
  while !start < n do
    let hi = if n - !start <= p.max then n else !start + p.max in
    let lo = !start + p.min in
    let h = ref 0 in
    let stop = ref (-1) in
    let i = ref !start in
    while !stop < 0 && !i < hi do
      h := ((!h lsl 1) lxor Array.unsafe_get gear (Char.code (String.unsafe_get s !i))) land mask62;
      incr i;
      if !i >= lo && !h land cut_mask = 0 then stop := !i
    done;
    let e = if !stop >= 0 then !stop else hi in
    out := (!start, e - !start) :: !out;
    start := e
  done;
  List.rev !out

let chunks s = cut default s
let piece s (off, len) = String.sub s off len
let pieces p s = List.map (piece s) (cut p s)

(* ---------------------------------------------------------------- the manifest *)

type manifest = Leaf of E4_addr.Ref.t list | Interior of E4_addr.Ref.t list
type groups = { g_avg : int; g_min : int; g_max : int }

let groups_default = { g_avg = 256; g_min = 64; g_max = 1024 }
let single_max_default = 1024
let single_max = single_max_default

let check_groups g =
  if not (g.g_min > 0 && is_pow2 g.g_avg && g.g_min <= g.g_avg && g.g_avg <= g.g_max) then
    invalid_arg
      (Printf.sprintf "E4_chunk: groups avg=%d min=%d max=%d" g.g_avg g.g_min g.g_max)

let group_cut g refs =
  check_groups g;
  let gmask = g.g_avg - 1 in
  let out = ref [] and cur = ref [] and k = ref 0 in
  let flush () =
    if !cur <> [] then begin
      out := List.rev !cur :: !out;
      cur := [];
      k := 0
    end
  in
  List.iter
    (fun (r : E4_addr.Ref.t) ->
      cur := r :: !cur;
      incr k;
      let natural = E4_addr.Addr.prefix63 r.E4_addr.Ref.addr land gmask = 0 in
      if (!k >= g.g_min && natural) || !k >= g.g_max then flush ())
    refs;
  flush ();
  List.rev !out

(* ---- the frame layer: E4_be only, never a second writer (brief §2.2) ---- *)

let f_nat n = E4_be.framed Eff_frame.tag_nat (E4_be.nat_digits n)
let f_list xs = E4_be.framed Eff_frame.tag_list (String.concat "" xs)
let f_bytes b = E4_be.framed Eff_frame.tag_bytes b
let f_ctor i args = E4_be.framed Eff_frame.tag_ctor (String.concat "" (f_nat i :: args))

let f_ref (r : E4_addr.Ref.t) =
  E4_be.framed Eff_frame.tag_ref
    (String.make 1 (Char.chr (E4_kind.byte r.E4_addr.Ref.kind))
    ^ E4_addr.Addr.bytes r.E4_addr.Ref.addr)

let encode_manifest = function
  | Leaf refs -> f_ctor 0 [ f_list (List.map f_ref refs) ]
  | Interior refs -> f_ctor 1 [ f_list (List.map f_ref refs) ]

(* One frame reader for this module's own payloads.  It reads frames through E4_be and adds
   no grammar: a tag it does not expect at a position is a refusal. *)
let read_ref s pos limit =
  match E4_be.read_frame s pos limit with
  | Some (tag, ppos, pend, fend) when tag = Eff_frame.tag_ref && pend - ppos = 33 -> (
    match E4_kind.of_byte (Char.code s.[ppos]) with
    | None -> None
    | Some kind -> (
      match E4_addr.Addr.of_digest_opt (String.sub s (ppos + 1) 32) with
      | None -> None
      | Some addr -> Some (E4_addr.Ref.make kind addr, fend)))
  | _ -> None

let read_refs_of_kind s pos limit kind =
  let rec go pos acc =
    if pos >= limit then Some (List.rev acc)
    else
      match read_ref s pos limit with
      | None -> None
      | Some (r, next) ->
        if E4_kind.equal r.E4_addr.Ref.kind kind then go next (r :: acc) else None
  in
  go pos []

let decode_manifest bytes =
  let n = String.length bytes in
  match E4_be.read_frame bytes 0 n with
  | Some (tag, ppos, pend, fend) when tag = Eff_frame.tag_ctor && fend = n -> (
    match E4_be.read_frame bytes ppos pend with
    | Some (t0, i0, e0, a0) when t0 = Eff_frame.tag_nat -> (
      match E4_be.nat_of_digits (String.sub bytes i0 (e0 - i0)) with
      | None -> None
      | Some idx when idx = 0 || idx = 1 -> (
        match E4_be.read_frame bytes a0 pend with
        | Some (tl, lpos, lend, lfend) when tl = Eff_frame.tag_list && lfend = pend -> (
          let kind = if idx = 0 then E4_kind.Chunk else E4_kind.Manifest in
          match read_refs_of_kind bytes lpos lend kind with
          | None -> None
          | Some refs -> Some (if idx = 0 then Leaf refs else Interior refs))
        | _ -> None)
      | _ -> None)
    | _ -> None)
  | _ -> None

(* ---------------------------------------------------------------- storing *)

let chunk_payload b = f_bytes b

let chunk_node ~spec b =
  E4_node.make ~version:0 ~kind:E4_kind.Chunk ~spec:(E4_addr.Addr.bytes spec) ~payload:(f_bytes b)

let put_node st (n : E4_node.t) =
  match E4_cas.put st n with
  | Ok (o, addr) -> (o, addr)
  | Error a ->
    raise
      (E4_cas.Store_error
         (Printf.sprintf "E4_chunk: the store refused a %s node: %s" (E4_kind.name n.E4_node.kind)
            (E4_cas.admission_word a)))

let store_counted st ~spec p image =
  let fresh = ref 0 and dup = ref 0 in
  let refs =
    List.map
      (fun (off, len) ->
        let o, addr = put_node st (chunk_node ~spec (String.sub image off len)) in
        (match o with
        | E4_cas.Fresh -> incr fresh
        | E4_cas.Duplicate -> incr dup
        | E4_cas.Conflict _ ->
          raise (E4_cas.Store_error "E4_chunk: a chunk address is occupied by another node"));
        E4_addr.Ref.make E4_kind.Chunk addr)
      (cut p image)
  in
  (refs, !fresh, !dup)

let store st ~spec p image =
  let refs, _, _ = store_counted st ~spec p image in
  refs

let store_manifest_counted st ~spec ?(groups = groups_default) ?(single_max = single_max_default) refs =
  let nodes = ref 0 and fresh = ref 0 and dup = ref 0 in
  let file m kind =
    let o, addr =
      put_node st
        (E4_node.make ~version:0 ~kind ~spec:(E4_addr.Addr.bytes spec) ~payload:(encode_manifest m))
    in
    incr nodes;
    (match o with
    | E4_cas.Fresh -> incr fresh
    | E4_cas.Duplicate -> incr dup
    | E4_cas.Conflict _ ->
      raise (E4_cas.Store_error "E4_chunk: a manifest address is occupied by another node"));
    E4_addr.Ref.make kind addr
  in
  (* level 0: the chunk refs.  One leaf while they fit; otherwise groups, and then the same
     rule one level up over the group refs, until one node holds the level (CH8). *)
  let root =
    if List.length refs <= single_max then file (Leaf refs) E4_kind.Manifest
    else begin
      let level = ref (List.map (fun g -> file (Leaf g) E4_kind.Manifest) (group_cut groups refs)) in
      while List.length !level > single_max do
        level := List.map (fun g -> file (Interior g) E4_kind.Manifest) (group_cut groups !level)
      done;
      file (Interior !level) E4_kind.Manifest
    end
  in
  (root, !nodes, !fresh, !dup)

let store_manifest st ~spec ?groups ?single_max refs =
  let r, _, _, _ = store_manifest_counted st ~spec ?groups ?single_max refs in
  r

(* ---------------------------------------------------------------- reading *)

let payload_of ro (r : E4_addr.Ref.t) kind =
  if not (E4_kind.equal r.E4_addr.Ref.kind kind) then None
  else
    match E4_cas.get_node ro r.E4_addr.Ref.addr with
    | Some n when E4_kind.equal n.E4_node.kind kind -> Some n.E4_node.payload
    | _ -> None

let get_chunk ro r =
  match payload_of ro r E4_kind.Chunk with
  | None -> None
  | Some payload -> (
    match E4_be.exact_frame payload with
    | Some (tag, b) when tag = Eff_frame.tag_bytes -> Some b
    | _ -> None)

let reassemble ro refs =
  let buf = Buffer.create 4096 in
  let rec go = function
    | [] -> Some (Buffer.contents buf)
    | r :: rest -> (
      match get_chunk ro r with
      | None -> None
      | Some b ->
        Buffer.add_string buf b;
        go rest)
  in
  go refs

let get_manifest ro r =
  match payload_of ro r E4_kind.Manifest with
  | None -> None
  | Some payload -> decode_manifest payload

(* The walk is explicit, not recursive over the whole tree at once: `fold_chunks` holds one
   chunk's bytes and a stack of refs, never the image (CH9, risk R8). *)
let fold_chunks ro root ~init ~f =
  let ok = ref true in
  let acc = ref init in
  let rec walk (r : E4_addr.Ref.t) =
    if !ok then
      if E4_kind.equal r.E4_addr.Ref.kind E4_kind.Chunk then
        match get_chunk ro r with None -> ok := false | Some b -> acc := f !acc b
      else
        match get_manifest ro r with
        | None -> ok := false
        | Some (Leaf refs) -> List.iter walk refs
        | Some (Interior refs) -> List.iter walk refs
  in
  walk root;
  if !ok then Some !acc else None

let flatten ro root =
  let ok = ref true in
  let out = ref [] in
  let rec walk (r : E4_addr.Ref.t) =
    if !ok then
      if E4_kind.equal r.E4_addr.Ref.kind E4_kind.Chunk then out := r :: !out
      else
        match get_manifest ro r with
        | None -> ok := false
        | Some (Leaf refs) -> List.iter walk refs
        | Some (Interior refs) -> List.iter walk refs
  in
  walk root;
  if !ok then Some (List.rev !out) else None

let reassemble_manifest ro root =
  match fold_chunks ro root ~init:(Buffer.create 4096) ~f:(fun b s -> Buffer.add_string b s; b) with
  | None -> None
  | Some buf -> Some (Buffer.contents buf)
