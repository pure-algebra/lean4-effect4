(* E4_index — see e4_index.mli for what this is, the slot layout, the laws L-IDX-0/1/2 and the
   deviations.  Lane P2, 2026-09-08. *)

open Effect4_engine

type seg = int
type off = int

type entry = { seg : seg; off : off; kind : E4_kind.t }

(* ============================================================ 1. the slot (D1) *)

let slot_bytes = 16
let kind_bits = 8
let off_bits = 43
let seg_bits = 11
let max_seg = (1 lsl seg_bits) - 1
let max_off = (1 lsl off_bits) - 1
let max_load = 0.6
let min_slots = 16

let pack_val ~seg ~off ~kind =
  if seg < 0 || seg > max_seg then invalid_arg "E4_index: segment out of range";
  if off < 0 || off > max_off then invalid_arg "E4_index: offset out of range";
  (seg lsl (kind_bits + off_bits)) lor (off lsl kind_bits) lor E4_kind.byte kind

let unpack_val v =
  let kb = v land ((1 lsl kind_bits) - 1) in
  match E4_kind.of_byte kb with
  | None -> None
  | Some kind ->
    Some
      {
        seg = v lsr (kind_bits + off_bits);
        off = (v lsr kind_bits) land ((1 lsl off_bits) - 1);
        kind;
      }

(* ============================================================ 2. the table *)

type ia = (int, Bigarray.int_elt, Bigarray.c_layout) Bigarray.Array1.t

type t = {
  mutable keys : ia;
  mutable vals : ia;
  mutable n_slots : int;
  mutable mask : int;
  mutable n : int;
  mutable growths : int;
  mutable max_probe : int;
  mutable confirms : int;
  mutable confirm_misses : int;
}

type index = t

let round_up_pow2 n =
  let n = if n < min_slots then min_slots else n in
  let p = ref min_slots in
  while !p < n do
    p := !p * 2
  done;
  !p

let alloc slots : ia * ia =
  let k = Bigarray.Array1.create Bigarray.int Bigarray.c_layout slots in
  let v = Bigarray.Array1.create Bigarray.int Bigarray.c_layout slots in
  Bigarray.Array1.fill k 0;
  Bigarray.Array1.fill v 0;
  (k, v)

let create ~slots =
  let s = round_up_pow2 slots in
  let keys, vals = alloc s in
  {
    keys;
    vals;
    n_slots = s;
    mask = s - 1;
    n = 0;
    growths = 0;
    max_probe = 0;
    confirms = 0;
    confirm_misses = 0;
  }

let with_capacity ~capacity = create ~slots:(round_up_pow2 (max 1 capacity * 2))

let count t = t.n
let cardinal t = t.n
let slots t = t.n_slots
let bytes t = t.n_slots * slot_bytes
let load_factor t = float_of_int t.n /. float_of_int t.n_slots

(* Raw insertion into a given pair of arrays: no growth, no idempotence test. *)
let raw_put keys vals mask key v =
  let j = ref (key land mask) in
  let steps = ref 0 in
  while Bigarray.Array1.unsafe_get vals !j <> 0 do
    j := (!j + 1) land mask;
    incr steps
  done;
  Bigarray.Array1.unsafe_set keys !j key;
  Bigarray.Array1.unsafe_set vals !j v;
  !steps

let grow t =
  let s = t.n_slots * 2 in
  let keys, vals = alloc s in
  let mask = s - 1 in
  for j = 0 to t.n_slots - 1 do
    let v = Bigarray.Array1.unsafe_get t.vals j in
    if v <> 0 then ignore (raw_put keys vals mask (Bigarray.Array1.unsafe_get t.keys j) v)
  done;
  t.keys <- keys;
  t.vals <- vals;
  t.n_slots <- s;
  t.mask <- mask;
  t.growths <- t.growths + 1

let add_at t addr ~seg ~off ~kind =
  let v = pack_val ~seg ~off ~kind in
  let key = E4_addr.Addr.prefix63 addr in
  (* IX7: an identical (key, value) already in the probe chain is a no-op. *)
  let j = ref (key land t.mask) in
  let dup = ref false in
  let stop = ref false in
  while not !stop do
    let sv = Bigarray.Array1.unsafe_get t.vals !j in
    if sv = 0 then stop := true
    else if sv = v && Bigarray.Array1.unsafe_get t.keys !j = key then begin
      dup := true;
      stop := true
    end
    else j := (!j + 1) land t.mask
  done;
  if not !dup then begin
    if float_of_int (t.n + 1) > max_load *. float_of_int t.n_slots then grow t;
    let steps = raw_put t.keys t.vals t.mask key v in
    if steps > t.max_probe then t.max_probe <- steps;
    t.n <- t.n + 1
  end

let add t addr e = add_at t addr ~seg:e.seg ~off:e.off ~kind:e.kind

let iter t f =
  for j = 0 to t.n_slots - 1 do
    let v = Bigarray.Array1.unsafe_get t.vals j in
    if v <> 0 then
      match unpack_val v with
      | Some e -> f (Bigarray.Array1.unsafe_get t.keys j) e
      | None -> ()
  done

(* ============================================================ 3. lookup (IX1) *)

type confirm = seg:seg -> off:off -> E4_addr.Addr.t option

let confirm_of_reader rd ~seg ~off =
  match E4_pack.read_header rd ~seg ~off with Some (a, _) -> Some a | None -> None

let find_unconfirmed t addr =
  let key = E4_addr.Addr.prefix63 addr in
  let j = ref (key land t.mask) in
  let res = ref None in
  let stop = ref false in
  while not !stop do
    let v = Bigarray.Array1.unsafe_get t.vals !j in
    if v = 0 then stop := true
    else if Bigarray.Array1.unsafe_get t.keys !j = key then begin
      res := unpack_val v;
      stop := true
    end
    else j := (!j + 1) land t.mask
  done;
  !res

(* The confirming probe: a slot whose key matches but whose record does not is a prefix
   collision -- pay for a read and KEEP PROBING (L-IDX-1). *)
let find_with t addr (confirm : seg:seg -> off:off -> E4_addr.Addr.t option) =
  let key = E4_addr.Addr.prefix63 addr in
  let j = ref (key land t.mask) in
  let res = ref None in
  let stop = ref false in
  while not !stop do
    let v = Bigarray.Array1.unsafe_get t.vals !j in
    if v = 0 then stop := true
    else if Bigarray.Array1.unsafe_get t.keys !j = key then begin
      match unpack_val v with
      | None -> j := (!j + 1) land t.mask
      | Some e -> (
        t.confirms <- t.confirms + 1;
        match confirm ~seg:e.seg ~off:e.off with
        | Some a when E4_addr.Addr.equal a addr ->
          res := Some e;
          stop := true
        | _ ->
          t.confirm_misses <- t.confirm_misses + 1;
          j := (!j + 1) land t.mask)
    end
    else j := (!j + 1) land t.mask
  done;
  !res

let find ~confirm t addr = find_with t addr confirm
let find_in rd t addr = find_with t addr (confirm_of_reader rd)
let mem ~confirm t addr = find ~confirm t addr <> None
let mem_in rd t addr = find_in rd t addr <> None

let find_full rd t addr =
  let len = ref (-1) in
  let confirm ~seg ~off =
    match E4_pack.read_header rd ~seg ~off with
    | Some (a, l) ->
      len := l;
      Some a
    | None -> None
  in
  match find_with t addr confirm with Some e -> Some (e, !len) | None -> None

type stats = {
  s_entries : int;
  s_slots : int;
  s_bytes : int;
  s_growths : int;
  s_max_probe : int;
  s_confirms : int;
  s_confirm_misses : int;
}

let stats t =
  {
    s_entries = t.n;
    s_slots = t.n_slots;
    s_bytes = bytes t;
    s_growths = t.growths;
    s_max_probe = t.max_probe;
    s_confirms = t.confirms;
    s_confirm_misses = t.confirm_misses;
  }

let reset_counters t =
  t.confirms <- 0;
  t.confirm_misses <- 0;
  t.max_probe <- 0

let heap_live_words () =
  Gc.compact ();
  (Gc.stat ()).Gc.live_words

(* ============================================================ 4. rebuild (IX2) *)

let from_start = (0, E4_pack.head_length)

type kind_at = E4_pack.reader -> seg:seg -> off:off -> E4_kind.t option

(* D5: the kind is the SECOND byte of node_bytes (E4_node's envelope), and no P1 entry point
   hands back two bytes of a payload, so the default reads the record. *)
let kind_at_default rd ~seg ~off =
  match E4_pack.read_at rd ~seg ~off with
  | Some (_, b) when String.length b >= 2 -> E4_kind.of_byte (Char.code b.[1])
  | _ -> None

(* The fast probe: one byte at a DOCUMENTED offset of the pack grammar
   (`E4_pack.record_header_length + 1` into a record is `node_bytes.[1]`, the kind byte of
   `E4_node.encode`), read out of a private read-only mapping of the segment file.  It
   reimplements no reader: it uses `E4_pack.seg_path` and the two exported constants and touches
   exactly one byte per record.  It is as trusting as the non-verifying scan it runs beside --
   neither checks a CRC -- and it does NOT see bytes a writer appends after the closure's first
   look at a segment, which is why it is for a rebuild to a fixed `pack_end` and nothing else. *)
let kind_at_of_dir ~dir : kind_at =
  let maps : (int, (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t option)
      Hashtbl.t =
    Hashtbl.create 8
  in
  let get seg =
    match Hashtbl.find_opt maps seg with
    | Some m -> m
    | None ->
      let m =
        match Unix.openfile (E4_pack.seg_path ~dir seg) [ Unix.O_RDONLY ] 0o600 with
        | exception Unix.Unix_error _ -> None
        | fd ->
          let size = (Unix.fstat fd).Unix.st_size in
          let r =
            if size <= 0 then None
            else
              Some
                (Bigarray.array1_of_genarray
                   (Unix.map_file fd Bigarray.char Bigarray.c_layout false [| size |]))
          in
          Unix.close fd;
          r
      in
      Hashtbl.replace maps seg m;
      m
  in
  fun _rd ~seg ~off ->
    match get seg with
    | None -> None
    | Some m ->
      let p = off + E4_pack.record_header_length + 1 in
      if p < 0 || p >= Bigarray.Array1.dim m then None
      else E4_kind.of_byte (Char.code (Bigarray.Array1.unsafe_get m p))

let rebuild ?(kind_at = kind_at_default) rd ~from t =
  E4_pack.scan rd ~from ~f:(fun addr seg off _len ->
      match kind_at rd ~seg ~off with
      | Some kind -> add_at t addr ~seg ~off ~kind
      | None -> ())

(* When the store directory is known, the fast probe is the one to use: it costs 1.7% over the
   header scan against the default probe's 3.9x (bench_index R1/R1b/R2). *)
let probe ?kind_at ?dir () =
  match (kind_at, dir) with
  | Some k, _ -> k
  | None, Some dir -> kind_at_of_dir ~dir
  | None, None -> kind_at_default

let of_pack ?kind_at ?dir ?capacity rd ~from =
  let t =
    match capacity with Some c -> with_capacity ~capacity:c | None -> create ~slots:1024
  in
  let stop = rebuild ~kind_at:(probe ?kind_at ?dir ()) rd ~from t in
  (t, stop)

(* ============================================================ 5. the file (IX6) *)

let magic = "E4IDX\000"
let version = "00000001"
(* magic 6 ++ version 8 ++ covers_seg 8 ++ covers_off 8 ++ slots 8 ++ count 8 ++ crc 4 *)
let head_length = 6 + 8 + 8 + 8 + 8 + 8 + 4

let be64 = E4_be.be64

let read_be64_exn s pos =
  match E4_be.read_be64 s pos with Some n -> n | None -> raise Exit

(* The two arrays as little-endian 8-byte words, in chunks, with a running CRC. *)
let chunk_words = 8192

let write_array oc (a : ia) slots crc =
  let buf = Bytes.create (chunk_words * 8) in
  let crc = ref crc in
  let i = ref 0 in
  while !i < slots do
    let m = min chunk_words (slots - !i) in
    for j = 0 to m - 1 do
      Bytes.set_int64_le buf (j * 8) (Int64.of_int (Bigarray.Array1.unsafe_get a (!i + j)))
    done;
    let s = Bytes.sub_string buf 0 (m * 8) in
    output_string oc s;
    crc := E4_crc.update !crc s;
    i := !i + m
  done;
  !crc

let read_array ic (a : ia) slots crc =
  let buf = Bytes.create (chunk_words * 8) in
  let crc = ref crc in
  let i = ref 0 in
  while !i < slots do
    let m = min chunk_words (slots - !i) in
    really_input ic buf 0 (m * 8);
    crc := E4_crc.update !crc (Bytes.sub_string buf 0 (m * 8));
    for j = 0 to m - 1 do
      Bigarray.Array1.unsafe_set a (!i + j) (Int64.to_int (Bytes.get_int64_le buf (j * 8)))
    done;
    i := !i + m
  done;
  !crc

let fsync_dir dir =
  match Unix.openfile dir [ Unix.O_RDONLY ] 0o600 with
  | fd ->
    (try Unix.fsync fd with Unix.Unix_error _ -> ());
    Unix.close fd
  | exception Unix.Unix_error _ -> ()

let save ~path t ~covers =
  let cseg, coff = covers in
  let dir = Filename.dirname path in
  (try Unix.mkdir dir 0o755 with Unix.Unix_error _ -> ());
  let tmp = path ^ ".tmp" in
  let oc = open_out_bin tmp in
  let head =
    magic ^ version ^ be64 cseg ^ be64 coff ^ be64 t.n_slots ^ be64 t.n
  in
  output_string oc head;
  output_string oc (E4_crc.be32 (E4_crc.string head));
  let crc = write_array oc t.keys t.n_slots E4_crc.init in
  let crc = write_array oc t.vals t.n_slots crc in
  output_string oc (E4_crc.be32 crc);
  flush oc;
  (try Unix.fsync (Unix.descr_of_out_channel oc) with Unix.Unix_error _ -> ());
  close_out oc;
  Sys.rename tmp path;
  fsync_dir dir

type load_verdict =
  | Loaded
  | No_file
  | Bad_file of string
  | Stale of { covers : seg * off; pack_end : seg * off }

let load_verdict_to_string = function
  | Loaded -> "Loaded"
  | No_file -> "No_file"
  | Bad_file s -> Printf.sprintf "Bad_file(%s)" s
  | Stale { covers = cs, co; pack_end = ps, po } ->
    Printf.sprintf "Stale(covers=%d:%d,pack_end=%d:%d)" cs co ps po

let is_pow2 n = n > 0 && n land (n - 1) = 0

let load_result ~path : (t * (seg * off), load_verdict) result =
  if not (Sys.file_exists path) then Error No_file
  else
    let ic = try Some (open_in_bin path) with Sys_error _ -> None in
    match ic with
    | None -> Error No_file
    | Some ic ->
      let fail msg =
        close_in_noerr ic;
        Error (Bad_file msg)
      in
      (try
         let size = in_channel_length ic in
         if size < head_length + 4 then fail "short file"
         else begin
           let head = really_input_string ic head_length in
           if String.sub head 0 6 <> magic then fail "magic"
           else if String.sub head 6 8 <> version then
             fail (Printf.sprintf "version %S" (String.sub head 6 8))
           else if E4_crc.read_be32 head (head_length - 4) <> Some (E4_crc.string (String.sub head 0 (head_length - 4)))
           then fail "head crc"
           else begin
             let cseg = read_be64_exn head 14 in
             let coff = read_be64_exn head 22 in
             let n_slots = read_be64_exn head 30 in
             let n = read_be64_exn head 38 in
             if not (is_pow2 n_slots) then fail "slots not a power of two"
             else if n_slots > 1 lsl 34 then fail "slots absurd"
             else if n < 0 || n > n_slots then fail "count above slots"
             else if size <> head_length + (n_slots * 16) + 4 then fail "body length"
             else begin
               let keys, vals = alloc n_slots in
               let crc = read_array ic keys n_slots E4_crc.init in
               let crc = read_array ic vals n_slots crc in
               let tail = really_input_string ic 4 in
               if E4_crc.read_be32 tail 0 <> Some crc then fail "body crc"
               else begin
                 close_in_noerr ic;
                 (* the count in the head must be the count in the body *)
                 let seen = ref 0 in
                 for j = 0 to n_slots - 1 do
                   if Bigarray.Array1.unsafe_get vals j <> 0 then incr seen
                 done;
                 if !seen <> n then Error (Bad_file "count disagrees with the body")
                 else
                   Ok
                     ( {
                         keys;
                         vals;
                         n_slots;
                         mask = n_slots - 1;
                         n;
                         growths = 0;
                         max_probe = 0;
                         confirms = 0;
                         confirm_misses = 0;
                       },
                       (cseg, coff) )
               end
             end
           end
         end
       with
      | End_of_file -> fail "truncated"
      | Exit -> fail "be64 out of range"
      | Sys_error m -> fail m)

let load ~path = match load_result ~path with Ok r -> Some r | Error _ -> None

let load_at ~path ~pack_end =
  match load_result ~path with
  | Error v -> Error v
  | Ok (t, covers) -> if covers = pack_end then Ok t else Error (Stale { covers; pack_end })

let open_index ?kind_at ?dir ~path rd ~pack_end =
  match load_at ~path ~pack_end with
  | Ok t -> (t, Loaded, None)
  | Error v ->
    let t = create ~slots:1024 in
    let stop = rebuild ~kind_at:(probe ?kind_at ?dir ()) rd ~from:from_start t in
    (t, v, Some stop)

(* ============================================================ 6. the by-kind index *)

module By_kind = struct
  (* One growable off-heap position array per kind byte.  A position is
     (seg lsl off_bits) lor off -- the same packing as `vals` without the kind byte, so it is
     always non-negative. *)
  type t = { arr : ia option array; len : int array }

  let create () = { arr = Array.make 24 None; len = Array.make 24 0 }

  let pack_loc ~seg ~off =
    if seg < 0 || seg > max_seg then invalid_arg "E4_index.By_kind: segment out of range";
    if off < 0 || off > max_off then invalid_arg "E4_index.By_kind: offset out of range";
    (seg lsl off_bits) lor off

  let ensure t b need =
    match t.arr.(b) with
    | Some a when Bigarray.Array1.dim a >= need -> a
    | prev ->
      let cap = ref (match prev with Some a -> Bigarray.Array1.dim a | None -> 0) in
      if !cap = 0 then cap := 16;
      while !cap < need do
        cap := !cap * 2
      done;
      let a = Bigarray.Array1.create Bigarray.int Bigarray.c_layout !cap in
      Bigarray.Array1.fill a 0;
      (match prev with
      | Some old -> Bigarray.Array1.blit old (Bigarray.Array1.sub a 0 (Bigarray.Array1.dim old))
      | None -> ());
      t.arr.(b) <- Some a;
      a

  let add t k ~seg ~off =
    let b = E4_kind.byte k in
    let n = t.len.(b) in
    let a = ensure t b (n + 1) in
    Bigarray.Array1.unsafe_set a n (pack_loc ~seg ~off);
    t.len.(b) <- n + 1

  let find t k =
    let b = E4_kind.byte k in
    match t.arr.(b) with
    | None -> []
    | Some a ->
      let acc = ref [] in
      for i = t.len.(b) - 1 downto 0 do
        let v = Bigarray.Array1.unsafe_get a i in
        acc := (v lsr off_bits, v land max_off) :: !acc
      done;
      !acc

  let count t k = t.len.(E4_kind.byte k)
  let cardinal t = Array.fold_left ( + ) 0 t.len

  let kinds t =
    List.filter (fun k -> t.len.(E4_kind.byte k) > 0) E4_kind.all

  let bytes t =
    Array.fold_left
      (fun acc a -> match a with None -> acc | Some x -> acc + (Bigarray.Array1.dim x * 8))
      0 t.arr

  let of_index (ix : index) =
    let t = create () in
    iter ix (fun _ e -> add t e.kind ~seg:e.seg ~off:e.off);
    t

  let rebuild ?(kind_at = kind_at_default) rd ~from =
    let t = create () in
    let stop =
      E4_pack.scan rd ~from ~f:(fun _addr seg off _len ->
          match kind_at rd ~seg ~off with Some k -> add t k ~seg ~off | None -> ())
    in
    (t, stop)
end

(* ============================================================ 7. the dependents index *)

module Deps = struct
  module M = Map.Make (String)
  module RS = Set.Make (E4_addr.Ref)

  (* dependee digest bytes -> (the referring Refs newest first, the SAME Refs as a set).
     The list is the answer `find` and `iter` owe (discovery order is part of what DP1
     claims); the set is only the idempotence test of `add`.

     Lane P7 finding F1 (2026-09-08-engine-lane-p7-delivery.md §5): the test used to be
     `List.exists` over the whole dependent list, so a HUB dependee -- the schema every
     node's spec names -- made `add` O(k) and the build Theta(n^2): 279 k nodes/s at 1e3,
     31 k at 1e4, 6.1 k at 5e4.  `RS.mem` is O(log k) and the fall is gone (the numbers are
     in the lane W receipt).  Nothing observable moved: `find`, `iter`, `cardinal` and
     `edges` answer exactly what they answered before, because the set is a projection of
     the list and never a second source of truth. *)
  type t = { m : (E4_addr.Ref.t list * RS.t) M.t; e : int }

  let empty = { m = M.empty; e = 0 }
  let cardinal t = M.cardinal t.m
  let edges t = t.e

  let add t ~dep ~by =
    let k = E4_addr.Addr.bytes dep in
    match M.find_opt k t.m with
    | None -> { m = M.add k ([ by ], RS.singleton by) t.m; e = t.e + 1 }
    | Some (l, s) ->
      if RS.mem by s then t else { m = M.add k (by :: l, RS.add by s) t.m; e = t.e + 1 }

  let of_node ~fields (n : E4_node.t) =
    let refs = List.map (fun (r : E4_addr.Ref.t) -> r.E4_addr.Ref.addr) (E4_node.checked_edges n) in
    let cids = E4_shape.cids_of fields n.E4_node.kind ~payload:n.E4_node.payload in
    refs @ cids

  let add_node t ~fields ~at (n : E4_node.t) =
    let by = E4_addr.Ref.make n.E4_node.kind at in
    List.fold_left (fun acc dep -> add acc ~dep ~by) t (of_node ~fields n)

  let find t dep =
    match M.find_opt (E4_addr.Addr.bytes dep) t.m with Some (l, _) -> List.rev l | None -> []

  let mem t dep = M.mem (E4_addr.Addr.bytes dep) t.m

  let iter t f =
    M.iter (fun k (l, _) -> f (E4_addr.Addr.of_digest k) (List.rev l)) t.m

  let rebuild ?(fields = E4_shape.table) rd ~from =
    let acc = ref empty in
    let stop =
      E4_pack.scan rd ~from ~f:(fun addr seg off _len ->
          match E4_pack.read_at rd ~seg ~off with
          | None -> ()
          | Some (_, b) -> (
            match E4_node.decode b with
            | Ok n -> acc := add_node !acc ~fields ~at:addr n
            | Error _ -> ()))
    in
    (!acc, stop)
end
