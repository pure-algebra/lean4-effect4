(* E4_pack — see e4_pack.mli for what this is and the behaviours it holds itself to.

   Layout of this file:
     1. the grammar constants and the small byte helpers
     2. `source`: "read n bytes at (seg, off)", implemented twice — over mmaps (the reader)
        and over a file descriptor (the writer's own recovery scan)
     3. `step_at`: one record, from a source; every scan in this file is a loop over it
     4. the reader
     5. the writer: the lock, staging, flush/sync, rotation, recovery, truncation *)

open Effect4_engine

(* ============================================================ 1. the grammar *)

let magic = "E4PACK\000"
let version = "00000001"
let head_length = 27
let record_tag = 'R'
let record_header_length = 41
let record_overhead = 45
let default_seg_max = 1 lsl 30

type seg = int
type off = int

exception Locked of string
exception Bad_pack of string

let pack_subdir dir = Filename.concat dir "pack"
let seg_name i = Printf.sprintf "%06d.pack" i
let seg_path ~dir seg = Filename.concat (pack_subdir dir) (seg_name seg)

(* A be64 whose top byte is >= 0x40 is at or above 2^62 and E4_be.read_be64 refuses it
   (amendment M9, PK5).  On this host `max_int = 2^62 - 1`, so no string the writer can hold
   reaches that bound: PK5 is a READ-side property, and `stage` guards only against a length
   that could not be framed at all. *)

let write_all fd s =
  let n = String.length s in
  let b = Bytes.unsafe_of_string s in
  let rec go o = if o < n then go (o + Unix.write fd b o (n - o)) in
  go 0

let fsync_dir path =
  match Unix.openfile path [ Unix.O_RDONLY ] 0 with
  | fd ->
    (try Unix.fsync fd with Unix.Unix_error _ -> ());
    Unix.close fd
  | exception Unix.Unix_error _ -> ()

let mkdir_p path =
  let rec go p =
    if p <> "" && p <> "/" && p <> "." && not (Sys.file_exists p) then begin
      go (Filename.dirname p);
      try Unix.mkdir p 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
    end
  in
  go path

let file_size path =
  match Unix.LargeFile.stat path with
  | st -> Some (Int64.to_int st.Unix.LargeFile.st_size)
  | exception Unix.Unix_error _ -> None

let list_segments dir =
  let d = pack_subdir dir in
  match Sys.readdir d with
  | exception Sys_error _ -> []
  | names ->
    let ok n =
      String.length n = 11
      && Filename.check_suffix n ".pack"
      &&
      let good = ref true in
      String.iteri (fun i c -> if i < 6 && not (c >= '0' && c <= '9') then good := false) n;
      !good
    in
    let idx = List.filter_map
        (fun n -> if ok n then int_of_string_opt (String.sub n 0 6) else None)
        (Array.to_list names)
    in
    List.sort compare idx

(* The 27 head bytes of a segment. *)
let head_bytes seg_index =
  let b = Buffer.create head_length in
  Buffer.add_string b magic;
  Buffer.add_string b version;
  Buffer.add_string b (E4_be.be64 seg_index);
  let crc = E4_crc.string (Buffer.contents b) in
  Buffer.add_string b (E4_crc.be32 crc);
  Buffer.contents b

(* One record, straight into a staging buffer: no per-record intermediate string, and the
   crc is folded over the four pieces in place. *)
let add_record buf ~digest ~node_bytes =
  let len = String.length node_bytes in
  let be = E4_be.be64 len in
  Buffer.add_char buf record_tag;
  Buffer.add_string buf be;
  Buffer.add_string buf digest;
  Buffer.add_string buf node_bytes;
  let c = E4_crc.update_char E4_crc.init record_tag in
  let c = E4_crc.update c be in
  let c = E4_crc.update c digest in
  let c = E4_crc.update c node_bytes in
  Buffer.add_string buf (E4_crc.be32 c)

let record_crc ~header ~node_bytes =
  (* [header] is the 41 header bytes. *)
  let c = E4_crc.update_char E4_crc.init record_tag in
  let c = E4_crc.update_sub c header 1 (record_header_length - 1) in
  E4_crc.update c node_bytes

(* ============================================================ 2. sources *)

type source = {
  src_size : seg -> int option;      (* None: no such segment *)
  src_refresh : seg -> int option;   (* re-stat and re-map; the fresh size *)
  src_read : seg -> off -> int -> string option;
}

let check_head src seg =
  match src.src_read seg 0 head_length with
  | None -> Error "the segment is shorter than its 27-byte head"
  | Some h ->
    if String.sub h 0 7 <> magic then Error "bad magic"
    else if String.sub h 7 8 <> version then
      Error (Printf.sprintf "pack version %S, this binary knows %S" (String.sub h 7 8) version)
    else
      let want = E4_crc.sub h 0 23 in
      (match (E4_be.read_be64 h 15, E4_crc.read_be32 h 23) with
       | Some i, Some c when c = want && i = seg -> Ok ()
       | Some i, Some c when c = want ->
         Error (Printf.sprintf "head says segment %d, the file is %d" i seg)
       | Some _, Some _ -> Error "head crc"
       | _ -> Error "short head")

(* ============================================================ 3. one record *)

type scan_stop =
  | Eof
  | Short of { seg : seg; off : off }
  | Bad_crc of { seg : seg; off : off }
  | Bad_digest of { seg : seg; off : off }
  | Host_limit of { seg : seg; off : off }
  | Bad_tag of { seg : seg; off : off; byte : int }
  | Bad_head of { seg : seg }

let scan_stop_to_string = function
  | Eof -> "Eof"
  | Short { seg; off } -> Printf.sprintf "Short(seg=%d,off=%d)" seg off
  | Bad_crc { seg; off } -> Printf.sprintf "Bad_crc(seg=%d,off=%d)" seg off
  | Bad_digest { seg; off } -> Printf.sprintf "Bad_digest(seg=%d,off=%d)" seg off
  | Host_limit { seg; off } -> Printf.sprintf "Host_limit(seg=%d,off=%d)" seg off
  | Bad_tag { seg; off; byte } -> Printf.sprintf "Bad_tag(seg=%d,off=%d,byte=%d)" seg off byte
  | Bad_head { seg } -> Printf.sprintf "Bad_head(seg=%d)" seg

type record = {
  r_addr : E4_addr.Addr.t;
  r_len : int;
  r_bytes : string option;
}

type step =
  | S_record of record * (seg * off)
  | S_next_seg of seg
  | S_stop of scan_stop

(* The size a source reports is cached (a stat per record would cost more than the whole
   scan); when a bound is about to end the walk we refresh once and retry.  That is what
   makes a scan of a file the writer is still growing correct. *)
let rec step_at ?(retried = false) src ~verify seg off =
  let retry () = if retried then None else Some (step_at ~retried:true src ~verify seg off) in
  let short () = match retry () with Some s -> s | None -> S_stop (Short { seg; off }) in
  match src.src_size seg with
  | None -> S_stop Eof
  | Some size ->
    if off > size then short ()
    else if off = size then
      (* the clean end of this segment — unless the writer grew it since we mapped it *)
      (if retried then S_next_seg (seg + 1)
       else
         match src.src_refresh seg with
         | Some n when n > size -> step_at ~retried:true src ~verify seg off
         | _ -> S_next_seg (seg + 1))
    else if off + record_overhead > size then short ()
    else (
      match src.src_read seg off record_header_length with
      | None -> short ()
      | Some h ->
        if h.[0] <> record_tag then S_stop (Bad_tag { seg; off; byte = Char.code h.[0] })
        else (
          match E4_be.read_be64 h 1 with
          | None -> S_stop (Host_limit { seg; off })
          | Some len ->
            let total = record_overhead + len in
            if off + total > size then short ()
            else
              let addr = E4_addr.Addr.of_digest (String.sub h 9 32) in
              let next = (seg, off + total) in
              if not verify then S_record ({ r_addr = addr; r_len = len; r_bytes = None }, next)
              else (
                match src.src_read seg (off + record_header_length) (len + 4) with
                | None -> short ()
                | Some tail ->
                  let body = String.sub tail 0 len in
                  let want = record_crc ~header:h ~node_bytes:body in
                  (match E4_crc.read_be32 tail len with
                   | None -> short ()
                   | Some stored ->
                     if stored <> want then S_stop (Bad_crc { seg; off })
                     else if E4_sha256.digest body <> E4_addr.Addr.bytes addr then
                       S_stop (Bad_digest { seg; off })
                     else
                       S_record
                         ({ r_addr = addr; r_len = len; r_bytes = Some body }, next)))))

(* Where the next segment's records begin, or the verdict that ends the walk. *)
let seg_start src s =
  match src.src_size s with
  | None -> Error Eof
  | Some size ->
    if size < head_length then Error (Bad_head { seg = s })
    else (
      match check_head src s with
      | Error _ -> Error (Bad_head { seg = s })
      | Ok () -> Ok (s, head_length))

(* The one walk.  [f] sees every admitted record; the result is the verdict and the position
   after the last admitted record. *)
let walk src ~verify ~from ~f =
  let last = ref from in
  let rec go (seg, off) =
    match step_at src ~verify seg off with
    | S_stop stop -> stop
    | S_next_seg s -> (
      match seg_start src s with
      | Error stop -> stop
      | Ok p ->
        last := p;
        go p)
    | S_record (r, next) ->
      f (seg, off) r;
      last := next;
      go next
  in
  let stop = go from in
  (stop, !last)

(* ============================================================ 4. the reader *)

type bigstring = (char, Bigarray.int8_unsigned_elt, Bigarray.c_layout) Bigarray.Array1.t

type rseg = {
  rs_fd : Unix.file_descr;
  mutable rs_map : bigstring option;
  mutable rs_len : int;
}

type reader = {
  rd_dir : string;
  rd_segs : (seg, rseg option) Hashtbl.t;
  mutable rd_closed : bool;
}

let map_of fd len =
  if len <= 0 then None
  else
    match
      Bigarray.array1_of_genarray
        (Unix.map_file fd Bigarray.char Bigarray.c_layout false [| len |])
    with
    | m -> Some m
    | exception Unix.Unix_error _ -> None

let rseg_remap rs len =
  rs.rs_map <- map_of rs.rs_fd len;
  rs.rs_len <- (match rs.rs_map with Some _ -> len | None -> 0);
  rs.rs_len

(* Absence is never cached: a segment the writer rotates into must become visible without
   reopening the reader.  A missing segment costs one failed openfile, once per scan end. *)
let reader_seg rd s =
  match Hashtbl.find_opt rd.rd_segs s with
  | Some (Some rs) -> Some rs
  | Some None | None -> (
    let path = seg_path ~dir:rd.rd_dir s in
    match Unix.openfile path [ Unix.O_RDONLY ] 0 with
    | exception Unix.Unix_error _ ->
      Hashtbl.replace rd.rd_segs s None;
      None
    | fd ->
      let len = match file_size path with Some n -> n | None -> 0 in
      let rs = { rs_fd = fd; rs_map = None; rs_len = 0 } in
      ignore (rseg_remap rs len);
      Hashtbl.replace rd.rd_segs s (Some rs);
      Some rs)

let reader_source rd =
  let size s = match reader_seg rd s with Some rs -> Some rs.rs_len | None -> None in
  let refresh s =
    match reader_seg rd s with
    | None -> None
    | Some rs -> (
      match file_size (seg_path ~dir:rd.rd_dir s) with
      | None -> Some rs.rs_len
      | Some n -> if n = rs.rs_len then Some n else Some (rseg_remap rs n))
  in
  let read s o n =
    match reader_seg rd s with
    | None -> None
    | Some rs -> (
      match rs.rs_map with
      | None -> None
      | Some m ->
        if o < 0 || n < 0 || o + n > rs.rs_len then None
        else
          let b = Bytes.create n in
          for i = 0 to n - 1 do
            Bytes.unsafe_set b i (Bigarray.Array1.unsafe_get m (o + i))
          done;
          Some (Bytes.unsafe_to_string b))
  in
  { src_size = size; src_refresh = refresh; src_read = read }

let open_reader ~dir =
  { rd_dir = dir; rd_segs = Hashtbl.create 8; rd_closed = false }

let close_reader rd =
  if not rd.rd_closed then begin
    Hashtbl.iter
      (fun _ v -> match v with Some rs -> (try Unix.close rs.rs_fd with Unix.Unix_error _ -> ()) | None -> ())
      rd.rd_segs;
    Hashtbl.reset rd.rd_segs;
    rd.rd_closed <- true
  end

let segments rd = list_segments rd.rd_dir

(* ---- the four reads ---- *)

type refusal =
  | No_segment of seg
  | Past_end of { seg : seg; off : off; size : int }
  | Not_a_record of { seg : seg; off : off; byte : int }
  | Truncated of { seg : seg; off : off }
  | Over_host_limit of { seg : seg; off : off }
  | Crc_mismatch of { seg : seg; off : off; crc_recorded : int; crc_computed : int }
  | Digest_mismatch of { seg : seg; off : off; dig_recorded : string; dig_computed : string }

let hex = E4_hex.of_bytes

let refusal_to_string = function
  | No_segment s -> Printf.sprintf "No_segment(%d)" s
  | Past_end { seg; off; size } -> Printf.sprintf "Past_end(seg=%d,off=%d,size=%d)" seg off size
  | Not_a_record { seg; off; byte } ->
    Printf.sprintf "Not_a_record(seg=%d,off=%d,byte=%d)" seg off byte
  | Truncated { seg; off } -> Printf.sprintf "Truncated(seg=%d,off=%d)" seg off
  | Over_host_limit { seg; off } -> Printf.sprintf "Over_host_limit(seg=%d,off=%d)" seg off
  | Crc_mismatch { seg; off; crc_recorded; crc_computed } ->
    Printf.sprintf "Crc_mismatch(seg=%d,off=%d,recorded=%08x,computed=%08x)" seg off
      crc_recorded crc_computed
  | Digest_mismatch { seg; off; dig_recorded; dig_computed } ->
    Printf.sprintf "Digest_mismatch(seg=%d,off=%d,recorded=%s,computed=%s)" seg off
      (hex dig_recorded) (hex dig_computed)

(* The whole record, with every check named.  [verify] decides whether the digest is
   recomputed; the CRC and the length are always checked. *)
let read_full src ~verify seg off =
  match src.src_size seg with
  | None -> Error (No_segment seg)
  | Some size0 ->
    let size = if off + record_overhead > size0 then
        (match src.src_refresh seg with Some n -> n | None -> size0)
      else size0
    in
    if off < 0 || off >= size then Error (Past_end { seg; off; size })
    else if off + record_overhead > size then Error (Truncated { seg; off })
    else (
      match src.src_read seg off record_header_length with
      | None -> Error (Truncated { seg; off })
      | Some h ->
        if h.[0] <> record_tag then Error (Not_a_record { seg; off; byte = Char.code h.[0] })
        else (
          match E4_be.read_be64 h 1 with
          | None -> Error (Over_host_limit { seg; off })
          | Some len ->
            if off + record_overhead + len > size then Error (Truncated { seg; off })
            else (
              match src.src_read seg (off + record_header_length) (len + 4) with
              | None -> Error (Truncated { seg; off })
              | Some tail ->
                let body = String.sub tail 0 len in
                let want = record_crc ~header:h ~node_bytes:body in
                (match E4_crc.read_be32 tail len with
                 | None -> Error (Truncated { seg; off })
                 | Some stored ->
                   if stored <> want then
                     Error
                       (Crc_mismatch { seg; off; crc_recorded = stored; crc_computed = want })
                   else
                     let recorded = String.sub h 9 32 in
                     if verify then (
                       let computed = E4_sha256.digest body in
                       if computed <> recorded then
                         Error
                           (Digest_mismatch
                              { seg; off; dig_recorded = recorded; dig_computed = computed })
                       else
                         Ok
                           { r_addr = E4_addr.Addr.of_digest recorded;
                             r_len = len;
                             r_bytes = Some body })
                     else
                       Ok
                         { r_addr = E4_addr.Addr.of_digest recorded;
                           r_len = len;
                           r_bytes = Some body }))))

let read rd ~seg ~off = read_full (reader_source rd) ~verify:true seg off

let read_at rd ~seg ~off =
  match read_full (reader_source rd) ~verify:false seg off with
  | Ok { r_addr; r_bytes = Some b; _ } -> Some (r_addr, b)
  | Ok _ | Error _ -> None

let read_header rd ~seg ~off =
  let src = reader_source rd in
  match step_at src ~verify:false seg off with
  | S_record (r, _) -> Some (r.r_addr, r.r_len)
  | S_next_seg _ | S_stop _ -> None

let blit_at rd ~seg ~off buf pos =
  match read_at rd ~seg ~off with
  | None -> -1
  | Some (_, b) ->
    let n = String.length b in
    if pos < 0 || pos + n > Bytes.length buf then
      invalid_arg "E4_pack.blit_at: the buffer is too small";
    Bytes.blit_string b 0 buf pos n;
    n

(* ---- the two scans ---- *)

let scan ?(verify = false) rd ~from ~f =
  let src = reader_source rd in
  let stop, _ = walk src ~verify ~from ~f:(fun (s, o) r -> f r.r_addr s o r.r_len) in
  stop

type scanned =
  | Scanned of (seg * off) * record
  | Stopped of scan_stop

let scan_seq ?(verify = false) rd ~from =
  let src = reader_source rd in
  let rec go (seg, off) () =
    match step_at src ~verify seg off with
    | S_stop stop -> Seq.Cons (Stopped stop, Seq.empty)
    | S_next_seg s -> (
      match seg_start src s with
      | Error stop -> Seq.Cons (Stopped stop, Seq.empty)
      | Ok p -> go p ())
    | S_record (r, next) -> Seq.Cons (Scanned ((seg, off), r), go next)
  in
  go from

(* ============================================================ 5. the writer *)

(* One staged run of bytes destined for one segment, starting at p_start in that segment. *)
type pending = { p_seg : seg; p_start : off; p_buf : Buffer.t }

type recovery = {
  from : seg * off;
  stop : scan_stop;
  records : int;
  ends_at : seg * off;
  truncated : bool;
  verified : bool;
}

type t = {
  w_dir : string;
  w_seg_max : int;
  w_lock_fd : Unix.file_descr;
  w_lock_key : string;
  mutable w_fds : (seg * Unix.file_descr) list;
  mutable w_pend : pending list;          (* newest first *)
  mutable w_cur_seg : seg;
  mutable w_cur_end : off;                (* the staged end within w_cur_seg *)
  mutable w_written : seg * off;
  mutable w_durable : seg * off;
  mutable w_staged : int;                 (* bytes buffered *)
  mutable w_staged_n : int;               (* records buffered *)
  mutable w_dirty : seg list;             (* written since the last fsync *)
  mutable w_closed : bool;
  w_recovery : recovery;
}

(* PK6: an in-process registry beside the fcntl lock.  Unix.lockf is per-PROCESS, so it does
   not refuse a second open_ in this one; the table does. *)
let held : (string, unit) Hashtbl.t = Hashtbl.create 8

let acquire_lock dir =
  let key = try Unix.realpath dir with Unix.Unix_error _ | Sys_error _ -> dir in
  if Hashtbl.mem held key then raise (Locked key);
  let path = Filename.concat dir "LOCK" in
  let fd = Unix.openfile path [ Unix.O_RDWR; Unix.O_CREAT ] 0o600 in
  (try Unix.lockf fd Unix.F_TLOCK 0
   with Unix.Unix_error _ ->
     (try Unix.close fd with Unix.Unix_error _ -> ());
     raise (Locked key));
  Hashtbl.replace held key ();
  (fd, key)

let release_lock t =
  (try Unix.lockf t.w_lock_fd Unix.F_ULOCK 0 with Unix.Unix_error _ -> ());
  (try Unix.close t.w_lock_fd with Unix.Unix_error _ -> ());
  Hashtbl.remove held t.w_lock_key

let fd_for t s =
  match List.assoc_opt s t.w_fds with
  | Some fd -> fd
  | None ->
    let fd = Unix.openfile (seg_path ~dir:t.w_dir s) [ Unix.O_RDWR ] 0o600 in
    t.w_fds <- (s, fd) :: t.w_fds;
    fd

(* The writer's own source: positioned reads through its file descriptors.  Used only by
   recovery at open, so a stat per size call is free. *)
let writer_source dir =
  let fds : (seg, Unix.file_descr option) Hashtbl.t = Hashtbl.create 4 in
  let get s =
    match Hashtbl.find_opt fds s with
    | Some v -> v
    | None ->
      let v =
        match Unix.openfile (seg_path ~dir s) [ Unix.O_RDONLY ] 0 with
        | fd -> Some fd
        | exception Unix.Unix_error _ -> None
      in
      Hashtbl.replace fds s v;
      v
  in
  let size s = match get s with None -> None | Some _ -> file_size (seg_path ~dir s) in
  let read s o n =
    match get s with
    | None -> None
    | Some fd ->
      let b = Bytes.create n in
      ignore (Unix.LargeFile.lseek fd (Int64.of_int o) Unix.SEEK_SET);
      let rec go got =
        if got = n then Some (Bytes.unsafe_to_string b)
        else
          match Unix.read fd b got (n - got) with
          | 0 -> None
          | r -> go (got + r)
          | exception Unix.Unix_error _ -> None
      in
      go 0
  in
  let close () =
    Hashtbl.iter (fun _ v -> match v with Some fd -> (try Unix.close fd with Unix.Unix_error _ -> ()) | None -> ()) fds
  in
  ({ src_size = size; src_refresh = size; src_read = read }, close)

let create_segment ~dir s =
  let path = seg_path ~dir s in
  let fd = Unix.openfile path [ Unix.O_RDWR; Unix.O_CREAT; Unix.O_TRUNC ] 0o600 in
  write_all fd (head_bytes s);
  Unix.fsync fd;
  fsync_dir (pack_subdir dir);
  fd

let open_at ?from ?(verify = true) ?(truncate = true) ~dir ~seg_max () =
  if seg_max <= head_length + record_overhead then
    invalid_arg "E4_pack.open_: seg_max is smaller than one record";
  mkdir_p dir;
  mkdir_p (pack_subdir dir);
  let lock_fd, lock_key = acquire_lock dir in
  let finish_with r cur_seg cur_end fds =
    { w_dir = dir;
      w_seg_max = seg_max;
      w_lock_fd = lock_fd;
      w_lock_key = lock_key;
      w_fds = fds;
      w_pend = [];
      w_cur_seg = cur_seg;
      w_cur_end = cur_end;
      w_written = (cur_seg, cur_end);
      w_durable = (cur_seg, cur_end);
      w_staged = 0;
      w_staged_n = 0;
      w_dirty = [];
      w_closed = false;
      w_recovery = r }
  in
  match list_segments dir with
  | [] ->
    let fd = create_segment ~dir 0 in
    finish_with
      { from = (0, head_length);
        stop = Eof;
        records = 0;
        ends_at = (0, head_length);
        truncated = false;
        verified = verify }
      0 head_length
      [ (0, fd) ]
  | segs0 ->
    (* A crash inside `create_segment` can leave a trailing file with no head.  It carries no
       record, so with [truncate] it is removed rather than called corruption. *)
    let segs =
      if not truncate then segs0
      else
        let rec drop l =
          match List.rev l with
          | s :: rest
            when (match file_size (seg_path ~dir s) with
                  | Some n -> n < head_length
                  | None -> true)
                 && rest <> [] ->
            (try Sys.remove (seg_path ~dir s) with Sys_error _ -> ());
            drop (List.rev rest)
          | _ -> l
        in
        drop segs0
    in
    let last = List.fold_left max 0 segs in
    let src, close_src = writer_source dir in
    (match check_head src last with
     | Error why ->
       close_src ();
       (try Unix.lockf lock_fd Unix.F_ULOCK 0 with Unix.Unix_error _ -> ());
       (try Unix.close lock_fd with Unix.Unix_error _ -> ());
       Hashtbl.remove held lock_key;
       raise (Bad_pack (Printf.sprintf "%s: %s" (seg_path ~dir last) why))
     | Ok () -> ());
    let start = match from with Some p -> p | None -> (last, head_length) in
    let n = ref 0 in
    let stop, ends_at = walk src ~verify ~from:start ~f:(fun _ _ -> incr n) in
    close_src ();
    (* A torn or corrupt RECORD is truncated away (PK3, crash family X1); a segment whose
       27-byte head does not check is not: there is no offset inside it that recovery
       reached, and deleting it would destroy bytes nobody has diagnosed.  It is reported
       and left for lane P4. *)
    let cut = match stop with Eof | Bad_head _ -> false | _ -> true in
    let did_truncate = ref false in
    let cseg, coff = ends_at in
    let fds = ref [] in
    if truncate && cut then begin
      (* PK3: the torn tail becomes the file's end, and every later segment goes. *)
      let fd = Unix.openfile (seg_path ~dir cseg) [ Unix.O_RDWR ] 0o600 in
      (match file_size (seg_path ~dir cseg) with
       | Some sz when sz > coff ->
         Unix.LargeFile.ftruncate fd (Int64.of_int coff);
         Unix.fsync fd;
         did_truncate := true
       | _ -> ());
      fds := [ (cseg, fd) ];
      List.iter
        (fun s ->
          if s > cseg then begin
            (try Sys.remove (seg_path ~dir s) with Sys_error _ -> ());
            did_truncate := true
          end)
        segs;
      if !did_truncate then fsync_dir (pack_subdir dir)
    end;
    finish_with
      { from = start;
        stop;
        records = !n;
        ends_at;
        truncated = !did_truncate;
        verified = verify }
      cseg coff !fds

let open_ ~dir ~seg_max = open_at ~dir ~seg_max ()

let dir t = t.w_dir
let seg_max t = t.w_seg_max
let pack_end t = t.w_durable
let durable_upto t = t.w_durable
let written_upto t = t.w_written
let staged_end t = (t.w_cur_seg, t.w_cur_end)
let staged_bytes t = t.w_staged
let staged_count t = t.w_staged_n
let recovery t = t.w_recovery

let ensure_pending t =
  match t.w_pend with
  | p :: _ when p.p_seg = t.w_cur_seg -> p
  | _ ->
    let p = { p_seg = t.w_cur_seg; p_start = t.w_cur_end; p_buf = Buffer.create 65536 } in
    t.w_pend <- p :: t.w_pend;
    p

(* PK8.  The new segment's 27-byte head is written and fsynced HERE, not staged: a segment
   file that exists but carries no head is indistinguishable at open from a corrupt one, and
   a rotation is rare enough (once per seg_max) that its fsync is not on any hot path. *)
let rotate t =
  let s = t.w_cur_seg + 1 in
  let fd = create_segment ~dir:t.w_dir s in
  t.w_fds <- (s, fd) :: t.w_fds;
  t.w_cur_seg <- s;
  t.w_cur_end <- head_length;
  let p = { p_seg = s; p_start = head_length; p_buf = Buffer.create 65536 } in
  t.w_pend <- p :: t.w_pend;
  p

let stage t ~addr ~node_bytes =
  if t.w_closed then invalid_arg "E4_pack.stage: the writer is closed";
  let len = String.length node_bytes in
  if len < 0 || len > max_int - record_overhead then
    invalid_arg "E4_pack.stage: node_len cannot be framed on this host (M9)";
  let total = record_overhead + len in
  let p = ensure_pending t in
  let p =
    if t.w_cur_end > head_length && t.w_cur_end + total > t.w_seg_max then rotate t else p
  in
  let off = t.w_cur_end in
  add_record p.p_buf ~digest:(E4_addr.Addr.bytes addr) ~node_bytes;
  t.w_cur_end <- off + total;
  t.w_staged <- t.w_staged + total;
  t.w_staged_n <- t.w_staged_n + 1;
  (t.w_cur_seg, off)

let append t ~digest ~node_bytes =
  if String.length digest <> 32 then
    invalid_arg "E4_pack.append: the digest is not 32 bytes";
  stage t ~addr:(E4_addr.Addr.of_digest digest) ~node_bytes

let flush t =
  if t.w_closed then invalid_arg "E4_pack.flush: the writer is closed";
  if t.w_pend <> [] then begin
    List.iter
      (fun p ->
        let n = Buffer.length p.p_buf in
        if n > 0 then begin
          let fd = fd_for t p.p_seg in
          ignore (Unix.LargeFile.lseek fd (Int64.of_int p.p_start) Unix.SEEK_SET);
          write_all fd (Buffer.contents p.p_buf);
          if not (List.mem p.p_seg t.w_dirty) then t.w_dirty <- p.p_seg :: t.w_dirty;
          t.w_written <- (p.p_seg, p.p_start + n)
        end)
      (List.rev t.w_pend);
    t.w_pend <- [];
    t.w_staged <- 0;
    t.w_staged_n <- 0
  end

let sync t =
  flush t;
  if t.w_dirty <> [] then begin
    List.iter (fun s -> Unix.fsync (fd_for t s)) (List.sort compare t.w_dirty);
    t.w_dirty <- []
  end;
  t.w_durable <- t.w_written

let commit = sync

let truncate_to t ~seg ~off =
  if t.w_closed then invalid_arg "E4_pack.truncate_to: the writer is closed";
  if t.w_staged > 0 then invalid_arg "E4_pack.truncate_to: bytes are staged";
  let dseg, doff = t.w_durable in
  if seg < dseg || (seg = dseg && off < doff) then
    invalid_arg
      (Printf.sprintf "E4_pack.truncate_to: (%d,%d) is below pack_end (%d,%d)" seg off dseg doff);
  let fd = fd_for t seg in
  Unix.LargeFile.ftruncate fd (Int64.of_int off);
  Unix.fsync fd;
  let removed = ref false in
  List.iter
    (fun s ->
      if s > seg then begin
        (match List.assoc_opt s t.w_fds with
         | Some f -> (try Unix.close f with Unix.Unix_error _ -> ())
         | None -> ());
        t.w_fds <- List.filter (fun (x, _) -> x <> s) t.w_fds;
        (try Sys.remove (seg_path ~dir:t.w_dir s) with Sys_error _ -> ());
        removed := true
      end)
    (list_segments t.w_dir);
  if !removed then fsync_dir (pack_subdir t.w_dir);
  t.w_cur_seg <- seg;
  t.w_cur_end <- off;
  t.w_written <- (seg, off);
  t.w_durable <- (seg, off);
  t.w_dirty <- []

let close t =
  if not t.w_closed then begin
    (try sync t with Unix.Unix_error _ -> ());
    List.iter (fun (_, fd) -> try Unix.close fd with Unix.Unix_error _ -> ()) t.w_fds;
    t.w_fds <- [];
    release_lock t;
    t.w_closed <- true
  end
