(* E4_wal — implementation.  The interface, the grammar and the deviations are in
   e4_wal.mli; this file adds only what a reader of the code needs.

   Shape: one grammar section (encode / decode of the head and of a row), one walker over the
   bytes of a single segment used by BOTH the reader and the writer's recovery, then the
   writer and the reader over it.  The walker is the only place that decides what damage is,
   so `replay`, `end_index` and `open_`'s recovery cannot drift apart. *)

open Effect4_engine

(* ---------------------------------------------------------------- the grammar *)

let magic = "E4LOG\000"
let version = "00000001"
let head_prefix_length = 30 (* magic 6 + version 8 + job_lo 8 + first 8 *)
let head_length = 34 (* + be32 head_crc *)
let row_header_length = 8 (* be32 row_len + be32 row_crc *)
let body_header_length = 9 (* row_tag + be64 index *)
let row_max = 1 lsl 20
let default_seg_max = 64 * 1024 * 1024
let min_seg_max = head_length + row_header_length + body_header_length

let tag_decision = 1
let tag_event = 2
let tag_checkpoint = 3
let tag_seal = 4

type seq = int

type row =
  | Decision of string
  | Event of string
  | Checkpoint_mark of { position : seq; addr : E4_addr.Addr.t option }
  | Seal of { next_first_seq : seq }

exception Locked of string
exception Row_too_large of int

let segment_name i = Printf.sprintf "%016x.seg" i

let job_dir ~dir ~job =
  Filename.concat (Filename.concat dir "log") (E4_addr.Addr.hex job)

(* The LAST eight bytes of the address, as raw bytes (deviation D3: never a be64 number). *)
let job_lo job =
  let b = E4_addr.Addr.bytes job in
  String.sub b (String.length b - 8) 8

let encode_head ~job ~first =
  let p = magic ^ version ^ job_lo job ^ E4_be.be64 first in
  p ^ E4_crc.be32 (E4_crc.string p)

(* (job_lo, first_index) of a well-formed head, or None. *)
let decode_head s =
  if String.length s < head_length then None
  else
    let p = String.sub s 0 head_prefix_length in
    match E4_crc.read_be32 s head_prefix_length with
    | None -> None
    | Some c ->
      if c <> E4_crc.string p then None
      else if String.sub p 0 6 <> magic then None
      else if String.sub p 6 8 <> version then None
      else (
        match E4_be.read_be64 p 22 with
        | None -> None
        | Some first -> Some (String.sub p 14 8, first))

let body_of_row ~index row =
  let tag, payload =
    match row with
    | Decision s -> (tag_decision, s)
    | Event s -> (tag_event, s)
    | Checkpoint_mark { position; addr } ->
      ( tag_checkpoint,
        E4_be.be64 position
        ^ (match addr with
           | None -> "\000"
           | Some a -> "\001" ^ E4_addr.Addr.bytes a) )
    | Seal { next_first_seq } -> (tag_seal, E4_be.be64 next_first_seq)
  in
  String.concat "" [ String.make 1 (Char.chr tag); E4_be.be64 index; payload ]

let frame_row body =
  E4_crc.be32 (String.length body) ^ E4_crc.be32 (E4_crc.string body) ^ body

let decode_body body =
  let n = String.length body in
  if n < body_header_length then None
  else
    match E4_be.read_be64 body 1 with
    | None -> None
    | Some index -> (
      let payload = String.sub body body_header_length (n - body_header_length) in
      let pn = String.length payload in
      match Char.code body.[0] with
      | 1 -> Some (index, Decision payload)
      | 2 -> Some (index, Event payload)
      | 3 -> (
        if pn < 9 then None
        else
          match E4_be.read_be64 payload 0 with
          | None -> None
          | Some position -> (
            match payload.[8] with
            | '\000' when pn = 9 ->
              Some (index, Checkpoint_mark { position; addr = None })
            | '\001' when pn = 9 + 32 ->
              let a = E4_addr.Addr.of_digest (String.sub payload 9 32) in
              Some (index, Checkpoint_mark { position; addr = Some a })
            | _ -> None))
      | 4 -> (
        if pn <> 8 then None
        else
          match E4_be.read_be64 payload 0 with
          | None -> None
          | Some next -> Some (index, Seal { next_first_seq = next }))
      | _ -> None)

(* ---------------------------------------------------------------- verdicts *)

type stop =
  | Eof
  | Short of seq
  | Bad_crc of seq
  | Bad_row of seq
  | Oversize of { at : seq; len : int }
  | Gap of { expected : seq; found : seq }
  | Bad_header of { path : string }
  | Wrong_job of { path : string }

let stop_to_string = function
  | Eof -> "eof: every stored row was delivered"
  | Short i -> Printf.sprintf "short: the row at index %d is cut off by the end of its segment" i
  | Bad_crc i -> Printf.sprintf "bad-crc: the row at index %d failed its checksum" i
  | Bad_row i -> Printf.sprintf "bad-row: the row at index %d is not a row (unknown tag or short body)" i
  | Oversize { at; len } ->
    Printf.sprintf "oversize: the row at index %d declares %d bytes, above row_max %d" at len row_max
  | Gap { expected; found } ->
    Printf.sprintf "gap: index %d is missing; the next stored row is %d" expected found
  | Bad_header { path } -> Printf.sprintf "bad-header: %s is not a segment of this log" path
  | Wrong_job { path } -> Printf.sprintf "wrong-job: %s belongs to another job" path

(* ---------------------------------------------------------------- files *)

let rec mkdir_p path =
  if path = "" || path = "." || Sys.file_exists path then ()
  else begin
    let parent = Filename.dirname path in
    if parent <> path then mkdir_p parent;
    try Unix.mkdir path 0o755 with Unix.Unix_error (Unix.EEXIST, _, _) -> ()
  end

let fsync_dir path =
  match Unix.openfile path [ Unix.O_RDONLY ] 0 with
  | exception Unix.Unix_error _ -> ()
  | fd ->
    (try Unix.fsync fd with Unix.Unix_error _ -> ());
    Unix.close fd

let read_file path =
  let ic = open_in_bin path in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> really_input_string ic (in_channel_length ic))

let rec write_all fd s pos len =
  if len > 0 then begin
    let n = Unix.write_substring fd s pos len in
    write_all fd s (pos + n) (len - n)
  end

let write_string fd s = write_all fd s 0 (String.length s)

let segment_files jd =
  let entries = try Sys.readdir jd with Sys_error _ -> [||] in
  let out = ref [] in
  Array.iter
    (fun e ->
      if Filename.check_suffix e ".seg" then begin
        let base = Filename.chop_suffix e ".seg" in
        if String.length base = 16 then
          match int_of_string_opt ("0x" ^ base) with
          | Some i when i >= 0 -> out := (i, Filename.concat jd e) :: !out
          | _ -> ()
      end)
    entries;
  List.sort (fun (a, _) (b, _) -> compare (a : int) b) !out

(* ---------------------------------------------------------------- the walker

   One segment's bytes, from its head to the first damage.  [f] is called for every DATA row
   whose index is at least [from]; a Seal is consumed and never delivered (D2). *)

type walk = {
  w_next : seq; (* the index after the last good data row *)
  w_end : int; (* the byte offset just past the last good row *)
  w_sealed : seq option; (* Some next_first_index when a Seal ended the segment *)
  w_stop : stop;
}

let walk_segment ~bytes ~path ~job ~from ~f =
  match decode_head bytes with
  | None -> { w_next = 0; w_end = 0; w_sealed = None; w_stop = Bad_header { path } }
  | Some (lo, first) ->
    if lo <> job_lo job then
      { w_next = first; w_end = 0; w_sealed = None; w_stop = Wrong_job { path } }
    else begin
      let n = String.length bytes in
      let pos = ref head_length in
      let index = ref first in
      let last_end = ref head_length in
      let sealed = ref None in
      let stop = ref Eof in
      let go = ref true in
      while !go do
        if !pos >= n then go := false
        else if n - !pos < row_header_length then begin
          stop := Short !index;
          go := false
        end
        else
          match (E4_crc.read_be32 bytes !pos, E4_crc.read_be32 bytes (!pos + 4)) with
          | Some len, Some crc ->
            if len > row_max then begin
              stop := Oversize { at = !index; len };
              go := false
            end
            else if n - !pos - row_header_length < len then begin
              stop := Short !index;
              go := false
            end
            else begin
              let body = String.sub bytes (!pos + row_header_length) len in
              if E4_crc.string body <> crc then begin
                stop := Bad_crc !index;
                go := false
              end
              else
                match decode_body body with
                | None ->
                  stop := Bad_row !index;
                  go := false
                | Some (bi, Seal { next_first_seq }) ->
                  if bi <> !index then begin
                    stop := Gap { expected = !index; found = bi };
                    go := false
                  end
                  else if next_first_seq <> !index then begin
                    stop := Gap { expected = !index; found = next_first_seq };
                    go := false
                  end
                  else begin
                    pos := !pos + row_header_length + len;
                    last_end := !pos;
                    sealed := Some next_first_seq;
                    go := false
                  end
                | Some (bi, r) ->
                  if bi <> !index then begin
                    stop := Gap { expected = !index; found = bi };
                    go := false
                  end
                  else begin
                    if bi >= from then f bi r;
                    pos := !pos + row_header_length + len;
                    last_end := !pos;
                    incr index
                  end
            end
          | _ ->
            stop := Short !index;
            go := false
      done;
      { w_next = !index; w_end = !last_end; w_sealed = !sealed; w_stop = !stop }
    end

(* ---------------------------------------------------------------- the reader *)

type reader = { r_dir : string; r_job : E4_addr.Addr.t }

let open_reader ~dir ~job = { r_dir = job_dir ~dir ~job; r_job = job }

let addr_of_hex_exn where h =
  match E4_addr.Addr.of_hex h with
  | Some a -> a
  | None -> invalid_arg (where ^ ": the job is not a 32-byte digest in hex")

let open_reader_job ~dir ~job =
  open_reader ~dir ~job:(addr_of_hex_exn "E4_wal.open_reader_job" job)

let close_reader (_ : reader) = ()
let segments r = segment_files r.r_dir

(* LG6: the last segment whose first index is at or below [from]. *)
let start_of arr from =
  let lo = ref 0 and hi = ref (Array.length arr - 1) and start = ref 0 in
  while !lo <= !hi do
    let mid = (!lo + !hi) / 2 in
    if fst arr.(mid) <= from then begin
      start := mid;
      lo := mid + 1
    end
    else hi := mid - 1
  done;
  !start

(* The one traversal: (the index one past the last good row, why it stopped). *)
let walk_from r ~from ~f =
  let arr = Array.of_list (segments r) in
  let n = Array.length arr in
  if n = 0 then (0, Eof)
  else begin
    let i = ref (start_of arr from) in
    let expected = ref (fst arr.(!i)) in
    let result = ref Eof in
    let go = ref true in
    while !go do
      if !i >= n then go := false
      else begin
        let first, path = arr.(!i) in
        if first <> !expected then begin
          result := Gap { expected = !expected; found = first };
          go := false
        end
        else begin
          let bytes = read_file path in
          let w = walk_segment ~bytes ~path ~job:r.r_job ~from ~f in
          expected := w.w_next;
          match w.w_stop with
          | Eof -> incr i
          | s ->
            result := s;
            go := false
        end
      end
    done;
    (!expected, !result)
  end

let replay r ~from ~f = snd (walk_from r ~from ~f)
let end_index r = walk_from r ~from:max_int ~f:(fun _ _ -> ())

let replay_seq r ~from ~verdict =
  let arr = Array.of_list (segments r) in
  let n = Array.length arr in
  let rec at i expected () =
    if i >= n then begin
      verdict := Eof;
      Seq.Nil
    end
    else begin
      let first, path = arr.(i) in
      if first <> expected then begin
        verdict := Gap { expected; found = first };
        Seq.Nil
      end
      else begin
        let acc = ref [] in
        let bytes = read_file path in
        let w =
          walk_segment ~bytes ~path ~job:r.r_job ~from ~f:(fun j row ->
              acc := (j, row) :: !acc)
        in
        let rows = List.to_seq (List.rev !acc) in
        match w.w_stop with
        | Eof -> Seq.append rows (at (i + 1) w.w_next) ()
        | s ->
          Seq.append rows (fun () ->
              verdict := s;
              Seq.Nil)
            ()
      end
    end
  in
  if n = 0 then
    (fun () ->
      verdict := Eof;
      Seq.Nil)
  else begin
    let s = start_of arr from in
    at s (fst arr.(s))
  end

exception Enough

let tape r ~from ~upto =
  let acc = ref [] in
  (try
     ignore
       (replay r ~from ~f:(fun i row ->
            if i >= upto then raise Enough
            else match row with Decision s -> acc := s :: !acc | _ -> ()))
   with Enough -> ());
  List.rev !acc

(* ---------------------------------------------------------------- the writer *)

type t = {
  w_dir : string;
  w_job : E4_addr.Addr.t;
  w_seg_max : int;
  mutable w_fd : Unix.file_descr;
  mutable w_seg_first : seq;
  mutable w_seg_bytes : int;
  mutable w_next : seq;
  mutable w_durable : seq;
  w_buf : Buffer.t;
  w_lock : Unix.file_descr;
  mutable w_closed : bool;
}

(* LG7: the in-process half of the single-writer discipline.  lockf(F_TLOCK) is a POSIX
   fcntl lock and does NOT conflict with another descriptor of the same process, so the
   claim table is what makes a second `open_` in one process raise. *)
let claims : (string, unit) Hashtbl.t = Hashtbl.create 8

let create_segment ~path ~job ~first =
  let fd = Unix.openfile path [ Unix.O_WRONLY; Unix.O_CREAT; Unix.O_APPEND ] 0o644 in
  write_string fd (encode_head ~job ~first);
  Unix.fsync fd;
  fd

let release_claim t =
  (try Unix.lockf t.w_lock Unix.F_ULOCK 0 with Unix.Unix_error _ -> ());
  (try Unix.close t.w_lock with Unix.Unix_error _ -> ());
  Hashtbl.remove claims t.w_dir

let open_ ~dir ~job ~seg_max =
  if seg_max < min_seg_max then
    invalid_arg
      (Printf.sprintf "E4_wal.open_: seg_max %d is below min_seg_max %d" seg_max min_seg_max);
  let jd = job_dir ~dir ~job in
  mkdir_p jd;
  if Hashtbl.mem claims jd then raise (Locked jd);
  let lock = Unix.openfile (Filename.concat jd "LOCK") [ Unix.O_RDWR; Unix.O_CREAT ] 0o644 in
  (try Unix.lockf lock Unix.F_TLOCK 0
   with Unix.Unix_error _ ->
     Unix.close lock;
     raise (Locked jd));
  Hashtbl.replace claims jd ();
  let fresh ~first =
    let path = Filename.concat jd (segment_name first) in
    let fd = create_segment ~path ~job ~first in
    fsync_dir jd;
    (fd, first, head_length, first)
  in
  let fd, seg_first, seg_bytes, next =
    match List.rev (segment_files jd) with
    | [] -> fresh ~first:0
    | (first, path) :: _ -> (
      let bytes = read_file path in
      let w = walk_segment ~bytes ~path ~job ~from:max_int ~f:(fun _ _ -> ()) in
      match w.w_stop with
      | Bad_header _ | Wrong_job _ | Gap _ ->
        (try Unix.lockf lock Unix.F_ULOCK 0 with Unix.Unix_error _ -> ());
        Unix.close lock;
        Hashtbl.remove claims jd;
        failwith ("E4_wal.open_: " ^ stop_to_string w.w_stop)
      | Eof | Short _ | Bad_crc _ | Bad_row _ | Oversize _ -> (
        match w.w_sealed with
        | Some first_of_next -> fresh ~first:first_of_next
        | None ->
          if w.w_end < String.length bytes then begin
            let tfd = Unix.openfile path [ Unix.O_WRONLY ] 0o644 in
            Unix.ftruncate tfd w.w_end;
            Unix.fsync tfd;
            Unix.close tfd
          end;
          let fd = Unix.openfile path [ Unix.O_WRONLY; Unix.O_APPEND ] 0o644 in
          (fd, first, w.w_end, w.w_next)))
  in
  {
    w_dir = jd;
    w_job = job;
    w_seg_max = seg_max;
    w_fd = fd;
    w_seg_first = seg_first;
    w_seg_bytes = seg_bytes;
    w_next = next;
    w_durable = next;
    w_buf = Buffer.create 65536;
    w_lock = lock;
    w_closed = false;
  }

let open_job ~dir ~job ~seg_max =
  open_ ~dir ~job:(addr_of_hex_exn "E4_wal.open_job" job) ~seg_max

let job t = t.w_job
let dir_of t = t.w_dir
let next_seq t = t.w_next
let last_index t = if t.w_next = 0 then None else Some (t.w_next - 1)
let durable_upto t = t.w_durable
let staged_bytes t = Buffer.length t.w_buf

let alive t what = if t.w_closed then invalid_arg ("E4_wal." ^ what ^ ": the writer is closed")

let stage t row =
  alive t "stage";
  (match row with
   | Seal _ -> invalid_arg "E4_wal.stage: a Seal is written by rotation, never staged"
   | Decision _ | Event _ | Checkpoint_mark _ -> ());
  let index = t.w_next in
  let body = body_of_row ~index row in
  let n = String.length body in
  if n > row_max then raise (Row_too_large n);
  Buffer.add_string t.w_buf (frame_row body);
  t.w_next <- index + 1;
  index

let append = stage

let flush_buf t =
  if Buffer.length t.w_buf > 0 then begin
    let s = Buffer.contents t.w_buf in
    Buffer.clear t.w_buf;
    write_string t.w_fd s;
    Unix.fsync t.w_fd;
    t.w_seg_bytes <- t.w_seg_bytes + String.length s;
    t.w_durable <- t.w_next
  end

let do_rotate t =
  let s = frame_row (body_of_row ~index:t.w_next (Seal { next_first_seq = t.w_next })) in
  write_string t.w_fd s;
  Unix.fsync t.w_fd;
  Unix.close t.w_fd;
  let path = Filename.concat t.w_dir (segment_name t.w_next) in
  let fd = create_segment ~path ~job:t.w_job ~first:t.w_next in
  fsync_dir t.w_dir;
  t.w_fd <- fd;
  t.w_seg_first <- t.w_next;
  t.w_seg_bytes <- head_length

let commit t =
  alive t "commit";
  flush_buf t;
  if t.w_seg_bytes >= t.w_seg_max then do_rotate t

let sync = commit

let rotate t =
  alive t "rotate";
  flush_buf t;
  do_rotate t

let checkpoint_mark t position =
  ignore (stage t (Checkpoint_mark { position; addr = None }) : seq);
  commit t

let close t =
  if not t.w_closed then begin
    flush_buf t;
    (try Unix.close t.w_fd with Unix.Unix_error _ -> ());
    release_claim t;
    t.w_closed <- true
  end

(* The byte offset at which the row of index [target] begins, walking the same grammar. *)
let offset_of_index bytes ~first ~target =
  let n = String.length bytes in
  let pos = ref head_length and idx = ref first and found = ref None and go = ref true in
  while !go do
    if !idx = target then begin
      found := Some !pos;
      go := false
    end
    else if !pos + row_header_length > n then go := false
    else
      match E4_crc.read_be32 bytes !pos with
      | None -> go := false
      | Some len ->
        if !pos + row_header_length + len > n then go := false
        else begin
          let body = String.sub bytes (!pos + row_header_length) len in
          (match decode_body body with
           | Some (_, (Decision _ | Event _ | Checkpoint_mark _)) -> incr idx
           | Some (_, Seal _) | None -> go := false);
          pos := !pos + row_header_length + len
        end
  done;
  !found

let truncate_to t target =
  alive t "truncate_to";
  if target > t.w_next || target < t.w_seg_first then
    invalid_arg
      (Printf.sprintf "E4_wal.truncate_to: %d is outside [%d, %d]" target t.w_seg_first t.w_next);
  Buffer.clear t.w_buf;
  let path = Filename.concat t.w_dir (segment_name t.w_seg_first) in
  let bytes = read_file path in
  match offset_of_index bytes ~first:t.w_seg_first ~target with
  | None -> invalid_arg (Printf.sprintf "E4_wal.truncate_to: no row at index %d" target)
  | Some off ->
    Unix.ftruncate t.w_fd off;
    Unix.fsync t.w_fd;
    t.w_seg_bytes <- off;
    t.w_next <- target;
    t.w_durable <- target
