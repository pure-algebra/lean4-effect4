(* E4_shape — see e4_shape.mli for what this is, the two findings behind it, and its
   behaviours.  Lane P2, 2026-09-08. *)

open Effect4_engine

(* ============================================================ 1. paths *)

type step = Arg of int | Each

type path = step list

let args (is : int list) : path = List.map (fun i -> Arg i) is

let path_to_string (p : path) : string =
  if p = [] then "."
  else String.concat "." (List.map (function Arg i -> string_of_int i | Each -> "*") p)

(* ============================================================ 2. the frame walk *)

let tag_bytes = 8
let tag_list = 4
let tag_pair = 5
let tag_some = 7
let tag_ctor = 10
let tag_ref = 11

let cid_length = 32

(* The positions of a frame's children, in order.  Only tags 4, 5, 7 and 10 have children
   (SH6); a ctor's leading nat frame is the constructor index and is not a child. *)
let child_positions (s : string) (pos : int) (limit : int) : int list =
  match E4_be.read_frame s pos limit with
  | None -> []
  | Some (tag, p, e, _) ->
    if tag = tag_list then begin
      let acc = ref [] in
      let cur = ref p in
      let bad = ref false in
      while (not !bad) && !cur < e do
        match E4_be.read_frame s !cur e with
        | None ->
          bad := true
        | Some (_, _, _, next) ->
          acc := !cur :: !acc;
          if next <= !cur then bad := true else cur := next
      done;
      if !bad || !cur <> e then [] else List.rev !acc
    end
    else if tag = tag_pair then begin
      match E4_be.read_frame s p e with
      | None -> []
      | Some (_, _, _, next) -> (
        match E4_be.read_frame s next e with
        | Some (_, _, _, n2) when n2 = e -> [ p; next ]
        | _ -> [])
    end
    else if tag = tag_some then begin
      match E4_be.read_frame s p e with
      | Some (_, _, _, next) when next = e -> [ p ]
      | _ -> []
    end
    else if tag = tag_ctor then begin
      (* the leading nat frame is the index; the children are the arguments after it *)
      match E4_be.read_frame s p e with
      | None -> []
      | Some (t0, _, _, after_index) ->
        if t0 <> 2 then []
        else begin
          let acc = ref [] in
          let cur = ref after_index in
          let bad = ref false in
          while (not !bad) && !cur < e do
            match E4_be.read_frame s !cur e with
            | None ->
              bad := true
            | Some (_, _, _, next) ->
              acc := !cur :: !acc;
              if next <= !cur then bad := true else cur := next
          done;
          if !bad || !cur <> e then [] else List.rev !acc
        end
    end
    else []

(* Every frame a path reaches, as positions, in tree order. *)
let resolve_positions ~(payload : string) (p : path) : int list =
  let limit = String.length payload in
  match E4_be.read_frame payload 0 limit with
  | None -> []
  | Some (_, _, _, frame_end) when frame_end <> limit -> []
  | Some _ ->
    let rec go (here : int list) (steps : path) =
      match steps with
      | [] -> here
      | Arg i :: rest ->
        let next =
          List.filter_map
            (fun pos ->
              let cs = child_positions payload pos limit in
              List.nth_opt cs i)
            here
        in
        go next rest
      | Each :: rest ->
        let next = List.concat_map (fun pos -> child_positions payload pos limit) here in
        go next rest
    in
    go [ 0 ] p

let resolve ~payload p =
  let limit = String.length payload in
  List.filter_map
    (fun pos ->
      match E4_be.read_frame payload pos limit with
      | Some (tag, ps, pe, _) -> Some (tag, ps, pe)
      | None -> None)
    (resolve_positions ~payload p)

(* ============================================================ 3. the table *)

type field =
  | Cid_field of path
  | Ref_field of path * E4_kind.t option
  | Stamp of path
  | Data_field of path

let field_path = function
  | Cid_field p -> p
  | Ref_field (p, _) -> p
  | Stamp p -> p
  | Data_field p -> p

type cls = Cls_cid | Cls_ref of E4_kind.t option | Cls_stamp | Cls_data | Cls_unknown

type status = Frozen | Shared of string list | Unused | Tombstoned | Pending

type row = {
  kind : E4_kind.t;
  status : status;
  carriers : string list;
  fields : field list;
  note : string;
}

type t = { by_byte : row array (* index = kind byte; slot 0 unused *) }

(* ---------------------------------------------------------------- the rows.

   Provenance for every row is in `carriers`; the shapes are read off the Lean `toVal`
   declarations named there, and off 2026-09-07-cas-design.md §4 and A2 §1.9 for the reserved
   bytes.  Nothing here is inferred from bytes (SH4). *)

let r_source =
  {
    kind = E4_kind.Source;
    status =
      Shared
        [ "Effect4.StdLib.Source"; "Effect4.Store.Pin"; "Effect4.Char.Implementation" ];
    carriers =
      [ "StdLib/Derived.lean:147"; "Store/PinDerived.lean:168";
        "Char/Conformance/Receipt.lean:151" ];
    fields = [];
    note =
      "three carriers of different arity (Source ctor 0 [String,String,Digest]; Pin ctor 0 with \
       ten fields, spanDigest at 8; Implementation): no ValPath is decidable from the byte \
       (finding R1'). Their Digest fields are stamps, never Cids.";
  }

let r_export =
  {
    kind = E4_kind.Export;
    status = Frozen;
    carriers = [ "Effect4.StdLib.Entry (StdLib/Derived.lean:227)" ];
    fields =
      [ Data_field (args [ 0 ]); Data_field (args [ 1 ]); Data_field (args [ 2 ]);
        Data_field (args [ 3 ]); Ref_field (args [ 4 ], Some E4_kind.Source) ];
    note = "ctor 0 [module:String, name:String, kind:ExportKind, line:Nat, source:Ref Source]";
  }

let r_type =
  {
    kind = E4_kind.Type;
    status = Unused;
    carriers = [];
    fields = [];
    note = "reserved for the extractor lane (Kind.lean:29-30); no Content instance today";
  }

let r_schema =
  {
    kind = E4_kind.Schema;
    status = Frozen;
    carriers = [ "Effect4.Schema.Document (Store/Genesis.lean:35)" ];
    fields = [ Data_field (args [ 0 ]); Data_field (args [ 1 ]) ];
    note =
      "ctor 0 [representation:Representation, references:List ReferenceEntry] \
       (Schema/Document.lean:127-132): no Ref, no Cid, no Digest field. A schema's only edge is \
       the node's spec (edge 0), which lives in the envelope and not in the payload.";
  }

let r_program =
  {
    kind = E4_kind.Program;
    status = Unused;
    carriers = [];
    fields = [];
    note =
      "no Content instance today (cas-design §4 row `program`, probe 1b). The payload will be \
       `Eff NativeOp` bytes and names nothing: its own Cid is what others name.";
  }

let r_annotation =
  {
    kind = E4_kind.Annotation;
    status =
      Shared
        [ "Effect4.Store.Annotation t"; "Effect4.Char.Evidence"; "Effect4.Char.Claim";
          "Effect4.Char.Target"; "Effect4.Char.Characterized"; "Effect4.Char.Receipt" ];
    carriers =
      [ "Store/Traits.lean:149"; "Char/Derived.lean:272"; "Char/Derived.lean:373";
        "Char/Derived.lean:877"; "Char/Derived.lean:1025"; "Char/Conformance/Receipt.lean:235" ];
    fields = [];
    note =
      "`Annotation t` is ctor 0 [subject:AnyRef, value:t, prev:Option (Ref Annotation)], but \
       Evidence is a five-constructor SUM (ctor 0..4) and the other four disagree again: no \
       ValPath is decidable from the byte (finding R1'). The subject and prev refs are still \
       found exactly, by E4_node.refs, because they are tag-11 frames (SH1).";
  }

let r_entry =
  {
    kind = E4_kind.Entry;
    status = Unused;
    carriers = [];
    fields = [];
    note = "reserved for the journal (Kind.lean:37-38)";
  }

let r_query =
  {
    kind = E4_kind.Query;
    status = Unused;
    carriers = [];
    fields = [];
    note = "reserved (Kind.lean:39-40)";
  }

let r_result =
  {
    kind = E4_kind.Result;
    status = Unused;
    carriers = [];
    fields = [];
    note = "reserved (Kind.lean:41-42)";
  }

let r_chunk =
  {
    kind = E4_kind.Chunk;
    status = Unused;
    carriers = [];
    fields = [];
    note =
      "the blob kind (Kind.lean:43-44; A2 §1.9 e4_chunk). A chunk's payload is one `bytes` \
       leaf: it holds no address at any path, which is exactly why a chunk is an INTERIOR node \
       (E4_kind.is_interior).";
  }

let r_tree =
  {
    kind = E4_kind.Tree;
    status = Frozen;
    carriers = [ "Effect4.Store.Tree (Store/PinDerived.lean:224)" ];
    fields = [ Ref_field ([ Arg 0; Each; Arg 1 ], None) ];
    note =
      "ctor 0 [bindings:List (String x AnyRef)]. The only row in the table that needs `Each` \
       (SH5, D1); the target's kind is not fixed by the shape (AnyRef), hence None.";
  }

let r_manifest =
  {
    kind = E4_kind.Manifest;
    status = Unused;
    carriers = [];
    fields = [];
    note = "the second blob kind (Kind.lean:47-48); no Content instance today";
  }

let r_component =
  {
    kind = E4_kind.Component;
    status = Frozen;
    carriers = [ "Effect4.Char.Manifest (Char/Derived.lean:734)" ];
    fields = List.map (fun i -> Data_field (args [ i ])) [ 0; 1; 2; 3; 4; 5; 6; 7; 8; 9 ];
    note =
      "ctor 0 with ten fields (Char/Manifest.lean:76-90), all strings, lists of strings or \
       lists of records. The `Evidence` values nested under `grades` carry theorem-name Digests, \
       but they sit under sum constructors at unbounded list depth and name nothing in the \
       store: they are not rows, and cids_of is [] here.";
  }

let r_vector =
  {
    kind = E4_kind.Vector;
    status =
      Shared [ "Effect4.Char.GSet a"; "Effect4.Char.Fact L C"; "Effect4.Char.Vector L C" ];
    carriers =
      [ "Char/Canonical.lean:102"; "Char/Canonical.lean:299"; "Char/Canonical.lean:368" ];
    fields = [];
    note = "three carriers share the byte (finding R1')";
  }

let r_fiber =
  {
    kind = E4_kind.Fiber;
    status = Tombstoned;
    carriers = [];
    fields = [];
    note =
      "reserved 2026-09-04, retired 2026-09-07 (cas-design §4); never minted, the byte is never \
       reused";
  }

(* ---- 16..23: reserved by CAS commit 1 and amendment M17; shapes from cas-design §4 and
       A2 §1.9. Nothing in this estate mints one until the Lean side lands them (SH4). ---- *)

let r_job =
  {
    kind = E4_kind.Job;
    status = Pending;
    carriers = [ "cas-design §4 row `job`" ];
    fields =
      [ Cid_field (args [ 0 ]); Cid_field (args [ 1 ]); Data_field (args [ 2 ]);
        Cid_field (args [ 3 ]) ];
    note =
      "ctor 0 [program:Cid Program, profile:Cid Profile, fuel:Nat, tape:Cid Tape]. THE row the \
       table exists for: three 32-byte `bytes` frames that are addresses and are \
       indistinguishable from blobs without it (finding R1). Cids are not edges (amendment M1), \
       so a job scans NO edge — cas-design §4's `references: none`.";
  }

let r_tape =
  {
    kind = E4_kind.Tape;
    status = Pending;
    carriers = [ "cas-design §4 row `tape`" ];
    fields = [];
    note = "List Api.Decision; named by Cid, names nothing";
  }

let r_log =
  {
    kind = E4_kind.Log;
    status = Pending;
    carriers = [ "cas-design §4 row `log`" ];
    fields = [ Ref_field (args [ 0 ], Some E4_kind.Job); Data_field (args [ 1 ]) ];
    note = "ctor 0 [job:Ref Job, events:List LogEvent]";
  }

let r_exits =
  {
    kind = E4_kind.Exits;
    status = Pending;
    carriers = [ "cas-design §4 row `exits`" ];
    fields = [ Ref_field (args [ 0 ], Some E4_kind.Job); Data_field (args [ 1 ]) ];
    note = "ctor 0 [job:Ref Job, exits per fiber]";
  }

let r_receipt =
  {
    kind = E4_kind.Receipt;
    status = Pending;
    carriers = [ "cas-design §4 row `receipt`" ];
    fields =
      [ Ref_field (args [ 0 ], Some E4_kind.Job); Data_field (args [ 1 ]);
        Ref_field (args [ 2 ], Some E4_kind.Exits); Ref_field (args [ 3 ], Some E4_kind.Log);
        Stamp (args [ 4 ]); Stamp (args [ 5 ]); Data_field (args [ 6 ]) ];
    note =
      "ctor 0 [job:Ref Job, outcome, exits:Ref Exits, log:Ref Log, stores:Digest, \
       engine:Digest, host:String]. `stores` and `engine` are STAMPS: 32-byte bytes frames that \
       name nothing in the store (finding R1).";
  }

let r_checkpoint =
  {
    kind = E4_kind.Checkpoint;
    status = Pending;
    carriers = [ "cas-design §4 row `checkpoint`; A2 §1.9" ];
    fields =
      [ Ref_field (args [ 0 ], Some E4_kind.Job); Data_field (args [ 1 ]);
        Ref_field (args [ 2 ], Some E4_kind.Tape); Stamp (args [ 3 ]); Data_field (args [ 4 ]) ];
    note =
      "ctor 0 [job:Ref Job, position:Nat, tapePrefix:Ref Tape, engine:Digest, image]. The image \
       is either a `bytes` leaf or ctor 1 [list of Ref Chunk]; the chunk refs are tag-11 frames \
       and E4_node.refs finds them without a row (SH1). `engine` is a stamp. The stable-cut \
       rule is admission: tapePrefix is a Ref, so a checkpoint over an unstored tape is \
       refused `Dangling` by the store (L-CP-1).";
  }

let r_profile =
  {
    kind = E4_kind.Profile;
    status = Pending;
    carriers = [ "cas-design §4 row `profile`" ];
    fields = [];
    note = "carrier owed to the owner (cas-design §12); no shape to transcribe yet";
  }

let r_table =
  {
    kind = E4_kind.Table;
    status = Pending;
    carriers = [ "amendment M17 (the ordinal ledger / KeyTable as a stored node)" ];
    fields = [];
    note =
      "byte 23 under A2 owner question OQ3's applied default; the ledger's own shape is owed \
       with the commit that lands it";
  }

let all_rows =
  [ r_source; r_export; r_type; r_schema; r_program; r_annotation; r_entry; r_query; r_result;
    r_chunk; r_tree; r_manifest; r_component; r_vector; r_fiber; r_job; r_tape; r_log; r_exits;
    r_receipt; r_checkpoint; r_profile; r_table ]

let table : t =
  let a = Array.make 24 r_source in
  List.iter (fun r -> a.(E4_kind.byte r.kind) <- r) all_rows;
  { by_byte = a }

let rows _ = all_rows
let row t k = t.by_byte.(E4_kind.byte k)
let status_of t k = (row t k).status
let fields_of t k = (row t k).fields

let class_at t k p =
  let r = row t k in
  match List.find_opt (fun f -> field_path f = p) r.fields with
  | Some (Cid_field _) -> Cls_cid
  | Some (Ref_field (_, kk)) -> Cls_ref kk
  | Some (Stamp _) -> Cls_stamp
  | Some (Data_field _) -> Cls_data
  | None -> Cls_unknown

(* ============================================================ 4. the queries *)

type mismatch = { m_kind : E4_kind.t; m_at : path; m_reason : string }

let mismatch_to_string m =
  Printf.sprintf "shape mismatch at %s.%s: %s" (E4_kind.name m.m_kind) (path_to_string m.m_at)
    m.m_reason

(* One field's frames, checked.  `want` names what the field expects. *)
let hits ~payload (p : path) = resolve ~payload p

let bytes32 ~payload k p (acc : (string list, mismatch) result) =
  match acc with
  | Error _ -> acc
  | Ok got -> (
    match hits ~payload p with
    | [] -> Error { m_kind = k; m_at = p; m_reason = "no such path" }
    | frames ->
      let rec go got = function
        | [] -> Ok got
        | (tag, ps, pe) :: rest ->
          if tag <> tag_bytes then
            Error
              { m_kind = k; m_at = p; m_reason = Printf.sprintf "tag %d, want %d" tag tag_bytes }
          else if pe - ps <> cid_length then
            Error
              {
                m_kind = k;
                m_at = p;
                m_reason = Printf.sprintf "bytes %d, want %d" (pe - ps) cid_length;
              }
          else go (String.sub payload ps cid_length :: got) rest
      in
      go got frames)

let ref_at ~payload k p (want : E4_kind.t option) (acc : (E4_addr.Ref.t list, mismatch) result) =
  match acc with
  | Error _ -> acc
  | Ok got -> (
    match hits ~payload p with
    | [] -> Error { m_kind = k; m_at = p; m_reason = "no such path" }
    | frames ->
      let rec go got = function
        | [] -> Ok got
        | (tag, ps, pe) :: rest ->
          if tag <> tag_ref then
            Error
              { m_kind = k; m_at = p; m_reason = Printf.sprintf "tag %d, want %d" tag tag_ref }
          else if pe - ps <> 1 + cid_length then
            Error
              {
                m_kind = k;
                m_at = p;
                m_reason = Printf.sprintf "ref payload %d, want %d" (pe - ps) (1 + cid_length);
              }
          else begin
            let b = Char.code payload.[ps] in
            match E4_kind.of_byte b with
            | None ->
              Error
                { m_kind = k; m_at = p; m_reason = Printf.sprintf "unregistered kind byte %d" b }
            | Some kk ->
              if (match want with Some w -> not (E4_kind.equal w kk) | None -> false) then
                Error
                  {
                    m_kind = k;
                    m_at = p;
                    m_reason =
                      Printf.sprintf "kind %s, want %s" (E4_kind.name kk)
                        (match want with Some w -> E4_kind.name w | None -> "any");
                  }
              else
                go
                  (E4_addr.Ref.make kk
                     (E4_addr.Addr.of_digest (String.sub payload (ps + 1) cid_length))
                  :: got)
                  rest
          end
      in
      go got frames)

let cids_of_checked t k ~payload =
  let r = row t k in
  let res =
    List.fold_left
      (fun acc f -> match f with Cid_field p -> bytes32 ~payload k p acc | _ -> acc)
      (Ok []) r.fields
  in
  match res with Ok xs -> Ok (List.rev_map E4_addr.Addr.of_digest xs) | Error e -> Error e

let stamps_of_checked t k ~payload =
  let r = row t k in
  let res =
    List.fold_left
      (fun acc f -> match f with Stamp p -> bytes32 ~payload k p acc | _ -> acc)
      (Ok []) r.fields
  in
  match res with Ok xs -> Ok (List.rev xs) | Error e -> Error e

let refs_of_checked t k ~payload =
  let r = row t k in
  let res =
    List.fold_left
      (fun acc f -> match f with Ref_field (p, w) -> ref_at ~payload k p w acc | _ -> acc)
      (Ok []) r.fields
  in
  match res with Ok xs -> Ok (List.rev xs) | Error e -> Error e

(* The lenient forms drop exactly what the checked form refuses (SH3). *)

let cids_of t k ~payload =
  let r = row t k in
  List.concat_map
    (function
      | Cid_field p ->
        List.filter_map
          (fun (tag, ps, pe) ->
            if tag = tag_bytes && pe - ps = cid_length then
              Some (E4_addr.Addr.of_digest (String.sub payload ps cid_length))
            else None)
          (hits ~payload p)
      | _ -> [])
    r.fields

let stamps_of t k ~payload =
  let r = row t k in
  List.concat_map
    (function
      | Stamp p ->
        List.filter_map
          (fun (tag, ps, pe) ->
            if tag = tag_bytes && pe - ps = cid_length then
              Some (String.sub payload ps cid_length)
            else None)
          (hits ~payload p)
      | _ -> [])
    r.fields

let refs_of t k ~payload =
  let r = row t k in
  List.concat_map
    (function
      | Ref_field (p, want) ->
        List.filter_map
          (fun (tag, ps, pe) ->
            if tag <> tag_ref || pe - ps <> 1 + cid_length then None
            else
              match E4_kind.of_byte (Char.code payload.[ps]) with
              | None -> None
              | Some kk ->
                if (match want with Some w -> not (E4_kind.equal w kk) | None -> false) then None
                else
                  Some
                    (E4_addr.Ref.make kk
                       (E4_addr.Addr.of_digest (String.sub payload (ps + 1) cid_length))))
          (hits ~payload p)
      | _ -> [])
    r.fields
