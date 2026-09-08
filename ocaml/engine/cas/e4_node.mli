(* E4_node — the node envelope: version, kind, spec, payload; the edge scan; the address.

   What it is: `Node.encode` / `Node.decode` (src/Effect4/Store/Node.lean:170-182) as OCaml,
   plus the edge scan `Val.refs` (:241-255), the malformed-ref test (:260-266) and the handle
   scan, done as ONE flat frame walk over the payload bytes with no value tree allocated.
   Knock-on O3 records that the OCaml estate had no node envelope at all: `encode_program`
   (ocaml/eff/eff_wire.ml:1056-1058) writes *payload* bytes.  This is the envelope around them.

     node_bytes := version kind spec payload
     version    := 0x00                    1   Node.lean:171; any other byte is Bad_version
     kind       := E4_kind.byte            1   an unregistered byte is a decode refusal
     spec       := digest                 32   edge 0, at kind `schema` (Node.lean:287)
     payload    := Val.encode v      (varies)  one Eff_frame value tree and nothing else

   There is NO second encoding here (brief §2.2): the frame layer is A1's `E4_be`
   (`read_be64`, the 9-byte header) and the UTF-8 rule is `Eff_frame.utf8_valid`; this module
   adds the two header bytes, the 32 spec bytes, and the traversal.

   Depends on: E4_kind, E4_addr, E4_be and E4_sha256 (ocaml/engine, lane M), Eff_frame
   (ocaml/eff, read-only).

   Behaviours:
   ND1 `encode` = version :: kind.byte :: spec ++ payload, and `decode (encode n) = Ok n` for
       every n with version 0 and a payload that is one well-formed frame tree
       (`Node.decode_encode`, Node.lean:190).                    by construction; tested
   ND2 Exact: `decode b = Ok n -> b = encode n`, so a trailing byte, a version other than 0, an
       unregistered kind byte and a short spec are all refusals (`Node.decode_exact`, :204).
       The refusal reported is the first failing test in the order version -> kind -> spec ->
       payload; Lean answers `none` for all of them alike, so the constructor is this side's
       diagnosis and never a semantic difference.                            tested
   ND3 `refs` equals `Val.refs` as a list, in traversal order: a left-to-right frame walk
       descending only into tags 4 (list), 5 (pair), 7 (some) and 10 (ctor).  A ref frame is a
       ref only when its kind byte is registered AND its digest is 32 bytes; otherwise it
       contributes nothing (Node.lean:241-255).                              tested (L-SCAN-1)
   ND4 `malformed_ref` equals `Val.malformedRef`: some tag-11 frame whose kind byte is
       unregistered or whose digest is not 32 bytes (Node.lean:260-266).     tested (L-SCAN-3)
   ND5 Tag 8 (`bytes`) is a LEAF.  A payload whose `bytes` frame happens to contain a valid
       ref frame yields NO ref and is not malformed — `Val.refs (.bytes bs) = []`
       (Node.lean:250).  The walk never descends into a bytes payload.
                                                                 by construction; tested (L-SCAN-2)
   ND6 `handles` lists the tag-12 frames as (kind byte, allocation index) in traversal order;
       `handle_in_content` is `is_content kind && handles <> []` (amendment M2).      tested
   ND7 `edges` is `{kind = Schema; addr = spec} :: refs`; `checked_edges` drops edge 0 exactly
       for the genesis (kind Schema with the zero spec) and for nothing else
       (`Node.checkedEdges`, :297).                                          tested
   ND8 A frame whose be64 length is >= 2^62 is `Host_limit`, never misread (amendment M9;
       `E4_be.read_be64` refuses, e4_be.mli:58-59, transcribing eff_frame.ml:159-167).  The
       OCaml byte language is therefore strictly contained in Lean's, whose `Val.WF` bound is
       2^64 (Val.lean:279-292): every node this host can hold, Lean holds.
                                                                 by construction; tested
   ND9 `address n = E4_sha256.digest (encode n)`, and nothing else is ever hashed
       (`Store.address`, Node.lean:354; L-CAS-1).                            tested
   ND10 `check_pure` is the prefix of `Store.putNode` (Store.lean:262-276) that is a function
       of the node alone, in Lean's order: oversize -> bad version -> malformed ref, with
       amendment M2's handle-in-content appended (A2 owner question OQ4's default: "after
       malformedRef, before edge checking").  The store-relative refusals — `dangling` and
       `wrongKind` over `checked_edges` — are lane P4's and are NOT here; what P4 needs from
       this module is `checked_edges`, in order, spec first.                 tested

   Deviations from docs/research/2026-09-08-engine-a2-persistence.md §1.5 (lane P0, 2026-09-08):
   D1  `decode`'s payload check validates the frame TREE without building it: tags, lengths,
       the bool byte, the shortest-form nat digit rule, UTF-8, the pair's two frames, the
       option's one, the ctor's leading nat frame.  It does NOT bound a `nat` frame's value:
       Lean's Nat is unbounded and a stored node may legitimately carry a 20-digit natural, so
       refusing it here would make this host narrower than Lean for no gain.  A `handle` key
       IS bounded (Host_limit above 2^62-1): a handle is an allocation index of this host's
       machine, and `E4_nat` says the host cannot have allocated that many.
   D2  Added beside §1.5's list: `make` (which enforces the 32-byte spec so `edges` is total),
       `scan_payload` / `payload_ok` / `scan_malformed_ref` / `scan_handles` (one traversal for
       lane P4 rather than three), `check_pure` with `pure_refusal`, and `oversize` /
       `bad_version` / `handle_in_content` as separate predicates so P4 can reorder them if
       golden G2 settles OQ4 differently.
   D3  `refs`, `malformed_ref` and `handles` answer `[]` / `false` / `[]` on a payload that is
       not one well-formed frame tree.  Such a node never reaches them: `check_pure` refuses
       it as `Oversize` first, exactly as `Store.putNode` tests `payload.WF` first.
       `scan_payload` is the total form and reports the error. *)

type t = {
  version : int;                 (* 0 for every admissible node *)
  kind : E4_kind.t;
  spec : string;                 (* exactly 32 bytes: edge 0, at kind Schema *)
  payload : string;              (* one Val frame tree *)
}

type decode_error =
  | Trailing                     (** bytes after the payload's one frame *)
  | Bad_version of int           (** the byte that was not 0 *)
  | Unregistered_kind of int     (** the byte no kind is filed under *)
  | Short_spec                   (** fewer than 34 header bytes *)
  | Bad_frame                    (** the payload is not one well-formed frame tree *)
  | Host_limit                   (** a frame length >= 2^62, amendment M9 (ND8) *)

type scan = {
  refs : E4_addr.Ref.t list;     (** Val.refs, in traversal order *)
  malformed : bool;              (** Val.malformedRef *)
  handles : (int * int) list;    (** (kind byte, allocation index), in traversal order *)
}

type pure_refusal =
  | Oversize of decode_error     (** the payload is not one well-formed frame tree; the
                                     carried error is `Host_limit` for amendment M9's case
                                     and lets lane P4 report `hostLimit` apart from
                                     `oversize` (A2 §1.9 CS2 rows 1 and 1') *)
  | Bad_version_byte of int
  | Malformed_ref
  | Handle_in_content

val make : version:int -> kind:E4_kind.t -> spec:string -> payload:string -> t
(** Invalid_argument unless the spec is exactly 32 bytes and the version is a byte. *)

val encode : t -> string
(** version :: kind.byte :: spec ++ payload (ND1). *)

val decode : string -> (t, decode_error) result
(** Exact (ND2). *)

val address : t -> E4_addr.Addr.t
(** sha256 (encode t) (ND9). *)

(* ---- the payload walk: one pass, no tree ---- *)

val payload_ok : string -> (unit, decode_error) result
(** The bytes are exactly one well-formed frame tree. *)

val scan_payload : string -> (scan, decode_error) result
(** Refs, the malformed verdict and the handles of a bare payload, in one traversal. *)

val scan_refs : string -> E4_addr.Ref.t list
(** [] on a payload that does not parse (D3). *)

val scan_malformed_ref : string -> bool
val scan_handles : string -> (int * int) list

val refs : t -> E4_addr.Ref.t list
(** ND3: Val.refs of the payload, in traversal order. *)

val malformed_ref : t -> bool
(** ND4: Val.malformedRef of the payload. *)

val handles : t -> (int * int) list
(** ND6: the tag-12 frames, in traversal order. *)

(* ---- the spec edge, the genesis, the edges admission checks ---- *)

val zero_digest : string
(** Thirty-two zero bytes (Node.lean:276). *)

val is_genesis : t -> bool
(** kind = Schema && spec = zero_digest (Node.IsGenesis, :291). *)

val edges : t -> E4_addr.Ref.t list
(** {Schema; spec} :: refs (Node.edges, :287) (ND7). *)

val checked_edges : t -> E4_addr.Ref.t list
(** Node.checkedEdges (:297): [edges], or [refs] alone for the genesis (ND7). *)

(* ---- the admission tests that are functions of the node alone (ND10) ---- *)

val oversize : t -> bool
val bad_version : t -> bool
val handle_in_content : t -> bool

val check_pure : t -> (unit, pure_refusal) result
(** oversize -> bad_version -> malformed_ref -> handle_in_content.  The store-relative
    `dangling` / `wrongKind` over [checked_edges] belong to lane P4. *)
