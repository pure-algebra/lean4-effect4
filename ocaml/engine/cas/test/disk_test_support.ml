(* Properties: checked images freeze bytes, roots, and durable boundary; preflight refuses
   without writing; reopened stores retain complete heads; damage is a fault value.
   These are finite controls of the actual disk writer, not a universal IO theorem. *)
open Effect4_engine_cas
let require condition message = if not condition then failwith message
let get = function Ok value -> value | Error _ -> failwith "unexpected refusal"
let opts = {E4_cas.default_opts with seg_max = 512; index_slots = 16}
let temp () = let path = Filename.temp_file ?temp_dir:(Sys.getenv_opt "E4_DISK_TMP") "e4-st2-" "" in Sys.remove path; Unix.mkdir path 0o700; path
let rec remove path =
  if Sys.is_directory path then begin
    Unix.chmod path 0o700;
    Array.iter (fun name -> remove (Filename.concat path name)) (Sys.readdir path);
    Unix.rmdir path
  end else begin Unix.chmod path 0o600; Sys.remove path end
let framed = E4_be.framed
let vstr value = framed Eff_frame.tag_string value
let vref kind address = framed Eff_frame.tag_ref (String.make 1 (Char.chr (E4_kind.byte kind)) ^ E4_addr.Addr.bytes address)
let node kind spec payload = {E4_node.version = 0; kind; spec; payload}
let schema = node E4_kind.Schema E4_node.zero_digest (vstr "schema")
let s = E4_node.address schema
let a = node E4_kind.Export (E4_addr.Addr.bytes s) (vstr "A")
let b = node E4_kind.Export (E4_addr.Addr.bytes s) (vstr "B")
let aa = E4_node.address a and ba = E4_node.address b
let t = node E4_kind.Export (E4_addr.Addr.bytes s) (vstr "T")
let ta = E4_node.address t
let u = node E4_kind.Export (E4_addr.Addr.bytes s) (framed Eff_frame.tag_some (vref E4_kind.Export ta))
let ua = E4_node.address u
let target digest : E4_control.target = {kind = E4_kind.Export; digest}
let transaction nodes moves : E4_disk.transaction = {txn_nodes = List.map E4_node.encode nodes; txn_moves = moves}
let initial = transaction [schema; a] [E4_control.Create ("docs/a", E4_control.Swap, target aa)]
let root_equal (a : E4_control.root) (b : E4_control.root) =
  String.equal a.name b.name && a.policy = b.policy && E4_kind.equal a.kind b.kind && E4_control.head_equal a.head b.head
let image_equal a b =
  List.equal (fun (at, x) (bt, y) -> E4_addr.Addr.equal at bt && String.equal x y) (E4_disk.nodes a) (E4_disk.nodes b)
  && List.equal root_equal (E4_disk.roots a) (E4_disk.roots b) && E4_disk.boundary a = E4_disk.boundary b
let root image name = List.find_opt (fun (r : E4_control.root) -> String.equal r.name name) (E4_disk.roots image)
let open_ directory = get (E4_disk.open_ ~dir:directory opts)
let snapshot disk = get (E4_disk.image disk)
let observation image =
  let nodes = List.map (fun (address, bytes) -> E4_addr.Addr.hex address ^ "=" ^ E4_hex.of_bytes bytes) (E4_disk.nodes image) in
  let roots = List.map (fun (r : E4_control.root) -> r.name ^ ":" ^ string_of_int (E4_root_policy.byte r.policy) ^ ":" ^
    string_of_int (E4_kind.byte r.kind) ^ ":" ^ E4_addr.Addr.hex r.head.digest ^ ":" ^ Z.to_string r.head.generation) (E4_disk.roots image) in
  "n[" ^ String.concat ";" nodes ^ "]r[" ^ String.concat ";" roots ^ "]"
let golden_path name =
  match Sys.getenv_opt "E4_CAS_GOLDENS" with
  | Some directory -> Filename.concat directory name
  | None ->
    let path = Filename.concat "../goldens" name in
    if Sys.file_exists path then path else failwith ("required golden missing: " ^ name)
let head_observation (head : E4_control.head) = E4_addr.Addr.hex head.digest ^ ":" ^ Z.to_string head.generation
let optional_head = function None -> "none" | Some head -> head_observation head
let admission_observation = function
  | E4_admission.Model why -> (match why with
    | E4_admission.Dangling address -> "dangling:" ^ E4_addr.Addr.hex address
    | E4_admission.Wrong_kind (address, expected, actual) ->
      Printf.sprintf "wrongKind:%s:%d:%d" (E4_addr.Addr.hex address) (E4_kind.byte expected) (E4_kind.byte actual)
    | E4_admission.Malformed_ref -> "malformedRef"
    | E4_admission.Handle_in_content -> "handleInContent"
    | E4_admission.Short_spec -> "shortSpec"
    | E4_admission.Unregistered_kind byte -> "unregisteredKind:" ^ string_of_int byte
    | E4_admission.Bad_frame -> "badFrame"
    | E4_admission.Trailing -> "trailing"
    | E4_admission.Unknown_tag byte -> "unknownTag:" ^ string_of_int byte
    | E4_admission.Oversize -> "oversize"
    | E4_admission.Bad_version -> "badVersion"
    | E4_admission.Conflict (address, node) -> "conflict:" ^ E4_addr.Addr.hex address ^ ":" ^ E4_hex.of_bytes (E4_node.encode node)
    | E4_admission.Bad_envelope -> "badEnvelope"
    | E4_admission.Poisoned (query, first, second) ->
      "poisoned:" ^ E4_addr.Addr.hex query ^ ":" ^ E4_addr.Addr.hex first ^ ":" ^ E4_addr.Addr.hex second)
  | E4_admission.Capacity reason -> "capacity:" ^ reason
  | E4_admission.Fault why -> "fault:" ^ E4_fault.word why
let transaction_observation = function
  | Error (E4_cas.Node_refused {index; why}) -> "error:node:" ^ Z.to_string index ^ ":" ^ admission_observation why
  | Error (E4_cas.Host_refused why) -> "host:" ^ admission_observation why
  | Error (E4_cas.Move_refused {name; why}) -> "error:" ^ (match why with
    | E4_control.No_root name -> "noRoot:" ^ name
    | E4_control.Stale_root {name; expected; actual} -> "staleRoot:" ^ name ^ ":" ^ optional_head expected ^ ":" ^ optional_head actual
    | E4_control.Pinned name -> "pinned:" ^ name
    | E4_control.Dangling address -> "target:" ^ name ^ ":dangling:" ^ E4_addr.Addr.hex address
    | E4_control.Wrong_kind {at; expected; actual} -> Printf.sprintf "target:%s:wrongKind:%s:%d:%d" name (E4_addr.Addr.hex at) (E4_kind.byte expected) (E4_kind.byte actual)
    | E4_control.Fork {name; head; target} -> "fork:" ^ name ^ ":" ^ E4_addr.Addr.hex head ^ ":" ^ E4_addr.Addr.hex target)
  | Ok receipt ->
    let nodes = List.map (fun (address, outcome) -> E4_addr.Addr.hex address ^ ":" ^
      match outcome with E4_cas.Fresh_node -> "fresh" | E4_cas.Duplicate_node -> "duplicate") receipt.E4_cas.receipt_nodes in
    let moves = List.map (function
      | E4_cas.Created generation -> "created:" ^ Z.to_string generation
      | E4_cas.Advanced generation -> "advanced:" ^ Z.to_string generation
      | E4_cas.Duplicate_move generation -> "duplicate:" ^ Z.to_string generation) receipt.E4_cas.receipt_moves in
    "ok:n[" ^ String.concat ";" nodes ^ "]m[" ^ String.concat ";" moves ^ "]"
