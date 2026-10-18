(* Properties: one locked writer; faults remain values; images hold values only.
   All byte input reaches E4_node.decode and the generated refusal adapter before admission.
   The store is admitted whole once, at open (a checked image); afterwards every record is this
   writer's own, admitted by its commit under the pack lock, so a commit costs its transaction and
   a read costs its node (re-hashed against its address). Bytes changed by another process while
   the lock is held are outside this model; reopening checks them.
   A host failure closes the uncertain writer; reopening performs checked recovery.
   Historical root ancestry and generation provenance are not reconstructed. *)
type t = { writer : E4_cas.t; mutable closed : bool }
type image = E4_cas.image
type transaction = E4_cas.transaction = { txn_nodes : string list; txn_moves : E4_control.move list }
type receipt = E4_cas.receipt
type error = E4_cas.transaction_error
let close disk =
  if not disk.closed then begin disk.closed <- true; E4_cas.close disk.writer end
let image disk =
  if disk.closed then Error (E4_admission.Fault (E4_fault.Store "writer closed"))
  else try E4_cas.checked_image (E4_cas.read_only disk.writer) with
    | Sys_error reason -> Error (E4_admission.Fault (E4_fault.Io reason))
    | E4_cas.Store_error reason -> Error (E4_admission.Fault (E4_fault.Store reason))
    | Unix.Unix_error (error, call, argument) ->
      Error (E4_admission.Fault (E4_fault.Io (call ^ " " ^ argument ^ ": " ^ Unix.error_message error)))

let open_ ~dir options =
  match E4_cas.open_rw ~dir options with
  | Error why -> Error why
  | Ok writer ->
    let disk = {writer; closed = false} in
    match (E4_cas.recovery writer).E4_cas.stop with
    | E4_cas.Refused {why; _} -> close disk; Error why
    | E4_cas.Clean | E4_cas.Torn _ -> (match image disk with
      | Ok _ -> Ok disk
      | Error why -> close disk; Error why)
let nodes image = image.E4_cas.image_nodes
let roots image = image.E4_cas.image_roots
let boundary image = image.E4_cas.image_boundary
let get_bytes image address =
  List.find_map (fun (at, bytes) -> if E4_addr.Addr.equal at address then Some bytes else None) (nodes image)
let read disk address =
  if disk.closed then Error (E4_admission.Fault (E4_fault.Store "writer closed"))
  else try
    match E4_cas.get_bytes (E4_cas.read_only disk.writer) address with
    | None -> Ok None
    | Some bytes when String.equal (E4_sha256.digest bytes) (E4_addr.Addr.bytes address) -> Ok (Some bytes)
    | Some _ -> Error (E4_admission.Fault (E4_fault.Corrupt address))
  with
  | Sys_error reason -> Error (E4_admission.Fault (E4_fault.Io reason))
  | E4_cas.Store_error reason -> Error (E4_admission.Fault (E4_fault.Store reason))
  | Unix.Unix_error (error, call, argument) ->
    Error (E4_admission.Fault (E4_fault.Io (call ^ " " ^ argument ^ ": " ^ Unix.error_message error)))
let commit ?hook disk transaction =
  if disk.closed then Error (E4_cas.Host_refused (E4_admission.Fault (E4_fault.Store "writer closed")))
  else
    let fail why = close disk; Error (E4_cas.Host_refused why) in
    try E4_cas.commit_transaction ?hook disk.writer transaction with
    | Invalid_argument reason -> fail (E4_admission.Capacity reason)
    | Sys_error reason -> fail (E4_admission.Fault (E4_fault.Io reason))
    | E4_cas.Store_error reason -> fail (E4_admission.Fault (E4_fault.Store reason))
    | Unix.Unix_error (error, call, argument) ->
      fail (E4_admission.Fault (E4_fault.Io (call ^ " " ^ argument ^ ": " ^ Unix.error_message error)))
