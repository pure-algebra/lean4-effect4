(* Properties: host capacity stays outside modeled refusals; corruption names its recorded
   address; raw-read refusals agree in ordinary admission and recovery. *)
open Effect4_engine_cas
open Disk_test_support

let test_capacity () =
  let directory = temp () in
  let disk = open_ directory in
  ignore (get (E4_disk.commit disk initial));
  E4_disk.close disk;
  let path = E4_control.control_path ~dir:directory in
  let payload = get (E4_control.read ~path) in
  let maximum = Z.pred (Z.shift_left Z.one 62) in
  let roots =
    List.map
      (fun (root : E4_control.root) ->
         { root with head = { root.head with generation = maximum } })
      (E4_control.roots payload)
  in
  E4_control.commit ~path { payload with roots };
  let disk = open_ directory in
  let before = snapshot disk in
  let calls = ref 0 in
  require
    (match
       E4_disk.commit
         ~hook:(fun _ -> incr calls)
         disk
         (transaction
            [ b ]
            [ E4_control.Advance
                ("docs/a", { digest = aa; generation = maximum }, target ba)
            ])
     with
     | Error (E4_cas.Host_refused (E4_admission.Capacity _)) -> true
     | _ -> false)
    "wire limit is not Capacity";
  require
    (!calls = 0 && image_equal before (snapshot disk) && get (E4_disk.read disk ba) = None)
    "capacity wrote nodes or roots";
  ignore
    (get
       (E4_disk.commit
          disk
          (transaction
             []
             [ E4_control.Advance
                 ("docs/a", { digest = aa; generation = maximum }, target aa)
             ])));
  require
    (image_equal before (snapshot disk))
    "duplicate near capacity changes generation";
  E4_disk.close disk;
  remove directory;
  let directory = temp () in
  require
    (match E4_disk.open_ ~dir:directory { opts with seg_max = 1 } with
     | Error (E4_admission.Capacity _) -> true
     | Ok disk ->
       E4_disk.close disk;
       false
     | _ -> false)
    "invalid writer capacity raises";
  let disk = open_ directory in
  E4_disk.close disk;
  remove directory
;;

let test_corrupt () =
  let directory = temp () in
  let pack = E4_pack.open_ ~dir:directory ~seg_max:512 in
  ignore
    (E4_pack.append pack ~digest:E4_node.zero_digest ~node_bytes:(E4_node.encode schema));
  E4_pack.sync pack;
  let ending = E4_pack.pack_end pack in
  E4_pack.close pack;
  E4_control.commit
    ~path:(E4_control.control_path ~dir:directory)
    { E4_control.initial with pack_end = ending; generation = 1 };
  require
    (match E4_disk.open_ ~dir:directory opts with
     | Error (E4_admission.Fault (E4_fault.Corrupt address)) ->
       E4_addr.Addr.equal address E4_addr.Addr.zero
     | Ok disk ->
       E4_disk.close disk;
       false
     | _ -> false)
    "forged resident is not Fault Corrupt";
  remove directory
;;

let test_recovery_mapping () =
  let unknown =
    "\000"
    ^ String.make 1 (Char.chr (E4_kind.byte E4_kind.Export))
    ^ E4_node.zero_digest
    ^ E4_be.framed 253 ""
  in
  let directory = temp () in
  let disk = open_ directory in
  require
    (match E4_disk.commit disk { txn_nodes = [ unknown ]; txn_moves = [] } with
     | Error
         (E4_cas.Node_refused
            { index; why = E4_admission.Model (E4_admission.Unknown_tag 253) }) ->
       Z.equal index Z.zero
     | _ -> false)
    "ordinary unknown tag mapping";
  E4_disk.close disk;
  let pack = E4_pack.open_ ~dir:directory ~seg_max:512 in
  ignore (E4_pack.append pack ~digest:(E4_sha256.digest unknown) ~node_bytes:unknown);
  E4_pack.sync pack;
  E4_pack.close pack;
  require
    (match E4_disk.open_ ~dir:directory opts with
     | Error (E4_admission.Model (E4_admission.Unknown_tag 253)) -> true
     | Ok disk ->
       E4_disk.close disk;
       false
     | _ -> false)
    "recovery lost unknown tag";
  remove directory
;;

let () =
  test_capacity ();
  test_corrupt ();
  test_recovery_mapping ();
  print_endline "disk capacity, corruption and shared recovery mapping passed"
;;
