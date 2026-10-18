(* Properties: a snapshot freezes nodes, roots and the durable boundary through later writes;
   a refused transaction rolls back whole; receipts carry full heads; read handles share one
   writer. The retained red control shows the old mutable read view aliasing its writer.
   These are finite host checks, not a filesystem theorem. *)
open Effect4_engine_cas
open Disk_test_support

let test_snapshot_atomic () =
  let directory = temp () in
  let disk = open_ directory in
  let empty = snapshot disk in
  ignore (get (E4_disk.commit disk initial));
  let first = snapshot disk in
  require
    (E4_disk.nodes empty = [] && E4_disk.roots empty = [])
    "frozen empty image sees later writes";
  require (List.length (E4_disk.nodes first) = 2) "initial image node order";
  let callbacks = ref 0 in
  let bad =
    transaction
      [ t; u ]
      [ E4_control.Advance ("missing", { digest = aa; generation = Z.one }, target ua) ]
  in
  require
    (match E4_disk.commit ~hook:(fun _ -> incr callbacks) disk bad with
     | Error
         (E4_cas.Move_refused { name = "missing"; why = E4_control.No_root "missing" }) ->
       true
     | _ -> false)
    "late root refusal";
  require
    (!callbacks = 0 && image_equal first (snapshot disk))
    "preflight writes before late refusal";
  require (E4_disk.get_bytes (snapshot disk) ta = None) "refused node became durable";
  let good =
    transaction [ a; t; u ] [ E4_control.Create ("docs/b", E4_control.Swap, target ua) ]
  in
  let writes = ref [] in
  let receipt =
    get
      (E4_disk.commit
         ~hook:(function
           | E4_cas.After_write n -> writes := n :: !writes
           | _ -> ())
         disk
         good)
  in
  require
    (List.map snd receipt.E4_cas.receipt_nodes
     = [ E4_cas.Duplicate_node; E4_cas.Fresh_node; E4_cas.Fresh_node ])
    "ordered node receipt";
  require (List.rev !writes = [ 1; 2 ]) "duplicates count as fresh writes";
  require
    (List.length (E4_disk.nodes first) = 2 && List.length (E4_disk.roots first) = 1)
    "retained image changed";
  let final = snapshot disk in
  E4_disk.close disk;
  Sys.remove (Filename.concat directory "index/000000.idx");
  let reopened = open_ directory in
  require (image_equal final (snapshot reopened)) "reopen or rebuilt index changes image";
  require
    (List.length (E4_disk.nodes first) = 2 && root first "docs/b" = None)
    "rebuilt index changed retained snapshot";
  E4_disk.close reopened;
  remove directory
;;

let test_heads () =
  let directory = temp () in
  let disk = open_ directory in
  ignore (get (E4_disk.commit disk initial));
  ignore
    (get
       (E4_disk.commit
          disk
          (transaction
             [ b ]
             [ E4_control.Advance
                 ("docs/a", { digest = aa; generation = Z.one }, target ba)
             ])));
  ignore
    (get
       (E4_disk.commit
          disk
          (transaction
             []
             [ E4_control.Advance
                 ("docs/a", { digest = ba; generation = Z.of_int 2 }, target aa)
             ])));
  let before = snapshot disk in
  require
    (match root before "docs/a" with
     | Some r -> Z.equal r.head.generation (Z.of_int 3)
     | None -> false)
    "ABA generation";
  require
    (match
       E4_disk.commit
         disk
         (transaction
            []
            [ E4_control.Advance
                ( "docs/a"
                , { digest = aa; generation = Z.one }
                , { kind = E4_kind.Schema; digest = s } )
            ])
     with
     | Error (E4_cas.Move_refused { why = E4_control.Stale_root _; _ }) -> true
     | _ -> false)
    "stale first";
  require (image_equal before (snapshot disk)) "stale changed image";
  E4_disk.close disk;
  let disk = open_ directory in
  require (image_equal before (snapshot disk)) "generation changed on reopen";
  E4_disk.close disk;
  remove directory
;;

let test_shared_handles () =
  let directory = temp () in
  let writer = get (E4_cas.open_rw ~dir:directory opts) in
  ignore (get (E4_cas.put writer schema));
  E4_cas.commit writer;
  let view = E4_cas.read_only writer in
  let old = get (E4_cas.checked_image view) in
  let before = old.E4_cas.image_nodes, old.image_roots, old.image_boundary in
  ignore (get (E4_cas.put writer a));
  ignore
    (get
       (E4_cas.advance_root
          writer
          (E4_control.Create ("docs/a", E4_control.Swap, target aa))));
  E4_cas.drop_index view;
  require (E4_cas.mem view aa) "rebuilt live index does not see committed node";
  require
    ((old.E4_cas.image_nodes, old.image_roots, old.image_boundary) = before)
    "shared pack/index changed checked image";
  require
    (List.length old.image_nodes = 1 && old.image_roots = [])
    "checked image follows mutable view";
  E4_cas.close writer;
  remove directory
;;

let test_old_snapshot_red () =
  let directory = temp () in
  let child = Unix.fork () in
  if child = 0
  then (
    let writer = get (E4_cas.open_rw ~dir:directory opts) in
    let old = E4_cas.read_only writer in
    ignore (get (E4_cas.put writer schema));
    E4_cas.commit writer;
    require (not (E4_cas.mem old s)) "legacy snapshot aliases writer";
    E4_cas.close writer;
    Unix._exit 74);
  let _, status = Unix.waitpid [] child in
  require (status = Unix.WEXITED 2) "legacy alias red did not fail";
  remove directory
;;

let () =
  test_snapshot_atomic ();
  test_heads ();
  test_shared_handles ();
  test_old_snapshot_red ();
  print_endline "disk snapshots, rollback, receipts, heads and retained alias red passed"
;;
