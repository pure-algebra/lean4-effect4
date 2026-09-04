(* `Effect4/Deep/Layer.lean` → `deep_layer.ml`.

   Seat W1, 2026-09-04. Report: `docs/research/2026-09-04-seat-w1-deep-port.md`.

   CHECKPOINT 1 of the port. What is here is the `Layers` family's arms, moved out of
   `deep_fibers.ml` unchanged so that the machine module holds no store: `Layer.lean` is
   where the memo world lives, so this is where its arms live. The carriers of `Layer.lean`
   — `LayerId`, `MemoMapId`, `CombineMode`, `Construction`, `LayerDesc`, `MemoEntry`,
   `MemoMap`, `MemoWorld`, `St` and the sixteen layer rows — are generated in deliverable 2
   and replace the `layer_state` improvisation below. Until then this module is A0's
   round-three code at its new address and the divergence table says so. *)

open Deep_fibers

(* The Layer memo world (`docs/ENVIRONMENT-DAG.md` M4b, `harness/trace/layer-tail.ts`): four
   declared layers, 0/1/2 memoised through one memo map and 3 = `Layer.fresh(layer 1)`,
   which constructs on every build and counts against base 1. The memo map's entries live
   in the root scope, so closing it drops them.
   NOT the `Layer.lean` carriers: see the checkpoint note above. *)
type layer_state = {
  counts : (int, int) Hashtbl.t;          (* base -> how many times its construction ran *)
  memo : (int, int) Hashtbl.t;            (* layer id -> the service it replays *)
  mutable root_open : bool;
  mutable registered : int list;          (* services whose finalizer is on the root, LIFO *)
  mutable release_log : int list;         (* every service released so far, oldest first *)
  service_scope : (int, int) Hashtbl.t;   (* service -> the layer scope of its construction *)
  mutable next_service : int;
  mutable next_layer_scope : int;
}

let layers : layer_state =
  { counts = Hashtbl.create 8; memo = Hashtbl.create 8; root_open = true; registered = [];
    release_log = []; service_scope = Hashtbl.create 8; next_service = 0;
    next_layer_scope = 0 }

let layers_reset () : unit =
  Hashtbl.reset layers.counts;
  Hashtbl.reset layers.memo;
  Hashtbl.reset layers.service_scope;
  layers.root_open <- true;
  layers.registered <- [];
  layers.release_log <- [];
  layers.next_service <- 0;
  layers.next_layer_scope <- 0

(* The `Layers` family's requests. *)
type Deep_fibers.store_request +=
  | Rlayer_build of int
  | Rlayer_provide_count of int
  | Rlayer_scope_of of int
  | Rlayer_close

(* `Layer.buildWithMemoMap(layer, memoMap, root)` answering `Context.get(context, Tag)`:
   the service object, which the memo entry replays unchanged on a hit
   (`harness/trace/layer-tail.ts:114-121`). Layer 3 is `Layer.fresh(layer 1)`, so it misses
   the memo every time and counts against base 1. *)
let arm_layer_build m f (layer : int) (ko : value kops) : unit =
  begin
    push_row (Rop ("build", Vnat layer));
    let ls = layers in
    let base = if layer = 3 then 1 else layer in
    let fresh = layer = 3 in
    let service =
      match (if fresh then None else Hashtbl.find_opt ls.memo layer) with
      | Some service -> service                                        (* the memo hit *)
      | None ->
        Hashtbl.replace ls.counts base
          (1 + match Hashtbl.find_opt ls.counts base with Some n -> n | None -> 0);
        let service = ls.next_service in
        ls.next_service <- service + 1;
        let layer_scope = ls.next_layer_scope in
        ls.next_layer_scope <- layer_scope + 1;
        Hashtbl.replace ls.service_scope service layer_scope;
        (* The construction registers its release finalizer on its own layer scope, which
           `memoMapBuild` forked from the root. A scope forked from a closed root is already
           closed, so the finalizer runs on the spot and the next `close` sees nothing. *)
        if ls.root_open then ls.registered <- service :: ls.registered
        else ls.release_log <- ls.release_log @ [ service ];
        if not fresh then Hashtbl.replace ls.memo layer service;
        service
    in
    answer_row m f "build" (Vhandle (handle_index "service" service)) ko
  end

let layer_arm m f (req : Deep_fibers.store_request) (ko : value kops) : unit =
  match req with
  | Rlayer_build layer -> arm_layer_build m f layer ko
  | Rlayer_provide_count base ->
    arm_state m f "provideCount" (Vnat base)
      (fun () ->
        Vnat (match Hashtbl.find_opt layers.counts base with Some n -> n | None -> 0))
      ko
  | Rlayer_scope_of h ->
    arm_state m f "scopeOf" (Vhandle h)
      (fun () ->
        let service = handle_target "service" h in
        match Hashtbl.find_opt layers.service_scope service with
        | Some sc -> Vhandle (handle_index "layerScope" sc)
        | None -> failwith "no layer scope for that service")
      ko
  | Rlayer_close ->
    arm_state m f "close" Vunit
      (fun () ->
        let ls = layers in
        if not ls.root_open then Vlist []
        else begin
          let released = ls.registered in
          ls.registered <- [];
          ls.root_open <- false;
          (* The memo map's entries live in the root scope. *)
          Hashtbl.reset ls.memo;
          ls.release_log <- ls.release_log @ released;
          Vlist (List.map (fun sv -> Vhandle (handle_index "service" sv)) released)
        end)
      ko
  | _ -> refuse "Effect4.Deep.Layers (unknown store_request)"

let () =
  let previous = (!interp).store_arm in
  (!interp).store_arm <-
    (fun m f req ko ->
      match req with
      | Rlayer_build _ | Rlayer_provide_count _ | Rlayer_scope_of _ | Rlayer_close ->
        layer_arm m f req ko
      | _ -> previous m f req ko)
