(* E4_cache — see e4_cache.mli for what this is and the behaviours it holds itself to. *)

(* ============================================================ 1. the CLOCK core

   One core serves both tiers.  The value is polymorphic and lives in a `'v option array`, so
   no dummy value is needed and "this slot is free" is `None` — the alternative, an `'a array`
   filled by `Obj.magic`, is refused by ocaml/STANDARDS.md §4.

   The key table is a `Bigarray.int` of `slot + 1`, 0 meaning empty, with LINEAR PROBING and
   BACKWARD-SHIFT deletion (Knuth 6.4 algorithm R): on a delete the hole is filled by the next
   entry that probed past it, so the table never holds a tombstone and a cache that has evicted
   a billion entries probes exactly as fast as a fresh one.  The table is at load <= 0.6, which
   is what guarantees that every probe loop below terminates: an empty position always exists.
*)

let max_load = 0.6
let default_entry_bytes = 1024
let min_slots = 16
let max_derived_slots = 1 lsl 20

let pow2_at_least (n : int) : int =
  let r = ref 16 in
  while !r < n do
    r := !r * 2
  done;
  !r

(* The hash of an address: seven of the low bytes, so it is independent of
   `E4_addr.Addr.prefix63` (which takes the HIGH bytes and is the index's key) and cannot
   inherit a collision forced against that one.  Always in 0 .. 2^56 - 1.

   The seven reads are written out rather than folded through a local `fun i -> ...`: without
   flambda, `ocamlopt` allocates a closure for a local function that captures `s`, and that
   closure is the whole of what a cache hit would allocate (measured: 4 minor words per hit
   with it, 0 without — test_cache E3). *)
let hash_bytes (s : string) : int =
  (Char.code (String.unsafe_get s 24) lsl 48)
  lor (Char.code (String.unsafe_get s 25) lsl 40)
  lor (Char.code (String.unsafe_get s 26) lsl 32)
  lor (Char.code (String.unsafe_get s 27) lsl 24)
  lor (Char.code (String.unsafe_get s 28) lsl 16)
  lor (Char.code (String.unsafe_get s 29) lsl 8)
  lor Char.code (String.unsafe_get s 30)

type 'v core = {
  c_cap : int;  (* capacity_bytes *)
  c_slots : int;
  c_mask : int;  (* the key table's size - 1 *)
  c_tbl : (int, Bigarray.int_elt, Bigarray.c_layout) Bigarray.Array1.t;
  c_addr : string array;  (* "" when the slot is free *)
  c_val : 'v option array;  (* None when the slot is free *)
  c_weight : int array;
  c_ref : Bytes.t;  (* the CLOCK reference bit, '\000' or '\001' *)
  c_free : int array;  (* a stack of free slots *)
  mutable c_free_top : int;
  mutable c_hand : int;
  mutable c_bytes : int;
  mutable c_entries : int;
  mutable c_hits : int;
  mutable c_misses : int;
  mutable c_evictions : int;
  mutable c_slot_evictions : int;
  mutable c_admissions : int;
  mutable c_refusals : int;
}

let create_core ~(slots : int) ~(capacity_bytes : int) : 'v core =
  let n = if slots < 1 then 1 else slots in
  let cap = if capacity_bytes < 0 then 0 else capacity_bytes in
  let want = int_of_float (ceil (float_of_int n /. max_load)) in
  let h = pow2_at_least (if want < min_slots then min_slots else want) in
  let tbl = Bigarray.Array1.create Bigarray.int Bigarray.c_layout h in
  Bigarray.Array1.fill tbl 0;
  {
    c_cap = cap;
    c_slots = n;
    c_mask = h - 1;
    c_tbl = tbl;
    c_addr = Array.make n "";
    c_val = Array.make n None;
    c_weight = Array.make n 0;
    c_ref = Bytes.make n '\000';
    c_free = Array.init n (fun i -> n - 1 - i);
    c_free_top = n;
    c_hand = 0;
    c_bytes = 0;
    c_entries = 0;
    c_hits = 0;
    c_misses = 0;
    c_evictions = 0;
    c_slot_evictions = 0;
    c_admissions = 0;
    c_refusals = 0;
  }

let derived_slots (capacity_bytes : int) : int =
  let n = capacity_bytes / default_entry_bytes in
  if n < min_slots then min_slots else if n > max_derived_slots then max_derived_slots else n

(* ---- the key table ---- *)

let ideal (c : 'v core) (slot : int) : int = hash_bytes c.c_addr.(slot) land c.c_mask

(* The table position holding [a], or -1.  Terminates: the table is at load <= 0.6, so an
   empty position always exists.  Written as a tail recursion and not as a `while` over three
   `ref`s so that a HIT ALLOCATES NOTHING (CA3): `ocamlopt` turns this into a loop over
   registers, where the refs would each cost a two-word block on the minor heap. *)
let rec probe (c : 'v core) (a : string) (i : int) : int =
  let v = Bigarray.Array1.unsafe_get c.c_tbl i in
  if v = 0 then -1
  else if String.equal (Array.unsafe_get c.c_addr (v - 1)) a then i
  else probe c a ((i + 1) land c.c_mask)

let table_find (c : 'v core) (a : string) : int = probe c a (hash_bytes a land c.c_mask)

let table_insert (c : 'v core) (a : string) (slot : int) : unit =
  let i = ref (hash_bytes a land c.c_mask) in
  while Bigarray.Array1.unsafe_get c.c_tbl !i <> 0 do
    i := (!i + 1) land c.c_mask
  done;
  Bigarray.Array1.unsafe_set c.c_tbl !i (slot + 1)

(* Knuth 6.4 R: empty position j, then pull forward the first entry past it whose ideal
   position is not cyclically inside (j, i].  No tombstone is ever written. *)
let table_delete (c : 'v core) (at : int) : unit =
  let j = ref at in
  let finished = ref false in
  while not !finished do
    Bigarray.Array1.unsafe_set c.c_tbl !j 0;
    let i = ref ((!j + 1) land c.c_mask) in
    let settled = ref false in
    while not !settled do
      let v = Bigarray.Array1.unsafe_get c.c_tbl !i in
      if v = 0 then (
        settled := true;
        finished := true)
      else begin
        let k = ideal c (v - 1) in
        let inside = if !j < !i then !j < k && k <= !i else !j < k || k <= !i in
        if inside then i := (!i + 1) land c.c_mask
        else begin
          Bigarray.Array1.unsafe_set c.c_tbl !j v;
          j := !i;
          settled := true
        end
      end
    done
  done

(* ---- slots ---- *)

let push_free (c : 'v core) (slot : int) : unit =
  c.c_free.(c.c_free_top) <- slot;
  c.c_free_top <- c.c_free_top + 1

let pop_free (c : 'v core) : int =
  c.c_free_top <- c.c_free_top - 1;
  c.c_free.(c.c_free_top)

(* Remove the entry the key table holds at position [at].  Not an eviction: the caller says
   what it was. *)
let remove_at (c : 'v core) (at : int) : unit =
  let slot = Bigarray.Array1.unsafe_get c.c_tbl at - 1 in
  table_delete c at;
  c.c_bytes <- c.c_bytes - c.c_weight.(slot);
  c.c_entries <- c.c_entries - 1;
  c.c_addr.(slot) <- "";
  c.c_val.(slot) <- None;
  c.c_weight.(slot) <- 0;
  Bytes.unsafe_set c.c_ref slot '\000';
  push_free c slot

(* CA3: advance the hand, clearing set reference bits, and evict the first occupied slot whose
   bit is clear.  Returns false when there was nothing to evict. *)
let evict_one (c : 'v core) ~(slot_bound : bool) : bool =
  if c.c_entries = 0 then false
  else begin
    let n = c.c_slots in
    let victim = ref (-1) in
    let guard = ref ((2 * n) + 2) in
    while !victim < 0 && !guard > 0 do
      decr guard;
      let h = c.c_hand in
      c.c_hand <- (if h + 1 = n then 0 else h + 1);
      match c.c_val.(h) with
      | None -> ()
      | Some _ ->
        if Bytes.unsafe_get c.c_ref h <> '\000' then Bytes.unsafe_set c.c_ref h '\000'
        else victim := h
    done;
    if !victim < 0 then false
    else begin
      let at = table_find c c.c_addr.(!victim) in
      if at < 0 then false
      else begin
        remove_at c at;
        c.c_evictions <- c.c_evictions + 1;
        if slot_bound then c.c_slot_evictions <- c.c_slot_evictions + 1;
        true
      end
    end
  end

(* ---- the operations ---- *)

let core_find (c : 'v core) (a : string) : 'v option =
  let at = table_find c a in
  if at < 0 then begin
    c.c_misses <- c.c_misses + 1;
    None
  end
  else begin
    let slot = Bigarray.Array1.unsafe_get c.c_tbl at - 1 in
    c.c_hits <- c.c_hits + 1;
    Bytes.unsafe_set c.c_ref slot '\001';
    Array.unsafe_get c.c_val slot
  end

let core_mem (c : 'v core) (a : string) : bool = table_find c a >= 0

let core_add (c : 'v core) (a : string) (v : 'v) (w : int) : unit =
  let w = if w < 0 then 0 else w in
  if w > c.c_cap then c.c_refusals <- c.c_refusals + 1
  else begin
    (* CA4: a replace is a remove and an insert, so `entries` does not move and the weight
       moves by the difference of the two values' weights and by nothing else. *)
    (match table_find c a with -1 -> () | at -> remove_at c at);
    while c.c_bytes + w > c.c_cap && c.c_entries > 0 do
      ignore (evict_one c ~slot_bound:false)
    done;
    if c.c_free_top = 0 then ignore (evict_one c ~slot_bound:true);
    if c.c_free_top = 0 || c.c_bytes + w > c.c_cap then c.c_refusals <- c.c_refusals + 1
    else begin
      let slot = pop_free c in
      c.c_addr.(slot) <- a;
      c.c_val.(slot) <- Some v;
      c.c_weight.(slot) <- w;
      (* CA3: an entry enters with its reference bit CLEAR and earns it on its first hit.  The
         alternative — enter with the bit set — gives every admission a free second chance, so
         a scan of N + 1 distinct addresses through a cache of N slots evicts the entry
         admitted one step ago instead of the oldest, and a hit is no longer what buys
         survival.  With the bit clear, an unread entry is FIFO and a read one is not. *)
      Bytes.unsafe_set c.c_ref slot '\000';
      table_insert c a slot;
      c.c_bytes <- c.c_bytes + w;
      c.c_entries <- c.c_entries + 1;
      c.c_admissions <- c.c_admissions + 1
    end
  end

let core_drop (c : 'v core) : unit =
  Bigarray.Array1.fill c.c_tbl 0;
  Array.fill c.c_addr 0 c.c_slots "";
  Array.fill c.c_val 0 c.c_slots None;
  Array.fill c.c_weight 0 c.c_slots 0;
  Bytes.fill c.c_ref 0 c.c_slots '\000';
  for i = 0 to c.c_slots - 1 do
    c.c_free.(i) <- c.c_slots - 1 - i
  done;
  c.c_free_top <- c.c_slots;
  c.c_hand <- 0;
  c.c_bytes <- 0;
  c.c_entries <- 0

let core_reset_counters (c : 'v core) : unit =
  c.c_hits <- 0;
  c.c_misses <- 0;
  c.c_evictions <- 0;
  c.c_slot_evictions <- 0;
  c.c_admissions <- 0;
  c.c_refusals <- 0

let occupied_slot (c : 'v core) (s : int) : bool =
  match Array.unsafe_get c.c_val s with None -> false | Some _ -> true

let core_invariant (c : 'v core) : (unit, string) result =
  if c.c_bytes > c.c_cap then
    Error (Printf.sprintf "bytes %d > capacity_bytes %d" c.c_bytes c.c_cap)
  else if c.c_entries > c.c_slots then
    Error (Printf.sprintf "entries %d > slots %d" c.c_entries c.c_slots)
  else if c.c_bytes < 0 then Error (Printf.sprintf "bytes %d < 0" c.c_bytes)
  else begin
    let live = ref 0 and weight = ref 0 in
    for s = 0 to c.c_slots - 1 do
      if occupied_slot c s then begin
        incr live;
        weight := !weight + c.c_weight.(s)
      end
    done;
    let occupied = ref 0 in
    for i = 0 to c.c_mask do
      if Bigarray.Array1.get c.c_tbl i <> 0 then incr occupied
    done;
    if !live <> c.c_entries then
      Error (Printf.sprintf "occupied slots %d <> entries %d" !live c.c_entries)
    else if !weight <> c.c_bytes then
      Error (Printf.sprintf "sum of weights %d <> bytes %d" !weight c.c_bytes)
    else if !occupied <> c.c_entries then
      Error (Printf.sprintf "key table holds %d <> entries %d" !occupied c.c_entries)
    else if c.c_free_top <> c.c_slots - c.c_entries then
      Error
        (Printf.sprintf "free stack %d <> slots %d - entries %d" c.c_free_top c.c_slots
           c.c_entries)
    else begin
      (* Every occupied slot is reachable from the key table by its own address, and the table
         points back at it: the backward-shift deletion's whole obligation. *)
      let bad = ref "" in
      for s = 0 to c.c_slots - 1 do
        if occupied_slot c s && String.equal !bad "" then begin
          let at = table_find c c.c_addr.(s) in
          if at < 0 then bad := Printf.sprintf "slot %d is not in the key table" s
          else if Bigarray.Array1.get c.c_tbl at - 1 <> s then
            bad := Printf.sprintf "slot %d is shadowed in the key table" s
        end
      done;
      if String.equal !bad "" then Ok () else Error !bad
    end
  end

(* ============================================================ 2. the bytes tier *)

module Bytes_cache = struct
  type t = string core

  type stats = {
    hits : int;
    misses : int;
    evictions : int;
    slot_bound_evictions : int;
    admissions : int;
    refusals : int;
    bytes : int;
    entries : int;
    slots : int;
    capacity_bytes : int;
  }

  let create_sized ~slots ~capacity_bytes = create_core ~slots ~capacity_bytes
  let create ~capacity_bytes = create_sized ~slots:(derived_slots capacity_bytes) ~capacity_bytes
  let find (t : t) (a : E4_addr.Addr.t) : string option = core_find t (E4_addr.Addr.bytes a)
  let mem (t : t) (a : E4_addr.Addr.t) : bool = core_mem t (E4_addr.Addr.bytes a)

  let add (t : t) (a : E4_addr.Addr.t) (v : string) : unit =
    core_add t (E4_addr.Addr.bytes a) v (String.length v)

  let get (t : t) (ro : E4_cas.ro) (a : E4_addr.Addr.t) : string option =
    match find t a with
    | Some v -> Some v
    | None -> (
      match E4_cas.get_bytes ro a with
      | None -> None
      | Some v ->
        add t a v;
        Some v)

  let drop = core_drop
  let reset_counters = core_reset_counters
  let bytes (t : t) = t.c_bytes
  let entries (t : t) = t.c_entries
  let slots (t : t) = t.c_slots
  let capacity_bytes (t : t) = t.c_cap
  let invariant = core_invariant

  let stats (t : t) : stats =
    {
      hits = t.c_hits;
      misses = t.c_misses;
      evictions = t.c_evictions;
      slot_bound_evictions = t.c_slot_evictions;
      admissions = t.c_admissions;
      refusals = t.c_refusals;
      bytes = t.c_bytes;
      entries = t.c_entries;
      slots = t.c_slots;
      capacity_bytes = t.c_cap;
    }

  let hit_ratio (s : stats) : float =
    let n = s.hits + s.misses in
    if n = 0 then 0.0 else float_of_int s.hits /. float_of_int n
end

let stats_of_core (c : 'v core) : Bytes_cache.stats =
  {
    Bytes_cache.hits = c.c_hits;
    misses = c.c_misses;
    evictions = c.c_evictions;
    slot_bound_evictions = c.c_slot_evictions;
    admissions = c.c_admissions;
    refusals = c.c_refusals;
    bytes = c.c_bytes;
    entries = c.c_entries;
    slots = c.c_slots;
    capacity_bytes = c.c_cap;
  }

(* ============================================================ 3. the decoded tier *)

module type VALUE = sig
  type t

  val kind : E4_kind.t
  val decode : string -> t option
  val weight : t -> int
end

module Decoded (V : VALUE) = struct
  type t = V.t core

  let create_sized ~slots ~capacity_bytes = create_core ~slots ~capacity_bytes
  let create ~capacity_bytes = create_sized ~slots:(derived_slots capacity_bytes) ~capacity_bytes
  let find (t : t) (a : E4_addr.Addr.t) : V.t option = core_find t (E4_addr.Addr.bytes a)
  let mem (t : t) (a : E4_addr.Addr.t) : bool = core_mem t (E4_addr.Addr.bytes a)

  let add (t : t) (a : E4_addr.Addr.t) (v : V.t) : unit =
    core_add t (E4_addr.Addr.bytes a) v (V.weight v)

  (* D5: the kind is checked, so a payload of another shape is never handed to V.decode. *)
  let get (t : t) (ro : E4_cas.ro) (a : E4_addr.Addr.t) : V.t option =
    match find t a with
    | Some v -> Some v
    | None -> (
      match E4_cas.get_node ro a with
      | None -> None
      | Some n ->
        if not (E4_kind.equal n.E4_node.kind V.kind) then None
        else (
          match V.decode n.E4_node.payload with
          | None -> None
          | Some v ->
            add t a v;
            Some v))

  let drop = core_drop
  let reset_counters = core_reset_counters
  let bytes (t : t) = t.c_bytes
  let entries (t : t) = t.c_entries
  let slots (t : t) = t.c_slots
  let capacity_bytes (t : t) = t.c_cap
  let invariant = core_invariant
  let stats (t : t) : Bytes_cache.stats = stats_of_core t
end

(* ============================================================ 4. a ready instance *)

module Node_value = struct
  type t = E4_node.t

  let kind = E4_kind.Program

  let decode (payload : string) : t option =
    match E4_node.payload_ok payload with
    | Error _ -> None
    | Ok () ->
      Some
        (E4_node.make ~version:0 ~kind:E4_kind.Program ~spec:E4_node.zero_digest ~payload)

  let weight (n : t) : int = 34 + String.length n.E4_node.payload
end

module Node_cache = struct
  type t = E4_node.t core

  let create_sized ~slots ~capacity_bytes = create_core ~slots ~capacity_bytes
  let create ~capacity_bytes = create_sized ~slots:(derived_slots capacity_bytes) ~capacity_bytes
  let find (t : t) (a : E4_addr.Addr.t) : E4_node.t option = core_find t (E4_addr.Addr.bytes a)
  let mem (t : t) (a : E4_addr.Addr.t) : bool = core_mem t (E4_addr.Addr.bytes a)

  let add (t : t) (a : E4_addr.Addr.t) (n : E4_node.t) : unit =
    core_add t (E4_addr.Addr.bytes a) n (34 + String.length n.E4_node.payload)

  let get (t : t) (ro : E4_cas.ro) (a : E4_addr.Addr.t) : E4_node.t option =
    match find t a with
    | Some n -> Some n
    | None -> (
      match E4_cas.get_node ro a with
      | None -> None
      | Some n ->
        add t a n;
        Some n)

  let drop = core_drop
  let reset_counters = core_reset_counters
  let bytes (t : t) = t.c_bytes
  let entries (t : t) = t.c_entries
  let slots (t : t) = t.c_slots
  let capacity_bytes (t : t) = t.c_cap
  let invariant = core_invariant
  let stats (t : t) : Bytes_cache.stats = stats_of_core t
end
