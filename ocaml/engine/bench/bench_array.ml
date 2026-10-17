(* bench_array.ml -- slice 3.1 of the OCaml estate refactor: how generated code should spell a
   Lean `Array` (decision D-3), by measurement.

   What it is: one probe program. A Lean `Array` is an OCaml `list` today, the shim
   (src/OCaml5/Lcnf/TypeRows.lean): `Array.push` is `xs @ [x]` and `Array.uget` is `List.nth`
   (src/OCaml5/Lcnf/Builtins.lean). Three spellings, the first at two chunk sizes, implement
   one signature, `SEQ` (the operations the Array rows need, with `set` and `replicate`), and
   each is measured against the shim:
     chunked-256  the chunked spine of E4_log.Vec (ocaml/engine/e4_log.ml), generalized with
                  set, replicate and fold: frozen 256-element chunks under a Map from chunk
                  number, and an open tail list, most recent first;
     chunked-32   the same spine with 32-element chunks, to price `set` against `get`;
     racc         a reversed immutable accumulator, converted at the read sites;
     reroot       a rerooting array (Baker 1991; Conchon and Filliatre 2007), a reference only.
   Every answer is checked against the shim's: the shim itself where it runs (n <= 10^4), and
   above that the same list built in linear time (`List.init`), which is the value the shim's
   rows produce. A spelling that answers differently is reported OUT.
   Depends on: Stdlib, Unix.

   Properties:
   A1  Every spelling answers as the shim on every operation and size it runs, or the run
       reports it OUT.                                         tested (every cell's check)
   A2  The three pure spellings write an array only inside the operation that creates it:
       `chunked` copies a frozen chunk before a `set`, so a retained version and its siblings
       keep their observations after later updates (rule 8).            by construction;
       tested (branch, old, set, replicate-shared)
   A3  `reroot` breaks rule 8 on purpose: a read of one version rewrites the shared buffer and
       the version nodes, so a retained sibling's representation changes even though its
       answers do not.                                                 tested (reroot-en5)
   A4  Nothing is asserted about the numbers: they are printed.          by construction

   Method: best of `reps` runs (default 3) by Unix.gettimeofday, native code, a full major
   collection before each run; a cell whose first run takes over five seconds runs once.
   Words: allocated is Gc.counters' minor + major - promoted over the build, read after a
   minor collection; retained is Gc.stat's live words after a full major collection, with
   the result held, less the same before. A cell whose cost is quadratic in n for that
   spelling is not run above n = 10^4 and prints "-".

   It is an EXECUTABLE, not a test: `dune test` does not run it.
   Run: cd ocaml && opam exec --switch=effect4 -- dune build engine/bench &&
        ./_build/default/engine/bench/bench_array.exe [reps] *)

let reps = if Array.length Sys.argv > 1 then int_of_string Sys.argv.(1) else 3
let sizes = [ 1_000; 10_000; 100_000; 1_000_000 ]
let quadratic_cap = 10_000
let switches = 100

(* The operations the Array rows of src/OCaml5/Lcnf/Builtins.lean need, with `set` (`uset`)
   and `replicate`. `get_exn` and `set_exn` take an index the caller has proved in range, as
   Lean's `uget`, `getInternal` and `uset` do. `quadratic` names the operations of this probe
   whose cost is quadratic in n for this spelling. *)
module type SEQ = sig
  type 'a t

  val name : string
  val empty : unit -> 'a t
  val push : 'a t -> 'a -> 'a t
  val size : 'a t -> int
  val get_exn : 'a t -> int -> 'a
  val set_exn : 'a t -> int -> 'a -> 'a t
  val to_list : 'a t -> 'a list
  val of_list : 'a list -> 'a t
  val replicate : int -> 'a -> 'a t
  val append_list : 'a t -> 'a list -> 'a t
  val fold_left : ('b -> 'a -> 'b) -> 'b -> 'a t -> 'b
  val quadratic : string list
end

(* ----------------------------------------------------------------------------- the shim *)

(* The rows as the route spells them today: `Array.push` is `xs @ [x]`, `Array.size` is
   `List.length`, `Array.uget` and `getInternal` are `List.nth`, `appendList` is `@`. There is
   no `set` row; this is the list spelling of one (`List.set`). *)
module Shim : SEQ = struct
  type 'a t = 'a list

  let name = "shim"
  let empty () = []
  let push xs x = xs @ [ x ]
  let size = List.length
  let get_exn = List.nth

  let rec set_exn xs i v =
    match xs with [] -> invalid_arg "Shim.set_exn" | x :: r -> if i = 0 then v :: r else x :: set_exn r (i - 1) v

  let to_list xs = xs
  let of_list xs = xs
  let replicate n v = List.init (max n 0) (fun _ -> v)
  let append_list = ( @ )
  let fold_left = List.fold_left
  let quadratic = [ "push"; "loop"; "reads"; "foldr"; "old"; "set" ]
end

(* --------------------------------------------------------------- the chunked spine *)

let rec replace_nth k v = function
  | [] -> invalid_arg "replace_nth"
  | x :: r -> if k = 0 then v :: r else x :: replace_nth (k - 1) v r

(* E4_log.Vec's carrier and its `append`, verbatim but for the chunk size, with `set`,
   `replicate`, `fold_left` and a linear `to_list` added. No array is written after the
   operation that creates it: `push` fills a fresh chunk, and `set` writes a copy. *)
module Chunked (C : sig
  val bits : int
end) : SEQ = struct
  module Im = Map.Make (Int)

  let bits = C.bits
  let chunk = 1 lsl bits
  let mask = chunk - 1

  type 'a t = {
    full : 'a array Im.t;  (** chunk number -> its frozen elements *)
    tail : 'a list;  (** the open chunk, most recent first *)
    tail_len : int;
    len : int;
  }

  let name = Printf.sprintf "chunked-%d" chunk
  let empty () = { full = Im.empty; tail = []; tail_len = 0; len = 0 }
  let size t = t.len

  let push t x =
    let tail = x :: t.tail and tail_len = t.tail_len + 1 and len = t.len + 1 in
    if tail_len = chunk then begin
      let a = Array.make chunk x in
      let rec fill i = function
        | [] -> ()
        | y :: rest ->
          a.(i) <- y;
          fill (i - 1) rest
      in
      fill (chunk - 1) tail;
      { full = Im.add ((len - 1) lsr bits) a t.full; tail = []; tail_len = 0; len }
    end
    else { t with tail; tail_len; len }

  (* The open tail holds positions [len - tail_len, len - 1] reversed, and every chunk below
     it is present, so a read takes `Map.find` and allocates no option (E4_log.Vec's `get`
     takes `find_opt`). *)
  let in_tail t i = i >= t.len - t.tail_len

  let get_exn t i =
    if i < 0 || i >= t.len then invalid_arg "Chunked.get_exn"
    else if in_tail t i then List.nth t.tail (t.len - 1 - i)
    else Array.unsafe_get (Im.find (i lsr bits) t.full) (i land mask)

  let set_exn t i v =
    if i < 0 || i >= t.len then invalid_arg "Chunked.set_exn"
    else if in_tail t i then { t with tail = replace_nth (t.len - 1 - i) v t.tail }
    else begin
      let a = Array.copy (Im.find (i lsr bits) t.full) in
      a.(i land mask) <- v;
      { t with full = Im.add (i lsr bits) a t.full }
    end

  (* Descending, so the list is built by consing and never reversed but for the tail. *)
  let to_list t =
    let chunks = Im.fold (fun _ a acc -> a :: acc) t.full [] in
    let rec cons_chunk a j acc = if j < 0 then acc else cons_chunk a (j - 1) (Array.unsafe_get a j :: acc) in
    List.fold_left (fun acc a -> cons_chunk a (chunk - 1) acc) (List.rev t.tail) chunks

  let fold_left f init t =
    List.fold_left f (Im.fold (fun _ a acc -> Array.fold_left f acc a) t.full init) (List.rev t.tail)

  let append_list t xs = List.fold_left push t xs
  let of_list xs = append_list (empty ()) xs

  (* One frozen chunk serves every full chunk: nothing writes it, and `set` copies it. *)
  let replicate n v =
    if n <= 0 then empty ()
    else
      let a = Array.make chunk v and full_chunks = n lsr bits and tail_len = n land mask in
      let rec chunks c m = if c = full_chunks then m else chunks (c + 1) (Im.add c a m) in
      { full = chunks 0 Im.empty; tail = List.init tail_len (fun _ -> v); tail_len; len = n }

  let quadratic = []
end

module Chunked_256 = Chunked (struct
  let bits = 8
end)

module Chunked_32 = Chunked (struct
  let bits = 5
end)

(* ------------------------------------------------------- the reversed accumulator *)

(* Push is a cons; a read in index order converts, walking from the newest element. *)
module Racc : SEQ = struct
  type 'a t = { rev : 'a list; len : int }

  let name = "racc"
  let empty () = { rev = []; len = 0 }
  let push t x = { rev = x :: t.rev; len = t.len + 1 }
  let size t = t.len

  let get_exn t i =
    if i < 0 || i >= t.len then invalid_arg "Racc.get_exn" else List.nth t.rev (t.len - 1 - i)

  let set_exn t i v =
    if i < 0 || i >= t.len then invalid_arg "Racc.set_exn" else { t with rev = replace_nth (t.len - 1 - i) v t.rev }

  let to_list t = List.rev t.rev
  let of_list xs = { rev = List.rev xs; len = List.length xs }
  let replicate n v = { rev = List.init (max n 0) (fun _ -> v); len = max n 0 }
  let append_list t xs = List.fold_left push t xs
  let fold_left f init t = List.fold_left f init (List.rev t.rev)
  let quadratic = [ "reads"; "foldr"; "old"; "set" ]
end

(* -------------------------------------------------------------- the rerooting array *)

(* One mutable buffer, held by the current version (the root); every other version is a diff
   towards it. A read or an update of any version first makes it the root, inverting each
   diff on the way, so every version answers right, but reading one version rewrites the
   nodes and the buffer that its siblings share. There is no polymorphic empty value: an
   empty array must be allocated, so `empty` takes `()`. *)
module Reroot = struct
  type 'a t = 'a node ref

  and 'a node =
    | Root of 'a array * int  (** the buffer and this version's length *)
    | Set of int * 'a * 'a t  (** the next version with this index holding this value *)
    | Pushed of 'a * 'a t  (** the next version with this value pushed *)
    | Popped of 'a t  (** the next version without its last element *)

  let name = "reroot"

  let grow a v =
    let b = Array.make (max 8 (2 * Array.length a)) v in
    Array.blit a 0 b 0 (Array.length a);
    b

  (* Walk to the root, then invert the diffs from the root's neighbour back to [t], so the
     walk and the inversion are both loops (a version 10^6 diffs away is common here). *)
  let reroot (t : 'a t) : 'a array * int =
    let rec path t acc =
      match !t with
      | Root (a, n) -> (a, n, acc)
      | Set (_, _, next) | Pushed (_, next) | Popped next -> path next (t :: acc)
    in
    let a, n, todo = path t [] in
    List.fold_left
      (fun (a, n) node ->
        match !node with
        | Set (i, v, next) ->
          let old = a.(i) in
          a.(i) <- v;
          node := Root (a, n);
          next := Set (i, old, node);
          (a, n)
        | Pushed (v, next) ->
          let a = if n < Array.length a then a else grow a v in
          a.(n) <- v;
          node := Root (a, n + 1);
          next := Popped node;
          (a, n + 1)
        | Popped next ->
          node := Root (a, n - 1);
          next := Pushed (a.(n - 1), node);
          (a, n - 1)
        | Root _ -> (a, n))
      (a, n) todo

  let empty () = ref (Root ([||], 0))

  let push t v =
    let a, n = reroot t in
    let a = if n < Array.length a then a else grow a v in
    a.(n) <- v;
    let res = ref (Root (a, n + 1)) in
    t := Popped res;
    res

  let size t = snd (reroot t)

  let get_exn t i =
    let a, n = reroot t in
    if i < 0 || i >= n then invalid_arg "Reroot.get_exn" else a.(i)

  let set_exn t i v =
    let a, n = reroot t in
    if i < 0 || i >= n then invalid_arg "Reroot.set_exn"
    else begin
      let old = a.(i) in
      a.(i) <- v;
      let res = ref (Root (a, n)) in
      t := Set (i, old, res);
      res
    end

  let to_list t =
    let a, n = reroot t in
    List.init n (fun i -> a.(i))

  let of_list xs =
    let a = Array.of_list xs in
    ref (Root (a, Array.length a))

  let replicate n v = ref (Root (Array.make (max n 0) v, max n 0))
  let append_list t xs = List.fold_left push t xs

  let fold_left f init t =
    let a, n = reroot t in
    let acc = ref init in
    for i = 0 to n - 1 do
      acc := f !acc a.(i)
    done;
    !acc

  let is_root t = match !t with Root _ -> true | Set _ | Pushed _ | Popped _ -> false
  let quadratic = []
end

module Reroot_seq : SEQ = Reroot

(* ------------------------------------------------------------------- the measuring *)

type cell = Skipped | Ran of float * bool  (** best milliseconds, and whether every answer was the shim's *)

let results : ((string * string * int) * cell) list ref = ref []
let memory : ((string * int) * (float option * float)) list ref = ref []
let checks : (string * string * bool) list ref = ref []
let ints_equal = List.equal Int.equal
let init n = List.init n Fun.id

(* Best of [reps] runs; a cell whose first run takes over five seconds runs once. *)
let best (f : unit -> 'r) : float * 'r =
  let run () =
    Gc.full_major ();
    let t0 = Unix.gettimeofday () in
    let r = f () in
    ((Unix.gettimeofday () -. t0) *. 1000., r)
  in
  let rec go k ms r =
    if k <= 1 then (ms, r)
    else
      let ms', r' = run () in
      go (k - 1) (Float.min ms ms') r'
  in
  let ms, r = run () in
  if ms > 5000. then (ms, r) else go reps ms r

(* OCaml 5 adds the minor heap's words to the counters at a minor collection, so one is run
   before each reading. *)
let allocated_words (f : unit -> 'r) : 'r * float =
  Gc.full_major ();
  let mi0, pr0, ma0 = Gc.counters () in
  let r = f () in
  Gc.minor ();
  let mi1, pr1, ma1 = Gc.counters () in
  (r, mi1 -. mi0 +. (ma1 -. ma0) -. (pr1 -. pr0))

let retained_words (f : unit -> 'v) : float =
  Gc.full_major ();
  let w0 = (Gc.stat ()).live_words in
  let v = f () in
  Gc.full_major ();
  let w1 = (Gc.stat ()).live_words in
  ignore (Sys.opaque_identity v);
  float_of_int (w1 - w0)

module Run (S : SEQ) = struct
  let build n =
    let rec go i t = if i = n then t else go (i + 1) (S.push t i) in
    go 0 (S.empty ())

  let cell op n (setup : unit -> 'v) (run : 'v -> 'r) (ok : 'v -> 'r -> bool) =
    let c =
      if List.mem op S.quadratic && n > quadratic_cap then Skipped
      else
        let v = setup () in
        let ms, r = best (fun () -> run v) in
        Ran (ms, ok v r)
    in
    results := ((S.name, op, n), c) :: !results

  (* [v1] holds 0 .. n-1, and [v2] is [v1] after n more pushes. *)
  let old_and_new n =
    let v1 = S.of_list (init n) in
    (v1, S.append_list v1 (List.init n (fun i -> n + i)))

  let ops n =
    cell "push" n Fun.id (fun () -> build n) (fun () t -> S.size t = n && ints_equal (S.to_list t) (init n));
    cell "loop" n Fun.id (fun () -> S.to_list (build n)) (fun () l -> ints_equal l (init n));
    cell "reads" n
      (fun () -> S.of_list (init n))
      (fun v ->
        let bad = ref 0 in
        for i = 0 to n - 1 do
          if S.get_exn v i <> i then incr bad
        done;
        !bad)
      (fun _ bad -> bad = 0);
    cell "foldr" n
      (fun () -> S.of_list (init n))
      (fun v ->
        let bad = ref 0 in
        for i = n - 1 downto 0 do
          if S.get_exn v i <> i then incr bad
        done;
        !bad)
      (fun _ bad -> bad = 0);
    cell "old" n
      (fun () -> old_and_new n)
      (fun (v1, v2) ->
        let bad = ref 0 in
        for i = 0 to n - 1 do
          if S.get_exn v1 i <> i then incr bad
        done;
        if S.get_exn v2 ((2 * n) - 1) <> (2 * n) - 1 then incr bad;
        !bad)
      (fun (v1, v2) bad -> bad = 0 && ints_equal (S.to_list v1) (init n) && ints_equal (S.to_list v2) (init (2 * n)));
    cell "branch" n
      (fun () -> S.of_list (init n))
      (fun v ->
        let a = S.push v (-1) in
        let b = S.push v (-2) in
        (S.to_list a, S.to_list b, S.to_list v))
      (fun _ (a, b, v) ->
        ints_equal a (init n @ [ -1 ]) && ints_equal b (init n @ [ -2 ]) && ints_equal v (init n));
    cell "set" n
      (fun () -> S.of_list (init n))
      (fun v ->
        let w = ref v in
        for i = 0 to n - 1 do
          w := S.set_exn !w i (2 * i)
        done;
        !w)
      (fun v w -> ints_equal (S.to_list w) (List.init n (fun i -> 2 * i)) && ints_equal (S.to_list v) (init n));
    cell "alternate" n
      (fun () -> old_and_new n)
      (fun (v1, v2) ->
        let bad = ref 0 in
        for k = 0 to switches - 1 do
          let i = k mod n in
          if S.get_exn v1 i <> i then incr bad;
          if S.get_exn v2 (n + i) <> n + i then incr bad
        done;
        !bad)
      (fun _ bad -> bad = 0)

  let words n =
    let push_quadratic = List.mem "push" S.quadratic && n > quadratic_cap in
    let allocated = if push_quadratic then None else Some (snd (allocated_words (fun () -> build n))) in
    let retained =
      retained_words (fun () -> if push_quadratic then S.of_list (init n) else build n)
    in
    memory := ((S.name, n), (allocated, retained)) :: !memory

  (* The rest of the interface, checked once per size against the shim's lists. *)
  let interface n =
    let check what ok = checks := (S.name, Printf.sprintf "%s at %d" what n, ok) :: !checks in
    let r = S.replicate n 7 in
    check "replicate" (ints_equal (S.to_list r) (List.init n (fun _ -> 7)));
    let r' = S.set_exn r 0 8 in
    check "replicate-shared: a set leaves the replicated original and its other chunks"
      (ints_equal (S.to_list r) (List.init n (fun _ -> 7))
      && ints_equal (S.to_list r') (List.init n (fun i -> if i = 0 then 8 else 7)));
    check "fold_left" (S.fold_left ( + ) 0 (S.of_list (init n)) = List.fold_left ( + ) 0 (init n));
    check "append_list" (ints_equal (S.to_list (S.append_list (S.of_list (init n)) [ n; n + 1 ])) (init (n + 2)));
    check "of_list and to_list" (ints_equal (S.to_list (S.of_list (init n))) (init n));
    check "size" (S.size (S.of_list (init n)) = n)

  let all () =
    List.iter
      (fun n ->
        ops n;
        words n;
        interface n)
      sizes
end

(* A3: reading a retained version rewrites its sibling. *)
let reroot_en5 () =
  let v = Reroot.of_list (init 10) in
  let a = Reroot.push v 100 in
  let b = Reroot.push v 200 in
  let b_root_before = Reroot.is_root b in
  let a_reads = Reroot.get_exn a 10 in
  let b_root_after = Reroot.is_root b and a_root_after = Reroot.is_root a in
  let b_reads = Reroot.get_exn b 10 in
  Printf.printf
    "reroot-en5: b is the root before a read of a: %b; after it, a is the root: %b and b is a diff: %b; \
     the answers stay right: a[10] = %d, b[10] = %d\n"
    b_root_before a_root_after (not b_root_after) a_reads b_reads;
  checks :=
    ("reroot", "en5: reading a rewrites b's node, answers unchanged",
      b_root_before && a_root_after && (not b_root_after) && a_reads = 100 && b_reads = 200)
    :: !checks

(* --------------------------------------------------------------------- the report *)

let spellings = [ Shim.name; Chunked_256.name; Chunked_32.name; Racc.name; Reroot.name ]

let ops_described =
  [ ("push", "n pushes onto an empty array");
    ("loop", "n pushes, then one to_list: the shape of the generated filterMapTR/takeTR loops");
    ("reads", "a read of every index, in order");
    ("foldr", "a read of every index, last first: Array.foldrMUnsafe.fold, behind List.foldrTR, zipIdxTR, setTR, eraseTR");
    ("old", "every index of a version, after n later pushes onto it, then the newest's last");
    ("branch", "two pushes onto one shared version, then all three read in full");
    ("set", "a set of every index, in order");
    ("alternate", Printf.sprintf "%d reads alternating between an old version and a newer one" switches) ]

let find_cell s op n =
  match List.find_opt (fun ((s', op', n'), _) -> String.equal s s' && String.equal op op' && n = n') !results with
  | Some (_, c) -> c
  | None -> Skipped

let print_ops () =
  List.iter
    (fun (op, what) ->
      Printf.printf "\n%s: %s (ms, best of %d)\n" op what reps;
      Printf.printf "%10s" "n";
      List.iter (fun s -> Printf.printf " %13s" s) spellings;
      print_newline ();
      List.iter
        (fun n ->
          Printf.printf "%10d" n;
          List.iter
            (fun s ->
              match find_cell s op n with
              | Skipped -> Printf.printf " %13s" "-"
              | Ran (ms, true) -> Printf.printf " %13.3f" ms
              | Ran (ms, false) -> Printf.printf " %9.3f OUT" ms)
            spellings;
          print_newline ())
        sizes)
    ops_described

let print_memory () =
  Printf.printf "\nwords per element: allocated by n pushes / retained by the result\n";
  Printf.printf "%10s" "n";
  List.iter (fun s -> Printf.printf " %15s" s) spellings;
  print_newline ();
  List.iter
    (fun n ->
      Printf.printf "%10d" n;
      List.iter
        (fun s ->
          match List.find_opt (fun ((s', n'), _) -> String.equal s s' && n = n') !memory with
          | None -> Printf.printf " %15s" "?"
          | Some (_, (allocated, retained)) ->
            let per w = w /. float_of_int n in
            let a = match allocated with None -> "-" | Some w -> Printf.sprintf "%.1f" (per w) in
            Printf.printf " %15s" (Printf.sprintf "%s/%.1f" a (per retained)))
        spellings;
      print_newline ())
    sizes

let () =
  Printf.printf "bench_array: OCaml %s, %d-bit words, best of %d, sizes %s\n" Sys.ocaml_version Sys.word_size reps
    (String.concat ", " (List.map string_of_int sizes));
  let module R1 = Run (Shim) in
  let module R2 = Run (Chunked_256) in
  let module R3 = Run (Chunked_32) in
  let module R4 = Run (Racc) in
  let module R5 = Run (Reroot_seq) in
  R1.all ();
  R2.all ();
  R3.all ();
  R4.all ();
  R5.all ();
  reroot_en5 ();
  print_ops ();
  print_memory ();
  let wrong s =
    List.exists (fun ((s', _, _), c) -> String.equal s s' && match c with Ran (_, false) -> true | Ran (_, true) | Skipped -> false) !results
    || List.exists (fun (s', _, ok) -> String.equal s s' && not ok) !checks
  in
  Printf.printf "\nanswers against the shim (every timed cell, and %d interface checks)\n" (List.length !checks);
  List.iter (fun s -> Printf.printf "  %-12s %s\n" s (if wrong s then "OUT: an answer differs" else "every answer is the shim's")) spellings;
  List.iter (fun (s, what, ok) -> if not ok then Printf.printf "  FAILED %s: %s\n" s what) (List.rev !checks)
