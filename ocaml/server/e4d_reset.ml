(* Resetting the avatar's global state between requests.

   `avatar_main.ml` is a one-shot process: it sets the tape, builds one machine, prints one
   TSV and exits, so the module-level mutable state in `deep_fibers.ml`, `deep_stores.ml` and
   `deep_layer.ml` never has to be cleared. A daemon serves many requests in one process, so
   it does.

   The avatar is consumed read-only (seat W1 owns those files), which means this module
   cannot add a `reset` there and instead clears the same fields from outside. Where the
   avatar already offers a reset -- `Deep_stores.store_reset` and `Deep_layer.layers_reset`,
   both of which W1's port added -- that one is called rather than a second copy of it.

   What is cleared, and where it lives:

     Deep_fibers.state          started, cleanups (the two lists the fiber fixture appends to)
     Deep_fibers.handles        the wire's handle space, plus handle_owner and next_handle
     Deep_fibers.Tape           entries, cursor
     Deep_fibers.sink           the service row list
     Deep_fibers.max_ops_before_yield, prevent_yield
     Deep_fibers.body_of_code   the root table a fork resolves through
     Deep_stores.store          the Ref heap, the Deferred store and its due queue, the
                                ScopeStore, the name counter -- through `store_reset`
     Deep_layer.layers          the memo world -- through `layers_reset`
     Corpus_run.globals, masked the corpus interpreter's slots and mask stack

   What is deliberately NOT reset: `Deep_fibers.fuzz_programs`, which is a registry a fuzz
   corpus fills at module-initialisation time and never a per-run value.

   The check that this list is complete is behavioural, not structural:
   `tests/test_client.py` runs the same program twice in one process and asserts the two
   answers are byte-identical. A leaked field shows up as a handle index, a `started` list or
   a memo count that differs on the second run. *)

open Deep_fibers

let reset_state () =
  state.started <- [];
  state.cleanups <- []

let reset_stores () =
  Deep_stores.store_reset ();
  Deep_layer.layers_reset ()

let reset_handles () =
  Hashtbl.reset handles;
  Hashtbl.reset handle_owner;
  next_handle := 0

let reset_rows () = sink := []

let reset_budget () =
  max_ops_before_yield := max_int;
  prevent_yield := false

(* The default root table is the fiber family's numeric body table, exactly the one
   `fibers_fixture.ml` installs at module initialisation. A corpus program overrides it
   through `Corpus_run.install`; a fixture program never does, so the default has to be put
   back before every run or a corpus program's roots would leak into the next request. *)
let reset_roots () =
  body_of_code := Fibers_fixture.body;
  Array.fill Corpus_run.globals 0 (Array.length Corpus_run.globals) Vunit;
  Corpus_run.masked := []

let all () =
  reset_state ();
  reset_stores ();
  reset_handles ();
  reset_rows ();
  reset_budget ();
  reset_roots ()
