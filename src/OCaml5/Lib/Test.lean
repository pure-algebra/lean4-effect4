import OCaml5.Lib.Order
import OCaml5.Lib.Map
import OCaml5.Lib.Set
import OCaml5.Lib.Deque
import OCaml5.Lib.Sexp
import OCaml5.Lib.Derived
import OCaml5.Lib.Stream
import OCaml5.Lib.Eio
import OCaml5.Lib.Picos

/-!
# `OCaml5.LibTest` — the executed witnesses for the library carriers

Status: seat W4 of the 2026-09-04 wave. Report:
`docs/research/2026-09-04-seat-w4-library-carriers.md`. Built with
`lake build OCaml5.LibTest`; every `#guard` and `decide` below is checked at build time by the
kernel, and no declaration in the `Lib/` tree uses `sorry`, `axiom`, `partial` or
`native_decide`.

One section per carrier, in the order of the report. Where a law is proved as a theorem the
witness here is the *executed* instance of it, which is what catches a definition that is
lawful-but-wrong.
-/

set_option autoImplicit false

namespace OCaml5.Lib.Test

open OCaml5.Lib

/-! ## `Order`: the comparator -/

#guard LinOrd.cmp 1 2 == Ordering.lt
#guard LinOrd.cmp 2 2 == Ordering.eq
#guard LinOrd.cmp 3 2 == Ordering.gt
#guard LinOrd.cmp "abc" "abd" == Ordering.lt
#guard LinOrd.cmp "ab" "abc" == Ordering.lt
#guard LinOrd.cmp [1, 2] [1, 2, 3] == Ordering.lt

example : LinOrd.cmp (3 : Nat) 3 = Ordering.eq := by decide
example : LinOrd.cmp "z" "a" = Ordering.gt := by decide

/-! ## `Map`: `Base.Map` -/

abbrev M := Map Nat String

/-- Built in one insertion order. -/
def m1 : M := ((Map.empty.set 2 "b").set 1 "a").set 3 "c"

/-- The same bindings, built in another. -/
def m2 : M := ((Map.empty.set 3 "c").set 1 "a").set 2 "b"

/-! **Insertion-independent canonical form**, executed (`Map.ext_find`, `Map.set_comm`). -/
#guard m1 == m2

#guard m1.keys == [1, 2, 3]
#guard m1.data == ["a", "b", "c"]
#guard m1.find 2 == some "b"
#guard m1.find 9 == none
#guard (m1.set 2 "B").find 2 == some "B"
#guard (m1.set 2 "B").find 1 == some "a"
#guard (m1.remove 2).find 2 == none
#guard (m1.remove 2).keys == [1, 3]

/-! `to_alist` is sorted; `of_alist ∘ to_alist = id` (`Map.toAlist_sorted`,
`Map.ofAlist_toAlist`). -/
#guard m1.toAlist == [(1, "a"), (2, "b"), (3, "c")]
#guard Map.ofAlist m1.toAlist == m1

/-! `fold` visits each key once, in key order (`Map.fold_visits_keys_in_order`). -/
#guard m1.fold ([] : List Nat) (fun k _ acc => acc ++ [k]) == [1, 2, 3]
#guard m1.fold 0 (fun _ _ n => n + 1) == 3
#guard m1.length == 3

/-- A left-biased `merge` (`Map.find_merge`). -/
def leftBiased (_ : Nat) (a b : Option String) : Option String :=
  match a, b with
  | some x, _ => some x
  | none, some y => some y
  | none, none => none

#guard (Map.merge leftBiased m1 ((Map.empty : M).set 4 "d")).keys == [1, 2, 3, 4]
#guard (Map.merge leftBiased m1 ((Map.empty : M).set 2 "B")).find 2 == some "b"
#guard (Map.merge leftBiased ((Map.empty : M).set 2 "B") m1).find 2 == some "B"
#guard (Map.merge leftBiased m1 (Map.empty : M)).find 9 == none

/-! ## `Set`: `Base.Set` -/

def s1 : Set Nat := Set.ofList [3, 1, 2]

#guard s1.toList == [1, 2, 3]
#guard s1.mem 2
#guard !s1.mem 9
#guard (s1.add 2).toList == [1, 2, 3]
#guard (s1.remove 2).toList == [1, 3]
#guard (s1.union (Set.ofList [4, 1])).toList == [1, 2, 3, 4]
#guard (s1.inter (Set.ofList [2, 5])).toList == [2]
#guard (s1.diff (Set.ofList [2])).toList == [1, 3]
#guard Set.ofList s1.toList == s1
#guard s1.fold ([] : List Nat) (fun x acc => acc ++ [x]) == [1, 2, 3]

/-! ## `Deque` and the dispatcher's buckets -/

def d1 : Deque String := ((Deque.empty.enqueueBack "a").enqueueBack "b").enqueueBack "c"

#guard d1.toList == ["a", "b", "c"]
#guard d1.length == 3
#guard (d1.dequeueFront.map (·.1)) == some "a"
#guard (d1.dequeueBack.map (·.1)) == some "c"
/-! FIFO, executed (`Deque.fifo`, `Deque.popAll_eq_toList`). -/
#guard Deque.popAll 5 d1 == ["a", "b", "c"]
#guard ((d1.enqueueBack "d").dequeueFront.map (·.1)) == some "a"

def b1 : Buckets String :=
  ((Buckets.empty.enqueue 1 "hi").enqueue 0 "lo").enqueue 1 "hi2"

/-! Ascending priority between buckets, FIFO within one (`Buckets.drain_eq_flatten`,
`Buckets.drain_priority_ascending`, `Buckets.drain_fifo_within_bucket`). -/
#guard Buckets.drainTasks b1 == ["lo", "hi", "hi2"]
#guard (Buckets.drain b1).1 == ["lo", "hi", "hi2"]
/-! Drained once (`Buckets.drained_once`). -/
#guard (Buckets.drain b1).2 == (Buckets.empty : Buckets String)
/-! One `enqueue`, one more delivery (`Buckets.drain_enqueue_length`). -/
#guard (Buckets.drainTasks (b1.enqueue 5 "last")).length == (Buckets.drainTasks b1).length + 1
#guard "last" ∈ Buckets.drainTasks (b1.enqueue 5 "last")

/-! ### The projection onto `Effect4.Machine.Dispatcher` -/

open Effect4.Machine in
/-- A Deep dispatcher at a first-order instantiation, built by three `enqueue`s. -/
def dsp : Effect4.Machine.Dispatcher Nat Nat Nat Nat Nat Nat Nat :=
  ((Effect4.Machine.Dispatcher.empty.enqueue 1 (Task.start ⟨7⟩)).enqueue 0
    (Task.start ⟨8⟩)).enqueue 1 (Task.start ⟨9⟩)

open Effect4.Machine in
/-- The same three `enqueue`s on `Buckets`. -/
def bsp : Buckets (Effect4.Machine.Task Nat Nat Nat Nat Nat Nat Nat) :=
  ((Buckets.empty.enqueue 1 (Task.start ⟨7⟩)).enqueue 0
    (Task.start ⟨8⟩)).enqueue 1 (Task.start ⟨9⟩)

/-! **The projection, executed** (`Dispatcher.bucketPairs_enqueue`). -/
#guard Dispatcher.bucketPairs dsp.buckets == bsp.entries

/-! **And the drains agree** (`Dispatcher.drain_projection`). -/
#guard (Effect4.Machine.Dispatcher.drain dsp).1 == Buckets.drainTasks bsp

open Effect4.Machine in
#guard (Effect4.Machine.Dispatcher.drain dsp).1
  == [Task.start ⟨8⟩, Task.start ⟨7⟩, Task.start ⟨9⟩]

/-! The invariant the projection needs, executed at this dispatcher
(`Dispatcher.enqueue_wf`). -/
#guard strictAsc (Dispatcher.bucketPairs dsp.buckets)

/-! ## `Sexp` -/

def sx : Sexp := .list [.atom "run", .list [.atom "fib", .atom "10"], .atom "a\"b\\c"]

/-! **Exactly-once round trip**, executed (`Sexp.parse_print`). -/
#guard Sexp.parse (Sexp.print sx) == some sx
#guard Sexp.parse (Sexp.print (.atom "")) == some (Sexp.atom "")
#guard Sexp.parse (Sexp.print (.list [])) == some (Sexp.list [])
#guard Sexp.parse (Sexp.print (.atom "\\\"")) == some (Sexp.atom "\\\"")

#guard Sexp.print (.atom "a") == "\"a\""
#guard Sexp.print (.list [.atom "a", .atom "b"]) == "(\"a\"\"b\")"
#guard Sexp.print (.list []) == "()"

/-! A text that is not a canonical printing parses to nothing rather than to something else. -/
#guard Sexp.parse "(" == none
#guard Sexp.parse "\"a" == none

/-! The shapes `[@@deriving sexp]` produces (`SexpOf.record_shape`,
`SexpOf.variant_shape_*`). -/
#guard SexpOf.record [("a", Sexp.atom "1"), ("b", Sexp.atom "2")]
  == Sexp.list [.list [.atom "a", .atom "1"], .list [.atom "b", .atom "2"]]
#guard SexpOf.variant "C" [] == Sexp.atom "C"
#guard SexpOf.variant "C" [Sexp.atom "1", Sexp.atom "2"]
  == Sexp.list [.atom "C", .atom "1", .atom "2"]

/-! ## `Derived`: the `ppx_jane` derivers -/

/-- A probe `StructDesc`, in declaration order. -/
def probeStruct : Ml.StructDesc :=
  { leanName := "Probe"
    site := "src/OCaml5/Lib/Test.lean"
    subst := []
    fields :=
      [ { leanName := "id", leanTy := Ml.LTy.nat }
      , { leanName := "name", leanTy := Ml.LTy.str }
      , { leanName := "tags", leanTy := Ml.LTy.lst Ml.LTy.str } ] }

/-! **`Fields.fold` visits every field once, in declaration order**
(`Fields.fold_visits_each_field_once`). -/
#guard Fields.fold probeStruct ([] : List String) (fun acc fd => acc ++ [fd.leanName])
  == ["id", "name", "tags"]
#guard Fields.fold probeStruct 0 (fun n _ => n + 1) == 3
#guard Fields.names probeStruct == ["id", "name", "tags"]

/-- A probe `InductiveDesc`, in declaration order. -/
def probeInductive : Ml.InductiveDesc :=
  { leanName := "Colour"
    site := "src/OCaml5/Lib/Test.lean"
    subst := []
    ctors := [{ leanName := "red" }, { leanName := "green" }, { leanName := "blue" }] }

/-! **`Variants.to_rank` is the constructor index** (`Variants.toRank_eq_index`). -/
#guard (Variants.names probeInductive).length == 3
#guard Variants.toRank probeInductive ((Variants.names probeInductive)[0]!) == some 0
#guard Variants.toRank probeInductive ((Variants.names probeInductive)[1]!) == some 1
#guard Variants.toRank probeInductive ((Variants.names probeInductive)[2]!) == some 2
#guard Variants.toRank probeInductive "NoSuchConstructor" == none

/-- The template, at a carrier: `Nat` with `sexp_of = Atom (toString n)`. -/
def natDerived : Derived Nat :=
  Derived.ofSexp (fun n => .atom (toString n)) (fun s => (Sexp.printC s).length)

#guard natDerived.equal 3 3
#guard !natDerived.equal 3 4
#guard natDerived.compare 3 4 == Ordering.lt
#guard natDerived.compare 4 3 == Ordering.gt
#guard natDerived.compare 3 3 == Ordering.eq
/-! `hash` is a function of the sexp (`Derived.hash_eq_of_eq`). -/
#guard natDerived.hash 3 == natDerived.hash 3

/-! ## `Stream`: the pull/push carriers -/

def ch : Channel Nat Unit := Channel.ofChunks [[1, 2], [3]]

#guard ch.emitted == [1, 2, 3]
#guard ch.terminator == none
#guard (ch.pull.1 matches Take.chunk [1, 2])

def runDone : Runner Nat Unit := Runner.run 40 (Runner.start ch 1)

/-! FIFO, at most once, with the terminator (`Runner.pipeline_invariant`,
`Runner.delivered_prefix_emitted`, `Runner.terminator_once`). -/
#guard runDone.sink.delivered == [1, 2, 3]
#guard runDone.sink.ending == some none
#guard runDone.emitted == [1, 2, 3]
/-! The bounded buffer never exceeds its capacity (`Runner.backpressure_bound`). -/
#guard runDone.sink.buffer.length ≤ 1
#guard (Runner.run 3 (Runner.start ch 1)).sink.buffer.length ≤ 1

/-- A failing channel reaches its one terminator. -/
def chFail : Channel Nat String := .emit [1] (.halt (some "boom"))

#guard chFail.terminator == some "boom"
#guard (Runner.run 20 (Runner.start chFail 2)).sink.ending == some (some "boom")

/-- The daemon's reply shape (for W2). -/
def reply : Channel Sexp String :=
  Stream.replyOfChunks [[Sexp.atom "row1", Sexp.atom "row2"], [Sexp.atom "row3"]]

#guard reply.emitted == [Sexp.atom "row1", Sexp.atom "row2", Sexp.atom "row3"]
#guard reply.terminator == none
#guard (Runner.run 40 (Runner.start reply 2)).sink.delivered
  == [Sexp.atom "row1", Sexp.atom "row2", Sexp.atom "row3"]
#guard (Runner.run 40 (Runner.start reply 2)).sink.ending == some none

/-! ## `Eio` -/

def sw : Eio.Switch := (Eio.Switch.empty.attach 1).attach 2

/-! **Every fiber is settled before the switch returns** (`Eio.Switch.exit_settles_every_fiber`).
-/
#guard ((sw.settle 1).exit true).fibers
  == [(1, Eio.FiberState.finished), (2, Eio.FiberState.cancelled)]
#guard (sw.exit false).fibers
  == [(1, Eio.FiberState.finished), (2, Eio.FiberState.finished)]

def race : Eio.Race := { entrants := [1, 2, 3] }

/-! **The losers are cancelled, each once, and the winner never**
(`Eio.Race.settle_cancels_losers`, `settle_cancels_each_loser_once`, `settle_spares_winner`). -/
#guard (race.settle 2).cancels == [1, 3]
#guard (race.settle 1).cancels == [2, 3]

/-! **A promise resolves at most once** (`Eio.Promise.resolve_once`). -/
#guard ((Eio.Promise.create.resolve 5).resolve 9).peek == some 5
#guard (Eio.Promise.create : Eio.Promise Nat).peek == none

/-! Every primitive is one `perform` (`Eio.fork_is_perform`). -/
#guard (Eio.fork (ν := Nat) .unit) matches Term.perform (.eff _ _)

/-! ## `Picos` -/

def comp0 : Picos.Computation Nat Unit := Picos.Computation.create

/-! **A computation settles at most once** (`Picos.Computation.tryReturn_succeeds_once`). -/
#guard (comp0.tryReturn 1).2
#guard !((comp0.tryReturn 1).1.tryReturn 2).2
#guard !((comp0.tryReturn 1).1.tryCancel ()).2
#guard ((comp0.tryReturn 1).1.peek).isSome
#guard !((comp0.tryReturn 1).1.isRunning)
#guard comp0.isRunning

/-! **A trigger fires once** (`Picos.Trigger.signal_idem`,
`Picos.Trigger.onSignal_only_before_signal`). -/
#guard Picos.Trigger.create.signal.isSignaled
#guard Picos.Trigger.create.signal.signal == Picos.Trigger.create.signal
#guard !(Picos.Trigger.create.signal.onSignal.2)
#guard Picos.Trigger.create.onSignal.2

/-! **An `Ivar` is filled at most once** (`Picos.Ivar.fill_once`, `Picos.Ivar.read_after_fill`).
-/
#guard ((Picos.Ivar.create : Picos.Ivar Nat).tryFill 7).2
#guard ((Picos.Ivar.create : Picos.Ivar Nat).tryFill 7).1.peek == some 7
#guard !(((Picos.Ivar.create : Picos.Ivar Nat).tryFill 7).1.tryFill 8).2
#guard (((Picos.Ivar.create : Picos.Ivar Nat).tryFill 7).1.tryFill 8).1.peek == some 7

/-! Every primitive is one `perform` (`Picos.await_is_perform`). -/
#guard (Picos.await (ν := Nat) .unit) matches Term.perform (.eff _ _)

end OCaml5.Lib.Test
