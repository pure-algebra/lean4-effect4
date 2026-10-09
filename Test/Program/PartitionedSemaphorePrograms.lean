import Effect4.Author
import Effect4.Library
import Effect4.Run

/-!
Finite Ref-backed callers of PartitionedSemaphore's scalar bookkeeping steps.
Placement: controls of partitioned-semaphore-bookkeeping, translation-simulation, R10.
Each update observes its reply and all three scalar fields after the atomic Ref operation.
These programs perform no waiter registration, cancellation, release, or wake delivery.
The reservation callers establish the waiting branch before invoking its arithmetic.
-/

set_option autoImplicit false
set_option maxRecDepth 16384
namespace Test.Program.PartitionedSemaphorePrograms
open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.PartitionedSemaphore

/-- Read all scalar fields through the public source interface. -/
def snapshot (cell : TermSrc) : TermSrc :=
  tuple [field cell "capacity", availableStep cell, field cell "waiting"]

def initial (capacity : Nat) : Src NativeOp :=
  bindWith (Ref.make (initialStep (nat capacity))) fun q =>
    bindWith (Ref.get q) fun cell => succeed (snapshot cell)

/-- First consume permits, then observe the next nonblocking attempt and its final cell. -/
def attempt (capacity first requested : Nat) : Src NativeOp :=
  bindWith (Ref.make (initialStep (nat capacity))) fun q =>
    bindWith (Ref.modifyWith q (fun cell => tryTakeStep (nat first) cell)) fun _ =>
      bindWith (Ref.modifyWith q (fun cell => tryTakeStep (nat requested) cell)) fun reply =>
        bindWith (Ref.get q) fun cell => succeed (tuple [reply, snapshot cell])

/-- Enter the insufficient-availability branch before evaluating reservation arithmetic. -/
def reservation (capacity first requested : Nat) : Src NativeOp :=
  bindWith (Ref.make (initialStep (nat capacity))) fun q =>
    bindWith (Ref.modifyWith q (fun cell => tryTakeStep (nat first) cell)) fun _ =>
      bindWith (Ref.modifyWith q (fun cell => reserveStep (nat requested) cell)) fun reply =>
        bindWith (Ref.get q) fun cell => succeed (tuple [reply, snapshot cell])

/-- Two reservations accumulate unmet need; this remains scalar accounting only. -/
def twoReservations : Src NativeOp :=
  bindWith (Ref.make (initialStep (nat 5))) fun q =>
    bindWith (Ref.modifyWith q (fun cell => tryTakeStep (nat 3) cell)) fun _ =>
      bindWith (Ref.modifyWith q (fun cell => reserveStep (nat 4) cell)) fun _ =>
        bindWith (Ref.modifyWith q (fun cell => reserveStep (nat 1) cell)) fun reply =>
          bindWith (Ref.get q) fun cell => succeed (tuple [reply, snapshot cell])

structure Case where
  name : String
  src : Src NativeOp
  expected : Store.Val

/-- The finite observation includes every scalar field, in a fixed display order. -/
def counts (capacity available waiting : Nat) : Store.Val :=
  .list [.nat capacity, .nat available, .nat waiting]

def cases : List Case := [
  ⟨"initialZero", initial 0, counts 0 0 0⟩,
  ⟨"initialFive", initial 5, counts 5 5 0⟩,
  ⟨"zeroOnZero", attempt 0 0 0, .list [.bool true, counts 0 0 0]⟩,
  ⟨"positiveOnZero", attempt 0 0 1, .list [.bool false, counts 0 0 0]⟩,
  ⟨"zeroAfterTake", attempt 5 2 0, .list [.bool true, counts 5 3 0]⟩,
  ⟨"takeCapacity", attempt 5 0 5, .list [.bool true, counts 5 0 0]⟩,
  ⟨"insufficient", attempt 5 3 3, .list [.bool false, counts 5 2 0]⟩,
  ⟨"excessive", attempt 5 0 6, .list [.bool false, counts 5 5 0]⟩,
  ⟨"secondTake", attempt 5 1 2, .list [.bool true, counts 5 2 0]⟩,
  ⟨"reservePartial", reservation 5 3 4, .list [.nat 2, counts 5 0 2]⟩,
  ⟨"reserveEmpty", reservation 5 5 3, .list [.nat 3, counts 5 0 3]⟩,
  ⟨"reserveCapacity", reservation 5 3 5, .list [.nat 3, counts 5 0 3]⟩,
  ⟨"twoReservations", twoReservations, .list [.nat 1, counts 5 0 3]⟩]

def observation (src : Src NativeOp) : Option Store.Val := do
  let built ← (Api.Author.program src).toOption
  match (Api.run built.program 1000).exit with
  | some (.success value) => some value
  | _ => none

#guard cases.length == 13 && (cases.map (·.name)).eraseDups.length == 13
#guard cases.all fun c => observation c.src == some c.expected

/-- Wrong behavior with the same success reply and callback type. -/
def forgotDeduction : Src NativeOp :=
  bindWith (Ref.make (initialStep (nat 5))) fun q =>
    bindWith (Ref.modifyWith q (fun cell => tuple [bool true, cell])) fun reply =>
      bindWith (Ref.get q) fun cell => succeed (tuple [reply, snapshot cell])

#guard (Api.Author.program forgotDeduction).toOption.isSome
#guard observation forgotDeduction == some (.list [.bool true, counts 5 5 0])
#guard observation forgotDeduction != observation (attempt 5 0 5)
-- A typed branch calculation does not establish its caller's branch premise.
#guard (Api.Author.program (reservation 5 1 2)).toOption.isSome
-- Outside that branch, zero unmet need still clears four available permits.
-- The matching successful attempt above leaves two permits available.
#guard observation (reservation 5 1 2) == some (.list [.nat 0, counts 5 0 0])
-- The reservation records unmet need, rather than the whole requested amount.
#guard observation (reservation 5 3 4) != some (.list [.nat 2, counts 5 0 4])
-- The public checker refuses a wrong request type and a wrong cell type.
#guard (Api.Author.program (bindWith (Ref.make (initialStep (nat 5))) fun q =>
  Ref.modifyWith q (fun cell => tryTakeStep (str "three") cell))).toOption.isNone
#guard (Api.Author.program (bindWith (Ref.make (nat 5)) fun q =>
  Ref.modifyWith q (fun cell => tryTakeStep (nat 3) cell))).toOption.isNone

end Test.Program.PartitionedSemaphorePrograms
