import Effect4.Author
import Effect4.Library.Queue.Defs
import Effect4.Program.Authoring.Application

/-!
# A bounded buffer: two producers and two consumers share one queue of capacity two

The buffer is the library's Queue (`Effect4.Queue`). A producer offers its numbers in order, and
waits while the buffer is full. A consumer takes as many numbers as it is told, and waits while
the buffer is empty. `transfer(count)` starts two producers and two consumers of `count` numbers
each, waits for all four, and answers the sum that the consumers took.
-/

set_option autoImplicit false

namespace Examples.BoundedBuffer

open Effect4 Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Authoring.Atom (add)

/-- The buffer's operations, at numbers. -/
def buffer : Queue.Definitions := Queue.Definitions.make "buffer" .nat

/-- A producer offers `from`, `from + 1`, … up to `count` numbers. -/
def producer (queue start count : TermSrc) : Src NativeOp :=
  forRange (nat 0) count fun i => buffer.offer queue (add start i)

/-- A consumer takes `count` numbers and answers their sum. -/
def consumer (queue count : TermSrc) : Src NativeOp :=
  foldRange (nat 0) count (nat 0) fun _ sum => eff do
    let n ← buffer.take queue
    return add sum n

/-- `transfer(count)`: two producers and two consumers of `count` numbers each over a buffer of
two. -/
def transfer (count : TermSrc) : Src NativeOp := eff do
  let queue ← Queue.bounded .nat 2
  let first ← fork (producer queue (nat 0) count)
  let second ← fork (producer queue (nat 100) count)
  let left ← fork (consumer queue count)
  let right ← fork (consumer queue count)
  let _ ← join first
  let _ ← join second
  let a ← join left
  let b ← join right
  return add a b

/-- The bounded buffer as an application: the buffer's definitions and one entry. -/
def application : Application NativeOp :=
  { name := "boundedBuffer"
    defs := buffer.defs
    entries := [{ name := "transfer", params := [("count", .nat)], body := transfer (var "count") }] }

end Examples.BoundedBuffer
