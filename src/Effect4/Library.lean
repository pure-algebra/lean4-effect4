module
public import Effect4.Library.Queue.Model
public import Effect4.Library.Semaphore.Model
public import Effect4.Library.Pool.Model
public import Effect4.Library.Latch.Model
public import Effect4.Library.Stream.Model
public import Effect4.Library.Queue.Defs
public import Effect4.Library.Queue.Ops
public import Effect4.Library.Semaphore.Defs
public import Effect4.Library.Semaphore.Ops
public import Effect4.Library.Pool.Ops
public import Effect4.Library.Latch.Steps
public import Effect4.Library.Latch.Registration
public import Effect4.Library.Stream.Ops
public import Effect4.Program.Stream
public import Effect4.Library.Ref

/-!
# Effect4.Library — the entry module of the prebuilt composed modules (decisions row 332)

A program that uses a Queue, a Semaphore, a Pool, a Latch or a stream imports this module, or
one composed module's own files. Each composed module keeps the name of latest's
(Effect 4.0.1) module, and its place in latest's graph of building blocks (decisions row 335).
Each module's model, the abstract transitions that its laws relate the steps to, stands beside its
steps. It declares nothing.
-/
