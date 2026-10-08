module
public import Effect4.Modules.Queue.Defs
public import Effect4.Modules.Queue.Ops
public import Effect4.Modules.Semaphore.Defs
public import Effect4.Modules.Semaphore.Ops
public import Effect4.Modules.Pool.Ops
public import Effect4.Modules.Latch.Steps
public import Effect4.Modules.Latch.Registration
public import Effect4.Modules.Stream.Ops
public import Effect4.Program.Stream

/-!
# Effect4.Library — the entry module of the prebuilt composed modules (decisions row 332)

A program that uses a Queue, a Semaphore, a Pool, a Latch or a stream imports this module, or
one composed module's own files. Each composed module keeps the name of latest's
(Effect 4.0.1) module, and its place in latest's graph of building blocks (decisions row 335).
It declares nothing.
-/
