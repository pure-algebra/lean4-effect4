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
public import Effect4.Library.PartitionedSemaphore.Steps
public import Effect4.Library.Stream.ArrayDefs
public import Effect4.Library.SynchronizedRef.Ops
public import Effect4.Library.PubSub.Steps

/-!
# Effect4.Library — the entry module of the prebuilt composed modules (decisions row 332)

A program imports this module or one composed module's own files.
Queue, Semaphore, Pool, Latch, Ref, SynchronizedRef and Stream retain latest's names (Effect 4.0.1).
The building-block records describe the implemented compositions under decisions row 335.
Each independent model stands beside the steps that its laws interpret.
PartitionedSemaphore exposes scalar bookkeeping; PubSub exposes capacity-one, replay-zero bookkeeping.
Their waiting and delivery operations remain open.
This entry module declares nothing.
-/
