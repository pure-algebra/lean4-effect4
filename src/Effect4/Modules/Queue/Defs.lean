module

public import Effect4.Modules.Queue.Ops
public import Effect4.Program.Authoring.Defs

/-!
# Modules.Queue.Defs — the Queue's operations as definitions (decisions row 328, slice PROC-4)

Each operation of `src/Effect4/Modules/Queue/Ops.lean` as a definition of a program's block
(`DefSrc`, `src/Effect4/Program/Authoring.lean`): written once for each message type that a
program uses, and invoked by name at each site. The body of each definition is the operation
itself, applied to the parts of its request, so the steps, the waiting wrapper and their laws
do not move (`src/Effect4/Laws/Modules/Queue/`).

| Definition | Parameters | Answer | The operation it holds |
| --- | --- | --- | --- |
| `takeD A` | the handle | `A` | `take A` |
| `offerD A` | the handle, a message | `boolean` | `offer A` |
| `pollD A` | the handle | `Option A` | `poll A` |
| `sizeD A` | the handle | `number` | `size A` |

Each is one call of `Def.of` (`src/Effect4/Program/Authoring/Defs.lean`): its `src` goes in a
module's `defs`, and its `call` has the operation's own type, so `(takeD A).call q` stands
where `take A q` stood.

**An argument is a value passed as the request.** No caller's term enters a binder of the
operation at the site: the minted names stay inside the body, at the closed scope. So the
hygiene of `Ops.lean` (a caller's `var` keeps its reading) holds at an invocation without a
condition on the caller's names.

**One message type, one set of names.** A definition is monomorphic. A program that uses two
message types declares the four definitions twice, under two suffixes (`defs A suffix`).

**What moves.** A use is one invocation in the printed module, where the operation's whole tree
stood before. Each invocation is one step of the machine and one suspension of the target, so
the least fuel of a run moves (`Test/Program/QueueDefs.lean` measures it).
-/

@[expose] public section

namespace Effect4.Queue

open Effect4.Program Effect4.Program.Authoring

/-- The handle's type at the message type `A`: the cell's `Ref`. -/
def handleTy (A : Ty) : Ty := .refOf (cellTy A)

/-- `Queue.take` as a definition: the handle is its request. -/
def takeD (A : Ty) (suffix : String := "") : Defined (TermSrc → Src NativeOp) :=
  Def.of ("queueTake" ++ suffix) [("queue", handleTy A)] A (take A)

/-- `Queue.offer` as a definition: the handle and the message are its request. -/
def offerD (A : Ty) (suffix : String := "") : Defined (TermSrc → TermSrc → Src NativeOp) :=
  Def.of ("queueOffer" ++ suffix) [("queue", handleTy A), ("message", A)] .bool (offer A)

/-- `Queue.poll` as a definition: the handle is its request. -/
def pollD (A : Ty) (suffix : String := "") : Defined (TermSrc → Src NativeOp) :=
  Def.of ("queuePoll" ++ suffix) [("queue", handleTy A)] (.option A) (poll A)

/-- `Queue.size` as a definition: the handle is its request. -/
def sizeD (A : Ty) (suffix : String := "") : Defined (TermSrc → Src NativeOp) :=
  Def.of ("queueSize" ++ suffix) [("queue", handleTy A)] .nat (size A)

/-- The four definitions at one message type under one suffix, for a module's `defs`. -/
def defs (A : Ty) (suffix : String := "") : List (DefSrc NativeOp) :=
  [(takeD A suffix).src, (offerD A suffix).src, (pollD A suffix).src, (sizeD A suffix).src]

end Effect4.Queue
