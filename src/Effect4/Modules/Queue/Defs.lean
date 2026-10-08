module

public import Effect4.Modules.Queue.Ops
public import Effect4.Program.Authoring.Module

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

`Definitions` declares the operation signatures once through `eff_module`
(`src/Effect4/Program/Authoring/Module.lean`). `Definitions.make "numbers" .nat` holds the
invocations and their definition list together. Use `api.take q`, and install that instance
with `api.install module` or `api.module main`.

The older `takeD`, `offerD`, `pollD`, `sizeD` and `defs` entry points retain their exact names.
They use the command's individual definition constructors. Their metadata has the same owner.

**An argument is a value passed as the request.** No caller's term enters a binder of the
operation at the site: the minted names stay inside the body, at the closed scope. So the
hygiene of `Ops.lean` (a caller's `var` keeps its reading) holds at an invocation without a
condition on the caller's names.

**One message type, one instance.** A definition is monomorphic. A program using two message
types constructs two `Definitions` values with distinct instance names. The older `defs A suffix`
entry point uses a distinct suffix for each message type.

**What moves.** A use is one invocation in the printed module, where the operation's whole tree
stood before. Each invocation is one step of the machine and one suspension of the target, so
the least fuel of a run moves (`Test/Program/QueueDefs.lean` measures it).
-/

@[expose] public section

namespace Effect4.Queue

open Effect4.Program Effect4.Program.Authoring

/-- The handle's type at the message type `A`: the cell's `Ref`. -/
def handleTy (A : Ty) : Ty := .refOf (cellTy A)

/-- The Queue operations declared once, with generated invocations and installation. -/
eff_module Definitions (A : Ty) where
  take (queue : handleTy A) : A := Effect4.Queue.take A queue;
  offer (queue : handleTy A) (message : A) : .bool := Effect4.Queue.offer A queue message;
  poll (queue : handleTy A) : (.option A) := Effect4.Queue.poll A queue;
  size (queue : handleTy A) : .nat := Effect4.Queue.size A queue

/-- `Queue.take` as a definition: the handle is its request. -/
def takeD (A : Ty) (suffix : String := "") : Defined (TermSrc → Src NativeOp) :=
  Definitions.definition.take ("queueTake" ++ suffix) A

/-- `Queue.offer` as a definition: the handle and the message are its request. -/
def offerD (A : Ty) (suffix : String := "") : Defined (TermSrc → TermSrc → Src NativeOp) :=
  Definitions.definition.offer ("queueOffer" ++ suffix) A

/-- `Queue.poll` as a definition: the handle is its request. -/
def pollD (A : Ty) (suffix : String := "") : Defined (TermSrc → Src NativeOp) :=
  Definitions.definition.poll ("queuePoll" ++ suffix) A

/-- `Queue.size` as a definition: the handle is its request. -/
def sizeD (A : Ty) (suffix : String := "") : Defined (TermSrc → Src NativeOp) :=
  Definitions.definition.size ("queueSize" ++ suffix) A

/-- The four definitions at one message type under one suffix, for a module's `defs`. -/
def defs (A : Ty) (suffix : String := "") : List (DefSrc NativeOp) :=
  [(takeD A suffix).src, (offerD A suffix).src, (pollD A suffix).src, (sizeD A suffix).src]

end Effect4.Queue
