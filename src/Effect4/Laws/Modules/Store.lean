import Effect4.Laws.Modules.Reading
import Effect4.Laws.Program.Typed.ListFold
import Effect4.Laws.Auto.Semantics

/-!
# The connectors of a step term to the store (decisions rows 255 and 257)

A step of a composed module is one pure term for a `Ref.modify` of the module's cell. A step
statement says what the term reads, and a typing statement says what the checker types it at.
This file joins each to the store. It names no module.

- **`step_updates`**: a step term that reads the pair of a reply and a next value, under the
  cell's current value as its last binder, is one atomic update of the cell. The store step
  reads the cell once, answers the reply and writes the next value (`refStep_modify`).
- **`step_keeps_cell`**: a step term that the checker types at the pair of a reply type and the
  cell's type keeps the cell a member of its type, and its reply is a member of the reply type
  (`ListFoldRules.step`, `src/Effect4/Laws/Program/Typed/ListFold.lean`).
- **`cell_read`**: a `Ref.get` of the cell answers its value and leaves the stores
  (`refStep_get`).

Placement. `step_updates` and `cell_read`: concept `translation-simulation`, requirement R10.
`step_keeps_cell`: concept `store-typing`, requirement R4. Their consumer is a wrapper's law,
which runs a step as one `Ref.modify`: the Queue's public path, and Semaphore's operations that
wait. The batteries show each route (`Test/Program/QueueRelation.lean`,
`Test/Program/QueueTyping.lean`, `Test/Program/SemaphoreRelation.lean`,
`Test/Program/SemaphoreSteps.lean`).

Reach. One store step of one cell, with the cell's value and the step's reading as premises.
`step_keeps_cell` takes the signature's atoms as the native table's, and the cell's membership
before the step. They establish no wrapper, no scheduling, no delivery and nothing of a host.
-/

set_option autoImplicit false

namespace Effect4.Modules

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring
open Effect4.Program.Typed

/-- **One atomic update.** A step term that reads the pair of a reply and a next value, under
the cell's current value as its last binder, is one `Ref.modify`: the store step reads the cell
once, answers the reply and writes the next value. Stated once, for every step of a
`Ref.modify`. Consumer: a wrapper's law, which runs each step so. It is the census clause
`refStep_modify`, and it needs no typing. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem step_updates {step : TermSrc} {env : Env} {path : List Nat} {current : String}
    {captured : List Val} {stores : Stores} {q : RefKey} {cell reply next : Val}
    (held : refPeek stores.refs q = some cell)
    (reads : Reads step (env.push [current]) path (captured ++ [cell])
      (Val.tuple [reply, next])) :
    ∃ f, step (env.push [current]) path = .ok f ∧
      syncOpStep (.refModify q f captured) stores =
        some ({ stores with refs := refPoke stores.refs q next }, reply) := by
  obtain ⟨f, elaborated, value⟩ := reads
  refine ⟨f, elaborated, ?_⟩
  show (refStep (.refModify q f captured) stores.refs).map
    (fun step => ({ stores with refs := step.2 }, step.1)) = _
  rw [refStep_modify stores.refs q f captured cell reply next held value]
  rfl

/-- **The typed half of the connector.** A step term that the checker types at the pair of a
reply type and the cell's type keeps the cell a member of its type, and its reply is a member
of the reply type. It is `ListFoldRules.step`, read at the value that the step answers.
Consumer: a wrapper's law, with a step's typing statement
(`src/Effect4/Laws/Modules/Queue/Typing.lean`,
`src/Effect4/Laws/Modules/Semaphore/Typing.lean`). -/
@[semantics "store-typing" (requirement := R4)]
theorem step_keeps_cell (sig : Signature NativeOp) (atoms : sig.atomOf = nativeAtomTy)
    {w : Typed.World} {tys : TyEnv} {captured : List Val} (typedEnv : EnvTyped w tys captured)
    {f : Term} {C B : Ty} (typed : termTy sig (tys ++ [C]) f = some (.prod B C))
    {stores : Stores} {q : RefKey} {cell reply next : Val}
    (held : refPeek stores.refs q = some cell) (member : Fits w cell C)
    (value : evalTerm (captured ++ [cell]) f = some (Val.tuple [reply, next])) :
    Fits w reply B ∧ Fits w next C := by
  obtain ⟨b, a, answered, -, fitsReply, fitsNext⟩ :=
    (fold_typed_atomic_update sig).step atoms w tys captured typedEnv f C B typed stores q cell
      held member
  rw [value] at answered
  have same : Val.tuple [reply, next] = Val.tuple [b, a] := Option.some.inj answered
  have parts : [reply, next] = [b, a] := Store.Val.list.inj same
  obtain ⟨rfl, rest⟩ := List.cons.inj parts
  obtain ⟨rfl, -⟩ := List.cons.inj rest
  exact ⟨fitsReply, fitsNext⟩

/-- **The read law of a cell.** A `Ref.get` of the cell answers its value and leaves the
stores. A step that is a term over that value writes nothing: the Queue's `sizeStep` is one. It
is the census clause `refStep_get`. -/
@[semantics "translation-simulation" (requirement := R10)]
theorem cell_read {stores : Stores} {q : RefKey} {cell : Val}
    (held : refPeek stores.refs q = some cell) :
    syncOpStep (.refGet q) stores = some (stores, cell) := by
  show (refStep (.refGet q) stores.refs).map
    (fun step => ({ stores with refs := step.2 }, step.1)) = _
  rw [refStep_get stores.refs q cell held]
  rfl

end Effect4.Modules
