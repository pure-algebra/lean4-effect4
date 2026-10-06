module

public import Effect4.Program.Authoring.Sugar

/-!
# Program.Authoring.Mask — the mask that restores, as a derived form

Decisions rows 227 and 244 to 246. rc.112's `uninterruptibleMask(f)` reads the fiber's flag
once, at its entry, and hands `f` one of two functions: the identity when the fiber is masked
already, `interruptible` otherwise (`vendor/effect-4.0.0-rc.112/src/internal/effect.ts`,
`uninterruptibleMask`). The language has that choice as data: the fiber action
`getInterruptible` answers the saved state, a value of the type `Ty.maskRestore`, and the node
`restore saved body` applies it.

The mask is a derived form over `bind`. It adds no constructor, no wire tag and no printed
shape of its own:

    uninterruptibleMask saved body  :=
      bind saved (withFiber Action.getInterruptible) (uninterruptible body)

The two builders here author that one expansion through the generated lifts
(`Program/Authoring/Lifts.lean`). The checker types it, and the printer prints it node by node
(`Codegen/Templates.lean`): the getter as `Effect.uninterruptibleMask((aN) => Effect.succeed(aN))`
and a restore site as `pipe(body, saved)`.

**The form's contract has one premise for its clients** (row 246): nothing is acquired or
registered before the body begins. The printed form is three checkpoints longer than the
native mask, and an interrupt at its entry ends it before its body starts.

No row of the form table (`Codegen/Forms.lean`) is added. A row there is also a foreign
spelling for the two ingest engines, and the native callback spelling is not read (the mask's
second note, F5; decisions row 215).
-/

@[expose] public section

namespace Effect4.Program.Authoring

open Effect4.Program

/-- `uninterruptibleMask saved body`: the body runs masked, and it names the saved state of the
fiber's entry flag as `saved`. A restore site is `restore (var saved) e`: `e` under
`interruptible` when the caller was interruptible, and `e` as it is when the caller was masked. -/
def uninterruptibleMask {Op : Type} (saved : String) (body : Src Op) : Src Op :=
  bind saved (withFiber Action.getInterruptible) (uninterruptible body)

/-- `uninterruptibleMaskWith fun restore => body`: the mask with its saved state under a name
minted for the scope, as rc.112 hands its body the function `restore`. `restore e` is the
restore site of this mask's saved state. No name an author writes is a minted name. So a
variable that the caller reads through `var` keeps its reading inside the body
(`var_push_minted`, `Laws/Program/Author.lean`, under its premises on the two names). -/
def uninterruptibleMaskWith {Op : Type} (body : (Src Op → Src Op) → Src Op) : Src Op :=
  minting "restore" fun saved => uninterruptibleMask saved (body (restore (minted saved)))

end Effect4.Program.Authoring
