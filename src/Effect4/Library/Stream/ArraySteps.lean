module

public import Effect4.Step.Callback

/-! The array extraction step uses the existing first-order Step language.
The callback returns its previous list and clears the cell.
Its consumers are `arrayBatch` and `arrayStep_agrees`. -/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Stream
open Effect4.Program Effect4.Program.Authoring Effect4.Modules

/-- One atomic extraction of a pending array. -/
def arrayStep (A : Ty) : Step [.list A] (.prod (.list A) (.list A)) :=
  .pair (.var (.here _ _)) (.emptyLike (.var (.here _ _)))

/-- The array step captures no outer inputs. -/
def arrayCaptures : {t : Ty} → Input [] t → TermSrc := fun {_} x => nomatch x

end Effect4.Stream
