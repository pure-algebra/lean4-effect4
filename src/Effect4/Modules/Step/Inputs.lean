module

public import Effect4.Modules.Step

/-!
# Named step input declarations

An input declaration is a list of names paired with their types.
It serves elaboration only: the step remains positional `Step` data.
The named declaration and source readers share this list as their input.
Their macros store neither names nor functions inside a step.
-/

@[expose] public section
namespace Effect4.Modules

/-- Compile-time input metadata; each name has one declared type. -/
abbrev InputContext := List (String × Program.Ty)

/-- The positional context computed from the one named declaration. -/
def InputContext.types (context : InputContext) : List Program.Ty := context.map Prod.snd

end Effect4.Modules
