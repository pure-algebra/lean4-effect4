module

public import Effect4.Modules.Semaphore.Ops
public import Effect4.Program.Authoring.Module

/-!
# Modules.Semaphore.Defs — declared Semaphore operations

`Definitions.make "permits"` constructs the invocations and their source definitions together.
`api.install module` installs that instance; `api.module main` makes a module around its main.
The operation bodies remain in `src/Effect4/Modules/Semaphore/Ops.lean`.

`make` retains its positive literal argument and stays an inline builder.
The protected forms accept program bodies and stay expanded under decisions row 328.
These declarations add no scheduling law or new module profile.
-/

@[expose] public section

namespace Effect4.Semaphore

open Effect4.Program Effect4.Program.Authoring

/-- The first-order Semaphore operations, with one declaration for each signature and body. -/
eff_module Definitions where
  take (self : .refOf cellTy) (count : .nat) : .nat := Effect4.Semaphore.take self count;
  release (self : .refOf cellTy) (count : .nat) : .nat := Effect4.Semaphore.release self count;
  takeIfAvailable (self : .refOf cellTy) (count : .nat) : .bool :=
    Effect4.Semaphore.takeIfAvailable self count

end Effect4.Semaphore
