module

public import Effect4.Library.Semaphore.Ops
public import Effect4.Program.Authoring.Module

/-!
# Modules.Semaphore.Defs — declared Semaphore operations

`Definitions.make "permits"` constructs the invocations and their source definitions together.
`api.install module` installs that instance; `api.module main` makes a module around its main.
The operation bodies remain in `src/Effect4/Library/Semaphore/Ops.lean`.

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

/-- **The Semaphore as a service** (decisions rows 338 and 339, slice CO-6b): an initial program
that makes a semaphore of `permits`, and the three first-order operations as the service's
methods. The block prints them as an Effect service named `name`, whose layer makes the
semaphore once (`printServices`, `src/Effect4/Codegen/Print.lean`). The protected forms take a
program body, so no method of a first-order service holds them. -/
def serviceDefs (name : String) (permits : Nat) (positive : 0 < permits := by decide)
    (suffix : String := "") : List (DefSrc NativeOp) :=
  [ DefSrc.serviceInit name
      { name := "semaphoreMake" ++ suffix, params := [], answer := .refOf cellTy,
        body := fun _ => make permits positive },
    DefSrc.serviceMethod name "take" (Definitions.definition.take ("semaphoreTake" ++ suffix)).src,
    DefSrc.serviceMethod name "release"
      (Definitions.definition.release ("semaphoreRelease" ++ suffix)).src,
    DefSrc.serviceMethod name "takeIfAvailable"
      (Definitions.definition.takeIfAvailable ("semaphoreTakeIfAvailable" ++ suffix)).src ]

end Effect4.Semaphore
