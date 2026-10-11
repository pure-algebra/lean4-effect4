import Effects.Coalgebra.Step
import Effects.Coalgebra.System
import Effects.Coalgebra.Bisim
import Effects.Coalgebra.Comodel
import Effects.Coalgebra.Protocol
import Effects.Coalgebra.Run
import Effects.Coalgebra.Sat
import Effects.Coalgebra.Indexed

/-!
# The coalgebra layer (v0.9.0; typed handlers, v0.9.1; indexed signatures, v0.10.0; v0.10.1)

The algebra's dual. A signature's programs are the initial algebra, folded by handlers; its
systems are coalgebras of one step (`Step`, `System`), read through their finite unfoldings.
Bisimulations and simulations (`Bisim`) compare systems; comodels (`Comodel`) are hosts that
answer operations from a state, and compose by routing, sharing, renaming along a lens, and
implementation by programs over another signature (program in, program out). Protocols of the
first order (`Protocol`) say which answers a host may give. `Run` runs a system against a host:
one simulation of a system by a program gives agreement against every host
(`Program.run_of_sim_program`).
`Sat` types programs and handlers by protocols: a program answered under a protocol ends in its
postcondition, a typed handler takes typed programs to typed programs, typed handlers compose, and
a host that meets the lower protocol meets the upper one behind a typed handler. `Indexed` adds
protocols of a higher order: worlds, and operations that a world offers, so an answer can open
operations (a promise and its await); a first-order signature is the one-world case.

Claims and their limits: `docs/CLAIM-BOUNDARY.md`, sections v0.9.0, v0.9.1 and v0.10.0. Contract:
`test/contracts/coalgebra.contract.md`; battery `EffectsTest/Coalgebra/CoalgebraContract.lean`.
-/
