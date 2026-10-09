import Effects.Coalgebra.Step
import Effects.Coalgebra.System
import Effects.Coalgebra.Bisim
import Effects.Coalgebra.Comodel
import Effects.Coalgebra.Protocol
import Effects.Coalgebra.Run

/-!
# The coalgebra layer (v0.9.0)

The algebra's dual. A signature's programs are the initial algebra, folded by handlers; its
systems are coalgebras of one step (`Step`, `System`), read through their finite unfoldings.
Bisimulations and simulations (`Bisim`) compare systems; comodels (`Comodel`) are hosts that
answer operations from a state, and compose by routing, sharing, renaming along a lens, and
implementation by programs over another signature (program in, program out). Protocols of the
first order (`Protocol`) say which answers a host may give. `Run` runs a system against a host:
one simulation of a system by a program gives agreement against every host
(`Program.run_of_sim_program`).

Claims and their limits: `docs/CLAIM-BOUNDARY.md`, section v0.9.0. Contract:
`test/contracts/coalgebra.contract.md`; battery `EffectsTest/Coalgebra/CoalgebraContract.lean`.
-/
