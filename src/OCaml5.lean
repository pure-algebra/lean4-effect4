-- OCaml5 — the Lean half of the OCaml estate (`ocaml/README.md`; lake library `OCaml5`).
-- Every library module is imported here so `lake build OCaml5` checks the whole model; the
-- `--run` drivers under `OCaml5.Tools` each declare a `main` and are globbed by the
-- lakefile instead of imported.

-- `Runtime/`: the OCaml 5 runtime reification: the `Stdlib.Effect` handler machine and its invariants,
-- the js_of_ocaml `effect.js` machine and the native ≈ jsoo relation, jsoo's block IR, the
-- Term → Code compiler, the CPS pass, backend-relative values, the Promise host.
import OCaml5.Jsoo.Code
import OCaml5.Runtime.Effect
import OCaml5.Runtime.Promise
import OCaml5.Runtime.Value
import OCaml5.Runtime.Witnesses
import OCaml5.Runtime.EffectJsoo
import OCaml5.Runtime.Compiler
import OCaml5.Jsoo.Cps
import OCaml5.Jsoo.CpsProof
import OCaml5.Runtime.Invariant
import OCaml5.Runtime.WitnessesJ
import OCaml5.Jsoo.Compile
import OCaml5.Compile.Agreement
import OCaml5.Compile.Dumps
import OCaml5.Compile.Fuzz
import OCaml5.Compile.Simulation
import OCaml5.Ir.Programs
import OCaml5.Ir.Fuzz
import OCaml5.Ir.Avatar
import OCaml5.Ir.Counterexamples
import OCaml5.Ir.RunUnderHandler
-- `Ml/`: the OCaml language model: typed syntax, the canonical printer, the profile checker, the
-- Lean → OCaml type reflection, the `{ f with }` → mutation pass.
import OCaml5.Ml.Identifier
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Reflect
import OCaml5.Ml.Profile
import OCaml5.Ml.Passes
import OCaml5.Ml.Check
-- Lean carriers with laws for the OCaml libraries the engine uses.
import OCaml5.Lib.Order
import OCaml5.Lib.Map
import OCaml5.Lib.Set
import OCaml5.Lib.Sexp
import OCaml5.Lib.Derived
import OCaml5.Lib.Stream
import OCaml5.Lib.Eio
import OCaml5.Lib.Picos
import OCaml5.Lib.Deque
import OCaml5.Lib.Test
-- The `Term` → OCaml renderer and the term fuzz generators (`MlTest`, the language model's
-- own battery, declares a `main` and is built through the lakefile's glob instead of imported
-- here). The avatar, its descriptions, its corpus and tapes are archived on
-- `archive/ocaml5-avatar` at `14e6835`.
import OCaml5.Runtime.Render
import OCaml5.Fuzz.Gen
import OCaml5.Fuzz.Term
-- The `Eff` program IR as an OCaml library (`ocaml/eff`): the closed world, the emitters,
-- the goldens. `Tools/EffGen.lean` is the driver.
import OCaml5.Eff.World
import OCaml5.Eff.Emit
import OCaml5.Eff.Goldens
-- The LCNF → OCaml backend (route 2 of the fidelity ladder): Lean's mono-phase compiler IR
-- as typed OCaml.
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate
-- Route 1: the Lean machine held by OCaml as an opaque value (`@[export]`ed session API
-- over `Effect4.Api`; `ocaml/link` links the static library).
import OCaml5.Bridge
