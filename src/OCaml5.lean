-- OCaml5 — the Lean half of the OCaml estate (`ocaml/README.md`; lake library `OCaml5`).
-- Every library module is imported here so `lake build OCaml5` checks the whole model; the
-- `--run` drivers under `OCaml5.Tools` each declare a `main` and are globbed by the
-- lakefile instead of imported.

-- Owner rule, 2026-09-17: on the OCaml side only what is made directly from LCNF stays. The
-- OCaml 5 runtime reification (`Runtime/`), the library carriers (`Lib/`), the type reflection
-- and the mutation pass of the language model and its battery (`Ml/Reflect`, `Ml/Passes`,
-- `MlTest`) were removed after `ddb51b6c`; the avatar they served is on `archive/ocaml5-avatar`.
-- `Ml/`: the part of the OCaml language model the LCNF backend prints through: typed syntax,
-- the canonical printer, the profile and its checker.
import OCaml5.Ml.Identifier
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Profile
import OCaml5.Ml.Check
-- The `Eff` program IR as an OCaml library (`ocaml/eff`): the closed world, the emitters,
-- the goldens. `Tools/EffGen.lean` is the driver.
import OCaml5.Eff.World
import OCaml5.Eff.Emit
import OCaml5.Eff.Goldens
import OCaml5.Eff.Metadata
-- The LCNF → OCaml backend (route 2, the one engine): Lean's mono-phase compiler IR as typed
-- OCaml. `Tools/LcnfGen.lean` is the driver.
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate
