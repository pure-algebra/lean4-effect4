-- OCaml5 — the Lean half of the OCaml estate (`ocaml/README.md`; lake library `OCaml5`).
-- Every library module is imported here so `lake build OCaml5` checks the whole model; the
-- `--run` drivers under `OCaml5.Tools` each declare a `main` and are globbed by the
-- lakefile instead of imported.

-- `Runtime/`: the OCaml 5 `Stdlib.Effect` handler machine (`Effect`, the model the `Lib`
-- carriers for Eio and Picos build on, and the site `Ml/Profile` cites for the effect
-- primitives) and backend-relative values (`Value`). The rest of the OCaml 5 reification
-- (the handler machine's invariants and witnesses, the js_of_ocaml machine and the native ≈
-- jsoo relation, jsoo's block IR, the Term → Code compiler, the CPS pass and its proofs, the
-- Promise host, the `Term` renderer and the term fuzz) is archived on `archive/ocaml5-avatar`
-- at `14e6835`, with the avatar it targeted and route 1 (`Bridge`, `ocaml/link`).
import OCaml5.Runtime.Effect
import OCaml5.Runtime.Value
-- `Ml/`: the OCaml language model: typed syntax, the canonical printer, the profile checker, the
-- Lean → OCaml type reflection, the `{ f with }` → mutation pass. `MlTest`, its battery,
-- declares a `main` and is built through the lakefile's glob instead of imported here.
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
-- The `Eff` program IR as an OCaml library (`ocaml/eff`): the closed world, the emitters,
-- the goldens. `Tools/EffGen.lean` is the driver.
import OCaml5.Eff.World
import OCaml5.Eff.Emit
import OCaml5.Eff.Goldens
-- The LCNF → OCaml backend (route 2, the one engine): Lean's mono-phase compiler IR as typed
-- OCaml. `Tools/LcnfGen.lean` is the driver.
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate
-- Route 1's Lean half, the `@[export]`ed session API over `Effect4.Api`. Its OCaml half
-- (`ocaml/link`) is archived; this module stays only because `harness/truth/Truth.lean`
-- cites it and that file is a stamp input of the truth family, so it leaves with the next
-- edit that re-stamps the truth artefacts.
import OCaml5.Bridge
