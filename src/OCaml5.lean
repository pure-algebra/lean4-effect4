-- OCaml5 — the Lean half of the OCaml estate (`ocaml/README.md`; lake library `OCaml5`).
-- Every library module is imported here so `lake build OCaml5` checks the whole model; the
-- `--run` drivers under `OCaml5.Tools` each declare a `main` and are globbed by the
-- lakefile instead of imported.

-- The OCaml 5 runtime reification: the `Stdlib.Effect` handler machine and its invariants,
-- the js_of_ocaml `effect.js` machine and the native ≈ jsoo relation, jsoo's block IR, the
-- Term → Code compiler, the CPS pass, backend-relative values, the Promise host.
import OCaml5.Code
import OCaml5.Effect
import OCaml5.Promise
import OCaml5.Value
import OCaml5.Witnesses
import OCaml5.EffectJsoo
import OCaml5.Compiler
import OCaml5.Cps
import OCaml5.CpsProof
import OCaml5.Invariant
import OCaml5.WitnessesJ
import OCaml5.Compile
import OCaml5.compile.Agreement
import OCaml5.compile.Dumps
import OCaml5.compile.Fuzz
import OCaml5.compile.Simulation
import OCaml5.ir.Programs
import OCaml5.ir.Fuzz
import OCaml5.ir.Avatar
import OCaml5.ir.Counterexamples
import OCaml5.ir.RunUnderHandler
-- The OCaml language model: typed syntax, the canonical printer, the profile checker, the
-- Lean → OCaml type reflection, the `{ f with }` → mutation pass.
import OCaml5.Ml.Identifier
import OCaml5.Ml.Syntax
import OCaml5.Ml.Render
import OCaml5.Ml.Reflect
import OCaml5.Ml.Profile
import OCaml5.Ml.Passes
import OCaml5.Ml.Check
-- Lean carriers with laws for the OCaml libraries the avatar and the daemon use.
import OCaml5.Lib.Order
import OCaml5.Lib.Map
import OCaml5.Lib.Set
import OCaml5.Lib.Sexp
import OCaml5.Lib.Derived
import OCaml5.Lib.Stream
import OCaml5.Lib.Eio
import OCaml5.Lib.Picos
import OCaml5.Lib.Deque
import OCaml5.LibTest
-- The Machine carriers rendered to OCaml (the avatar's generated half) and the program
-- fuzz (`Fuzz` declares the driver's `main`; `MlTest`, the language model's own battery,
-- declares another and is built through the lakefile's glob instead of imported here).
import OCaml5.Render
import OCaml5.Fuzz
-- The LCNF → OCaml backend (route 2 of the fidelity ladder): Lean's mono-phase compiler IR
-- as typed OCaml.
import OCaml5.Lcnf.Dump
import OCaml5.Lcnf.Naming
import OCaml5.Lcnf.Types
import OCaml5.Lcnf.Translate
-- The Machine descriptions derived from the environment, and the projection guard that
-- compares them with the hand descriptions in `OCaml5.Render`.
import OCaml5.Derived.Fibers
import OCaml5.Derived.Stores
import OCaml5.Derived.Context
import OCaml5.Derived.Layer
import OCaml5.DerivedCheck
-- Route 1: the Lean machine held by OCaml as an opaque value (`@[export]`ed session API
-- over `Effect4.Api`; `ocaml/link` links the static library).
import OCaml5.Bridge
