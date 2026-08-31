import CasExamples.AgentStep
import CasExamples.ForeignRepresentation
import CasExamples.PutTree
import CasExamples.Roots
import CasExamples.SchemaDeriving

/-!
# CasExamples — the language, used

Consumers of `Cas`, kept outside the language library (the Concrete
split): `lake build` still kernel-checks them, but nothing in `Cas`
imports them. `AgentStep` is the flagship: the agent step written as a
program of the agent language, run over grammar-built content under
the production digest. `SchemaDeriving` exercises the opt-in schema
deriver against ordinary and parameterized structures;
`ForeignRepresentation` checks the TypeScript/Effect Schema surface.
-/
