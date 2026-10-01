import Effect4.Program.Provision

/-!
# Provision contract — the requirement algebra and the layer signature, frozen

Plan: `docs/research/2026-09-04-provision-algebra.md` §2–§3, §9 (R2). The module under
contract is `src/Effect4/Program/Provision.lean` (spiked as `src/Effect4/Program/Provision.lean`).

Every obligation below is ascribed at its exact proposition and supplied by name with `@`
or with its type arguments fixed, so a declaration that keeps the frozen name but weakens
the statement fails here (`Test/Machine/Environment/ContextKeyContract.lean` is the model).
The executable receipts are `#guard`s in the idiom of `Test/Program/CompileContract.lean`:
a `#guard` that runs the Layer machine is a finite probe at one fuel and nothing more, and
the machine halves of the four register rows stay `#guard`s on purpose (a kernel `decide`
over a fuel-512 run is the cost `docs/research/2026-09-03-survey-lean-core.md` finding 22
measured). The typing halves are theorems by `decide`.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-PROV-CE-001` — `merge` provides a sibling's requirement. Refuted: the sibling shape
  types with the bindings still required, and the machine dies with `serviceNotFound`.
* `E4-PROV-CE-002` — the layer signature determines the built context. Refuted: `leftWins`
  and `rightWins` share a signature and build different contexts (CE 5 lifted).
* `E4-PROV-CE-003` — `Layer.orDie` is one more layer description. Refuted twice over: the
  typing answers `E := never`, and since the join the compile route builds it as
  `catch_(build, die)` (`Layer.ts:3327`) — a leaf's typed failure comes out as the defect
  (the `#guard`s in `Provision.lean`); before the join the Layer machine's lowering refused it
  by name (`PROV-FB-ORDIE-DESC`).
* `E4-PROV-CE-004` — a string literal is a layer value. Refuted by the typing
  (`PROV-FB-STRING-VALUE`): `litVal` (`Program/Typing.lean`) admits no string as a layer
  value. Since DB-15 (2026-09-08) strings are machine values on the native route
  (`Program/Native.lean` `Lit.toVal`); the layer-value refusal is the provision route's own.
-/

set_option autoImplicit false

namespace Test.Program.ProvisionContract

open Effect4
open Effect4.Machine.Env (Requirement Ctx Context)
open Effect4.Program
open Effect4.Program.Provision

/-! ## D0 — `Row.diff`, at the requirement instance -/

section RowDiff

end RowDiff

/-! ## D1 — the signature and the provision algebra -/

section Algebra

#synth DecidableEq LayerTy

end Algebra

/-! ## D2 — the adjunction and the references -/

section Adjunction

end Adjunction

/-! ## D3 — the term, its typing, the app -/

section Term

#synth DecidableEq (LayerTerm DocsOp)

end Term

/-! ## D4 — the specification and its totality -/

section Build

end Build

/-! ## The register rows -/

section Register

-- Part 4 (2026-09-12): these typing receipts were `decide` theorems; the typing now consults
-- the well-founded `Ty.sub` at every row request, which the kernel cannot unfold, so they
-- are the same finite claims as `#guard`s, evaluated by the compiler.

-- `E4-PROV-CE-001`, the typing half: siblings under `merge` keep the bindings required.
#guard (layerTy docsSig siblingMistake).map LayerTy.requires =
  some (Requirement.ofList [dbBinding, rateBinding])

-- `E4-PROV-CE-001`, the positive control: `provideMerge` closes the same two layers.
#guard (layerTy docsSig deploymentLayer).map LayerTy.requires = some Requirement.empty

-- `E4-PROV-CE-001`, the machine half: the mistake dies, the deployment builds.
#guard (docsLayer siblingMistake).map buildSucceeds = some false
#guard (docsLayer deploymentLayer).map buildSucceeds = some true

-- `E4-PROV-CE-002`, the typing half: one signature.
#guard layerTy docsSig leftWins = layerTy docsSig rightWins

-- `E4-PROV-CE-002`, the run half: two contexts, through the specification and the machine.
#guard (build docsSem leftWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 2))
#guard (build docsSem rightWins Context.empty).map (fun c => c.getV dbKey) = some (some (.nat 1))
#guard (docsLayer leftWins).map buildServices = some [(10, 2), (3, 0)]
#guard (docsLayer rightWins).map buildServices = some [(10, 1), (3, 0)]

-- `E4-PROV-CE-003`: typed with `E := never`; the machine half (`orDie` builds, and turns a
-- leaf's failure into a defect) is the `#guard` pair in `Provision.lean`.
#guard (layerTy docsSig (.orDie servicesLayer)).map LayerTy.error = some Ty.never
#guard (docsLayer (.orDie deploymentLayer)).map buildSucceeds = some true

/-- `E4-PROV-CE-004` (`PROV-FB-STRING-VALUE`): a string literal is refused by the typing. -/
theorem string_value_refused : layerTy docsSig (.succeed dbKey (.str "db")) = none := by decide

end Register

end Test.Program.ProvisionContract
