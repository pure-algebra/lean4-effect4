import Lean
import Lean.Util.CollectAxioms
import Effect4.Machine.Key

/-!
# Context-key declaration and receipt join

Test-only metaprogramming for the `ENV-LEAF-KEY-IDENTITY` closure and the
local `ENV-LEAF-KEY-ORDER-BRIDGE` receipt.  The checker takes its 97-name
owned-declaration census from Lean's elaborated environment, not from source
text.  That census includes compiler-generated structural companions.  The
25-name frozen Context Key API and the 14-name additive Std bridge API are
reported separately.  The checker verifies every allocated owner, checks the
contracted and bridge theorem declarations, and confirms the axiom-free
receipt recorded by `Test/Environment/AxiomReport.lean`.

`ServiceName`, `ServiceTypeCode`, and `ServiceKey` remain one passive leaf.
`ServiceUniverse` is recorded against the existing Context graph edge
`ENV-KEY-INTERP`; this module creates no proof graph and closes no semantic
edge.  The later additive bridge to Lean's standard lawful-order classes is
reported separately from the frozen 25-name Context Key API; it derives from
the same `ServiceKey.Lt` and creates neither a carrier nor another order.  Its
exact instance, relation, and kernel-computation receipts attach only to the
`DATA-PG-ROW/ORDER` route.  This module records the route but does not own that
edge's closure status; `Test.Data.RowAssurance` does.

The generic commands are exposed only so the bounded reaction fixtures can
exercise the same detector against extra, missing, and owner-drifted
declarations.
-/

open Lean Meta Elab Command

namespace Test.Environment.ContextKeyAssurance

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"environment context-key evidence mismatch: {detail}"

private def declarationOwner? (environment : Environment) (name : Name) : Option Name := do
  if let some moduleIndex := environment.getModuleIdxFor? name then
    environment.header.moduleNames[moduleIndex]?
  else if environment.contains name then
    some environment.mainModule
  else
    none

private def declarationsOwnedBy (environment : Environment) (owner : Name) : List Name :=
  environment.constants.toList.foldl (init := []) fun declarations entry =>
    let name := entry.1
    if !name.isInternal && declarationOwner? environment name == some owner then
      name :: declarations
    else
      declarations

private def checkOwners (expectedOwner : Name) (names : List Name) : CommandElabM Unit := do
  let environment ← getEnv
  for name in names do
    unless environment.contains name do
      failJoin m!"missing declaration {name}"
    let actualOwner := declarationOwner? environment name
    unless actualOwner == some expectedOwner do
      failJoin m!"owner drift for {name}: expected {expectedOwner}, found {actualOwner}"

private def checkExactModuleSurface
    (expectedOwner : Name) (expected : List Name) : CommandElabM Unit := do
  checkOwners expectedOwner expected
  let actual := declarationsOwnedBy (← getEnv) expectedOwner
  let unexpected := actual.filter fun name => !expected.contains name
  let missing := expected.filter fun name => !actual.contains name
  unless unexpected.isEmpty && missing.isEmpty do
    failJoin m!"owned declaration census for {expectedOwner}: unexpected {unexpected}; missing {missing}"

private def expectedOwnedDeclarations : List Name :=
  [ `Effect4.ServiceKey
  , `Effect4.ServiceKey.Carrier
  , `Effect4.ServiceKey.Conflict
  , `Effect4.ServiceKey.Le
  , `Effect4.ServiceKey.Lt
  , `Effect4.ServiceKey.carrier_def
  , `Effect4.ServiceKey.casesOn
  , `Effect4.ServiceKey.conflict_iff
  , `Effect4.ServiceKey.ctorIdx
  , `Effect4.ServiceKey.instDecidableLE
  , `Effect4.ServiceKey.instDecidableConflict
  , `Effect4.ServiceKey.instIsLinearOrder
  , `Effect4.ServiceKey.instIsPartialOrder
  , `Effect4.ServiceKey.instIsPreorder
  , `Effect4.ServiceKey.instLE
  , `Effect4.ServiceKey.instLawfulOrderLT
  , `Effect4.ServiceKey.le_antisymm
  , `Effect4.ServiceKey.le_iff
  , `Effect4.ServiceKey.le_refl
  , `Effect4.ServiceKey.le_total
  , `Effect4.ServiceKey.le_trans
  , `Effect4.ServiceKey.lt_asymm
  , `Effect4.ServiceKey.lt_iff
  , `Effect4.ServiceKey.lt_iff_le_not_le
  , `Effect4.ServiceKey.lt_irrefl
  , `Effect4.ServiceKey.lt_trans
  , `Effect4.ServiceKey.lt_trichotomy
  , `Effect4.ServiceKey.mk
  , `Effect4.ServiceKey.mk.inj
  , `Effect4.ServiceKey.mk.injEq
  , `Effect4.ServiceKey.mk.noConfusion
  , `Effect4.ServiceKey.mk.sizeOf_spec
  , `Effect4.ServiceKey.name
  , `Effect4.ServiceKey.noConfusion
  , `Effect4.ServiceKey.noConfusionType
  , `Effect4.ServiceKey.rec
  , `Effect4.ServiceKey.recOn
  , `Effect4.ServiceKey.service
  , `Effect4.ServiceKey.transport
  , `Effect4.ServiceKey.transport_rfl
  , `Effect4.ServiceName
  , `Effect4.ServiceName.casesOn
  , `Effect4.ServiceName.ctorIdx
  , `Effect4.ServiceName.mk
  , `Effect4.ServiceName.mk.inj
  , `Effect4.ServiceName.mk.injEq
  , `Effect4.ServiceName.mk.noConfusion
  , `Effect4.ServiceName.mk.sizeOf_spec
  , `Effect4.ServiceName.noConfusion
  , `Effect4.ServiceName.noConfusionType
  , `Effect4.ServiceName.rec
  , `Effect4.ServiceName.recOn
  , `Effect4.ServiceName.value
  , `Effect4.ServiceTypeCode
  , `Effect4.ServiceTypeCode.casesOn
  , `Effect4.ServiceTypeCode.ctorIdx
  , `Effect4.ServiceTypeCode.mk
  , `Effect4.ServiceTypeCode.mk.inj
  , `Effect4.ServiceTypeCode.mk.injEq
  , `Effect4.ServiceTypeCode.mk.noConfusion
  , `Effect4.ServiceTypeCode.mk.sizeOf_spec
  , `Effect4.ServiceTypeCode.noConfusion
  , `Effect4.ServiceTypeCode.noConfusionType
  , `Effect4.ServiceTypeCode.rec
  , `Effect4.ServiceTypeCode.recOn
  , `Effect4.ServiceTypeCode.value
  , `Effect4.ServiceUniverse
  , `Effect4.ServiceUniverse.Carrier
  , `Effect4.ServiceUniverse.casesOn
  , `Effect4.ServiceUniverse.ctorIdx
  , `Effect4.ServiceUniverse.exists_carrier_collision
  , `Effect4.ServiceUniverse.mk
  , `Effect4.ServiceUniverse.mk.inj
  , `Effect4.ServiceUniverse.mk.injEq
  , `Effect4.ServiceUniverse.mk.noConfusion
  , `Effect4.ServiceUniverse.mk.sizeOf_spec
  , `Effect4.ServiceUniverse.noConfusion
  , `Effect4.ServiceUniverse.noConfusionType
  , `Effect4.ServiceUniverse.rec
  , `Effect4.ServiceUniverse.recOn
  , `Effect4.instDecidableEqServiceKey
  , `Effect4.instDecidableEqServiceKey.decEq
  , `Effect4.instDecidableEqServiceKey.decEq.match_1
  , `Effect4.instDecidableEqServiceName
  , `Effect4.instDecidableEqServiceName.decEq
  , `Effect4.instDecidableEqServiceName.decEq.match_1
  , `Effect4.instDecidableEqServiceTypeCode
  , `Effect4.instDecidableEqServiceTypeCode.decEq
  , `Effect4.instDecidableEqServiceTypeCode.decEq.match_1
  , `Effect4.instDecidableLtServiceKey
  , `Effect4.instLTServiceKey
  , `Effect4.instReprServiceKey
  , `Effect4.instReprServiceKey.repr
  , `Effect4.instReprServiceName
  , `Effect4.instReprServiceName.repr
  , `Effect4.instReprServiceTypeCode
  , `Effect4.instReprServiceTypeCode.repr
  ]

private def contractedApiDeclarations : List (Name × String) :=
  [ (`Effect4.ServiceName, "ENV-KEY-01")
  , (`Effect4.ServiceName.mk, "ENV-KEY-01")
  , (`Effect4.ServiceName.value, "ENV-KEY-01")
  , (`Effect4.ServiceTypeCode, "ENV-KEY-01")
  , (`Effect4.ServiceTypeCode.mk, "ENV-KEY-01")
  , (`Effect4.ServiceTypeCode.value, "ENV-KEY-01")
  , (`Effect4.ServiceKey, "ENV-KEY-01")
  , (`Effect4.ServiceKey.mk, "ENV-KEY-01")
  , (`Effect4.ServiceKey.name, "ENV-KEY-01")
  , (`Effect4.ServiceKey.service, "ENV-KEY-01")
  , (`Effect4.ServiceKey.rec, "ENV-KEY-01")
  , (`Effect4.ServiceKey.lt_iff, "ENV-KEY-02")
  , (`Effect4.ServiceKey.lt_irrefl, "ENV-KEY-02")
  , (`Effect4.ServiceKey.lt_trans, "ENV-KEY-02")
  , (`Effect4.ServiceKey.lt_trichotomy, "ENV-KEY-02")
  , (`Effect4.ServiceKey.Conflict, "ENV-KEY-03")
  , (`Effect4.ServiceKey.conflict_iff, "ENV-KEY-03")
  , (`Effect4.ServiceUniverse, "ENV-KEY-04")
  , (`Effect4.ServiceUniverse.mk, "ENV-KEY-04")
  , (`Effect4.ServiceUniverse.Carrier, "ENV-KEY-04")
  , (`Effect4.ServiceKey.Carrier, "ENV-KEY-04")
  , (`Effect4.ServiceKey.carrier_def, "ENV-KEY-04")
  , (`Effect4.ServiceKey.transport, "ENV-KEY-04")
  , (`Effect4.ServiceKey.transport_rfl, "ENV-KEY-04")
  , (`Effect4.ServiceUniverse.exists_carrier_collision, "ENV-KEY-04")
  ]

private def orderBridgeApiDeclarations : List Name :=
  [ `Effect4.ServiceKey.Le
  , `Effect4.ServiceKey.instLE
  , `Effect4.ServiceKey.le_iff
  , `Effect4.ServiceKey.instDecidableLE
  , `Effect4.ServiceKey.lt_asymm
  , `Effect4.ServiceKey.le_refl
  , `Effect4.ServiceKey.le_trans
  , `Effect4.ServiceKey.le_antisymm
  , `Effect4.ServiceKey.le_total
  , `Effect4.ServiceKey.lt_iff_le_not_le
  , `Effect4.ServiceKey.instIsPreorder
  , `Effect4.ServiceKey.instIsPartialOrder
  , `Effect4.ServiceKey.instIsLinearOrder
  , `Effect4.ServiceKey.instLawfulOrderLT
  ]

private def theoremReceipts : List (Name × String) :=
  [ (`Effect4.ServiceKey.lt_iff, "ENV-KEY-02")
  , (`Effect4.ServiceKey.lt_irrefl, "ENV-KEY-02")
  , (`Effect4.ServiceKey.lt_trans, "ENV-KEY-02")
  , (`Effect4.ServiceKey.lt_trichotomy, "ENV-KEY-02")
  , (`Effect4.ServiceKey.conflict_iff, "ENV-KEY-03")
  , (`Effect4.ServiceKey.carrier_def, "ENV-KEY-04")
  , (`Effect4.ServiceKey.transport_rfl, "ENV-KEY-04")
  , (`Effect4.ServiceUniverse.exists_carrier_collision, "ENV-KEY-04")
  ]

private def orderBridgeTheoremReceipts : List Name :=
  [ `Effect4.ServiceKey.le_iff
  , `Effect4.ServiceKey.lt_asymm
  , `Effect4.ServiceKey.le_refl
  , `Effect4.ServiceKey.le_trans
  , `Effect4.ServiceKey.le_antisymm
  , `Effect4.ServiceKey.le_total
  , `Effect4.ServiceKey.lt_iff_le_not_le
  ]

/-!
The bridge is a separate local receipt, not a new Context proof graph.  These
declarations make the exact synthesis and relation checks part of the Lean
module that the generator must compile before it may report the bridge leaf.
-/

private abbrev orderBridgeLEReceipt : LE Effect4.ServiceKey :=
  inferInstance

private abbrev orderBridgeDecidableLEReceipt (a b : Effect4.ServiceKey) :
    Decidable (a ≤ b) :=
  inferInstance

private theorem orderBridgeLinearOrderReceipt : Std.IsLinearOrder Effect4.ServiceKey :=
  inferInstance

private theorem orderBridgeLawfulOrderLTReceipt : Std.LawfulOrderLT Effect4.ServiceKey :=
  inferInstance

private theorem orderBridgeLeRelationReceipt (a b : Effect4.ServiceKey) :
    a ≤ b ↔ (a < b ∨ a = b) :=
  Effect4.ServiceKey.le_iff a b

private theorem orderBridgeLtRelationReceipt (a b : Effect4.ServiceKey) :
    a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
  Effect4.ServiceKey.lt_iff_le_not_le a b

private theorem orderBridgeComputesForwardReceipt :
    (Effect4.ServiceKey.mk (Effect4.ServiceName.mk 0)
        (Effect4.ServiceTypeCode.mk 9)) ≤
      Effect4.ServiceKey.mk (Effect4.ServiceName.mk 1)
        (Effect4.ServiceTypeCode.mk 0) := by
  decide

private theorem orderBridgeComputesBackwardReceipt :
    ¬ ((Effect4.ServiceKey.mk (Effect4.ServiceName.mk 1)
          (Effect4.ServiceTypeCode.mk 0)) ≤
        Effect4.ServiceKey.mk (Effect4.ServiceName.mk 0)
          (Effect4.ServiceTypeCode.mk 9)) := by
  decide

private def orderBridgeReceiptRows : List (String × String) :=
  [ ("instance-synth", "LE Effect4.ServiceKey")
  , ("instance-synth", "Decidable (a <= b) for Effect4.ServiceKey")
  , ("instance-synth", "Std.IsLinearOrder Effect4.ServiceKey")
  , ("instance-synth", "Std.LawfulOrderLT Effect4.ServiceKey")
  , ("relation", "a <= b iff a < b or a = b")
  , ("relation", "a < b iff a <= b and not b <= a")
  , ("computation", "ServiceKey(0,9) <= ServiceKey(1,0)")
  , ("computation", "not ServiceKey(1,0) <= ServiceKey(0,9)")
  ]

private def checkOrderBridgeReceipts : CommandElabM Unit := do
  let _ : LE Effect4.ServiceKey := orderBridgeLEReceipt
  let _ : (a b : Effect4.ServiceKey) → Decidable (a ≤ b) :=
    orderBridgeDecidableLEReceipt
  let _ : Std.IsLinearOrder Effect4.ServiceKey := orderBridgeLinearOrderReceipt
  let _ : Std.LawfulOrderLT Effect4.ServiceKey := orderBridgeLawfulOrderLTReceipt
  let _ : ∀ a b : Effect4.ServiceKey, a ≤ b ↔ (a < b ∨ a = b) :=
    orderBridgeLeRelationReceipt
  let _ : ∀ a b : Effect4.ServiceKey, a < b ↔ a ≤ b ∧ ¬ b ≤ a :=
    orderBridgeLtRelationReceipt
  let _ := orderBridgeComputesForwardReceipt
  let _ := orderBridgeComputesBackwardReceipt

private def axiomReceipts : List Name :=
  [ `Effect4.ServiceName
  , `Effect4.ServiceTypeCode
  , `Effect4.instDecidableEqServiceName
  , `Effect4.instDecidableEqServiceTypeCode
  , `Effect4.ServiceKey
  , `Effect4.instDecidableEqServiceKey
  , `Effect4.instReprServiceKey
  , `Effect4.ServiceKey.Lt
  , `Effect4.instLTServiceKey
  , `Effect4.instDecidableLtServiceKey
  , `Effect4.ServiceKey.lt_iff
  , `Effect4.ServiceKey.lt_irrefl
  , `Effect4.ServiceKey.lt_trans
  , `Effect4.ServiceKey.lt_trichotomy
  , `Effect4.ServiceKey.Le
  , `Effect4.ServiceKey.instLE
  , `Effect4.ServiceKey.le_iff
  , `Effect4.ServiceKey.instDecidableLE
  , `Effect4.ServiceKey.lt_asymm
  , `Effect4.ServiceKey.le_refl
  , `Effect4.ServiceKey.le_trans
  , `Effect4.ServiceKey.le_antisymm
  , `Effect4.ServiceKey.le_total
  , `Effect4.ServiceKey.lt_iff_le_not_le
  , `Effect4.ServiceKey.instIsPreorder
  , `Effect4.ServiceKey.instIsPartialOrder
  , `Effect4.ServiceKey.instIsLinearOrder
  , `Effect4.ServiceKey.instLawfulOrderLT
  , `Effect4.ServiceKey.Conflict
  , `Effect4.ServiceKey.instDecidableConflict
  , `Effect4.ServiceKey.conflict_iff
  , `Effect4.ServiceUniverse
  , `Effect4.ServiceKey.Carrier
  , `Effect4.ServiceKey.carrier_def
  , `Effect4.ServiceKey.transport
  , `Effect4.ServiceKey.transport_rfl
  , `Effect4.ServiceUniverse.exists_carrier_collision
  ]

private def checkTheoremReceipts : CommandElabM Unit := do
  let environment ← getEnv
  for name in theoremReceipts.map Prod.fst ++ orderBridgeTheoremReceipts do
    match environment.find? name with
    | some (.thmInfo _) => pure ()
    | some _ => failJoin m!"contracted theorem {name} is not a theorem declaration"
    | none => failJoin m!"missing contracted theorem {name}"

private def checkAxiomReceipts : CommandElabM Unit := do
  for name in axiomReceipts do
    let axioms ← collectAxioms name
    unless axioms.isEmpty do
      failJoin m!"axiom receipt for {name}: expected none, found {axioms.toList}"

private def checkContextKeyAssurance : CommandElabM Unit := do
  checkExactModuleSurface `Effect4.Context.Key expectedOwnedDeclarations
  checkOwners `Effect4.Context.Key (contractedApiDeclarations.map Prod.fst)
  checkOwners `Effect4.Context.Key orderBridgeApiDeclarations
  checkTheoremReceipts
  checkAxiomReceipts
  checkOrderBridgeReceipts

private def allocationFor (name : Name) : Option String :=
  if (`Effect4.ServiceName).isPrefixOf name ||
      (`Effect4.instDecidableEqServiceName).isPrefixOf name ||
      (`Effect4.instReprServiceName).isPrefixOf name then
    some "E4-TYPE-ENV-SERVICE-NAME"
  else if (`Effect4.ServiceTypeCode).isPrefixOf name ||
      (`Effect4.instDecidableEqServiceTypeCode).isPrefixOf name ||
      (`Effect4.instReprServiceTypeCode).isPrefixOf name then
    some "E4-TYPE-ENV-SERVICE-TYPE-CODE"
  else if (`Effect4.ServiceUniverse).isPrefixOf name then
    some "E4-TYPE-ENV-SERVICE-UNIVERSE"
  else if (`Effect4.ServiceKey).isPrefixOf name ||
      (`Effect4.instDecidableEqServiceKey).isPrefixOf name ||
      (`Effect4.instDecidableLtServiceKey).isPrefixOf name ||
      (`Effect4.instLTServiceKey).isPrefixOf name ||
      (`Effect4.instReprServiceKey).isPrefixOf name then
    some "E4-TYPE-ENV-SERVICE-KEY"
  else
    none

private def localReceiptFor (name : Name) : String :=
  if orderBridgeApiDeclarations.contains name then
    "ENV-LEAF-KEY-ORDER-BRIDGE"
  else
    "ENV-LEAF-KEY-IDENTITY"

private def emitContextKeyAssurance : CommandElabM Unit := do
  checkContextKeyAssurance
  for name in expectedOwnedDeclarations do
    let some allocation := allocationFor name
      | failJoin m!"owned declaration {name} has no manifest allocation"
    liftIO <| IO.println s!"E4CTX\towned-declaration\t{name}\tEffect4.Context.Key\t{allocation}\t{localReceiptFor name}"
  for (name, obligation) in contractedApiDeclarations do
    liftIO <| IO.println s!"E4CTX\tapi\t{name}\tEffect4.Context.Key\t{obligation}"
  for name in orderBridgeApiDeclarations do
    liftIO <| IO.println s!"E4CTX\torder-bridge-api\t{name}\tEffect4.Context.Key\tENV-LEAF-KEY-ORDER-BRIDGE"
  for (name, obligation) in theoremReceipts do
    liftIO <| IO.println s!"E4CTX\ttheorem\t{name}\t{obligation}\taxioms=none"
  for name in orderBridgeTheoremReceipts do
    liftIO <| IO.println s!"E4CTX\torder-bridge-theorem\t{name}\tENV-LEAF-KEY-ORDER-BRIDGE\taxioms=none"
  for (kind, statement) in orderBridgeReceiptRows do
    liftIO <| IO.println s!"E4CTX\torder-bridge-receipt\t{kind}\t{statement}\tENV-LEAF-KEY-ORDER-BRIDGE"
  for name in axiomReceipts do
    liftIO <| IO.println s!"E4CTX\taxiom\t{name}\tENV-AX-KEY\tnone\t{localReceiptFor name}"

syntax (name := effect4CheckContextKeyAssurance)
  "#effect4_check_context_key_assurance" : command

syntax (name := effect4EmitContextKeyAssurance)
  "#effect4_emit_context_key_assurance" : command

syntax (name := effect4CheckExactCurrentModuleSurface)
  "#effect4_check_exact_current_module_surface " "[" ident,* "]" : command

syntax (name := effect4CheckContextDeclarationOwners)
  "#effect4_check_context_declaration_owners " ident "[" ident,* "]" : command

elab_rules : command
  | `(#effect4_check_context_key_assurance) =>
      checkContextKeyAssurance

elab_rules : command
  | `(#effect4_emit_context_key_assurance) =>
      emitContextKeyAssurance

elab_rules : command
  | `(#effect4_check_exact_current_module_surface [$names:ident,*]) => do
      let environment ← getEnv
      checkExactModuleSurface environment.mainModule
        (names.getElems.map Syntax.getId).toList

elab_rules : command
  | `(#effect4_check_context_declaration_owners $owner:ident [$names:ident,*]) =>
      checkOwners owner.getId (names.getElems.map Syntax.getId).toList

end Test.Environment.ContextKeyAssurance
