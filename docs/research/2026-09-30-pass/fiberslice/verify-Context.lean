import Research.Pass.FiberSlice.Core

/-! Verifier probe (fiberslice): the seat's proposed context clause (`servicesFit`, Holes.lean
:82-88, copied verbatim) refuses a key with no static type. The typed world's `ServicesOk`
(`Laws/Program/Typed/Admission.lean:30-34`) leaves such keys unconstrained. Does a context the
program itself reads (`getContext`) carry such keys, so that a host echoing it back is refused?
Finite checks, not proofs. Research evidence, outside the Test root. Base `be15b062`. -/

set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace Research.Pass.FiberSliceVerify.Context
open Effect4 Effect4.Machine Effect4.Program Research.Pass.FiberSlice

/-- Copied from the seat's `Holes.lean`. -/
def servicesFit (v : Val) : Bool :=
  match Val.context? v with
  | none => false
  | some ctx => ctx.services.entries.all fun s =>
    match nativeServiceTy s.key with
    | some ty => Val.hasTy s.valueVal ty
    | none => false

def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩

/-- The root's own context, read inside a scope and under a provided `nat` service. -/
def readCtx : Api.Program :=
  .scoped (.provideService natKey (.lit (.nat 5)) (.withFiber .getContext))

#guard (Api.typeOf readCtx).map (·.answer) = some Ty.context

def ctxVal : Option Val :=
  match (Api.run readCtx 1000).exit with
  | some (.success v) => some v
  | _ => none

#guard ctxVal.isSome
#guard ctxVal.all fun v => Val.hasTy v Ty.context
-- the keys it carries, and whether each has a static type
def keysAndTypes : List (ServiceKey × Option Ty) :=
  match ctxVal.bind Val.context? with
  | some ctx => ctx.services.entries.map fun s => (s.key, nativeServiceTy s.key)
  | none => []

#guard keysAndTypes.any fun (k, _) => k == natKey
-- the verdict of the proposed clause on the program's own context
#eval keysAndTypes.map fun (k, t) => (k.name.value, k.service.value, t.isSome)
#eval ctxVal.map servicesFit

/-- The same read under a provided layer (layers add the current memo map to the context). -/
def readCtxLayer : Api.Program :=
  .provideLayer (.effect natKey (.succeed (.lit (.nat 7)))) false (.withFiber .getContext)

#guard (Api.typeOf readCtxLayer).map (·.answer) = some Ty.context

def ctxLayer : Option Val :=
  match (Api.run readCtxLayer 1000).exit with
  | some (.success v) => some v
  | _ => none

#guard ctxLayer.isSome
#guard ctxLayer.all fun v => Val.hasTy v Ty.context
def layerKeys : List (ServiceKey × Option Ty) :=
  match ctxLayer.bind Val.context? with
  | some ctx => ctx.services.entries.map fun s => (s.key, nativeServiceTy s.key)
  | none => []

#eval layerKeys.map fun (k, t) => (k.name.value, k.service.value, t.isSome)
-- the proposed clause refuses the program's own context under a layer: a key with no static
-- type (the machine's own) is in it, and `servicesFit` answers `false` there
#guard layerKeys.any fun (_, t) => t.isNone
-- that key is the machine's memo map (`Machine/ContextMap.lean:670`)
#guard layerKeys.any fun (k, t) => k == Effect4.Machine.Env.currentMemoMapKey && t.isNone
#guard ctxLayer.map servicesFit = some false
-- while the scoped context (no layer) passes
#guard ctxVal.map servicesFit = some true

end Research.Pass.FiberSliceVerify.Context
