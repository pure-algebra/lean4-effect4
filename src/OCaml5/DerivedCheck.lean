import OCaml5.Render
import OCaml5.Derived.Fibers
import OCaml5.Derived.Stores
import OCaml5.Derived.Context
import OCaml5.Derived.Layer

/-!
# DerivedCheck — the hand descriptions against the Lean environment

The projection guard: every fact a hand `StructDesc`/`InductiveDesc` in `Render.lean` states
about the *Lean* side — name, parameters, field names and types in order (substitutes
excluded, holes and erasures included), constructor names and argument names and types —
must equal what `tools/Describe.lean` read off the environment into `Derived/*.lean`.
A `DIFF` is either an abbreviation in the hand copy (to be corrected there) or drift of the
Machine since the port (a finding). The full overlay that lets the hand copies be deleted
comes after this guard is green.
-/

namespace OCaml5.Ml.DerivedCheck

open OCaml5.Ml

/-- What the renderer consumes of a Lean type under a substitution: a substituted head loses
its arguments (the `Subst` is keyed on the head, so the hand copies abbreviate them), every
other head keeps its arguments, normalised the same way. `leanParams` is not compared: the
avatar's profile fixes the parameters by substitution, so an empty list there is a decision. -/
partial def norm (keys : List String) : LTy → LTy
  | .app h args => if keys.contains h then .app h [] else .app h (args.map (norm keys))

def projS (d : StructDesc) : String :=
  let keys := d.subst.map (·.1)
  (repr (d.leanName,
    (d.fields.filter fun f => match f.kind with | .substitute => false | _ => true).map
      fun f => (f.leanName, norm keys f.leanTy))).pretty 100000

def projI (d : InductiveDesc) : String :=
  let keys := d.subst.map (·.1)
  (repr (d.leanName,
    d.ctors.map fun c => (c.leanName, c.args.map fun a => (a.leanName, norm keys a.leanTy)))).pretty 100000

/-- The derived twin normalised under the *hand* description's substitution. -/
def projS' (hand derived : StructDesc) : String := projS { derived with subst := hand.subst }
def projI' (hand derived : InductiveDesc) : String := projI { derived with subst := hand.subst }

def report (tag : String) (hand derived : String) : IO Unit :=
  if hand == derived then IO.println s!"OK   {tag}"
  else IO.println s!"DIFF {tag}\n  hand    {hand}\n  derived {derived}"

def checks : List (String × String × String) :=
  [ ("Fibers.frameFiber", projS Avatar.frameFiber, projS' Avatar.frameFiber Derived.Fibers.frameFiber),
    ("Fibers.runFiber", projS Avatar.runFiber, projS' Avatar.runFiber Derived.Fibers.runFiber),
    ("Fibers.observer", projI Avatar.observer, projI' Avatar.observer Derived.Fibers.observer),
    ("Fibers.runEvent", projI Avatar.runEvent, projI' Avatar.runEvent Derived.Fibers.runEvent),
    ("Fibers.runDecision", projI Avatar.runDecision, projI' Avatar.runDecision Derived.Fibers.runDecision),
    ("Fibers.cmd", projI Avatar.cmd, projI' Avatar.cmd Derived.Fibers.cmd),
    ("Fibers.withFiberAction", projI Avatar.withFiberAction, projI' Avatar.withFiberAction Derived.Fibers.withFiberAction),
    ("Stores.refKey", projS Deep.Stores.refKey, projS' Deep.Stores.refKey Derived.Stores.refKey),
    ("Stores.deferredKey", projS Deep.Stores.deferredKey, projS' Deep.Stores.deferredKey Derived.Stores.deferredKey),
    ("Stores.err", projI Deep.Stores.err, projI' Deep.Stores.err Derived.Stores.err),
    ("Stores.defect", projI Deep.Stores.defect, projI' Deep.Stores.defect Derived.Stores.defect),
    ("Stores.fnName", projI Deep.Stores.fnName, projI' Deep.Stores.fnName Derived.Stores.fnName),
    ("Stores.finName", projI Deep.Stores.finName, projI' Deep.Stores.finName Derived.Stores.finName),
    ("Stores.ctx", projS Deep.Stores.ctx, projS' Deep.Stores.ctx Derived.Stores.ctx),
    ("Stores.completion", projI Deep.Stores.completion, projI' Deep.Stores.completion Derived.Stores.completion),
    ("Stores.syncOp", projI Deep.Stores.syncOp, projI' Deep.Stores.syncOp Derived.Stores.syncOp),
    ("Stores.raceName", projI Deep.Stores.raceName, projI' Deep.Stores.raceName Derived.Stores.raceName),
    ("Stores.progName", projI Deep.Stores.progName, projI' Deep.Stores.progName Derived.Stores.progName),
    ("Stores.name", projI Deep.Stores.name, projI' Deep.Stores.name Derived.Stores.name),
    ("Stores.actionName", projI Deep.Stores.actionName, projI' Deep.Stores.actionName Derived.Stores.actionName),
    ("Stores.thunk", projI Deep.Stores.thunk, projI' Deep.Stores.thunk Derived.Stores.thunk),
    ("Stores.finalizerStrategy", projI Deep.Stores.finalizerStrategy, projI' Deep.Stores.finalizerStrategy Derived.Stores.finalizerStrategy),
    ("Stores.scopeState", projI Deep.Stores.scopeState, projI' Deep.Stores.scopeState Derived.Stores.scopeState),
    ("Stores.scope", projS Deep.Stores.scope, projS' Deep.Stores.scope Derived.Stores.scope),
    ("Stores.deferredCell", projS Deep.Stores.deferredCell, projS' Deep.Stores.deferredCell Derived.Stores.deferredCell),
    ("Stores.deferredStore", projS Deep.Stores.deferredStore, projS' Deep.Stores.deferredStore Derived.Stores.deferredStore),
    ("Stores.scopeEntry", projS Deep.Stores.scopeEntry, projS' Deep.Stores.scopeEntry Derived.Stores.scopeEntry),
    ("Stores.scopeStore", projS Deep.Stores.scopeStore, projS' Deep.Stores.scopeStore Derived.Stores.scopeStore),
    ("Stores.stores", projS Deep.Stores.stores, projS' Deep.Stores.stores Derived.Stores.stores),
    ("Context.serviceKey", projS Deep.Context.serviceKey, projS' Deep.Context.serviceKey Derived.Context.serviceKey),
    ("Context.service", projS Deep.Context.service, projS' Deep.Context.service Derived.Context.service),
    ("Context.context", projS Deep.Context.context, projS' Deep.Context.context Derived.Context.context),
    ("Context.reference", projS Deep.Context.reference, projS' Deep.Context.reference Derived.Context.reference),
    ("Context.err", projI Deep.Context.err, projI' Deep.Context.err Derived.Context.err),
    ("Context.defect", projI Deep.Context.defect, projI' Deep.Context.defect Derived.Context.defect),
    ("Context.val", projI Deep.Context.val, projI' Deep.Context.val Derived.Context.val),
    ("Context.contextUpdate", projI Deep.Context.contextUpdate, projI' Deep.Context.contextUpdate Derived.Context.contextUpdate),
    ("Layer.layerId", projS Deep.Layer.layerId, projS' Deep.Layer.layerId Derived.Layer.layerId),
    ("Layer.memoMapId", projS Deep.Layer.memoMapId, projS' Deep.Layer.memoMapId Derived.Layer.memoMapId),
    ("Layer.serviceKey", projS Deep.Layer.serviceKey, projS' Deep.Layer.serviceKey Derived.Layer.serviceKey),
    ("Layer.defect", projI Deep.Layer.defect, projI' Deep.Layer.defect Derived.Layer.defect),
    ("Layer.contextUpdate", projI Deep.Layer.contextUpdate, projI' Deep.Layer.contextUpdate Derived.Layer.contextUpdate),
    ("Layer.combineMode", projI Deep.Layer.combineMode, projI' Deep.Layer.combineMode Derived.Layer.combineMode),
    ("Layer.construction", projI Deep.Layer.construction, projI' Deep.Layer.construction Derived.Layer.construction),
    ("Layer.layerDesc", projI Deep.Layer.layerDesc, projI' Deep.Layer.layerDesc Derived.Layer.layerDesc),
    ("Layer.finName", projI Deep.Layer.finName, projI' Deep.Layer.finName Derived.Layer.finName),
    ("Layer.syncOp", projI Deep.Layer.syncOp, projI' Deep.Layer.syncOp Derived.Layer.syncOp),
    ("Layer.progName", projI Deep.Layer.progName, projI' Deep.Layer.progName Derived.Layer.progName),
    ("Layer.name", projI Deep.Layer.name, projI' Deep.Layer.name Derived.Layer.name),
    ("Layer.actionName", projI Deep.Layer.actionName, projI' Deep.Layer.actionName Derived.Layer.actionName),
    ("Layer.thunk", projI Deep.Layer.thunk, projI' Deep.Layer.thunk Derived.Layer.thunk),
    ("Layer.scopeState", projI Deep.Layer.scopeState, projI' Deep.Layer.scopeState Derived.Layer.scopeState),
    ("Layer.scope", projS Deep.Layer.scope, projS' Deep.Layer.scope Derived.Layer.scope),
    ("Layer.scopeEntry", projS Deep.Layer.scopeEntry, projS' Deep.Layer.scopeEntry Derived.Layer.scopeEntry),
    ("Layer.scopeStore", projS Deep.Layer.scopeStore, projS' Deep.Layer.scopeStore Derived.Layer.scopeStore),
    ("Layer.memoEntry", projS Deep.Layer.memoEntry, projS' Deep.Layer.memoEntry Derived.Layer.memoEntry),
    ("Layer.memoMap", projS Deep.Layer.memoMap, projS' Deep.Layer.memoMap Derived.Layer.memoMap),
    ("Layer.st", projS Deep.Layer.st, projS' Deep.Layer.st Derived.Layer.st) ]

#eval do
  for (tag, hand, derived) in checks do report tag hand derived
  let n := (checks.filter fun (c : String × String × String) => c.2.1 == c.2.2).length
  IO.println s!"== {n} / {checks.length} agree"

end OCaml5.Ml.DerivedCheck
