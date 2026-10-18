import Effect4.Store.Domain.Derived.Program
import Effect4.Store.Domain.Derived.Value
import Effect4.Machine.ContextMap

/-!
# The canonical instance of the machine's service context

The machine's context (`Machine.Env.Ctx`, `Machine/ContextMap.lean`) is a list of services with a
proof that their keys are distinct, and a service's value type depends on its key. The generator
writes neither: a `Prop` field is not a carrier, and it does not compose a dependent field. These
two instances are written by hand, in the generator's own encoding of a structure (`ctor 0` over
the fields), so the bytes are the ones it would write for the data fields. At `ValU` every key's
carrier is `Val`, so a service is a key and a value tree.

Reading a context decides the key condition again: a duplicate key refuses, and reading never
drops or reorders an entry. No proof is serialized. A machine name that captures a context
(`Machine.Ctx`, through `Machine.EffName`) now has a canonical image, so the run view the tool
answers with (`Live.View`) is encodable; the Tool group (`Tool/ToolDerived.lean`) uses them.
-/

set_option autoImplicit false

namespace Effect4.Store

open Effect4.Machine

namespace ServiceC

/-- A service at `ValU`: a struct of its key and its value tree. -/
def shapeDoc : ShapeDoc :=
  ⟨.struct "_root_.Effect4.Machine.Env.Service" [("key", (shape _root_.Effect4.ServiceKey).root),
     ("value", (shape _root_.Effect4.Store.Val).root)],
   (shape _root_.Effect4.ServiceKey).defs ++ (shape _root_.Effect4.Store.Val).defs⟩

def toVal : Env.Service Env.ValU → Val
  | ⟨k, v⟩ => .ctor 0 [Canonical.toVal k, Canonical.toVal (α := Val) v]

def ofVal : Val → Option (Env.Service Env.ValU)
  | .ctor 0 [v0, v1] =>
    match Canonical.ofVal (α := ServiceKey) v0, Canonical.ofVal (α := Val) v1 with
    | some k, some v => some ⟨k, v⟩
    | _, _ => none
  | _ => none

theorem ofVal_toVal (a : Env.Service Env.ValU) : ofVal (toVal a) = some a := by
  obtain ⟨k, v⟩ := a
  -- the value's type is `Carrier ValU k`, which reduces to `Val` only past reducible unfolding
  have hv : Canonical.ofVal (α := Val) (Canonical.toVal (α := Val) v) = some v :=
    Canonical.ofVal_toVal (α := Val) v
  simp only [toVal, ofVal, Canonical.ofVal_toVal, hv]

theorem ofVal_exact {v : Val} {a : Env.Service Env.ValU} (h : ofVal v = some a) :
    v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 v1 =>
    split at h
    · next b0 b1 h0 h1 =>
      injection h with h
      subst h
      simp only [toVal]
      rw [Canonical.ofVal_exact h0, Canonical.ofVal_exact h1]
    · exact nomatch h
  · exact nomatch h

theorem fits (a : Env.Service Env.ValU) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨k, v⟩ := a
  apply accepts_struct
  exact
    (acceptsFields_cons _ _ _ _ _ _
      (acceptsIn_mono_of_subset (fun _ hp => mem_append_of_left hp) _ _ (Canonical.fits k))
      (acceptsFields_cons _ _ _ _ _ _
        (acceptsIn_mono_of_subset (fun _ hp => mem_append_of_right hp) _ _
          (Canonical.fits (α := Val) v))
        (acceptsFields_nil _)))

instance instCanonical : Canonical (Env.Service Env.ValU) :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

end ServiceC

namespace ContextC

/-- A context: a struct of its entry list. -/
def shapeDoc : ShapeDoc :=
  ⟨.struct "_root_.Effect4.Machine.Env.Context"
      [("entries", (shape (List (Env.Service Env.ValU))).root)],
   (shape (List (Env.Service Env.ValU))).defs⟩

def toVal : Env.Ctx → Val
  | ⟨es, _⟩ => .ctor 0 [Canonical.toVal es]

/-- Read the entries, then decide the key condition again: a duplicate key refuses. -/
def ofVal : Val → Option Env.Ctx
  | .ctor 0 [v0] =>
    match Canonical.ofVal (α := List (Env.Service Env.ValU)) v0 with
    | some es => if h : (es.map Env.Service.key).Nodup then some ⟨es, h⟩ else none
    | none => none
  | _ => none

theorem ofVal_toVal (a : Env.Ctx) : ofVal (toVal a) = some a := by
  obtain ⟨es, h⟩ := a
  simp only [toVal, ofVal, Canonical.ofVal_toVal, h, dite_true]

theorem ofVal_exact {v : Val} {a : Env.Ctx} (h : ofVal v = some a) : v = toVal a := by
  unfold ofVal at h
  split at h
  · next v0 =>
    split at h
    · next es hes =>
      split at h
      · next hn =>
        injection h with h
        subst h
        simp only [toVal]
        rw [Canonical.ofVal_exact hes]
      · exact nomatch h
    · exact nomatch h
  · exact nomatch h

theorem fits (a : Env.Ctx) : shapeDoc.accepts (toVal a) = true := by
  obtain ⟨es, _⟩ := a
  apply accepts_struct
  exact acceptsFields_cons _ _ _ _ _ _ (Canonical.fits es) (acceptsFields_nil _)

instance instCanonical : Canonical Env.Ctx :=
  ⟨shapeDoc, toVal, ofVal, ofVal_toVal, ofVal_exact, fits⟩

-- A duplicate key refuses.
#guard (ofVal (.ctor 0 [Canonical.toVal
  ([⟨Env.maxOpsKey, Val.nat 1⟩, ⟨Env.maxOpsKey, Val.nat 2⟩] : List (Env.Service Env.ValU))])).isNone

end ContextC

end Effect4.Store
