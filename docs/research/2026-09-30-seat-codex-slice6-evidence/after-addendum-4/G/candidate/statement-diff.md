# G statement changes

Exactly the two leaf rules and two leaf inversion conclusions acquire service lookup and normalized subtyping. Other rules and the checker agreement theorem signatures retain their shape. This candidate is uncompiled.

## src/Effect4/Laws/Program/Typing/HasTy.lean

Before:

```lean
  /-- `Layer.succeed(key, value)` (`Layer.ts:1074`): a service from a value already in hand.
  The premise is that the literal is in the machine's value alphabet — a string is not
  (`PROV-FB-STRING-VALUE`) — and the value's *type* plays no part. -/
  | succeed {key : ServiceKey} {value : Lit} {v : _root_.Effect4.Machine.Env.Val} :
      litVal value = some v →
      LayerHasTy sig (.succeed key value) ⟨Requirement.single key, .never, Requirement.empty⟩
  /-- `Layer.effect(key, body)` (`Layer.ts:1427`): the layer provides its key with the body's
  error, and requires the body's **scope-free** row — the layer's own scope answers the body's
  `Scope` requirement (`:1438`, `bodyRequires`). -/
  | effect {key : ServiceKey} {body : Eff Op} {t : EffTy} :
      HasTy sig [] body t →
      LayerHasTy sig (.effect key body) ⟨Requirement.single key, t.error, bodyRequires sig t⟩
```

After:

```lean
  /-- `Layer.succeed(key, value)` (`Layer.ts:1074`): a service from a value already in hand.
  The literal is in the machine's value alphabet — a string is not
  (`PROV-FB-STRING-VALUE`) — and its type is below the key's declared service type. -/
  | succeed {key : ServiceKey} {value : Lit} {v : _root_.Effect4.Machine.Env.Val} {ty : Ty} :
      litVal value = some v →
      sig.serviceTy key = some ty →
      Ty.sub (Lit.ty value).normalize ty.normalize = true →
      LayerHasTy sig (.succeed key value) ⟨Requirement.single key, .never, Requirement.empty⟩
  /-- `Layer.effect(key, body)` (`Layer.ts:1427`): the layer provides its key with the body's
  error, and requires the body's **scope-free** row — the layer's own scope answers the body's
  `Scope` requirement (`:1438`, `bodyRequires`). Its answer is below the key's service type. -/
  | effect {key : ServiceKey} {body : Eff Op} {t : EffTy} {ty : Ty} :
      HasTy sig [] body t →
      sig.serviceTy key = some ty →
      Ty.sub t.answer.normalize ty.normalize = true →
      LayerHasTy sig (.effect key body) ⟨Requirement.single key, t.error, bodyRequires sig t⟩
```

## src/Effect4/Laws/Program/Typing/CheckInversion.lean

Before:

```lean
theorem inv_layer_succeed (sig : Signature Op) (p : List Nat) (key : ServiceKey) (value : Lit) :
    ∀ l, checkLayer sig p (.succeed key value : LayerTerm Op) = .ok l →
      ∃ v, litVal value = some v ∧
        l = ⟨Requirement.single key, .never, Requirement.empty⟩ := by
  aesop (rule_sets := [Effect4.Checker])

theorem inv_layer_effect (sig : Signature Op) (p : List Nat) (key : ServiceKey) (body : Eff Op) :
    ∀ l, checkLayer sig p (.effect key body) = .ok l →
      ∃ t, check sig [] (p ++ [0]) body = .ok t ∧
        l = ⟨Requirement.single key, t.error, bodyRequires sig t⟩ := by
  aesop (rule_sets := [Effect4.Checker])

```

After:

```lean
theorem inv_layer_succeed (sig : Signature Op) (p : List Nat) (key : ServiceKey) (value : Lit) :
    ∀ l, checkLayer sig p (.succeed key value : LayerTerm Op) = .ok l →
      ∃ v ty, litVal value = some v ∧ sig.serviceTy key = some ty ∧
        Ty.sub (Lit.ty value).normalize ty.normalize = true ∧
        l = ⟨Requirement.single key, .never, Requirement.empty⟩ := by
  aesop (rule_sets := [Effect4.Checker])

theorem inv_layer_effect (sig : Signature Op) (p : List Nat) (key : ServiceKey) (body : Eff Op) :
    ∀ l, checkLayer sig p (.effect key body) = .ok l →
      ∃ t ty, check sig [] (p ++ [0]) body = .ok t ∧ sig.serviceTy key = some ty ∧
        Ty.sub t.answer.normalize ty.normalize = true ∧
        l = ⟨Requirement.single key, t.error, bodyRequires sig t⟩ := by
  aesop (rule_sets := [Effect4.Checker])

```

The old succeed rule required only `litVal value = some v`. The old effect rule required only closed-body HasTy. Neither related the produced value to `sig.serviceTy key`. The new premises add that missing relationship; the layer signature still carries exactly the same output key, error and requirement row.

`checkLayer_sound`, `checkLayer_complete`, `layerTy_sound`, `layerTy_complete` and `layerHasTy_unique` keep their existing statements. The source candidate changes only the two constructor applications in checkLayer_sound; the existing completeness bank and downstream projection proofs are to be checked without speculative edits.
