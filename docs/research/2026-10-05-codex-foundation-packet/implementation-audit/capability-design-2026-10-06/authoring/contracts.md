# Concrete capability contracts

Status: proposed, uncompiled interface notation. The frozen source is `4b57609c03ad0a38fd81cfc2c09ea5731dfe7ff0`.
These names describe capabilities. They are not new declarations in the repository.

## Source identity

```text
Document = immutable Built + revision identity
Address = node path
        | containing node path + term slot + nested term path
        | containing node path + cause path + nested term path
```

`Built` supplies the exact program, row table and admission certificate.
The current signature is `⟨table, []⟩`. The revision validator binds these inputs together.
An address has meaning only under that document. Row names remain separate display metadata.

## Inspect

```text
inspectRaw : Document × Address -> Except ViewRefusal RawFocus
inspectChecked : Document × Address -> Except ViewRefusal CheckedFocus
```

`RawFocus` contains the exact selected existing syntax and its original address.
`CheckedFocus` adds inherited context data and the local checker's result.
It retains the sort and argument mode instead of forcing every focus into one type field.

An effect focus records `TyEnv`, `EffTy` and its exact `Checker.check` equation.
A term focus records `TyEnv`, the `argTy` constant flag, `Ty` and its exact inference equation.
A loop focus records all five roles, the cursor type and the body type.
Later statement views also retain the generator state. Layer views retain their closed-context rule.

The equations must be connected to the supplied root certificate by the successful checker descent.
An equation under a freely chosen environment is not enough.
One minimal implementation instruments the existing checker and proves that erasing the view preserves its result.
Its local-view theorem additionally validates each parent-to-child context transition.
This is checker evidence, not a second acceptance judgment.

First checked scope: effect-to-effect source routes in admitted reference-free programs, including Routing and nested loops.
Ordinary effect term slots and their nested terms are supported. Non-effect source families refuse opaquely.
General raw inspection and whole rebuild remain available outside that scope.
Unsupported checked routes produce a view refusal, not a claim that the program is ill-typed.

Loop data uses these exact equations, with `C = cursorTy.getD C0`:

```text
termTy sig Γ initial = some C0
termTy sig (Γ ++ [C]) test = some bool
Checker.check sig (Γ ++ [C]) (p ++ [0]) body = ok ⟨B,E,R⟩
termTy sig (Γ ++ [C,B]) step = some C1
termTy sig (Γ ++ [C]) result = some D
Ty.sub C0.normalize C.normalize = true
Ty.sub C1.normalize C.normalize = true
whole type = ⟨D,E,R⟩
```

For general original syntax with references, the checked body is `Eff.expandIn root body`.
A reference origin must distinguish its use, target and nested expansion origin.
The reference-free initial scope does not fabricate that missing mapping.

## Replace and rebuild

```text
replace : Document × Address × Replacement -> Except EditRefusal Document
```

`Replacement` matches the addressed existing sort. The operation constructs a candidate and calls `Built.rebuild`.
The output law combines exact structural replacement with `rebuild_spec` and `rebuild_admitted`.
The old table and names remain. The new type may differ.

Refusals distinguish stale identity, invalid address, wrong sort and whole-admission failure.
A type-preserving variant adds an explicitly named comparison on the resulting `EffTy`.
Neither variant promises behavior preservation or a transport of the old run.

## Scoped composition

New source uses existing minted builders and `LoopSpec`.
A stored fragment carries its old input `TyEnv`; insertion names the split `pre ++ post` and inserted types.

```text
insertUnused : stored fragment × insertion description -> shifted existing Eff
```

The typing contract uses `effTy_weaken` or `effTy_insert` and `Signature.WeakenNatural`.
The proposed behavior connector compares `meaningB` after matching insertion into the value environment.
Both cursor and body-answer positions move when an outer loop input is inserted.
An arbitrary input map or capture substitution is outside this initial operation.

## Rewrite with an explicit loop observation

```text
rewrite : admitted input -> candidate
certificate : both Looped and ∀ k env stores, meaningB k input env stores = meaningB k candidate env stores
```

The certificate is a Laws-layer result. The candidate separately passes whole admission before public execution.
For a known pass, the API returns the exact candidate and the applicable claim data.
A theorem name in a serialized result is explanatory metadata, not a machine-checked proof object.

The first pass removes suspensions in both straight and looped programs.
The runtime connector additionally requires a finished bounded meaning from empty inputs and stores.
It yields separate sufficient fuel bounds. It does not compare same-fuel frontiers.

## Explain a runtime point

```text
runtimeView : reached run + source identity + selected activation -> read-only point/frame projection
```

A typed explanation requires the existing typed-state hypotheses for that run and tape.
For a loop frame, retain reference validity, world/service agreement, `EnvTyped` captures and `Fits` for the cursor.
The proof uses `LoopChecked`, `LoopFrameTyped` and `LoopProtocol`.
Other continuations retain their later-world quantification and machine/token correlation.

`FramePath` supplies path composition inside that proof.
It does not turn the projection into a mutable source lens or a unique frame-type inference procedure.

## Domain correction

The initial `Looped` restriction on inspection is superseded. Routing needs host performs and `catchIf`.
These are ordinary checker cases, even though the synchronous loop meaning excludes them.
Only the semantic rewrite keeps the `Looped` restriction.
The exact revised route and term-slot domain is in `../next-slices/focus/brief.md`.
