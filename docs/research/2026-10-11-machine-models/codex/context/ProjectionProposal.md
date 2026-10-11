# Context type projection for central integration

`Codegen.Types.ofNormalized` needs the `Ty.contextOf` case before `Ty.handle`.
This file proposes that case; it does not edit the deferred `Codegen.Types` module.

```lean
  | .contextOf keys =>
    let services := keys.elems.map fun key =>
      if key = Effect4.Machine.Env.scopeKey then TypeRef.name ["Scope", "Scope"] []
      else TypeRef.literal ("k" ++ toString key.name.value ++ "_" ++ toString key.service.value)
    some (.name ["Context", "Context"] [match services with
      | [] => .name ["never"] []
      | [service] => service
      | many => .union many])
```

The empty row projects to `Context.Context<never>`.
An ordinary key projects to its full name and carrier-code identity.
Scope projects to Effect's existing `Scope.Scope` identity.
This is the rule `Codegen.keyIdentifier` uses in `src/Effect4/Codegen/PrintLeaf.lean`.
The reference contains a union when the row names several services.
This projection describes promised static keys, not actual service values or execution.

`Ty.renderRaw` currently renders every nonempty key as its full literal identity.
The central projection should also align that printer's Scope case with `Scope.Scope`.
A shared key reference belongs below both printers; it should not create a dependency cycle.

The full derived scheduler reaches this missing case through its existing authoring and Laws imports.
The source checker, annotation, admission, compiler, canonical image and native controls compile separately.
Automatic approval review refuses the delegated printer edit twice because the target slice is deferred.
The coordinator owns the required projection and the later behaviour sweep.
