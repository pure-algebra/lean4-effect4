# Context type projection for central integration

`Codegen.Types.ofNormalized` lacks the `Ty.contextOf` case.
The coordinator owns this target migration.

A context row names promised static keys, not service values.
The empty row projects to `Context.Context<never>`.
Ordinary keys use their full name and carrier-code identity.
A nonempty row projects through a union of these service references.

`Codegen.keyIdentifier` treats the signature's `scopeKey` specially.
`Codegen.Print.declarationType` accepts signatures with different Scope keys.
A projection that hardcodes `Env.scopeKey` therefore fails for some signatures.
The earlier proposed hardcoded arm is withdrawn after the coordinator's review.

The target projection needs the active signature's Scope key or a located refusal.
`Ty.renderRaw` remains signature-free diagnostic spelling.
It prints every key's full literal identity and makes no target Scope claim.

The source checker, annotation, admission, compiler, canonical image and native controls compile separately.
The full derived scheduler reaches the missing target case through existing imports.
Automatic approval review refuses the delegated printer edit because the target slice is deferred.
The coordinator owns the projection and later behaviour sweep.
