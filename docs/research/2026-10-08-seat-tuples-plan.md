# Generic typed tuple slice

The base is `9fbe735f`. The slice replaces tuple arity constructors with typed item data.

`StepItems Γ ts` holds one `Step Γ t` per declared item type. `Step.tuple` consumes those items.
`tupleShape` selects a product for two items. Other lengths retain the tuple type.
The existing `tuple2` and `tuple3` names become compatibility builders.
The translation retains the existing flat native tuple terms and values.

The generic packing and reading helpers serve `step-language-sound`, translation-simulation, R10.
Their consumer is the tuple arm of `Step.sound_core`, followed by module agreement laws.
The typing helpers serve `step-language-typed`, store-typing, R4.
Their consumer is `Step.typed_core`, followed by Queue operation typing.
The scope helper serves `operation-data-scoped`, initial-algebras-folds, R4.
Its consumer is module scope evidence used by `Api.Author.build`.
The generic-result frame helper serves `step-frame`, translation-simulation, R10.
Its consumer preserves the existing `Step.frame` statement.
Renaming and erased compilation retain their existing observations and consumers.

These laws require the existing input reading, typing, scope, identity, and normalization premises.
They establish no whole-record deriving support, allocation correspondence, progress, or target execution claim.
The checked `Modeled` profile and the host boundary remain unchanged.

The controls cover lengths zero through four, malformed typed items, normalization refusals, and Queue consumers.
