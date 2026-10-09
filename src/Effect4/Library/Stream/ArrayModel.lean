module

/-!
# The independent transition of an array source

Latest `vendor/effect-4.0.1/src/Stream.ts:1052-1053`, `fromArray`, emits one nonempty array through `Channel.succeed`.
Latest `vendor/effect-4.0.1/src/Channel.ts:1139-1152`, `fromEffect`, records completion before returning that one effect.
This model observes the emitted batch and remaining batch.
It represents completion by an empty pending list under decisions row 331.
It imports neither the machine nor the stored step.
Placement: `stream-array-step-agreement`, role simulation, `translation-simulation`, R10.
Its consumer is `arrayStep_agrees`; whole-source and outside-runtime agreement remain separate.
-/

@[expose] public section
set_option autoImplicit false
namespace Effect4.Stream.ArrayModel

/-- Extract the pending batch and retain no pending elements. -/
def pull {A : Type} (pending : List A) : List A × List A := (pending, [])

end Effect4.Stream.ArrayModel
