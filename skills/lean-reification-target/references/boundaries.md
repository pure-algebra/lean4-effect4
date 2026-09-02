# Transformation boundaries

## The named arrows

For each actual arrow state the domain, result, refusal policy, retained
information, and evidence. Common arrows are raw input to checked syntax,
checked syntax to a proof carrier, source syntax to target syntax, target
syntax to bytes, bytes to parsed target, and target execution to observations.
Use separate records when these have different authorities.

Reification of existing source needs an admitted source language and a relation
to the emitted data. Producing a parse tree is not a proof that the tree has
the source program's behavior. Conversely, generating source from a Lean model
does not ingest arbitrary programs in that language. Keep these directions
visible when naming tools and completion claims.

## Codecs and identity

State the equations only on the domain where they hold:

- decoding an encoding reconstructs the checked value;
- encoding an accepted decoding reconstructs the raw input, if exact views are
  promised, or its specified normal form otherwise;
- normalization is idempotent and has the claimed semantic/identity relation;
- equal bytes imply the required equality of normalized programs, if injective
  encoding is part of the identity contract.

Preserve distinctions until the declared policy resolves them: duplicate map
keys, entry order, absent versus empty fields, Unicode spelling, signed zero,
NaN payloads or other numeric distinctions when admitted, reference sharing,
and unreachable stored content. JavaScript object syntax can alter meaning for
special keys; a source renderer must be checked against the actual target
grammar and object construction behavior.

A function defined in Lean is deterministic on its inputs. That fact alone
does not establish correct quoting, capture avoidance, exact byte identity, a
decode/render round trip, or semantic preservation.

## Compiler relation

State the observation map and environment/decision relation before choosing
forward or backward simulation. For an all-target-runs safety claim, excluding
extra bad target behavior is essential. A simulation in the opposite direction
may establish implementability of source behaviors while allowing those extras.
Equivalence needs the specified directions, including divergence or fairness
conditions when claimed. Name any stuttering that may be hidden.

Choose universal verified transformation or per-artifact validation according
to the contract. A verified validator needs a theorem that acceptance implies
the required source-target relation. Retain the exact pair and certificate it
checked. Rejected or timed-out validation is not acceptance. A compiler that
always refuses can satisfy conditional correctness, so separately exercise
the promised positive source profile.

## Host conformance

Record the exact layers under test. A Schema document codec accepting data
does not imply that revival, parsing, validation, or application execution
accepts it. A generated file typechecking does not prove its emitted functions
agree with the Lean definitions.

Use a corpus whose source coverage is independently accounted for. Include
directional encode/decode cases, failure cases, nested routes, and boundary
values relevant to the profile. If the Lean generator emits both tests and
expected results, retain an independent host observer or coverage check that
can expose a shared omission.

Pin installed package bytes independently of an upstream tag when the harness
uses those bytes. Check compiler/runtime versions, exact generated-file set,
case identity/order where required, and the intended diagnostic provider.
Reject an empty or partially analyzed project even if its diagnostic list is
empty. A mutation test must reach the claimed detector, and a restored control
must pass afterward.

Foreign implementations, clocks, scheduler policies, cancellation delivery,
runtime object identity, and resource effects remain external assumptions
unless explicitly modeled and related. Name any quotient between the model's
observations and the host's, and keep conformance claims within it.
