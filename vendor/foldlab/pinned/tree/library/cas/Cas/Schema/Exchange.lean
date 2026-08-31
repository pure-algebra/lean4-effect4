import Cas.Schema.Notation
import Cas.Schema.Projection
-- The scheme VERSION byte a node carries is the grammar's ratified
-- constant, not a second spelling of `0` — `Cas/Grammar/Sorts.lean` is
-- a leaf over `Cas.Core.Node`, so citing it here costs one edge and
-- keeps the byte owned in one place.
import Cas.Grammar.Sorts

/-!
# The exchange kind — interactions as content

R15 rules the agent seam SYMMETRIC: an agent programs the store as a
client of `CasSig`, and the store programs an agent as a handler of
`LlmSig`, where `infer` is an operation whose ANSWER ENTERS ONLY AS
RECORDED CONTENT. This module is the stored form of that recording.
Nothing here is new theory: an exchange is a described kind like any
other, it rides the same CAS admission law, and its provenance is the
DAG walk the store already performs.

One exchange node records one turn of the seam:

- `prompt` — the word put to the model. Prose is already the estate's
  most common authoring surface; storing it makes it addressable,
  citable, and diffable like every other word.
- `answer` — what came back, verbatim. Under the R15 acquisition loop
  the answer is EVIDENCE and carries no trust; recording it is what
  makes the later gates auditable, so the bytes are kept as spoken and
  are never normalized here.
- `subject` — the content the exchange was about, addressed and never
  inlined.

## Why the subject is a union and the role is not

`subject` is `ExchangeSubject`, a tagged union, because "what an
exchange is about" is genuinely ALTERNATIVES and a `StoreRef` demands
one kind tag: a first exchange is about stored content of the schema
plane, and a following exchange is about the exchange before it. That
second arm is what makes a conversation a DAG walk rather than a list
the store cannot see — provenance of an answer is `subject` followed to
exhaustion. Adding an arm is how the kind grows to a new plane.

A `role` field (system/user/model) is deliberately NOT spelled. Role is
a property of an UTTERANCE, and an exchange is the PAIR; R15's seam has
exactly one operation and one answer, so position already determines
which side spoke, and a role tag would state that same fact twice. If
multi-party transcripts ever want spelling, the growth is a separate
`Utterance` kind, and it wants the dormant replay vocabulary
(`docs/effect-replay/CONTEXT.md` — Solicited delegation, Decision
trace) reactivated by ruling first, not quietly redefined here.

## The kind tag is a WORKING tag, not plane identity

`exchangeKindTag` is `0x58`, chosen here so that the exchange arm of
`ExchangeSubject` has a tag to demand and a chain can be built at all.
It is NOT registered as a reserved tag: exactly as with the sidecar
annotation kind, minting plane identity is ruling 9's question and
wants Lean and TypeScript counterparts together. Until that ruling,
`0x58` is the tag this kind's callers reside at, and `Cas.value`
accepts it because it is unreserved.

Like `Cas.Schema.Annotation`, this module keeps compiler
metaprogramming an opt-in import — the schema emitter and the mirrors
import it; the runtime facade does not.
-/

namespace Cas.Schema

open Cas.Schema.Notation

/-- The kind tag exchange nodes reside at. A WORKING tag, not a minted
plane identity: see the reserved-tag note above. -/
def exchangeKindTag : UInt8 := 0x58

/-- What one exchange is about, by plane: a schema node, or the
exchange that came before it. The arms are addressed references, so a
conversation's provenance is a walk and never a copy. -/
cas_union ExchangeSubject where
  | exchange (address : StoreRef exchangeKindTag)
  | schema (address : StoreRef schemaKindTag)

-- The generator's discrimination claim, checked at elaboration.
#guard ExchangeSubject.schemaCode.discriminated

/-- One recorded turn of the agent seam: the word put to the model, the
answer that came back, and the content the exchange was about. -/
cas_struct Exchange where
  answer : String
  prompt : String
  subject : ExchangeSubject

/-! ## Put from Lean — the acceptance for the projection bridge

The exchange is the first described kind Lean can PUT rather than only
mint, and this is the pin that says so. The turn below is the exact one
the effects suite records (`test/SchemaExchange.test.ts`), stored
through the exact same projection — kind tag `0x58`, revision 1 — and
the payload bytes are compared against that suite's own recorded string
character for character.

The comparison is honest at both ends. The subject's ADDRESS never
reaches the payload: a typed reference lowers to the positional marker
`{"$ref":0}` and rides the node's reference array instead. So the
payload half of the pin is address-free and compares verbatim against
the runtime's recording, while the reference half is what carries the
address and the kind tag the store's admission law checks. -/

/-- The pin's subject address. Its bytes reach the reference array and
never the payload — which is why the payload pin below is a literal
rather than a computation over this value. -/
def pinSubject : Addr32 := ⟨List.replicate 32 0xab, by simp⟩

/-- One recorded turn, the same one the effects suite stores. -/
def pinExchange : Exchange :=
  { answer := "a struct of seven fields, one of them a typed reference"
  , prompt := "what does this schema describe?"
  , subject := .schema ⟨pinSubject⟩ }

-- The payload bytes agree with the runtime mirror's, envelope included:
-- `SchemaExchange.test.ts` records this string for the same value.
#guard putPayload 1 pinExchange == some
  "{\"revision\":1,\"value\":{\"answer\":\"a struct of seven fields, one of them a typed reference\",\"prompt\":\"what does this schema describe?\",\"subject\":{\"_tag\":\"schema\",\"address\":{\"$ref\":0}}}}"

-- One typed edge, at the schema kind, addressing the subject — the same
-- reference array the suite asserts.
#guard putRefs 1 pinExchange == some [⟨schemaKindTag, pinSubject⟩]

-- The node itself: the exchange kind tag, that one edge, and the
-- payload's UTF-8 bytes.
#guard (putNode Cas.Grammar.schemeVersion exchangeKindTag 1 pinExchange).map
    (fun n => (n.version, n.tag, n.refs))
  == some (Cas.Grammar.schemeVersion, exchangeKindTag,
      [⟨schemaKindTag, pinSubject⟩])

end Cas.Schema
