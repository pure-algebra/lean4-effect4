# Foldlab language-neutral effect protocol

Status: **SCAFFOLD**, 2026-08-31

This is the shared interface boundary for reified effectful programs. It keeps
the Effect Core programme larger than any one host language:

| Authority | Owns |
| --- | --- |
| neutral protocol | stable identities, canonical bytes, profile membership, portable vectors |
| Lean Effect Core | checked admission, relational denotation, classifications, proofs |
| existing CAS model | current `Sig`, `Prog`, `PProg`, refusal, schema, and byte identities |
| Effect TypeScript adapter | rc.112 source mapping, generated codecs, runtime and language-service checks |
| future adapters | language-specific bindings over the same admitted protocol rows |

The eventual generic call/reply frame will identify the protocol digest,
correlation, operation, and canonical request/response bytes. Transport failure
is a separate signature and never becomes a program's typed effect merely
because a host disconnected.

`effect-ts-rc112` is one planned profile. Its cutover can close after its own
rows, adapter, vectors, language-service coverage, and Lean relations close.
That does not claim every language or every effectful interface has cut over.

No canonical manifest exists yet. The current files establish ownership and
generation boundaries only.
