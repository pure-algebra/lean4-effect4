# P row-128 exactness: bounded static review

Integration pin: `4034bd5ee6c33c904e947c80b6b72c6b81966b89`. Exactness probes were added in `eb4c0e53`; the inspected `P8Codec.lean` and `P8Schema.lean` have no diff from that commit at the integration pin. Final P is `c894c979`. Read-only source/log inspection; no compiler, build, generator, or repository edits.

**No contradiction found in P’s stated exactness theorems. One concrete acceptance-profile mismatch remains for W1 to reconcile.**

## W1: documentation annotations on checks need more than copying P’s reader

`brief-W1.md:47–49` allows documentation annotations on the exact `isInt`/nonnegative filters. Its dispatch amendment (`:70–76`) selects row 179’s eight-key allowlist and asks W1 to copy P’s proofs. But `P8Schema.lean:93–96` compares complete checks directly to the annotation-free `isIntCheck`/`nonNegativeCheck`; its normalizer keeps check annotations unchanged (`:72–73`). Merely changing the node-level `normAnn` does not change either fact.

Smallest control, **not compiled here**, follows directly from those definitions:

```lean
-- Under open Effect4 Effect4.Schema:
let r : Representation := .number none
  [Check.named "effect/schema/isInt" .null none
    (some [⟨"title", .str "documented integer"⟩])]
-- ProbeP.SchemaExact.ofSchemaC r = none
```

`Check.named` preserves that annotation argument (`Schema/Authoring.lean:18–21`), while `Bridge.isIntCheck` uses its default `none` (`Schema/Bridge.lean:26–27`). This is a stricter reader, not a false exactness proof. To meet W1’s stated filter profile, normalize permitted filter annotations before whole-check comparison and in `N_S`, then extend/recheck the corresponding number-case proof. Keep unknown/semantic annotations refused. Otherwise explicitly retain the narrower filter acceptance domain in the brief. This does not reopen the separately recorded `arbitrary`-annotation policy question.

## Scope and preservation checks

- **JSON duplicates are not hidden.** `P8Codec.lean:35–56` uses stable insertion sorting with no deduplication; `sortE_perm` (`:90–102`) preserves every entry. The imported `Codec.fields?` requires exact object length and a singleton match for each requested name (`Schema/Codec.lean:74–82`). `fields?_normJ` and `decodeRawC_normJ` establish order independence; they do not discard repeated keys.
- **The union repair preserves the encoder’s choice explicitly.** `P8Codec.lean:437–440` reads a second-branch value only when it is not a member of the first; the exactness proof reads both filters (`:1030–1049`). `normJ` does not reorder union branches. The red control (`:1108–1118`) refuses the noncanonical Success image and keeps the Failure image.
- **The successful-value domain remains restricted.** `encodeC` still performs production’s existing decode-back check (`:443–456`; production `Schema/Codec.lean:229–241`). “No re-encoding guard” means no new reader-side route-(a) re-encode. It does not mean the checked encoder becomes total on all members. P explicitly leaves old/new encoder-domain equality unproved (`P/note.md:391–393,659–660`).
- **No new-constructor proof is smuggled in.** P8 imports production Ty and the production bridge/codec (`P8Schema:1–9`, `P8Codec:1–8`), unlike P2–P7’s expanded type copy. Schema acceptance is today’s forms, exact bare checks, plain binary tuples, and binary `anyOf`; unhandled representations refuse (`P8Schema:89–160`). Codec unsupported heads likewise refuse (`P8Codec:441`). The theorems do not establish codecs/exactness for the later record/map/tuple/app/new-leaf additions.
- **Annotation loss is named and conditional.** The actual P probe uses a concrete two-key denylist, explicitly assumed complete (`P8Schema:35–45`), not the dispatched allowlist. Node annotations and the defect slot are guarded (`:81–83,89–159`); successful reads preserve all remaining structure modulo `normS` (`:411–525`). Policy replacement and its production proof/checks are W1 work. The retraction additionally requires closed types and `reservedFree` (`:328–338`); this premise is explicitly carried by W1 (`:74`), not concealed.
- **Bridge level matters.** The writer in the theorem is `Bridge.schema`; public `Ty.schema` normalizes first (`Schema/Bridge.lean:243–249`). W1 (`:38–41`) and row 128 explicitly retain that boundary. `N_S` does not justify erasing ordered-union differences or claiming exactness against the unrestricted normalizing public writer. This is already recorded scope, not a new defect.

The committed P logs report `exit=0` and the printed final theorems at `[propext, Quot.sound]` or less (`P/probes/logs/P8Codec.log`, `P8Schema.log`). Those are inspected producer receipts, not independently reproduced proof runs. No broader host/rc.112 acceptance equivalence follows from these Lean syntax equations alone.
