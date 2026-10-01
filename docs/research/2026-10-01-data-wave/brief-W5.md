# Seat W5: the Schema and JSON arms per form, with the laws (commit 5)

Filled at dispatch: base (main after W1 and W4 merge), `S/note.md`'s K2 table and profile.
Rules: `README.md` here, plan §4, `AGENTS.md` (tsgo 7 only).

**The one thing.** Each form's arms are theorems of construction 1's embeddings: `schema` and
`ofSchema` at `objects` with named properties (optional keys as `optionalKey`/`optional`),
`Record`, `Union` of structs with a `_tag` literal (the whole-union image check), `Number`/`Int`,
`Null`/`Undefined`, `Arrays` with elements for tuples, declarations with type parameters for `app`;
the codec's object layout over the named value (row 165) with `fields?`'s exact field set and
`N_J`; the three laws (`ofSchema_schema` modulo `N_S`, `decode_of_encode`, `encode_sub`) and the
exactness theorems of commit 1 extended to every form.

## The work

1. The arms, form by form, each lifting its refusal-by-name from commit 4, with the law and a
   red/green pair in `Test/Schema/`.
2. The readable profile's text (S's algebra over `cata_representation`, the admission predicate,
   the annotation allowlist) as a second export beside `moduleSyntax`, with S's asserting controls;
   rc.112's behaviour at the edges reproduced under bun on files in `Test/` or the host lane.
3. Row 8's dedupe at the emitter (option (C)) if S measured it as a few lines.
4. Narrow builds; the `schema-codec` gate; `#print axioms`.

Receipt `receipt-W5.md`: the arms and laws per form; the profile's controls; the lines for rows 8,
123 (its input), 128 and the readable-profile row.
