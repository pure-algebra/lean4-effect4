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

## Filled from probe S (2026-10-01; `type-language-probe/S/note.md` §7.2, §1.1, §1.3, §3, §5)

- **The arms in production idiom:** `S/patches/Bridge.lean.after`, `Codec.lean.after`,
  `LawsSchemaCodec.lean.after` (+764/−142 against `bff50631`); the K2 table is §1.1. Two copy
  devices translate: the copy's `optKey τ` field is the record field's optional flag; the copy orders
  fields by UTF-8 bytes while P's current copy is tag-first: the arms use only `canonF` and its laws,
  so the order is the one commit 4 lands.
- **Per form, arm, refusal and a red/green pair in `Test/Schema/`:** record (`objects`, string
  names; refusals at `[n]`, `[]`, `[k]`, `["annotations"]`, `[n, "annotations"]`,
  `["indexSignatures"]`; the codec over row 165's `ctor 0 [list names, list slots]`, strict: unnamed,
  repeated and missing keys refused; route A's adapter as `conv false`); optional key (`isOptional`;
  `optional(A)` once `undefined` lands; `red_optionalNull`); map (`Record(String, V)` only; repeated
  key refused; keys ascending in the value); tagged unions (no new arm; `ofSchema` reads n-ary
  `anyOf` right-nested, refuses `oneOf` and fewer than two members; `red_flatWithoutNS`);
  `Number`/`Int` (commit 1's whole checks; `number` reads plain `Number`; its codec on commit 3's
  frame); `Null`/`Undefined` (faces and retraction; codec when row 160 rules the images); tuples
  (`Arrays`, plain elements, no rest; arity two is `prod`); `app` (a declaration with type parameters;
  reserved ids read as their constructors; codec refused by name); `bytes` if row 161 (a)
  (`Declaration("effect/schema/Uint8Array")`; base64 codec owed).
- **Laws:** `ofSchema_schema` with the premise `t.schemaWf = true` (also `ofSchema_schema_cty`,
  `CTy.ofSchema_schema`) until formation gives it; `decode_of_encode`, `hasTy_decode`,
  `encode_injective` keep their text; `encode_sub` from P's `hasTy_sub` at the new forms;
  `adapt_member`; `codec_sub_adapt` under row 122's union premise (`red_codecSubAdaptUnion`);
  commit 1's exactness extended. Keep `red_sharedImage` and `red_repeat`.
- **The readable profile** (row 169): `S/probes/ReadableProfile.lean` as a module beside
  `Codegen/Schema.lean`, its 37 guards and 6 red controls as a contract battery, the pre-rendered key
  device replaced by the bumped package's per-key spelling; the conformance lane (S's `host/q3-*.ts`,
  `q4-routes.ts`) as one host check read by `make check-target`; `arbitrary` as the ninth key if
  ruled. May split out as seat SF (S §7.3) after W5.
- **Row 8's (C):** `dedupeRefs` and the checked entry points (`S/probes/RefDedupe.lean`), the seven
  consumers moved to `Except`, the three laws; the three fixtures stay byte-identical.
