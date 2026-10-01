# Seat R: the terms, the faces, and the acceptance harness

Read `README.md` here first. Your folder: `docs/research/2026-10-01-type-language-probe/R/`.
Worktree `/Users/pooks/Dev/lean4-effect4-probe-R`, branch `probe/R`. Read in full: synthesis §3.1
R3.9, §3.2 stage 1's acceptance, §3.3 "TypeScript printer and reader", §7 items 6–8, §8 Q8;
Codex's record review §3 and `practical-review.md` items 2 and 5, with `field-names.cjs` and its
log (`/private/tmp/codex-record-review-2026-10-01/`); the programs seat's `ProbeTodayP2.lean` and
`note.md` (`2026-10-01-data-probe/programs/`); `src/Effect4/Machine/Term.lean` (`Term`: var, lit,
app), `src/Effect4/Program/NativeAtom.lean` (the atom rows), `src/Effect4/Program/Typing/Rules.lean`
(`litArgTy`, DI-15's literal rule, `argsTy`), `src/Effect4/Codegen/Types.lean` (`ofNormalized`,
`parseLegacy`'s exclusion of object types at `:18-21`, `:268-321`), `src/Effect4/Codegen/Read.lean`
(the declared-type match at `:356`, the term reader at `:143-155`), `src/Effect4/Codegen/
SourceBindings.lean:170-180` (identifier bytes for member names), `src/Effect4/Codegen/Schema.lean:32`
(`Schema.dataObject`'s `Object.fromEntries`), the vendored TypeScript syntax
(`.lake/packages/typescript/TypeScript/TypeRef.lean:17-18` object types, `Syntax.lean:46`, `:70`
object literals and member access), `Test/contracts/README.md` (DI-78: the packet before the code),
`docs/core/host-boundary.md` §7 (row 122: the boundary projection, Decision 12 route A).

**The one thing.** Records need two term forms (construction and field projection) and a printed
and read-back face, and the choice between the atom route (synthesis §8 Q8: atoms, labels read
from literal arguments as `pair` reads its tag) and dedicated `Term` constructors is not settled
by a probe: Codex shows the atom route cannot check a field index through the existing argument
interface (numeric literals all type `.nat`; `evalFieldAccess` ignores the name). Decide it with
a model that includes the checker's interface, and extend the question to the other forms the
data wave adds (optional fields, maps, tagged unions): construction, projection, update, the tag
`select`, and what each prints as.

## Questions

1. **Term forms, both routes on a model.** On a copy of `Term`/`Terms` and `termTy`/`evalTerm`
   with the checker's literal rule: (a) atoms `recordMake`/`recordGet` whose typing rule is
   type-directed (the field name a `lit` argument; the result type read from the record type's
   canonical position; a wrong-but-in-range index refused; an unknown name a located refusal);
   (b) constructors `Term.record (fields : List (String × Term))` and `Term.field (t : Term)
   (name : String)`. For each: `termTy`'s rule, `evalTerm`'s equation, term soundness
   (`evalTerm_fits`'s new arms, seat A's `EnvTyped` form at your base), the generated `Term`
   folds (`cata_term`, `Terms`), the wire family's tag, and the measured lines. Recommend one,
   with the reason stated as a theorem shape (what the atom route cannot state).
2. **Name preservation.** Positional values carry no names, so printing and JSON encoding are
   type-directed: show on the model that `print` of a record value at its type yields `{ a: x }`
   with names from the type, that `read` recovers the term, and `read_print`/`read_exact` at the
   new forms (the reader's declared-type match at `Read.lean:356` needs `TypeRef.object` from
   source ingest: `Types.lean`'s legacy parser excludes object types; measure the parser arm).
   Non-identifier and special names: bracket syntax for `a-b`, the safe construction for
   `__proto__` (`Schema.dataObject`'s strategy; Codex's `field-names.cjs`: a quoted `__proto__`
   literal does not create the own property), Unicode names; the reader accepts exactly the chosen
   image. Run the host controls with `node` on files in your folder; record versions.
3. **The printed types.** `ofNormalized` → `TypeRef.object` with `readonly` fields in canonical
   order; optional fields as `a?: τ` (stage 4's policy: `optionalKey` versus `optional`, which
   admits an explicit `undefined`); maps as `Readonly<Record<K, V>>` or `ReadonlyMap`? (read what
   rc.112's `Schema.Record` types as, `vendor/.../Schema.ts`); tagged unions as discriminated
   unions `{ readonly _tag: "A", … } | …`. For each the `tsgo` check of a printed module
   (`tsgo` 7 at the harness's version; name it) and the assignability lane (row 68:
   `tools/Tools/TyVectors.lean` pairs → `generated/assignability.tsv`): the record pairs to add
   (permutations agree; width `incomplete`), run on a copy of the vectors into your folder.
4. **The boundary projection** (row 122, route A): the adapter lays a wider host object out
   canonically and drops extra keys; the strict codec refuses extra, duplicate and missing keys:
   the paired control (adapter strips, codec rejects) on the model; where the adapter lives today
   (`host-boundary.md` §7, the keyed `HostSession`) and the function it needs.
5. **The acceptance harness.** `ProbeTodayP2.lean` re-spelled with records: what it needs from
   P, Q and S (the exact list: `Ty.record`, the two term forms, the Schema arm, the codec arm, the
   adapter, the error adapter for DB-15's tagged pairs, the keyed session, two host rows); the
   scripted host answering rc.112's objects; the three expected answers; the `tsgo` check of the
   printed module against p2's idiomatic signatures. Write the harness skeleton as a probe that
   compiles today with the record parts stubbed by name (a `sorry`-free skeleton: the stubs are
   `Option`-returning placeholders with `#guard_msgs` noting what is missing), so the data wave's
   commit 8 is a diff, not a design.

## Deliverable

`R/note.md`: per question the evidence; the recommendation on the term forms with the theorem
shape; the printed forms table (type, TypeScript spelling, `tsgo` result, the reader arm); the
contract packet draft for the two term forms (DI-78: laws, preconditions, falsifiers) under
`R/contracts/`; the harness skeleton under `R/probes/`; the brief text for the data wave's
commits 6, 7 and 8; the decisions rows to amend or add (a term-form row; row 122's adapter; row 126
if equality at records is touched).
