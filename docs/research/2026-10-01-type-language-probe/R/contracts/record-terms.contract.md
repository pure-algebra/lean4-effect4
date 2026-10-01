# Record term forms: construction and field projection (DI-78 packet, draft)

Status: **draft by probe seat R, 2026-10-01; not frozen.** It freezes when the owner rules the
value clause (proposed row R-1) and the term forms (proposed row R-2); the battery below is then
written red before any implementation, as `Test/contracts/README.md` requires. Written against the
recommended value clause (record values carry their canonical names); §6 states what changes if
row 119's positional clause stands.

Implementation (to be): `src/Effect4/Machine/Term.lean` (two `Term` constructors, the
`evalTerm` arms, `getField`), `src/Effect4/Program/Typing/Rules.lean` (the `argTy` arms and their
located refusals), `src/Effect4/Program/Authoring.lean` (the builders `record`, `field`),
`src/Effect4/Codegen/PrintLeaf.lean` (`printTerm`), `src/Effect4/Codegen/Read.lean` (`readTerm`),
`ts/eff/read.ts` (`readTerm`, `typeName`), the lean4-typescript package (element access and,
if `__proto__` is admitted, computed keys), the generated groups (Fold, Derived, eff, wire, lcnf, ts).

Battery (to be): `Test/Program/RecordTermContract.lean` (laws and red controls),
`Test/Codegen/RecordFacesContract.lean` (printer and reader), a host lane file under
`harness/truth/` for the name classes (node) and the printed module (tsgo).

Model evidence (research, not a battery): `docs/research/2026-10-01-type-language-probe/R/probes/`
`Q1Positional.lean`, `Q1Named.lean`, `Q1NestedTermRed.lean`, `Q2Faces.lean`, `Q1Bill.lean`;
host controls under `R/host/names/` and `R/host/p2/`.

## 1. Boundary

```lean
-- Machine/Term.lean, appended to the mutual Term/Terms block (wire tags record: 3, field: 4)
| record (labels : List String) (args : Terms)
| field (target : Term) (name : String)
```

The labels are written order and are kept (they print back). `Terms` carries the values, so no
family is nested: `Term`'s equality and wire codec still derive (`Q1NestedTermRed.lean` pins the
refusal of `record (fields : List (String × Term))`). A record value is the carrier's existing
frames, `ctor 0 [list names, list values]`, names and values in the canonical field order (UTF-8
bytes, `Ty.key`'s order); no `Val` constructor is added.

## 2. Required laws (theorem shapes)

- **L1 typing, construction.** `argTy sig Γ c (.record ls ts) = some τ ↔ ∃ tys, argsTy sig Γ false ts
  = some tys ∧ ls.length = tys.length ∧ distinct ls ∧ τ = .record (ls.zip tys)`. Field values are
  typed outside the literal rule (`false`): TypeScript widens a literal field of an object literal.
- **L2 typing, projection.** `argTy sig Γ c (.field t n) = some τ ↔ ∃ fs, argTy sig Γ false t =
  some (.record fs) ∧ lookupName n (canon fs) = some τ`. A union of records, `never` or `unknown`
  as the target is refused (TypeScript reads a property of a union only where every member has it;
  that rule belongs to stage 2's select).
- **L3 located refusal.** The checker refuses with a path and one of `notARecord`, `unknownName n`,
  `arity labels values`, `repeated n`; `explain = none ↔ typed` holds at the new forms (K4).
- **L4 evaluation.** `evalTerm env (.record ls ts) = (evalTerms env ts).bind fun vs => if ls.length
  = vs.length then some (recordVal (canon (ls.zip vs))) else none` and `evalTerm env (.field t n) =
  (evalTerm env t).bind (getField n)`, `getField n (ctor 0 [list ns, list vs]) = (idx n ns).bind
  (vs[·]?)`. No type is consulted.
- **L5 soundness** (row 148's `evalTerm_fits` with progress): `AtomsSound → EnvTyped w Γ env →
  argTy (nativeSignature table) Γ c t = some τ → ∃ v, evalTerm env t = some v ∧ Fits w v τ`.
  Model: `Q1Named.sound` (`[propext, Quot.sound]`).
- **L6 permutation.** A permuted record literal denotes the same value: for a permutation `π` of
  the label-value pairs, `evalTerm env (.record (π ls) (π ts)) = evalTerm env (.record ls ts)`
  (owed; it follows from `canon` being a function of the set of distinct-key pairs).
- **L7 folds.** `evalTerm`, `argTy`, `printTerm`, `Term.scoped`, `Term.weaken` are folds of the
  generated `TermAlgebra` (`hom_eq_cata_term`); the new fields are `term_record : List String →
  R .terms → R .term` and `term_field : R .term → String → R .term`. Model: `evalTerm_fold`.
- **L8 weakening.** `argTy_weaken`, `termTy_weaken`, `tagTest?_weaken` keep their statements
  (`Typing/Rules.lean:294-370`) with the two new arms.
- **L9 round trip.** `read_print`: `scoped n t → readTerm n (printTerm t) = .ok t`; `read_exact`:
  `readTerm n x = .ok t → printTerm t = x`, with no type argument to either. Model:
  `Q2Faces.Named.read_print`, `Q2Faces.Named.read_exact`.
- **L10 the image per name class.** Construction prints `{ a: x }` when every label is an ASCII
  identifier (`SourceBindings.identifierBytes`) other than `__proto__`, every key quoted otherwise,
  every key computed (`{ ["__proto__"]: x }`) when a label is `__proto__`; projection prints `t.n` at
  such an identifier and `t["n"]` otherwise; the reader accepts exactly that image.
- **L11 the target.** The printed module of the stage-1 acceptance passes `tsgo` against p2's
  idiomatic signatures with DB-15's error adapter (`R/host/p2/printed-p2-records.ts`: exit 0).
- **L12 conservativity** (DI-47). On record-free terms every existing definition and law is
  unchanged: wire tags appended, every existing golden byte-identical, every corpus verdict
  unchanged.

## 3. Preconditions

Row 119 (`Ty.record`, canonical order, repeated names refused at formation); the value clause of
row R-1; the name domain of row R-3 (every string with the three images of L10, or identifiers
only with the others refused by name until the lean4-typescript forms land).

## 4. Falsifiers (each a battery entry; proposed counterexample rows `E4-RECORD-CE-001`…)

| Id (proposed) | Attack | Expected | Model witness |
| --- | --- | --- | --- |
| 001 | `recordGet` as an atom over positional values is sound for some evaluator | refuted for every evaluator | `Q1Positional.recordGet_unsound`, `recordGetAt_unsound`, `index_blind` |
| 002 | a name-only projection over positional values evaluates soundly | refuted for every untyped evaluator | `Q1Positional.NameOnly.unsound` |
| 003 | a type-blind reader inverts the printer when the stored projection carries a position | refuted | `Q2Faces.no_untyped_reader` |
| 004 | a repeated label types | refused (`repeated`); TS2300/TS1117 on the target | `Q1Positional` §10 `#guard` |
| 005 | a projection of an unknown name or of a non-record types | refused, located | §10 `#guard`s |
| 006 | `eq` at a record types (DI-35, row 126) | refused | to write |
| 007 | width subsumption inside a program (`{a, b}` used at `{a}`) | refused by name (B-accept) | to write; row 68's `record/width` is `incomplete` |
| 008 | the printer emits the plain `{ __proto__: x }` (tsgo accepts it; node shows no own property) | never emitted | `R/host/names/forms-trap.ts`, `field-names.cjs` |
| 009 | `Object.fromEntries` is a typed record image (`Schema.dataObject`'s strategy) | refused by tsgo, TS2741 | `R/host/names/forms-red.ts` |
| 010 | the reader accepts a non-canonical image (a quoted identifier key, a bare non-identifier, a bracket at an identifier) | refused | `Q2Faces` §8 `#guard`s |
| 011 | `record (fields : List (String × Term))` derives equality | refused, pinned | `Q1NestedTermRed.lean` |
| 012 | positional values keep a union of records faithful | refuted: one value, two objects | `Q1Positional.union_value_ambiguous`, `positional_not_injective` |

## 5. Non-guarantees

No update form (spread) and no optional field in this packet (stage 4 and probe T's N1 bring
optional keys into the wave: their packet extends L1, L2, L4 with the absent-name rule); no tag
select (stage 2's packet: `Decision` gains a record arm); no claim about rc.112 accepting what the
printer emits beyond the `tsgo` checks named; every model theorem is about its model.

## 6. If row 119's positional value clause stands

L2 and L4 change: the projection stores its checked position, `field (target : Term) (index : Nat)
(name : String)`, typed by `(canon fs)[index]? = some (name, τ)` with the extra refusal
`wrongIndex n expected given` (`Q1Positional.sound`, `field_sound`), evaluated by `vs[index]?`.
L9 then holds only for a reader given the checker's environment: `argTy sig Γ c t = some τ →
readTermT sig Γ (printTerm t) = some t` (`Q2Faces.read_print`), and the tree has no such reader
(`Codegen/Read.lean:143-155` and `ts/eff/read.ts:647-668` are untyped, and the TypeScript reader has
no checker), so the packet must also specify the resolution step (the Lean table reader threading
the checker's environments, or an unresolved projection form resolved at admission) and its own
laws. Falsifier 012 then stands against stage 2, which needs a discriminant-first order or a
formation refusal of overlapping record branches.
