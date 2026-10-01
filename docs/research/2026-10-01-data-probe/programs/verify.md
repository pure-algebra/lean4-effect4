# Verifier of seat PROGRAMS (data probe, 2026-10-01)

**The one thing.** The seat's order stands, and every one of its probes reproduces byte for
byte. "Paper first, the record slice after G and H2 part one" holds. "The typed state reads `Ty`
in `Typed/Membership.lean` only" also holds, now by an environment census that sees `cases` as
well as `induction`. But each of its four paper decisions is framed wrong: one refuted (E), one
already taken (K), one that cannot be ruled apart from `Ty.sub` (V), and one under-billed (P):

- **E (type encoding): refuted.** The spine does not turn each `Ty` induction into a mutual pair.
  A single-motive eliminator (the tree's own idiom for `Json`), registered as
  `@[induction_eliminator]`, keeps the plain `induction t` with one added `record` case (proved).
  So the measurements do not favour the row extension.
- **K (JSON normaliser): already taken.** Today's codec reads its objects with an exact field set
  in any order and refuses extra keys (tested on `Option`; `Result`, `Exit` and `Cause` go through
  the same `fields?` or exact patterns, reading). So `N` is a reordering, and the divergence from
  rc.112's "ignore" default is already live.
- **V (value shape): cannot be ruled alone.** Width subtyping, which the note's row-68 shape asks
  for, is sound against the proved `hasTy_sub`/`fits_sub` only when values carry their labels
  (tested and proved in miniature). Also, `Val.ctor` under a struct shape already prints objects
  (tested). So V and `Ty.sub` are one decision.
- **P (handle-free payloads): bigger than stated.** It reaches six unconditional lemmas, not
  three. A payload carrier that is handle-free by construction is a third option the note does not
  list.

Two more gaps. `normalize` distributes a product over its union fields (tested: three binary
columns give eight members), and records need a rule for it that the note omits. And the ingest
census of 34 projects puts in-program decoding (route B) second only to `Schema.Struct` among the
heads the recognizer could not lift: about 756 against 2,032. So "route B waits for a program"
is a scope call for the owner to make with that number, not a finding.

Status: done, 2026-10-01. The tree is `refactor/phase1-phase3` at `ba9783c3`; that is the merge
`bc77e97f` plus docs-only `ba9783c3`. No tracked file was edited (`git status` clean). No
`lake build`, `make`, generator, `git add` or `git commit` ran, and the slice6 worktree was not
touched. Every Lean file compiled through the one-compiler lock with `-DwarningAsError=true`, one
at a time. A first verifier instance had left `verify-rerun-*` files whose ProbeBill run was
terminated mid-output; this instance overwrote them with a full rerun.

Evidence words: **proved** (a kernel theorem I ran, axioms printed), **tested** (a finite check I
ran), **reading** (read, not run), **assumed**. Every run here is a finite probe; the miniatures
import nothing from the tree and model obligations, they do not discharge the tree's.

Short paths as in the seat's note: `Program/…`, `Laws/…`, `Schema/…`, `Store/…` are under
`src/Effect4/`.

## 1. Verdicts

| id | verdict | evidence |
| --- | --- | --- |
| PROG-D1 | confirmed | **Reading** of every cited line of p1–p5, dogfood 1–3 and dogfood 6 §5: all match. The counts hold: records 5/5, a variant or union 4/5 (p3's is the core `Exit`), a payload read 4/5, JSON decoded 2/5, signed 2/5, recursive 0/5, structural equality 0/5. Two nits. "Three keep a record in state" names p3's log, which is a list cell; p3's record state is its `Queue<Job>` (p3:100). p1's `Cache` keys are strings and its values are deferred lookups (p1:73-75), so "keys code" is loose. |
| PROG-D2 | partly | Mostly **reading**, and the per-program lists are incomplete. p1 also needs `int` (`-e.status`, p1:78; the note's own §3.5). p2 and p3 need a number-to-text atom, and none exists among the 33 (`Program/NativeAtom.lean`; p2:104; p3:47, :48, :57, :84, :90; the rc.112 p3 log in `hostruns.log`). The RC12 evidence is not about records (D3). |
| PROG-D3 | partly | **Tested**, reproduced: `verify-rerun-ProbeTodayP2.log` is byte-identical, 10 guards. Two claims do not hold. (a) **Tested**: the tags are absorbed because of the probe's spelling `prod string string` (`ProbeTodayP2.lean:41`). With DB-15's literal tag, `prod (lit "SqlError") string`, the same handler builds and keeps every tag in both `withAuth`'s and `handle`'s error column (`verify-Refute.lean` §B, 5 guards). The real gap with rc.112 is that `catchIf` subtracts a caught tag only when nothing remains (DI-17, `Program/Typing/Rules.lean:217-222`), where rc.112's `catchTag` subtracts it. (b) "CurrentUser cannot be a service holding a record" rests on RC12. **Tested**: RC12's verdict, `serviceCarrier: signature none`, comes back the same for a `string` or `nat` carrier at code 12 (`verify-Refute.lean` §A). `Author.build` cannot declare any new service today (`nativeServiceTy`; `Test/Program/AuthorContract.lean:280`). The record refusal is rows 114 and 118 (**reading**). A smaller point: the rc.112 type compared (p2:117-120) is `main`'s, after `provide`, not `handle`'s. |
| PROG-D4 | partly | **Tested**, reproduced: green exits 0; red exits 1 with 12 errors (9 TS2345, 3 TS2375, `verify-tsgo.log`). Not every error is a positional projection on an object. **Tested**, red control split in two (`verify-ts/`): objects with pair errors give 10 errors, and pairs with the `SqlError` class give exactly the other 2 (TS2375 at columns 198 and 452). **Reading** of those two messages: the printed `Effect.suspend(() => c ? … : …)` carries no type arguments, so tsgo fixes `E` from the first branch when no candidate covers the class. The adapter the note cites (`DESIGN-BASIS.md:634-641`) is DB-15's error adapter, `Effect.mapError(toPair)`. Records alone would not flip T1 green. |
| PROG-D5 | partly | **Proved**, miniature reproduced: `dec_enc` at `[propext, Quot.sound]` and `enc_dec` at `[propext]`, logs byte-identical. Five problems. (i) The K2-to-JSON shape drops the tree's admission premise: `encode_of_hasTy` and `decode_encode` need `Ty.isCodecValue t v = true` (`Laws/Schema/Codec.lean:49-68`; the S-3 amendment, `Schema/Codec.lean:6-8`). (ii) The miniature decodes like rc.112's strip-unknown-keys default; the tree's codec does not (D10, **tested**). (iii) Three items are capabilities, not theorem shapes: folds regenerate, the scan's arm, wire tags 20/21. No conservativity shape is given for the core append (old types' clauses unchanged, old bytes decode the same; DI-47's "old-value exact decoding"). (iv) The width rule is sound against the proved `hasTy_sub`/`fits_sub` only for labeled values (D9, **tested** and **proved**). (v) The shapes are written over a `Fields` spine, while D8 recommends the extension. |
| PROG-D6 | partly | **Tested**, instrument reproduced byte-identically: `Ty` 65 rows / 27, `Err` 6/6, `Val` 241/16, `Lit` 7/7, `NativeAtom` 3/3; 16 `fold_of` lines. **Tested**, precedent: 44 files, +1,192/−488, `cases-policy.json` +954/−423 (`git show --numstat 0a2cb898`). Three corrections. (a) 65 and 38 count matcher rows; they are 58 and 31 distinct definitions. (b) **Tested**, proofs by an environment census (`verify-TyProofCensus.lean`): 27 hand-written theorems use `Ty`'s recursor, 6 generated ones do, and 2 use `fun_induction Ty.sub`. The seat's 30 includes `fits_mono`, which is a one-line corollary (`Membership.lean:829-831`). A further 28 theorems case on `Ty` and were not counted (19 hand-written, 9 generated in `TyView`). (c) **Reading**: at least six exhaustive `Ty` readers sit outside `Effect4`, where the instrument does not look: `tools/Tools/ProfileJson.lean:20`, `tools/Conform/Effect4/LcnfMl.lean:165` and `:271`, `tools/Conform/Effect4/LcnfSemantics.lean:41`, `src/OCaml5/Eff/Goldens.lean:90`, `src/OCaml5/Eff/Emit.lean:367`. The precedent's commit message names them. |
| PROG-D7 | partly | **Tested**, module claim confirmed by a stronger instrument: no theorem in any other `Typed/` module uses `Ty`'s recursor or `casesOn` (environment census), and no definition there matches on `Ty` (bill). The named five are wrong. `fits_mono` is not an induction. `fits_sub` is `fun_induction Ty.sub`, so its cases follow `sub`'s arms, which the record stage changes. `flatFits_fits` and `flatFits_map` case on `Ty` and are missing. The guard is checkable by the census, not "by the same grep": a grep for `induction` misses `cases`, `match` and `rcases`. |
| PROG-D8 | refuted | **Tested**, reproduced: plain `induction` refuses the mutual type, and the derived `Repr` is opaque and partial; the gate refuses partial definitions (`Test/Audit/AxiomGate.lean:439-440`, **reading**). The finding's conclusion is wrong. **Proved** (`verify-SpineInduction.lean`, all at `[propext]`): `induction t using T.rec (motive_2 := …)` closes the law in one theorem (`fitsT_defT_using`), and so does the recursor in term mode. A single-motive eliminator with a membership hypothesis for the fields, registered as `@[induction_eliminator]`, keeps the plain `induction t with` and adds one `record` case and one helper (`T.ind`, `fitsFs_defFs_of`, `fitsT_defT_plain`). The single-motive companion is the tree's own idiom for `Json` (`src/Effect4/Data/Json.lean:311-338`, there `@[elab_as_elim]`); the registration is the one new step. The helper has the same shape as the extension's `defU_list`. So the proof costs do not favour the extension. The spine's real extra is one hand `Repr`, already priced at about 20 lines (type algebra note §1.2). The extension's is junk in `Ty` plus a well-formedness premise. |
| PROG-D9 | partly | **Reading**: V1's analysis holds; products are positional (`Program/Typed.lean:80-83`). **Tested**: `ShapeDoc.print` prints a `.list` as an array whatever the shape (`verify-Refute.lean` §D). Two things are missing. First, a third option. **Tested**: `Val.ctor` under a `Shape.struct` or `Shape.sum` document already prints `{"id":2,"name":"bob"}` and `{"_tag":"Withdraw","amount":25}` (`Store/Domain/Shape.lean:493-524`). It needs no `Val` append, and `Result`/`Exit` values are `Val.ctor` today (`Program/Typed.lean:97-101`). V2, by contrast, forces `printIn`, one of the 16 forced `Val` readers. Second, a stronger case for labeled values (V2) than the note makes. **Tested** red and green, and **proved** in miniature (`verify-WidthCoupling.lean`, `hasTyObj_sub` at `[propext, Quot.sound]`): width subtyping is sound against `hasTy_sub`/`fits_sub` (`Laws/Program/Admits.lean:183`, `Membership.lean:837`) only when values carry their labels. So V decides row 68's shape. |
| PROG-D10 | partly | **Reading**: rc.112's default confirmed (`SchemaAST.ts:445-448`, `:2254-2290`). But the tree's codec already reads objects strictly. **Tested** (`verify-Refute.lean` §C, 6 guards): `Option`'s object decodes in either key order, refuses an extra or a duplicate key, and re-encodes in one order (`fields?`, `Schema/Codec.lean:74-82`). `Result`, `Exit` and `Cause` use the same `payload?`/`fields?` (**reading**). **Reading**: rc.112's `Option` codec is a union of `Struct`s with the "ignore" default (`Schema.ts:9719-9729`). So K is already taken, on the strict side. Today's codec is already exact only modulo key order, and a record codec that follows `fields?` needs `N` = reorder only. |
| PROG-D11 | partly | **Tested** by grep: the three lemmas and the 7 use sites in 6 files reproduce. The direction is confirmed: DB-15 refuses `Err.value` for exactly this reason. The bill is understated. `Err.image_handleFree` (`Machine/Alphabets.lean:123`) and `Defect.image_handleFree` (`:165`) fail too. `Val.keys_exitErr` (`Laws/Machine/Handles.lean:194`) is a further derived lemma, used at `Handles.lean:1125`, `:1149`, `:5338` and `Membership.lean:456`. `valOfErr_keys` is proved by cases on `Err`, not derived. A typing premise cannot reach `Image.HandleFree`, which has no type in scope. So P has a third option: a payload carrier that is handle-free by construction, which keeps all six lemmas unconditional (**reading**). |
| PROG-D12 | confirmed | **Tested**: no Makefile target names `compat` or the baseline (grep). `check-compat` and its comparator were deleted at `243ca0dd` (`git show --stat`). The policy file last changed at `c885f04a` (2026-09-17) and names `Ty.lit` but not `refOf`, `deferredOf`, `var` or `unknown` (python over the JSON). **Reading**: `docs/STATE.md:443-445` records the owner's cut of the compatibility lane on 2026-09-19. Nuance: §1.1 cites rows 56 and 61, which do run (`check-cases`) or print (`#exhaustive_gate`). Restating §1.1 matches the owner's cut; restoring the gate would reverse it. |
| PROG-D13 | partly | **Reading**: S-1 to S-5 hold. `Bridge.lean:38-63` has 20 arms; `ofSchema_schema` is at `:140`; `Api.schemaOf` (`Api.lean:136-138`) has zero callers (grep); the codec laws are at `:50` and `:62`, with the admission premise; `check-schema-codec` exists (`Makefile:412`). But "decided" rests on gitignored notes: `git check-ignore` reports `2026-09-10-schema-at-boundaries.md` and `…-boundary-decisions.md`. Tracked files presuppose D12 by name (decisions rows 5 and 9, `api-surface.md:74`, `coherence-principle.md:219-221`, `Api.lean:134`), but no register row carries its text. "D12" also names scout C's `Repr` choice (`api-surface.md:100`, `:227`) and the foundations' certificate protocol (`STATE.md:41`, `Test/Program/ProtocolCertificates.lean:3`). |
| PROG-D14 | partly | **Tested**: route A reproduced. "Needed by none of the five if route A is used" holds by moving each decode into the host. **Tested** (python over `docs/research/ingest-delivery/commit-4/census/summary.json`): across 34 pinned projects, `Schema.decodeUnknownEffect` is the second most frequent head the recognizer could not lift, 547 in 5 projects, after `Schema.Struct` at 2,032 in 12. The decode heads together (`decodeUnknown*`, `fromJsonString`, `decodeEffect`, `decode`) come to about 756. Route B is not a rare need. |
| PROG-D15 | confirmed | **Tested**, reproduced (`ProbeTodayP2.lean:229`; `ProbeRedControls.lean:93-95`). **Reading**: `internalHandleScan`'s `unknown` arm is `none` (`Program/Admission.lean:78`). |
| PROG-D16 | partly | **Reading** and **tested**: the printed program and its JSON are unchanged (`TypeRef.tuple` has no labels, `TypeRef.lean:15`; RC14 reproduced). But "`ofSchema` already ignores annotations" holds on the node only: an annotated tuple element is refused (`Bridge.lean:73-78`, the pattern at `:127`). **Tested** (`verify-StageC.lean`, 3 guards): names on the elements read back as `none`, names on the node read back as the pair. So §3.1's requirement holds only for one name list on the node. |
| PROG-D17 | confirmed | **Tested**: RC6, RC8 and RC15 reproduced. **Tested**: `-15` also decodes to `none` at `unknown`, and `-0.0` to `none` at `nat`. **Reading**: `Lcnf/Types.lean:53` maps `Int` to `int`; `Translate.lean:162-176` has `Nat.*` builtins only; `wire-tags.json:37` lists `Lit`'s four constructors; row 108's text matches. |
| PROG-D18 | confirmed | **Reading**: no register row covers recursive types (grep of DESIGN-ISSUES, decisions, DESIGN-BASIS), and system-map §8 R3 says "recursive types untracked". The synthesis's D10 (`synthesis.md:1138-1149`) proposes the row. **Tested**: no `Schema.suspend` is among the census's 40 most frequent `Schema` heads, which is consistent with "no slice yet". |
| PROG-D19 | confirmed | **Reading**: the queue matches addendum 5 ("C step 5, D's held users, F, G, H1, then H2 part one"; rows 111–116 come "after G") and the route matches system-map §3. **Tested** (census): no theorem or definition in H2's modules (`Typed/Admission`, `Residual`, `Stack`) recurses or cases on `Ty`. **Reading**: `ExitOk` reads `FitsExit`, and `internalHandleScan` is a `TyAlgebra` (`Admission.lean:58`), so an append forces its field. The 60–75 files stay **assumed**. |
| PROG-D20 | partly | **Tested**: the 32 guards and `RedMustFail`'s four errors reproduce byte-identically. Three problems. RC12 is not a record falsifier: the verdict is the same for `string` and `nat` carriers. "Variants with one payload field are exact today" is too strong: `selectTag` eliminates them, but their image is a tagged pair, not rc.112's `{_tag, amount}` object, so the field name is lost and a host answering the object would be refused, as in RC3. And F1 asserts an atom named `record`, which is a guessed name. |

## 2. What the seat missed

1. **Normalisation distributes products over unions, and records inherit it unless a rule says
   otherwise.** `normalize` multiplies a product out over its union columns
   (`Ty.productMembers`, `Program/Ty.lean:603-604`; type algebra note §5.1; boundary decisions T3).
   **Tested** (`verify-Refute.lean` §E): p2's `User` (a literal-union `role`) is already two
   products after normalisation, and three binary union columns give eight members. A record arm
   that follows `prod` would grow exponentially in its union fields, and TypeScript does not
   distribute object types. The record stage owes a decision on `normalize`, `Normal`, `key` and
   `sub` at a record. None of the note's shapes mentions it.
2. **Decision K is already taken by the tree's codec.** Every object it reads needs an exact
   field set, accepts any key order, and refuses extra and duplicate keys (`fields?`,
   `Schema/Codec.lean:74-82`). **Tested** on `Option`; `Result`, `Exit` and `Cause` go through
   `payload?`/`fields?` or exact one-entry patterns (`:87-89`, `:98-150`, **reading**). rc.112's codecs for the
   same schemas are `Struct` unions with "ignore" (`Schema.ts:9719-9729`, **reading**). So the
   divergence already exists and is not named in the codec's profile note (`Schema/Codec.lean:12-15`
   says the profile is rc.112 `toCodecJson`). A record codec that follows `fields?` needs `N` =
   reorder only.
3. **V and row 68 are one decision.** The tree proves subtyping sound for membership
   (`hasTy_sub`, `Laws/Program/Admits.lean:183`; `fits_sub`, `Membership.lean:837`). Width
   subtyping keeps that law only if values carry labels (**tested** red and green, **proved** in
   miniature: `verify-WidthCoupling.lean`). Positional records force a depth-only `sub`, which the
   row-68 differential would record as `incomplete` rows. Labeled records allow TypeScript's width
   rule but force `printIn` and the other 15 `Val` readers. Separately, `Val.ctor` under a struct
   or sum shape already prints rc.112's objects (**tested**), which matters only if `sub` stays
   depth-only.
4. **Variants may need no constructor of their own.** TypeScript's variant is a union of
   records discriminated by a literal field (p5:23-25 is literally that). With a record
   constructor plus the existing `lit` and `union`, the `variant (cases : Fields)` constructor of
   type algebra §1.3 is redundant. That would cut one constructor, its wire tag and its arms from
   the bill (**reading**; it rests on point 1's no-distribution rule for records).
5. **The spine has a cheap eliminator.** The tree already writes a single-motive companion for a
   nested type (`Json.ind`, `src/Effect4/Data/Json.lean:311-338`, `@[elab_as_elim]`). The same
   companion for `Ty`/`Fields`, registered as `@[induction_eliminator]`, keeps every
   `induction t with` proof's shape (**proved** in miniature, `verify-SpineInduction.lean`).
6. **The bill misses four kinds of reader.** (a) Six exhaustive `Ty` matches sit in the Tools,
   Conform and OCaml5 libraries, outside `#exhaustive_gate`'s reach (D6 row, **reading**). (b) 28
   theorems case on `Ty` without induction (**tested**, census). (c) Two theorems depend on
   `Ty.sub`'s arm list through `fun_induction` (`cata_admits_sub`, `fits_sub`), and the record
   stage changes those arms. (d) `internalHandleScan` is the one hand `TyAlgebra` instance
   (`Program/Admission.lean:58`).
7. **Decision P has a third option, and a larger reach.** The six unconditional handle-freeness
   lemmas (D11 row) all hold today by cases on `Err`'s four constructors. A payload carrier that
   cannot hold a handle, rather than a typing premise threaded through the image laws, keeps them
   unconditional (**reading**).
8. **The ingest census reorders some priorities.** Across 34 pinned projects (**tested**, python
   over the census summary), these are the heads the recognizer could not lift:

   | Head | Count | Projects |
   | --- | ---: | ---: |
   | `Schema.Struct` | 2,032 | 12 |
   | in-program decode (`decodeUnknownEffect` alone: 547) | about 756 | at least 5 |
   | `Schema.Union` | 265 | 8 |
   | `Schema.Literals` | 138 | 8 |
   | `Schema.Array` | 79 | 6 |
   | `Schema.Record` (keyed data) | 48 | 7 |
   | `TaggedStruct` / `TaggedUnion` | 44 / 20 | |
   | optional fields (`optional`, `optionalKey`, `NullOr`) | 25 | |

   Records come first, as the seat says. Route B and keyed data maps are not "0 in the world", and
   optional fields need a policy: absent versus `undefined`, given that `fields?` refuses a
   missing key. The five model programs alone under-sample these.
9. **The error-typing gap with rc.112 is `catchIf`, not absorption.** Boundary decisions T3 and
   decision 3 make the tagged column a union of literal-tagged pairs and the residual match
   `Exclude`. The tree's `catchIfError` (DI-17, `Program/Typing/Rules.lean:217-222`) subtracts a
   caught tag only when nothing remains (**tested**: the caught tags stay in `handle`'s column,
   `verify-Refute.lean` §B).
10. **Two of the twelve tsgo errors come from the error channel, not from records.** They are
    DB-15's `toPair` adapter left out of the red file, plus a printed `suspend` over a ternary
    with no type arguments (**tested**, `verify-ts/`).
11. **The service-carrier claim needs the Σ_app slice first.** `Author.build` can declare no new
    service at all today (**tested**). Row 118's structured carriers come after rows 111–114 land.
12. **D12 is not carried as a ruling by any tracked register row, and the name is overloaded.**
    See the D13 row.
13. **Stage (c) breaks the read-back if names go on tuple elements** (**tested**,
    `verify-StageC.lean`).
14. **No conservativity shape for the core append.** DI-47's ruling lists old-value exact
    decoding and typing/admission permission among the things to compare. With the comparator
    deleted, that obligation is now unstated anywhere for a `Ty` append (**reading**).
15. **Number-to-text is a need of p3 as well as p2.** p3's log lines (p3:47, :48, :57, :84, :90)
    print numbers; no atom does it (**reading**).

## 3. Probes, commands, results

Every Lean command ran from the repository root through
`bash /private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/0b88b41e-40ac-47c3-a942-8b02c701bb13/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <file>`,
one at a time. `D` below is this folder.

| File (in `D`) | What | Result |
| --- | --- | --- |
| `verify-rerun.sh` → `verify-rerun-<probe>.log`, `verify-rerun-summary.txt` | the seat's six Lean probes, its own command | exit codes 0, 0, 0, 0, 1 (`RedMustFail`), 0; every log **byte-identical** to the seat's (`cmp`) |
| `verify-tsgo.log` | `ts/eff/node_modules/.bin/tsgo -p ts/tsconfig.json` and `-p ts/tsconfig.red.json` (tsgo 7.0.0-dev.20260629.1) | green exit 0; red exit 1, 12 errors (9 TS2345, 3 TS2375), same as `ts/typecheck.log` |
| `verify-ts/verify-objects-pairerr.ts`, `verify-ts/verify-pairs-classerr.ts`, their tsconfigs, `verify-ts/verify-ts.log` | the red control split into its two causes. The prelude and the printed line are copied from the seat's red file; only the row declarations differ | objects with pair errors: exit 1, 10 errors; pairs with the class error: exit 1, 2 errors (TS2375 at columns 198 and 452) |
| `verify-SpineInduction.lean`, `.log` | can the `Ty`/`Fields` spine keep one-theorem induction? | exit 0. **Proved** at `[propext]`: `fitsT_defT_using` (`induction … using T.rec (motive_2 := …)`), `fitsT_defT_term` (recursor in term mode), `T.ind` (`@[induction_eliminator]`), `fitsFs_defFs_of`, `fitsT_defT_plain` (plain `induction t with`) |
| `verify-TyProofCensus.lean`, `.log` | every `Effect4.*` theorem, private ones included, that uses `Ty.rec`/`recOn`/`brecOn`/`binductionOn`, or `Ty.casesOn` directly or through its matchers | exit 0. 34 by recursor (one is Lean's `Ty.brecOn.eq`; 6 generated in `Program/Fold` and `Store/Domain/Derived/Program`; 27 hand-written); 28 more by case analysis only; within `Laws/Program/Typed/`, only `Membership` appears |
| `verify-Refute.lean`, `.log`; `verify-Refute.explore.log` | §A RC12's green neighbours; §B literal-tagged infrastructure errors; §C today's codec on objects; §D `ShapeDoc.print` of `Val.ctor`; §E product distribution | exit 0, 24 guards. The explore log is the first run, which printed the outcomes and stopped on four missing `Repr Json` instances (exit 1); the guards pin what it printed |
| `verify-StageC.lean`, `.log` | names as annotations on a tuple node or on its elements | exit 0, 3 guards (element annotations: `none`) |
| `verify-WidthCoupling.lean`, `.log` | width subtyping against positional or labeled record values | exit 0, 5 guards (one red: the positional value of the wider record is not a member of the narrower). **Proved**: `hasTyObj_sub` at `[propext, Quot.sound]` |
| `verify-sha256.txt` | hashes of every file above | |

Other commands, all read-only:

- `git show --numstat 0a2cb898` and `git show --stat 243ca0dd`;
- `git log -- Test/fixtures/baseline/` and `git cat-file -e 0a2cb898:<path>` for the readers
  born since;
- `git check-ignore -v` on the two 2026-09-10 notes;
- `grep` and `git grep` for each count cited above;
- python over `Test/fixtures/baseline/66ee4657-supplement-v1.policy.json` and over
  `docs/research/ingest-delivery/commit-4/census/summary.json`.

The seat's files are unchanged: their hashes match the seat's `sha256.txt` and `ts/sha256.txt`.

**Bounded evidence:**

- every check is a finite probe;
- the three miniatures (spine, width, the seat's K2) import nothing from the tree;
- the census counts are the recognizer's "unknown heads" (one per distinct engine answer), not
  a full usage count;
- the TypeScript split shows where the errors come from by subtraction; it is not a printer fix.

**Open for the coordinator:**

- the decision rows the seat proposes (V, E, K, P) should be re-cut as follows: V together with
  `Ty.sub`'s width rule; E with the eliminator measurement; K as naming the existing strict codec
  policy; P with the carrier-by-construction option;
- add a normalisation rule for records (§2.1);
- weigh route B with the census number (§2.8).
