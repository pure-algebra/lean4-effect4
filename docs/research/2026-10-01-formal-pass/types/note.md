# Seat TYPES: the type system and the signature discipline in the literature's terms (formal pass, 2026-10-01)

## The one thing

**M5 is false as stated, on a checked, closed, admitted, host-free program with no annotation**
(proved, `M5CounterProbe.lean`, `typedState_load_false`, axioms `[propext, Quot.sound]`). The
program is:

```text
fork(x := if true then 1 else "x"; succeed(pair(x, undefined)));  if true then f else f
```

The cause is a mismatch between two orders on types:

- **The checker compares and joins in the normalized order.** Its subsumption premises read
  `sub (normalize a) (normalize b)`, and `Ty.join a b = normalize (union a b)`.
- **`Fits` compares a handle's declared type with the raw order `Ty.sub`**, which does not
  distribute products over unions.

So the fork's certificate is the raw `prod (nat | string) unit`, the root's checked answer is the
canonical form of the fiber type, and the root's final exit does not fit it. The red controls
behind it are proved on the tree's own `Fits`, and the checker's side is tested:

- a fiber declared at the raw product does not fit the canonical form of its own type;
- a cell declared at the canonical form does not fit the raw spelling;
- a value that fits both arms of a `select` does not fit the select's joined answer.

The same closure, `Fits w v a → Fits w v (Ty.join a b)` (and its `subN` form for an annotated
loop cursor), is what every M6 step that joins answers will need: `select`, `catchCause`,
`catchIf`, `matchCause`, races, generator joins. That part is reading. At states after load the
existential world can sometimes choose a sharper declaration; at load it cannot, because the
fork's certificate is forced by the checker.

**Propose registering it as `E4-TYPED-CE-009`.** The smallest amendment stays inside one module,
`Laws/Program/Typed/Membership.lean`, the one module row 132 already names:

1. Compare declarations in the checker's order (`subN`) inside `Fits`'s handle arms, and in the
   protocol entries that compare a declared type with a certificate.
2. Prove `fits_normalize`, `fits_subN` and `fits_join_left`/`fits_join_right` as `hasTy_normalize`
   and `hasTy_join_left`/`hasTy_join_right` are proved.

The amended handle arms are proved invariant under normalization, and the counterexample's leaf
holds under them (`TypesOrderProbe.lean` §6, §7).

Everything else checked here holds, or is owed with a clear shape:

- The type order is a preorder whose quotient by the checker's order is the canonical-form
  partial order, with `join` as least upper bound (proved). Raw mutual subtyping is strictly
  finer (proved).
- Conservativity C1–C8 is well formed after rows 111–116, and nothing in the rulings blocks a
  single R2 theorem.
- Inhabitance is a fold. Its agreement with `Fits` is proved in the sound direction, and in both
  directions on the data fragment.
- Both K2 retractions become exact embeddings when the read is guarded by the writer's image
  (proved in general, and tested on the counterexamples row 128 cites).

## 0. Base, scope, evidence words

- **Base.** `refactor/phase1-phase3` at `ea5b28b5` (docs-only commit after `efd67af1`; sources
  unchanged since the merge `9ad8a7c0`, and the `.olean` files the probes import were built after
  it, so the probes read the tree as it stands). `git status` clean. Nothing tracked was edited; no
  `lake build`, `make`, generator, `git add` or `git commit`. `/Users/pooks/Dev/lean4-effect4-slice6`
  untouched. Every Lean compile went through the one-compiler lock
  (`serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`), one at a time.
- **Files written** (this folder only): `note.md`;
  - `TypesOrderProbe.lean` (probe A): `.log` final (a copy of `.run4.log`); `.run1.log` the failed
    first run; `.run2.log` and `.run3.log` intermediate;
  - `InhabitedProbe.lean` (probe B): `.log` final; `.run1.log` the failed first run; `.run2.log`;
  - `ExactByImageProbe.lean` (probe C): `.log`, `.run1.log`;
  - `M5CounterProbe.lean` (probe D): `.log` final; `.run1.log` the failed first run; `.run2.log`,
    `.run3.log`;
  - `KernelEvalProbe.lean`: `.log` final; `.run1.log`–`.run5.log` are scratch prints, two of them
    failed on a name, no claim rests on them.
  - `RecordWorldProbe.lean` (probe E, a model): `.log` final; `.run1.log` the failed first run (a
    doc comment before `mutual`); `.run2.log`.
- **Evidence words.** **proved**: a kernel theorem I compiled here, axioms printed at
  `[propext, Quot.sound]` or less (or a tree theorem whose statement I read and that a probe of mine
  used, said so). **tested**: a finite check I ran (`#guard`). **reading**: code or notes read, not
  run. **assumed**: not checked. A tree theorem I only read is "proved in tree (reading)".
  Literature is marked **read (note)** when a tree note read it at the cited place, **by name**
  when I cite it from general knowledge without reading it in this pass (section numbers then
  come from memory and are not verified), **assumed** when nothing here checks it.
- **Short paths.** `Program/…`, `Laws/…`, `Machine/…`, `Schema/…`, `Codegen/…` are under
  `src/Effect4/`. "Probe A/B/C/D/E" are this folder's `TypesOrderProbe.lean`, `InhabitedProbe.lean`,
  `ExactByImageProbe.lean`, `M5CounterProbe.lean`, `RecordWorldProbe.lean`.

## 1. The table

Severity: **high** = an open milestone obligation is false as stated for checked programs;
**medium** = a law the plan relies on has no definition or proof, with its shape known;
**low** = wording, ownership or tidiness. "—" = nothing owed.

| Object | Formal notion | Literature | Tree definition | Laws proved | Laws owed | Severity |
| --- | --- | --- | --- | --- | --- | --- |
| `Ty` (20 constructors) | the free (initial) term algebra of a ground, first-order signature; `TyAlgebra`/`cata_ty` its unique homomorphisms | Goguen, Thatcher, Wagner, Wright 1977 (by name, coherence principle's list) | `Program/Ty.lean:37-75`; `Program/Fold.lean:31-56` | `hom_eq_cata_ty` (uniqueness), `key_injective`, derived `DecidableEq` (proved in tree, reading) | — | — |
| `Ty.sub` | algorithmic structural subtyping (syntax-directed, transitivity a theorem not a rule) with union types (left distributes, right chooses), a literal rule, top `unknown`, bottom `never`, invariant cells and deferreds | Pierce, *TAPL* 2002, ch. 15–16 (by name); union rules as in Pierce 1991 and Dunfield 2014 (by name); declaration-site variance from rc.112 (row 60) | `Program/Ty.lean:437-456` | `sub_refl`, `sub_trans` (`Laws/Program/TypeAlgebra.lean:40-118`), `hasTy_sub`, `sub_sound`, `sub_not_complete` (`Laws/Program/Template.lean:312-322`) (proved in tree, reading); used by probe A | — (sound and deliberately incomplete; §2.3) | — |
| `normalize`, `Normal`, `CTy` | a normal-form function: flatten, sort and deduplicate unions, absorb non-maximal members, distribute products over unions; `CTy` is its image (fixed points) | normal forms for unions as in TypeScript's union reduction (read, type-algebra note §5.1); semantic subtyping as the complete alternative, Frisch, Castagna, Benzaken 2008 (assumed, type-algebra note §5.3) | `Program/Ty.lean:563-753`, `CTy` `:842-884` | `normalize_idem`, `normal_normalize`, `Normal.fixed`, `hasTy_normalize`, `sub_normalize_of_sub` (one-way) (proved in tree, reading) | `fits_normalize` (false today, gap TY-01) | high (via TY-01) |
| the order the checker uses, `subN a b := sub (normalize a) (normalize b)` | a preorder on raw `Ty` whose kernel is equality of normal forms: `Ty/≡N ≅ CTy` | quotient of a preorder by its equivalence (standard) | not named in the tree; read at `Typing/Rules.lean:114-117` (`rowTy`), `Laws/Program/Typing/HasTy.lean:186-187, 244` (iterate, provideService) | probe A: `subN_refl`, `subN_trans`, `sub_le_subN`, `subN_equiv_iff`, `ofRaw_eq_iff` (proved); raw mutual `sub` is strictly finer: `T_not_sub_normal`, `normal_sub_T` (proved) | name it in the tree, use it wherever two declared types are compared (TY-01, TY-02) | medium |
| `CTy` with `CTy.join` | a bounded join-semilattice: partial order, least upper bound `join`, bottom `never`, top `unknown`; no meets (no intersection types), so not a lattice | TAPL §16.3 joins and meets (by name) | `Laws/Program/TypeAlgebra.lean:1096-1121` | `instIsPartialOrder` (with `sub_antisymm_canonical`), `instLawfulOrderSup` (`sub_join_iff`), `never_le`, `le_unknown`, `join_comm`, `join_assoc`, `join_self`, `join_never`, `join_unknown` (proved in tree, reading) | — | — |
| `Ty.infer`'s `join` flag (the atoms slice's "common supertype, never a union") | a partial maximum: the binding moves to the new candidate only when the old one is below it; incomparable candidates are not joined | TypeScript `getCommonSupertype` (read, type-algebra note §3.2); local type inference, Pierce and Turner 2000 (by name) | `Program/Ty.lean:508-528` | `matchTemplate_sound`: the guard is the law, so inference can lose completeness and never soundness (proved in tree, reading) | anchored completeness (L4, owed elsewhere) | — |
| `HasTy` (six mutual judgments, 63 rules) and the checker | an algorithmic typing relation: syntax-directed, subsumption only at application points (row requests, service provision, the loop cursor, fixed atom arguments); types are unique; the checker is a located refusal (K4) and one fold | TAPL §16.2, minimal typing (by name); bidirectional typing for the cursor annotation, Dunfield and Krishnaswami 2021 (by name, type-algebra note §8) | `Laws/Program/Typing/HasTy.lean:64-496`; `Program/Checker.lean` | `check_sound`, `check_complete`, `hasTy_unique` (`Laws/Program/Typing/Sound.lean:130`), `explain_none_iff` (proved in tree, reading) | C3 reflection (§3.2) | medium |
| `Signature`, Σ = Σ_core ⊕ Σ_app | a signature as data: Σ_app is the row table (operations indexed by position) and the service table (sorted constants: a key's sort is its code, the table interprets sorts as types) | signatures as data, Benke, Dybjer, Jansson 2003 (by name, coherence principle §1); many-sorted signatures, Goguen and Burstall's institutions 1992 (by name) | `Program/Typing/Rules.lean:49-66`; `Program/Native.lean:269-296, 316-321` | typing over any signature (188 binders, tested by three seats; reading) | `LawfulSig`, `admitSig_ok_iff`, `SigProgram` (§3) | medium |
| extension Σ ⊑ Σ′ (DI-47 applied to Σ_app) | conservative extension of a specification (a persistent extension: old models embed unchanged) and of a type system (modular type soundness) | Ehrig and Mahr 1985, persistency (by name); Delaware, Oliveira, Schrijvers, *Meta-theory à la carte*, POPL 2013 (by name); Swierstra 2008 §2, §6 (read, model-probe pedigree seat) | not in the tree; `SigExtends` exists only in `docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:84-90` | C3 monotone half (`hasTy_ext`, `check_ext`, `rows_append`, `services_append`), generic C1/C2/C4 (`inl_iff`, `along_bind`, `interpret_along`, `c4_iff`), C5 red controls (proved in those probes; rerun by the audit; reading here) | C3 reflection, concrete C4, C6's shape, operational C2, C7, C8 (§3.2) | medium |
| `Fits w v t` | a Kripke (world-indexed) unary logical relation on first-order values, i.e. a value typing under a store typing; no step-indexing is needed because `Ty` has no function or recursive types | TAPL ch. 13, store typings (by name); Ahmed 2004 thesis, Kripke logical relations for state (by name, foundations review §4.1 via the model-probe synthesis §3.1); de Vilhena 2022 thesis, protocols (read, model-probe pedigree) | `Laws/Program/Typed/Membership.lean:87-148` | `fits_mono`, `fits_map`, `fits_sub` (raw), `fits_hasTy`, `fits_live`, `fitsExit_success_iff`, `fitsExit_failure_iff`, `fitsExit_sub`, `flatFits_fits`, `fits_list_iff`, `fold_of` connector (proved in tree, reading) | `fits_normalize`, `fits_join_left/right`, `fits_subN` (false today: TY-01, and M5 is refuted through it, probe D); term soundness `evalTerm_fits` (TY-07); the reply bridge (TY-11); `ServicesFit` at `w.serviceTy` (row 112) | high |
| `World`, `World.leHost` | Kripke worlds: the fiber, promise and heap typings plus ghost resume types and external spellings, ordered by table extension | TAPL ch. 13, Σ ⊆ Σ′ (by name); Iris worlds (by name) | `Laws/Program/Typed/World.lean:52-140`; `Validity.lean:18-44` | the order laws (proved in tree per the model-probe synthesis §2.2 R4; reading) | shape A's static `serviceTy` (row 112) | — |
| `inhabited : Ty → Bool` (row 127) | the emptiness test of a type, a fold; agrees with `Fits` | emptiness of regular tree languages, decidable (by name; Comon et al., TATA) | not in the tree; probe B `inhabitedAlg` | probe B: `inhabited_of_fits`, `inhabited_of_hasTy` (sound, both judgments), `fits_of_inhabited_handleFree`, `inhabited_iff_handleFree`, `fiber_inhabited`, `cell_inhabited`, `promise_inhabited`, `inhabited_sub`, the DI-67 counterexamples (proved) | one world for several handle positions (amalgamation); `inhabited (normalize t) = inhabited t`; the admission refusal (TY-03) | medium |
| `Ty.schema` / `Ty.ofSchema` | a retraction (a prism that satisfies only its first law); exactness modulo a named normaliser makes it a partial isomorphism | Rendel and Ostermann 2010, Pickering, Gibbons, Wu 2017, McBride 2011 (by name, coherence principle) | `Schema/Bridge.lean:38-137` | `ofSchema_schema` on closed types (proved in tree, reading); probe C: `ofSchemaExact_retract`, `ofSchemaExact_exact` (proved) | exactness for the unguarded read, with `N_S` named (TY-09) | medium |
| JSON codec `encode`/`decode` | a retraction on the codec domain; not injective on its image today | Foster et al. 2007 (by name) | `Schema/Codec.lean:153-245`; `Laws/Schema/Codec.lean` | `decode_of_encode`, `decode_encode`, `hasTy_decode`, `encode_sub`, `encode_injective` (proved in tree, reading); probe C: `decodeExact_retract`, `decodeExact_exact`, `decodeExact_sound` (proved) | exactness, with `N_J` named (TY-09) | medium |
| `Canonical` instances; the printer and reader | complete partial isomorphisms (both laws) | Rendel and Ostermann 2010 (by name) | `Store/Carrier/Image.lean:39-47`; `Laws/Codegen/Read.lean` | `ofVal_toVal`, `ofVal_exact`, `read_print`, `read_exact` (proved in tree, reading) | — | — |
| reply admission (`admitAnswer`, `externalValue`, row 97) | a located refusal over a value; it preserves a capability-safety invariant (every handle in the state was minted by the machine) | Miller 2006 thesis; Devriese, Birkedal, Piessens 2016, capability safety as a logical relation (by name) | `Program/Admit.lean:59-75`; `Program/Compile.lean:1371-1382` | the session's envelope and at-most-once laws (`Laws/Api/HostSession.lean`; reading) | the receipt theorem `accept r v = ok → Fits w′ v r.answer` and its bridge lemma (TY-11) | medium |
| the host-row domain bit (row 116) | monotonicity of the protocol family in the signature (a demand cannot appear for an operation outside the domain) | de Vilhena 2022, protocol refinement (read, model-probe pedigree) | owed in `asyncPre`, `Laws/Program/Typed/Residual.lean:110-112` | red control `typedProg_not_table_monotone` (proved by the TREE verifier, rerun by the audit; reading) | the monotonicity lemma with the bit | low |
| the service table as a static world component (rows 112–114) | the interpretation of the service sorts, fixed along the world order | sorted constants interpreted by a model (by name) | `Program/Native.lean:269-296`; `Machine/Key.lean:337-349` (`carrier_def`) | `one_code_two_carriers` (red control, proved by the audit; reading) | `ServicesFit` at `w.serviceTy`; the agreement premises of `servicesFit_map` and `fits_map` | medium |
| records (row 119, not in the tree) | closed records with depth and permutation subtyping and no width rule; width as an explicit boundary coercion (a projection, the `get` of a lens), never a subsumption rule | TAPL §15.2 record rules and §15.6 coercion semantics (by name); Breazu-Tannen et al. 1991, Luo 1999 (by name); row types are a "false friend" for a ground `Ty`, Rémy 1994, Gaster and Jones 1996, Leijen 2005 (by name, types scout via the data probe §6.4) | data-probe models | `fitsFields_exact_mono`, `positional_width_unsound`, `hasTyV_normalize_fails`, `SynthRecord.hasTy_normalize`, `fits_coerce` (proved in those models, rerun by the data synthesis; reading); with a world and a handle former, probe E: `raw_not_invariant` (red), `fitsN_normalize`, `normalize_idem`, `fitsN_mono` (proved, model) | everything in the tree (stage 1); the record cases of TY-01 and TY-10 | medium |

## 2. The type language as an algebra (question 1)

### 2.1 The order and its quotient

**What the tree proves (reading, all proved in tree).** `Ty.sub` is reflexive and transitive on raw
types (`sub_refl`, `Program/Ty.lean`; `sub_trans`, `Laws/Program/TypeAlgebra.lean:117`), so
`(Ty, sub)` is a preorder. On canonical types `CTy = {t // normalize t = t}` it is antisymmetric
(`sub_antisymm_canonical`, `:1035`), and `CTy.instIsPartialOrder` and `CTy.instLawfulOrderSup`
(`:1098-1108`) package it as a partial order with `CTy.join` as least upper bound.

**What "the quotient by mutual subtyping" is.** DI-15 (amended 2026-09-11) says "identity is
subtyping-equivalence". That is true on `CTy`. It is not true of the raw order:

- **proved (probe A, `T_not_sub_normal`, `normal_sub_T`, `T_subN_equiv`):** for
  `T := prod (nat | string) unit`, `sub (normalize T) T = true` and `sub T (normalize T) = false`,
  although `normalize T = normalize (normalize T)`. Raw `sub` is a choice per member on the right,
  and the left side is a single product member. It never distributes; only `normalize` does
  (`Ty.lean`'s own docstring: "distribution remains in normalization"; `sub_normalize_of_sub` is
  one-way, "No converse is asserted", `TypeAlgebra.lean:1049`).
- **proved (probe A, `subN_equiv_iff`, `ofRaw_eq_iff`):** the order that does have `CTy` as its
  quotient is `subN a b := sub (normalize a) (normalize b)`. It is a preorder (`subN_refl`,
  `subN_trans`), it contains the raw order (`sub_le_subN`), and its kernel is exactly equality of
  normal forms: `subN a b ∧ subN b a ↔ normalize a = normalize b`. So `Ty/≡N` is isomorphic to
  `(CTy, sub)`. `normalize` (that is, `CTy.ofRaw`) is the quotient map, and canonical forms are the
  representatives.

So the precise statement is a quotient of a preorder by its equivalence: canonical forms
represent the `subN`-classes, not the raw `sub`-classes. **The checker already uses `subN`**
(reading): `rowTy` normalizes request and template (`Typing/Rules.lean:114-117`), and `HasTy.iterate`
and `HasTy.provideService` compare `sub x.normalize y.normalize`
(`Laws/Program/Typing/HasTy.lean:186-187, 244`). The answer join `EffTy.joinAnswer a b = some
(Ty.join a b)` returns a canonical form. **`Fits` and the typed state's protocol entries use raw
`sub`** (`Membership.lean:25-38`; `Residual.lean:107-127`; `Assembly.lean:36`). That mismatch is
gap TY-01 (§4.3).

### 2.2 The two joins

There are two "join" operations, and they are different objects.

- **`Ty.join a b = normalize (union a b)`** (`Program/Ty.lean`, after `normalize_idem`). On `CTy` it
  is the least upper bound in the syntactic order (proved in tree, `sub_join_left`,
  `sub_join_right`, `join_least`, `sub_join_iff`). With `never` it is a commutative, associative,
  idempotent monoid (`join_comm`, `join_assoc`, `join_self`, `join_never`), with `unknown`
  absorbing (`join_unknown`). So `(CTy, join, never, unknown)` is a **bounded join-semilattice**.
  There is no meet: `Ty` has no intersection type, and nothing in the plan needs one (the
  type-algebra note §5.2: no contravariant position exists, so the inference never needs a meet).
- **The atoms slice's "join = common supertype, never a union"** is `Ty.infer`'s `join` flag
  (`Program/Ty.lean:508-528`). It is a partial maximum: a template parameter's binding moves to a
  new candidate only when the old binding is below it, and two incomparable candidates are never
  joined. The guard `matchTemplate` then refuses the application, which is TypeScript's own
  behaviour (`tsgo` refuses `ite(b, n, s)` with TS2345, the docstring at `:496-507`). This is not a
  least upper bound and is not meant to be one. The two do not conflict.

### 2.3 Soundness and incompleteness of the order

`sub` is sound for membership (`sub_sound` = `hasTy_sub`; `fits_sub` for `Fits`) and deliberately
incomplete against value containment. The tree registers one witness, `sub_not_complete`
(`Laws/Program/Template.lean:322`): `option (nat | string)` and `option nat | option string` have the
same members, and `sub` refuses the pair. Two more of the same kind:

- `prod never nat` is canonical, empty, and not below `never` (no product annihilation;
  `Ty.factors`' docstring; reading, and its emptiness proved in probe B);
- `T` above is not below its own normal form in the raw order (proved, probe A).

This is the standard position of a syntactic, structural subtyping relation (TAPL ch. 15–16, by
name). The complete alternative is set-theoretic semantic subtyping (Frisch, Castagna, Benzaken
2008; assumed, type-algebra note §5.3), which needs intersections, negations and an exponential
decision procedure, and the estate has ruled against it. Nothing here asks to change that. It asks
that every place comparing two types for the same purpose use the same one of the two orders.

### 2.4 Distribution, and what it does to records

`normalize` distributes `prod` over `union` on either side, and only `prod`, never `list` (DI-15
amended, clause 2). A product of k binary-union columns therefore normalizes to 2^k members (the
data probe's three binary union columns give eight; data synthesis §6.3, tested there). Row 119's
clause (d) keeps records as factors: a record is **not** distributed over its union-typed fields.
Formally:

- **The order stays a partial order on canonical forms.** `record {a: nat | string}` and
  `record {a: nat} | record {a: string}` are two different canonical forms with the same members.
  They are not mutual subtypes (the right-hand rule chooses per member), so antisymmetry is
  untouched. The price is one more registered incompleteness of the `sub_not_complete` kind. The
  stage-1 brief should land that as a named theorem, not leave it in a note (TY-10).
- **Normalization inside fields still distributes products.** `normalize (record fs)` sorts the
  fields and normalizes each field type, so a field `prod (nat | string) unit` becomes a union of
  products. TY-01 therefore reaches every handle type whose argument is a record with such a
  field. The amendment for TY-01 covers it.
- **Raw `sub` at records must compare canonical name lists** (row 119's R3.3 says "the canonical
  name lists are equal"). If the record arm compared written order, raw `sub` would also miss
  field permutation, and `sub r (normalize r)` would fail for every permuted record. That is a
  second, larger way into TY-01. Reading the data synthesis, its model probes compare canonical
  order. The stage-1 brief should make it an explicit acceptance item (TY-10).

### 2.5 Decidability: `sub`, normalization, inhabitance

- **`sub` is decidable by construction.** It is a total `Bool` function, terminating by the measure
  `sizeOf a + sizeOf b` (`Program/Ty.lean:456`). Plain `decide` and `rfl` do not evaluate it
  (well-founded recursion), but `decide +kernel` does (proved: `KernelEvalProbe.lean` `k1`, `k2`;
  probe D evaluates the whole checker that way). So concrete facts are kernel computations, and
  general facts go through the view lemmas (`sub_args_*`, `sub_eq_false_of_not_sameHead`,
  `sub_union_left/right`) or through membership (`hasTy_sub`), as probe A does. The tree's comment
  at `Laws/Program/Template.lean:332-333` says the kernel does not reduce it; that is TY-15. Its cost
  is the antichain's quadratic number of `sub` calls times the recursion, and distribution is
  exponential in nested products of unions (type-algebra note §5.1). That is accepted for the
  sizes this language sees.
- **Inhabitance is a fold** (probe B, `inhabitedAlg : TyAlgebra (fun _ => Bool)`, so a census-rule
  traversal): `never`, `int` and `var` are empty; `prod` is a conjunction; `except` and `union` are
  disjunctions; everything else is inhabited. The handle formers are inhabited at **every**
  argument, `fiberOf never never` included (a fiber that never completes), in some world (proved,
  `fiber_inhabited`, `cell_inhabited`, `promise_inhabited`); `option`, `list`, `exitOf` and
  `causeOf` by `none`, `[]`, a failure with no typed reason and the empty cause. Row 127's agreement
  theorem and its status are in §4.4.
- **With recursive types** (row 124: recursion through nominal declarations in Σ_app),
  inhabitance becomes a least fixed point over the declaration graph (`{next: T}` is empty), and
  subtyping a greatest fixed point (Amadio and Cardelli, TOPLAS 15(4), 1993; TAPL ch. 20–21; by
  name). Both stay decidable for regular types. Row 124 already says "inhabitance as a least fixed
  point"; its `sub` should be stated coinductively (or nominally, as row 124 proposes) when it
  lands. Nothing is owed now.

### 2.6 Records, width and depth (row 119), in the literature's terms

TAPL's record subtyping has three rules (§15.2, by name): width (`S-RcdWidth`, extra fields
forgotten), depth (`S-RcdDepth`, fieldwise subtyping), permutation (`S-RcdPerm`). Row 119 adopts
**depth and permutation, and not width**:

- permutation is quotiented away by the canonical field order (a normal form for the permutation
  equivalence), so it costs nothing in the order;
- depth is the exact rule, proved monotone for membership in the data probe's tree model
  (`fitsFields_exact_mono`, reading);
- width is unsound with positional values (`positional_width_unsound`, proved there, reading),
  because a value laid out for `{a, b, c}` read at `{a, c}` takes `b`'s slot.

Width is realized instead as an **explicit coercion at the boundary**: the row adapter projects
rc.112's wider object onto the declared fields. In the literature that is coercion semantics for
subtyping (TAPL §15.6; Breazu-Tannen, Coquand, Gunter, Scedrov 1991; Luo 1999; by name), with the
coercion made explicit and confined to one place. In the lens vocabulary of §5 it is the `get` of
a lens from the host object to the program record (Foster et al. 2007, by name). Only `get` is
needed, because the reply flows one way. Its law is the data probe's `fits_coerce` shape (proved in
the verifier's model, reading): `sub a b → Fits v a → Fits (coerce a v b) b`, stated at the
adapter. Inside a program, width is refused by name (row 119).

Row polymorphism (Wand; Rémy 1994; Gaster and Jones 1996; Leijen 2005; by name) is the other
standard answer to extensible records. It needs type variables in program types. `Ty` is ground
outside row templates and `Eff` has no binder for a row variable, so the types scout's verdict
stands (a "false friend"; by name through the data synthesis §6.4). Closed records with explicit
boundary coercions are the right formal object for this language.

## 3. The signature parameter and conservativity (question 2)

### 3.1 What Σ_core and Σ_app are, formally

- **Σ_core is the signature of the free objects themselves** (`Eff`, `Ty`, `NativeOp`'s built-ins,
  `SyncOp`, `FiberOp`, `NativeAtom`, `Err`, `Defect`, `HandleKind`). Growing it changes the
  inductive types. With no equations on `Eff` or `Ty`, adding a constructor never identifies two
  old terms. The old term algebra embeds into the new one's reduct unchanged, which is Ehrig and
  Mahr's *persistent* extension in its trivial, equation-free case (by name). What can change is
  every *function* defined by a hand match with a catch-all. That is why row 56's classifier rule
  and row 61's inventory are the right instruments.
  Conservativity across a change of the inductive is a statement about two versions of a type.
  Lean can only state it for the new type's κ-free fragment, by keeping a copy of each old
  function. So DI-47's finite gate over retained baselines is not a weakness of the plan. It is
  the only form the statement has: a translation validation of the two versions, with goldens and
  admission verdicts as the observation. R3.8's "on κ-free types every existing function and law
  is unchanged" is that gate's specification (reading, data synthesis §3.1).
- **Σ_app is data an application supplies:** the row table (operations indexed by position, a
  family over `NativeOp.external i`) and the service table. In algebraic-specification terms the
  service table is an interpretation of *sorts*: a `ServiceKey` is a constant `(name, code)`, its
  code is its sort, and the table maps sorts to carrier types (row 113; `Machine/Key.lean:347`,
  `carrier_def`: "selection is by the code, never by the nominal name"). The typing judgment is
  parametric in a `Signature Op` record (`Typing/Rules.lean:49-66`) whose Σ_core fields (`atomOf`,
  `constAtom`, `scopeKey`) are fixed and whose Σ_app fields (`dom`, `rowOf`, `serviceTy`) are
  computed from the tables (`nativeSignature`, `Program/Native.lean:316-321`). Typing is proved
  over every such record (`check_sound`, `check_complete`; reading).

### 3.2 C1–C8 over the tree's objects

`Σ ⊑ Σ′` below is DI-47's relation on Σ_app as rows 111 and 115 restrict it: declared appends of
the *complete assembled* table, fresh unreserved names, fresh codes, no insertion, override or
reorder. A **Σ-program** is one whose every `perform` names an operation in `dom Σ`, and every key
the checker looks up (`service`, `provideService`, and, after row 105, a layer's key) has a carrier
for its code in Σ, or is the reserved Scope key. That is exactly the set of reads the checker's
algebra makes of the signature. Rows 113 and 116 make this definition well formed (§3.3).

| | Theorem shape over the tree's objects | Status | Notes |
| --- | --- | --- | --- |
| **C1 syntax** | for Σ_app, `ι = id : Eff NativeOp → Eff NativeOp` (an appended row is `external i` at a larger valid range; a key is data), restricted to `SigProgram Σ` | **trivial** for Σ_app (reading). The free-monad C1 (`inl_injective`, `inl_bind`, `along_bind`; proved in the package and the pedigree probe) concerns the denotation signatures `StoreSig ⊕ FiberSig` and Σ_core, and `MorphismCollapse.lean` shows a general signature morphism is not injective (audit) | DB-01 should say C1 is vacuous for Σ_app, so the free-monad lemmas are not cited as Σ_app's conservativity (TY-06) |
| **C2 meaning** | operational until DI-69: `SigProgram Σ p → TapeIn Σ tape → obs (run (t ++ t′) p tape fuel) = obs (run t p tape fuel)`. The runtime reads the table only at registration and preparation, through `externalRow table i` with `i < t.length` | **owed**. One program tested, insertion refuted (pedigree verify `VerifyRun.lean`; reading). With DI-69 it becomes `interpret_along` for `Sum StoreSig (RowSig t)` (generic, proved in the pedigree probe) | a run simulation (K3) with invariant "every parked external index < t.length"; sessions compare tables exactly (`Api/HostSession.lean:129-150`), so C2 for sessions is by pinning (row 115) |
| **C3 checker** | `SigExtends Σ Σ′ → SigProgram Σ p → Checker.check Σ′ env path p = Checker.check Σ env path p`, as `Except` values, refusals included | monotone half **proved** in a probe (`hasTy_ext`, `check_ext`; equality on programs Σ accepts follows because `check` is a function). Reflection **owed** | reflection is **fold congruence**: the checker is one fold (`Program/Checker.lean`, header), and two algebras that agree on the reads a program's nodes make give the same fold on that program. State one generic `cata_congr_on` for the generated folds and C3 is an instance (TY-04) |
| **C4 protocol typing** | `SigProgram Σ p → (TypedProg ⟨p, t ++ t′⟩ w ty (denoteR p) ↔ TypedProg ⟨p, t⟩ w ty (denoteR p))` | generic iff **proved** for exact old protocols (`c4_iff`, pedigree verify); concrete **owed**; red control `typedProg_not_table_monotone` **proved** (TREE verify, rerun by the audit; reading) | with row 116's domain bit, `Ψ_F t` and `Ψ_F (t ++ t′)` agree on `dom t` and the old protocol has no entry outside it, so the "exact old protocols" premise of `c4_iff` holds. The proof is an induction on `TypedProg` using C3 both ways (`PointTyped`, `memoGet` and `asyncPre` read the checker or the rows) |
| **C5 world** | for services under shape A (row 112): `π w := { w with serviceTy := Σ.serviceTy }`; `ServicesFit (π w) ctx ↔ ServicesFit w ctx` whenever every key of `ctx` is typed by Σ. Rows add no world component | red controls **proved** (pedigree: `reflection_needs_back`, `order_widening_loses_typing`, `post_refinement_needed`; verify: `mono_needed`, `pre_refinement_needed`; reading); the construction **owed** | within a run the order fixes `serviceTy` (equality); across signatures `π` is restriction. This is the "lookup-agreement premise" the audit adds to `servicesFit_map` and `fits_map` (`Membership.lean:721-732`) |
| **C6 local lawfulness** | write `LawfulSig Σ := (∀ e ∈ Σ, Local e) ∧ Σ.Pairwise Compatible`; then `LawfulSig (Σ ++ ε) ↔ LawfulSig Σ ∧ LawfulSig ε ∧ ∀ e ∈ Σ, ∀ e′ ∈ ε, Compatible e e′` is `List.forall_append` with `List.pairwise_append` | **owed** (shape only today). Admission is whole-table now, so a lawless appended row revokes old programs (tested, pedigree verify `VerifyAdmission.lean`; reading) | the local row clauses: registrable (`checkTable`), no built-in collision, value-row trailing, no `int` (`findInt`), no internal handle in answer or error (row 97), templates admissible and well scoped, **every column inhabited or `never` (row 127)**, every required key typed. The local service clauses: name ≥ `firstFreeName`, flat carrier, no conflict with the built-in table (row 114). The pairwise clauses: distinct `rowKey`s; one carrier per code (row 113). Face lawfulness (`LawfulSpelling`, `rowNamesSafe`) stays a per-face predicate conjoined at the face (audit §4) (TY-05) |
| **C7 representation** | `SigProgram Σ p → print Σ′ p = print Σ p ∧ encodeProgram p unchanged ∧ read Σ′ (print Σ p) = some p` | under row 115 the only instance today is `Σ′ = Σ` (artifacts and sessions pinned to their complete table), so C7 is trivial now and **owed** with DI-01 step 8 (linking) | wire indices are stable under append (reading); a fresh service key changes the printed spelling until row 105 (tested by the pedigree verifier; reading) |
| **C8 forms** | per form `f`: `∀ args, Readable (expand f args)`, tied to R10's behaviour law | **owed** per form (outside this seat; programs verify X3 is the standing counterexample, reading) | — |

### 3.3 One theorem for R2, and whether the rulings allow it

R2 can be stated once. Take `Σ ⊑ Σ′` (DI-47 on Σ_app), `LawfulSig Σ′` carried on the source (row
114), and a Σ-program `p`:

```lean
theorem conservative (hε : SigExtends Σ Σ′) (hΣ′ : LawfulSig Σ′) (hp : SigProgram Σ p) :
    Checker.check Σ′ [] [] p = Checker.check Σ [] [] p                         -- C3
  ∧ (admitProgram p Σ′.table).isOk = (admitProgram p Σ.table).isOk         -- C6, as a consequence
  ∧ (∀ w ty, TypedProg ⟨p, Σ′⟩ w ty (denoteR p) ↔ TypedProg ⟨p, Σ⟩ (π w) ty (denoteR p))  -- C4 + C5
  ∧ (∀ tape ∈ Tapes Σ, ∀ fuel, obs (run Σ′ p tape fuel) = obs (run Σ p tape fuel))      -- C2
```

Every milestone statement `M Σ` instantiated at `Σ′` and restricted to Σ-programs then says what
`M Σ` said. That is the model probe's "the Σ′ instance of a theorem says of an old program exactly
what the Σ instance said". **Nothing in rows 111–116 prevents this theorem. The rulings are what
make it well formed:**

- row 111 confines it to Σ_app (Σ_core is the finite gate of §3.1);
- row 112 gives `π`: restriction of a static world field;
- row 113 makes "a key typed by Σ" a property of the key's code. Keyed by key, one code could carry
  two carriers (`one_code_two_carriers`, proved by the audit, reading), and the runtime selects the
  carrier by code, so "typed by Σ" would not be well defined;
- row 114 puts the lawfulness evidence on the source, so the hypothesis `LawfulSig Σ′` is available
  where M5 and M6 quantify;
- row 115 limits C7 and the session part of C2 to pinned artifacts: the theorem is stated over
  signatures now and applied to artifacts once linking exists;
- row 116 supplies the domain bit C4's iff needs.

**What is missing is definitions and three proofs, not decisions.** The definitions: `SigExtends`,
`SigProgram`, `LawfulSig`, `π` (none in the tree; `SigExtends` is only in `R2Probe.lean`). The
proofs: C3 reflection (fold congruence), concrete C4 (induction on `TypedProg`), operational C2 (a
run simulation, or DI-69). Literature for the whole: conservative extension of a type system with
proof reuse is the subject of Delaware, Oliveira and Schrijvers, *Meta-theory à la carte* (POPL
2013), and its successor for monadic semantics (ICFP 2013), by name. Coproducts of signatures
with injections are Swierstra 2008 (read, pedigree seat). If the fiber layer ever gains an
equational theory, the sum of theories is Hyland, Plotkin and Power, TCS 357, 2006 (by name; the
model probe's caveat stands).

## 4. Semantic typing: `Fits` as a logical relation (question 3)

### 4.1 What `Fits` is

`Fits w v t` (`Laws/Program/Typed/Membership.lean:87-148`) is a **Kripke unary logical relation**
on first-order values: a family of value predicates indexed by a world and defined by structural
recursion on `Ty`. The world is a **store typing** in TAPL's sense (ch. 13, by name), widened to
every handle sort:

- `Γ` types fibers;
- `Π` types deferreds;
- `Ρ` types cells;
- `Θ` holds ghost resume types;
- the external allocation table gives external spellings.

`World.leHost` is the extension order (Σ ⊆ Σ′ in TAPL; "future worlds" in the Kripke literature;
Ahmed 2004 thesis, Iris; by name). Because `Ty` has no function type and no recursive type,
`Fits` needs no step-indexing (Appel and McAllester 2001, by name): a cell's arm reads the cell's
**declared** type and does not recurse into its contents. The contents are typed by a separate store
invariant, `preds.HeapCell w key v := ∀ ty, w.Ρ key = some ty → Fits w v ty` (`Assembly.lean:60`),
TAPL's "the store is well typed under the store typing". This is the clean first-order split of
value typing and store typing, and it is why `Fits` can be a fold (`fold_of
Effect4.Program.Typed.Fits`, `Membership.lean:248`). `TypedProg` above it is a protocol typing in
de Vilhena's sense (thesis 2022, read by the model-probe pedigree seat): `Typed o Ψ w Q p`
specialised, with `Fits`/`FitsExit` as the result predicate.

### 4.2 The lemmas a logical relation is expected to have

| Expected lemma | Tree | Status |
| --- | --- | --- |
| monotone in the world (Kripke monotonicity) | `fits_mono`, `fits_map` (`Membership.lean:729-831`) | **proved in tree** (reading) |
| closed under subtyping | `fits_sub` (`:837`), raw `sub` | **proved in tree** for the raw order (reading); **false** for the checker's order and for its join: `not_fits_fiber_normal`, `not_fits_cell_raw`, `not_fits_join` (**proved**, probe A) — TY-01 |
| invariant under normalization | `hasTy_normalize` holds for the executable check; for `Fits` nothing | **false** at the handle arms (probe A; `hasTy_invariant` is the contrast) — TY-01 |
| agreement with the executable check | `fits_hasTy`: `Fits w v t → Val.hasTy v t w.allocated` (`:269`) | **proved in tree** (reading). The converse is not expected (the check is coarse at handles by design, row 44). Its restriction to handle-free values at context-free types is the reply bridge, **owed** (TY-11) |
| agreement with the syntactic judgment on values | `HasTy` types programs, not values. The value-level law is term soundness: `termTy sig env t = some ty → EnvTyped w env vals → evalTerm vals t = some v → Fits w v ty` | **absent** (TY-07). The older layer has it for the coarse check (`evalTerms_hasTy`, `Laws/Program/Typed.lean:999-1015`; reading). For `Fits`, the `fst`/`snd` case over a union of products answers at `Ty.join` (`projectProduct`, `Program/NativeAtom.lean:47-56`), so it needs TY-01 first |
| the exit clause | `fitsExit_success_iff`, `fitsExit_failure_iff`, `fitsExit_of_clean`, `cleanExit_of_never_fits`, `fitsExit_sub`, `fitsExit_mono` (`:162-960`) | **proved in tree** (reading). The shape-defect conjunct (`ExitOk`, row 107) is part one in flight, part two held (row 117); outside this seat |
| the cause clause | `CauseFits`, `causeFits_map`; typed failures are handle-free by the closed alphabet (`valOfErr_keys`, `causeImage_handleFree`) | **proved in tree** (reading) |
| liveness (every named handle is declared) | `fits_live` (`:520`); `unknown` requires `Live` (row 96 D4) | **proved in tree** (reading) |
| the context arm reads the static service table | `ServicesFit w ctx.services` reads `nativeServiceTy` at flat carriers (`FlatFits`, `flatFits_fits`) | the flat arm is **proved in tree** (reading). Row 112 moves the read to `w.serviceTy` (**owed**, Σ_app slice). The flat restriction is what keeps `Fits` structural: a structured carrier would make the context arm recurse into `Fits` at a type that is not a subterm of `handle contextTarget`, so row 118's "its own recursion" is a well-foundedness requirement, not a style choice |
| a fold | `fold_of Effect4.Program.Typed.Fits` (`:248`) | **proved in tree** (the connector; reading) |

### 4.3 TY-01 in detail: two orders, one judgment

**The facts.**

- **proved (probe A, §3):** in `w0 := initialWorld ⟨T, never, ∅⟩`, `Fits w0 (fiber root)
  (fiberOf T never)` holds and `Fits w0 (fiber root) (fiberOf (normalize T) never)` does not.
- **proved (probe A, §3):** in a world declaring cell 0 at the canonical form, the cell fits
  `refOf (normalize T)` and not `refOf T`.
- **proved (probe A):** each pair is one type in the checker's order (`fiber_types_equiv`,
  `cell_types_equiv`).
- **proved (probe A, §5, `not_fits_join`):** the fiber fits each arm of a join and does not fit
  `Ty.join (fiberOf T never) (fiberOf T never)`, which is `normalize (fiberOf T never)`.

**What the checker does (tested, probe A, §4 and §5).**

- The checker gives `succeed (pair x undefined)` with `x : nat | string` the raw answer `T`. The
  `pair` scheme does not normalize (`Program/NativeAtom.lean:21-25`, deliberate). So a fork of it
  declares `Γ id = ⟨T, …⟩`: `fiberPost .fork` stores the certificate `PointTyped` computed
  (`Residual.lean:156`, reading).
- The checker types `select true (succeed f) (succeed f)` at `fiberOf (normalize T) never`.
- The checker accepts `iterate` with the cursor annotated at `fiberOf (normalize T) never` from the
  initial value `f : fiberOf T never`.

**M5 is false on a checked program (proved, probe D).** The program is
`fork(child); if true then f else f`, where `child` is the closed
`x := if true then 1 else "x"; succeed(pair(x, undefined))`.

- **Premises hold, by kernel evaluation (`decide +kernel`):** `Api.typeOf prog3 [] = some rootTy3`
  with `rootTy3 = ⟨fiberOf (normalize T) never, never, ∅⟩`, which is closed. The child checks at
  `⟨T, never, ∅⟩` at the empty environment. Admission accepts the program (tested).
- **`m5_false`: no world types the loaded state.** It walks the tree's own definitions:
  - `TypedState` gives the root fiber's `SavedOk` at `Γ root = rootTy3`; the empty stack forces
    the code's type to `rootTy3`;
  - the root's code (`denoteR`) opens a guard, whose body is the fork;
  - the fork's precondition `BodyTyped`/`PointTyped` at the empty environment forces the
    certificate to the checker's type of the child (`check_sound`, then `effTy_complete`, then the
    kernel-computed `child_cert`);
  - the fork's continuation must be typed at a world that declares fiber 1 at that certificate
    (built with the tree's own `fork_extension`), and the guard's saved arm must continue from
    there;
  - through two constructions and the select's checkpoint, the code ends in
    `pure (success (fiber 1))` at `rootTy3`, and `leaf_false` refutes that exit.
- **`typedState_load_false`** refutes the obligation's universally quantified statement
  (`Assembly.lean:154-156`).

The proof needs a fiber inversion of `TypedProg` that the tree does not state (`fiber_inv`,
proved in the probe, and worth landing beside `guard_inv` and `store_inv`).

**What it means for M6 (reading).** The capstone `typedState_reachable` is planned as M5 plus
step preservation, so for this program its proof route breaks at the base. Whether the capstone's
statement itself fails here is not shown. `RReachable` states are replays, and at later states the
existential world can declare the fiber at a sharper type: `prod nat unit`, which the runtime value
fits and which is a member of the canonical union. The general step obligations meet the same
closure wherever a continuation is typed at the checker's environment (`PointTyped`'s `EnvTyped`,
`Typed/Admission.lean:21-24, 35-40`): after a join the bound value must fit the joined answer, and
in a loop the cursor must fit the annotation. That covers `select`, `catchCause`, `catchIf`,
`matchCause`, the race (`EffsHasTy`), the generator's `GenTy.joinAnswerT` and `iterate`; the
obligations are `step_evaluate`, `step_loop` and `step_deliver` (`Assembly.lean:167-175`), all
`#proof_wanted`. Probe D's shape is the template for a reachable witness if the coordinator wants
one per construct.

**The smallest amendment** (one module, `Membership.lean`, as row 132 already requires):

1. Compare declarations in the checker's order:
   `FiberDeclared w id a e := ∃ fty, w.Γ id = some fty ∧ subN fty.answer a ∧ subN fty.error e`,
   and `Equiv` with `subN` both ways (`RefDeclared`, `PromiseDeclared`).
2. Prove `fits_normalize : Fits w v (normalize t) ↔ Fits w v t`. Its union and product cases are
   `hasTy_normalize`'s (`TypeAlgebra.lean:125-320`), with `fits_sub` in place of `hasTy_sub`; its
   handle cases are `fiberDeclaredN_normalize` and `equivN_normalize`, **proved** in probe A §6.
3. Prove `fits_subN` and `fits_join_left`/`fits_join_right`, as `hasTy_join_left`/`hasTy_join_right`
   (`TypeAlgebra.lean:1080-1092`).
4. Use `subN` in the protocol entries that compare a declared type with a certificate:
   `asyncPre`'s deferred arm, `fiberPre`'s `awaitAll` and `raceAll`, `CompletionStrong.ofRefGet`
   (`Residual.lean:107-127`, `Assembly.lean:36`).

`fits_sub` keeps its proof: `fiberDeclaredN_sub` (probe A) is its handle case. The red control turns
green (`fiberDeclaredN_w0`, proved). The rejected alternative, normalizing every checker type, is
what `NativeAtom.lean:21-25` refuses, because it changes the typing judgment and the printed faces.

Two smaller observations in the same module:

- **Two heap typings exist (reading).** `WorldValid.cells` types cell contents with the coarse
  check (`ValueOk` and `HeapCell`, `World.lean:69-102`), and `preds.HeapCell` types them with
  `Fits` (`Assembly.lean:60`). The coarse one follows from the strong one by `fits_hasTy`. It can be
  derived rather than kept as a second invariant (TY-08, low).
- **The context arm's `Live w v`** duplicates what `fits_live` derives for every other arm. It is
  there because `ServicesFit` alone does not give liveness for the context's own keys. That is
  correct as written and needs no change.

### 4.4 Inhabitance and `Fits` (row 127)

**The theorem shape** row 127 asks for, and what probe B proves:

```lean
-- the fold
def inhabited (t : Ty) : Bool := cata_ty inhabitedAlg t
-- agreement, both directions, at some world
theorem inhabited_iff (t : Ty) : inhabited t = true ↔ ∃ (w : World) (v : Val), Fits w v t
-- the admission predicate on every answer, error, request and table column
def admitColumn (t : Ty) : Bool := t.normalize == .never || inhabited t
```

- **Sound direction, proved (probe B):** `inhabited_of_fits` (every world) and
  `inhabited_of_hasTy` (every allocation table, DI-67's own frozen wording). Structural recursion,
  no premise. So refusing `inhabited t = false` never refuses a type with a member.
- **Complete direction, proved on the handle-free fragment, with a world-independent witness**
  (`fits_of_inhabited_handleFree`, `inhabited_iff_handleFree`). The handle formers are inhabited at
  every argument (`fiber_inhabited`, `cell_inhabited`, `promise_inhabited`). **Owed:** one world
  for several handle positions at once. That is amalgamation: declare each needed handle at a fresh
  key. It is routine by the world order and `fits_mono`, but it is not written.
- **Closure under the raw order, proved:** `inhabited_sub`, by `fun_induction Ty.sub`, so the check
  respects subsumption. **Owed:** `inhabited (normalize t) = inhabited t`. It follows from
  `inhabited_sub` and the membership laws of `normalizeRow` and `productMembers`, as
  `hasTy_normalize` does.
- **DI-67's counterexamples on the tree, proved (red controls):** `prod never nat` and `except
  never never` are canonical (`Normal.fixed`), not `never`, and have no member at any world or under
  any allocation table. `admitColumn` refuses both (`admit_refuses_prod_never_nat`,
  `admit_refuses_except_never_never`). Tested: `never`, `union never never`, `list never`,
  `option never`, `fiberOf never never` and `exitOf never never` stay admitted.
- **Tested, and worth keeping as two rules:** `inhabited` refuses `int` only where `int` empties the
  type. `list int` is inhabited by `[]`, while the `int` scan (`findInt`,
  `Program/Admission.lean:31-41`) refuses it syntactically. The scan is DB-15's representation
  refusal and inhabitance is DI-67's emptiness refusal. Keep both, with their own located reasons.
- **The data synthesis's "answer-only template parameter typed at `never`"** (an unbound `var 0` in
  a supplied row's answer) is covered too: `inhabited (var i) = false` and `var i` is not `never`,
  so `admitColumn` refuses that column. `Row.wellScoped` is the sharper, syntactic reason, and
  admission does not check it for supplied rows today. Both belong in C6's local row clauses.

### 4.5 Do records keep the laws? (row 119)

**Not checked on the tree's `Fits`.** `Ty` has no record constructor, and adding one is the stage-1
slice, so it is not cheap. **Checked on a model instead (probe E, `RecordWorldProbe.lean`).** It is
the data probe's record model (`SynthRecordOrder.lean`; its order lemmas copied verbatim, hash
recorded) extended with the two things that model lacked: a world (a fiber table) and a handle
type former whose membership arm reads a declaration. All of the following are proved, at
`[propext, Quot.sound]` or less:

- **Red control (`raw_not_invariant`).** With the raw order in the handle arm, as the tree's
  `FiberDeclared` is today, a fiber declared at `record [(2, nat), (1, str)]` (written out of
  canonical order) fits that type and not its normal form. Records reach TY-01 through field
  permutation alone, with no union anywhere.
- **With TY-01's amendment (`fitsN_normalize`),** membership is invariant under normalization with
  no premise: the record arm reads canonical order (the data probe's repair) and the handle arm
  reads normal forms. `amended_fits_normal` is the red control turned green.
- **`normalize_idem`:** normalization stays idempotent with records and handles.
- **`fitsN_mono`:** membership is monotone in the world; the record arm transports through
  `canon_map`, `mem_canon` and a positional monotonicity lemma.

**Reading** (the data probe's models, proved there and rerun by its synthesis seat):

- closure under the exact record order (`fitsFields_exact_mono`);
- width with positional values is unsound (`positional_width_unsound`);
- agreement of the arm with the executable check (`fitsV_iff_hasTyV`).

So the records design keeps every law `Fits` has today. It does not repair the one `Fits` lacks
(TY-01), and with records TY-01 has a second entrance, field permutation, unless the handle arms
compare normal forms. It adds one requirement of its own: raw `sub` at records compares canonical
name lists (§2.4, TY-10). TY-01's amendment makes even that requirement unnecessary for `Fits`,
though not for the checker's other uses of raw `sub`.

## 5. The exact embeddings, K2 (question 4)

### 5.1 The laws in the literature's terms

K2 is a pair `write : A → F`, `read : F → Option A` with three laws:

- (a) `write` is total on a stated domain `D`;
- (b) **retraction**: `read (write a) = some a` on `D`;
- (c) **exactness**: `read f = some a → N f = N (write a)`, modulo a named normaliser `N`.

With (b) alone, `write` is a split monomorphism and `read` a one-sided inverse. `read` may still
accept inputs outside the image. That is the widening `AGENTS.md` warns about. With (b) and (c), and
`read` invariant under `N`, the pair is a **partial isomorphism** between `D` and the `N`-classes of
the image (Rendel and Ostermann, *Invertible Syntax Descriptions*, 2010; by name, coherence
principle's list). In optics vocabulary it is a **lawful prism**, `review = write` and
`preview = read`, with both prism laws (Pickering, Gibbons, Wu, *Profunctor Optics*, 2017; by name).
`Canonical`'s fields `ofVal_toVal` and `ofVal_exact` are exactly those two laws
(`Store/Carrier/Image.lean:45-47`; coherence principle §1, read). Lenses (Foster, Greenwald, Moore,
Pierce, Schmitt, TOPLAS 29(3), 2007; by name) are the product-side analogue, with GetPut and PutGet.
§2.6's boundary projection is a lens `get`.

**Proved (probe C, generic, `[propext]` only):** any retraction becomes an exact embedding modulo
`N` when its read is guarded by the writer's image:
`readExact f := (read f).filter (fun a => (write a).map N = some (N f))`.

- `readExact_exact` gives (c).
- `readExact_retract` keeps (b).
- `readExact_le`: the guard only refuses.
- `readExact_iff`: when `read` is `N`-invariant, the guarded read answers exactly the `N`-classes of
  the images.

This is the general form of row 128's repairs. Each named repair (the whole-check comparison, the
canonical-branch check) is a way to make the unguarded read already satisfy the guard, without the
re-encoding cost.

### 5.2 Each embedding against the laws

| Pair | Domain and normaliser | (b) retraction | (c) exactness |
| --- | --- | --- | --- |
| `Canonical` instances (`toVal`/`ofVal`) | every value of the carrier; `N = id` | **proved in tree** (`ofVal_toVal`) | **proved in tree** (`ofVal_exact`) |
| printer/reader | the readable domain, which excludes annotated loops (DI-91); `N = id` on `Expr` | **proved in tree** (`read_print`, law 11) | **proved in tree** (`read_exact`, law 12) |
| `Ty.schema`/`Ty.ofSchema` | closed types; `N_S` = drop the annotations that do not change decoding, and with records, order a struct's properties canonically. Annotations that change decoding (`parseOptions`, `identifier`) are refused by name, never normalized away (data synthesis NS1) | **proved in tree** (`ofSchema_schema`, `Schema/Bridge.lean:140`) | **false today**: a check is read by its id alone (`checkId`, `:62`), so a filter group, an aborted filter or a payload all read as `int` (data verify V1; V1a **tested** again here, probe C). **Proved for the guarded read** (`ofSchemaExact_exact`, probe C) |
| JSON codec `encode`/`decode` | `isCodecValue` at canonical types; `N_J` = object key order (the owner-approved S-3 clause, `schema-codec.contract.md:26`) | **proved in tree** (`decode_of_encode`, `decode_encode`) | **false today**: `decode` is not injective on the image, because `Val` is untyped (`Exit.success v` and `Result.failure v` are both `ctor 0 [v]`), so two images with different key sets decode to one value (data verify V2; **tested** again here). **Proved for the guarded read** (`decodeExact_exact`); the guard refuses V2's `Success` image and keeps the `Failure` image (**tested**) |

**Row 128 is confirmed:** both are retractions only, and the vocabulary amendment is right. The
second commit of stage 1 can take either route:

- the guard (probe C's `readExact`, at the cost of one re-encoding per decode);
- exactness by construction. For `decodeRaw`'s union arm, accept a value from branch `b` only if no
  earlier branch's membership test holds of it. That is the encoder's own selection rule
  (`encodeRaw`'s union arm, `Schema/Codec.lean:174-176`), so the decoder selects the canonical
  branch. For `ofSchema`, compare whole checks, and refuse the `TypeParameter` declaration.

`encode_injective` (proved in tree) is a different law. It says `write` is injective, which the
retraction already implies. V2 breaks injectivity of `read` on the image, which is what exactness
adds.

**Why exactness matters beyond tidiness.** When row 123's in-program `decode τ` lands, an inexact
decoder is an observable face divergence. rc.112 decodes V2's `Success` image as an `Exit` success,
while Lean's value re-encodes as a `Result` failure. So NS2's host-face agreement needs (c) first.
On the host reply path the codec is not used, because a reply is a `Val`, not JSON (data synthesis
NS5).

## 6. The boundary (question 5)

### 6.1 What the reply rule is, formally

Decision 12's route A (row 122): host data enters a program only as a reply to a host row, checked
at the row's declared columns. The check, `admitAnswer` (`Program/Admit.lean:59-75`), is a located
refusal (K4) over a completion:

- **A success value** must be handle-free data of the row's answer type, or, at a handle-typed row,
  a natural that requests a fresh external allocation (`externalValue`,
  `Program/Compile.lean:1371-1382`: `Val.hasTy` and an empty handle list, or the allocation case).
- **A failure** must fit `errAdmits` at the row's error type. The error alphabet is closed and
  handle-free (`valOfErr_keys`, `causeImage_handleFree`), so "typed failures need no new check"
  (host-boundary §5) is a theorem of the alphabet, not a policy.
- **A delayed cell read** (`ofRefGet`) checks the cell's current contents.

Row 97's table rule refuses internal handle kinds (fiber, cell, deferred, scope, context) in host
rows' answer and error types (`findInternalHandleInTable`, `Program/Admission.lean:58-95`, a
generated `TyAlgebra` instance, so a fold).

### 6.2 Handle-freeness is a store well-formedness invariant

The **minted-handle invariant** says every handle reachable in a state names something the machine
allocated (`mintedIn`/`handleLive`, `Program/Admit.lean:15-26`; in the typed state, `Live w v`). It
has three readings, and they agree:

- **store typing:** TAPL's well-formed store under a store typing requires every location a value
  mentions to be in the typing's domain (ch. 13, by name); `Live` is that clause;
- **capability safety:** "no forged references" (Miller 2006 thesis, by name). Devriese, Birkedal
  and Piessens (EuroS&P 2016, by name) give it as a Kripke logical relation over worlds, which is
  what `Fits` plus `Live` is for this first-order language;
- **world extension:** an external allocation on application (`allocated ++ [target]`) is a step
  of `World.leHost` (it requires `Extends` on the allocation table), so `fits_mono` transports every
  other judgment across it.

Row 97's value rule keeps the invariant by construction: a reply introduces no handle but a fresh
external one minted at application. Typed failures cannot carry one. That is the formal content of
"handle-freeness as an invariant".

### 6.3 The receipt theorem and its bridge

host-boundary §4.5's receipt theorem, specialised to the interim profile:

```lean
theorem reply_fits (hT : TypedState src ty w m) (hrow : externalRow t i = some row)
    (hadm : admitAnswer row m fiber token (.ofExit (.success v)) = none)
    (hprep : externalValue row.answer m.allocated v = some (alloc′, v′)) :
    Fits w′ v′ row.answer   -- w′: w with its external allocation table extended to alloc′
```

Its core is a **bridge lemma**, owed (TY-11):

```lean
theorem fits_of_hasTy_handleFree (hfree : Store.Val.handles v = []) (hctx : noContext t = true)
    (h : Val.hasTy v t alloc = true) : Fits w v t
```

It holds by the same structural recursion as `fits_hasTy`, read backwards. A handle-free value meets
no handle arm, and `unknown`'s `Live` holds of a value with no keys (`live_of_keys_nil`). The
context arm is the one exception: the coarse check accepts any context-shaped value, `Fits` also
requires `ServicesFit` and `Live`, and that is why row 97's table rule must keep refusing context
in answer types until a context validation exists (the side audit's `ContextBridge.lean` point,
via the model-probe synthesis R5). The allocation case is the external arm of `HandleFits`:
`allocated′[index]? = some target` holds by construction. Row 96 parks "the reply-to-`Fits` bridge"
with the runtime twin, which is consistent: it is owed, small, and needed only when the host lane
unparks. The converse, "every semantically valid, representable reply is accepted"
(host-boundary §4.5), is the K4 completeness of `admitAnswer` against `ReplyFits`, owed.

### 6.4 What the host-row domain bit buys

`asyncPre`'s external arm (`Residual.lean:110-112`) reads `rowOf op` without `dom op`. Outside the
table, `rowOf` is the placeholder row, whose columns are `never`. `never` is below every type, so
the entry holds vacuously at a short table and constrains at a longer one. The protocol family is
then not monotone in the table (`typedProg_not_table_monotone`, proved by the TREE verifier and
rerun by the audit; reading). Requiring the bit makes an out-of-domain registration have **no** entry
(precondition `False`), which is the demand-forward direction of protocol refinement (de Vilhena,
read by the pedigree seat). C4's "exact old protocols" premise then holds (§3.2). At the runtime
boundary the same fact is already enforced: `admit` refuses a reply for an index outside the table
as `notExternal` (`Program/Admit.lean:77-89`). The bit makes the proof side say what the runtime
does. It is an extension need, not an M6 need, as the audit says, because the parking route never
reads the table.

## 7. Gaps, each with its smallest amendment

Kinds: **gap-fundamental** (an open milestone obligation is false as stated), **gap-rigor** (a law
or definition the plan relies on is missing), **gap-tidiness** (wording, naming, ownership).
**confirmed** and **account** items are listed in the returned findings, not here.

| Id | Kind | Gap | Smallest amendment |
| --- | --- | --- | --- |
| TY-01 | gap-fundamental | `Fits` and the typed state's protocol entries compare declared types with raw `sub`, and the checker compares and joins in `subN`. `Fits` is not closed under the checker's subsumption or join, and not invariant under `normalize` (three red controls proved on the tree's `Fits`; the checker's types tested). **M5's `typedState_load` is false** on a checked, closed, admitted, host-free program (`typedState_load_false`, proved, probe D). The M6 cases for `select`, `catchCause`, `catchIf`, `matchCause`, races, generator joins and annotated loops need the same closure (reading) | in `Membership.lean`: `subN` in `FiberDeclared`, `RefDeclared`/`Equiv`, `PromiseDeclared`; then `fits_normalize`, `fits_subN`, `fits_join_left/right` by `hasTy_normalize`'s and `hasTy_join_left/right`'s proofs; `subN` in `asyncPre`'s deferred arm, `fiberPre`'s `awaitAll`/`raceAll`, `CompletionStrong.ofRefGet`. Handle arms proved invariant (probe A §6); the counterexample's leaf holds under them (`prog3_leaf_amended`). Register probe D as `E4-TYPED-CE-009` (proposed) and keep it as the red control. Land the amendment with the Σ_app slice, which edits the same module |
| TY-02 | gap-tidiness | DI-15 says "identity is subtyping-equivalence"; that is true on `CTy` and false for raw `sub` (`T_not_sub_normal`) | name `Ty.subN` (or state the order on `CTy` only) and `subN_equiv_iff` in `TypeAlgebra.lean`; amend DI-15's sentence to "identity is equality of normal forms, the kernel of `subN`", and the system map's type row to say `Ty/≡N = CTy` |
| TY-03 | gap-rigor | DI-67 is enforced for `int` only (row 127). Inhabitance has no definition, no agreement theorem and no admission clause in the tree | `inhabited` as a `TyAlgebra` instance; probe B's theorems (sound against `Fits` and `Val.hasTy`, complete on the data fragment, the three handle witnesses, `inhabited_sub`) plus the two owed ones (one world for several handles by fresh keys; `inhabited (normalize t) = inhabited t`); `admitColumn` at every answer, error, request and table column, with its own located reason |
| TY-04 | gap-rigor | C3's reflection (the checker gives the same answer, refusals included, on a Σ-program under any extension) is unproved, and "Σ-program" is undefined | define `SigProgram Σ p` as the checker's reads (operations in `dom Σ`, looked-up keys whose codes have carriers); prove one generic `cata_congr_on` for generated folds (algebras that agree on the reads of a term's nodes give the same fold) and get C3 as an instance, instead of a seventh hand induction |
| TY-05 | gap-rigor | `LawfulSig` does not exist; admission checks the whole table, so a lawless appended row revokes old programs (tested by the pedigree verifier); `admitProgram`'s last arm invents a key when `Table.lawful` fails and `checkLawful` finds nothing (`Program/Admission.lean:169`) | write `LawfulSig Σ := (∀ e ∈ Σ, Local e) ∧ Σ.Pairwise Compatible` with the clauses of §3.2's C6 row (rows 97, 113, 114, 127, `int`, registrable, templates admissible and well scoped); then C6 is `List.forall_append` with `List.pairwise_append`; prove `Table.lawful t = false → Table.checkLawful t ≠ none` and delete the invented key |
| TY-06 | gap-tidiness | DB-01 (to be amended with C1–C8) would cite the free-monad injection laws as R2's C1, but for Σ_app the syntax map is the identity | DB-01: "C1 is vacuous for Σ_app (rows and keys are data); for Σ_core growth, conservativity is the equation-free persistent extension plus DI-47's finite gate, the only form a two-version statement has" |
| TY-07 | gap-rigor | no term-level soundness for `Fits`: `termTy sig env t = some ty → EnvTyped w env vals → evalTerm vals t = some v → Fits w v ty`. `step_evaluate` needs it, and its `fst`/`snd` case over unions of products answers at `Ty.join` | state and prove `evalTerm_fits` after TY-01, by the term fold (the coarse twin `evalTerms_hasTy` exists, `Laws/Program/Typed.lean:999-1015`) |
| TY-08 | gap-tidiness | two heap typings: `WorldValid.cells` (coarse `ValueOk`) and `preds.HeapCell` (`Fits`) | derive the coarse one from the strong one by `fits_hasTy` at a good place; keep one invariant |
| TY-09 | gap-rigor | the K2 exactness laws of `ofSchema` and the JSON codec are false today and their normalisers are not functions (row 128, confirmed: V1a and V2 tested again) | name `N_S` and `N_J` as functions; take probe C's guard (`readExact`, proved) or make the reads exact by construction (`decodeRaw`'s union arm selects the encoder's canonical branch; `ofSchema` compares whole checks and refuses `TypeParameter`); keep V1/V2 as red controls; before row 123's in-program decoder |
| TY-10 | gap-rigor | records (row 119) need: raw `sub` at records comparing **canonical** name lists (else a permuted record is not below its normal form and TY-01 widens: probe E's `raw_not_invariant`, proved on a model, shows permutation alone reaches a handle arm); the non-distribution incompleteness named; `inhabited`'s and `Fits`'s record arms in canonical order | stage-1 acceptance items: a positive control that a permuted record is raw-below its normal form (it must hold), a theorem `record_sub_not_complete` beside `sub_not_complete`, the record arms in `inhabitedAlg` and `Fits` after TY-01, and one field-order normaliser shared by `normalize`, `N_S`, `N_J` and `Shape.struct` |
| TY-11 | gap-rigor | the receipt theorem for host replies has no bridge from the runtime check to `Fits` (parked by row 96) | `fits_of_hasTy_handleFree` (handle-free value, context-free type) and the allocation case; keep context refused in host-row answers until context validation exists. Owed when the host lane unparks |
| TY-12 | gap-tidiness | row 116's bit has a red control (`typedProg_not_table_monotone`) but no positive control | add `typedProg_rows_append` (with the bit) beside it in the Σ_app slice |
| TY-13 | gap-tidiness | `AdmitRefusal.uninhabited at` names the `int` scan, which is a representation refusal: `list int` is inhabited and still refused (tested, probe B) | when row 127 lands, give the two refusals distinct names (for example `intType at` for DB-15's scan, `uninhabited at` for DI-67's check) |
| TY-14 | gap-tidiness | DI-67's frozen statement reads `Val.hasTy` under some allocation table; row 127 says "agreeing with `Fits`" | state both agreement theorems (probe B proves the sound half of each); cite both in `foundation-wave2.contract.md:217` when it is reconciled |
| TY-15 | gap-tidiness | `Laws/Program/Template.lean:332-333` says the kernel does not reduce the well-founded `Ty.sub`; `decide +kernel` does (`KernelEvalProbe.lean` `k1`, `k2`; probe D's `prog3_typed`, `child_cert`, `T_not_sub`, all proved). So concrete facts about `sub`, `normalize`, `join` and the checker can be certified directly | correct the comment; prefer `decide +kernel` for concrete type facts in fixtures and counterexamples (the estate already uses it for certificates) |
| TY-16 | gap-rigor | `TypedProg` has `guard_inv`, `store_inv` and the payload inversions, but no inversion for an ordinary fiber operation; probe D proves one (`fiber_inv`) | land `fiber_inv` beside `guard_inv` in `Residual.lean`; M6's step proofs and every typed-state counterexample need it |

## 8. What the next briefs should add

**The Σ_app slice** (rows 111–116; the first slice of the M5–M7 brief, after G):

1. The definitions, in `Laws`, not in a probe: `SigExtends`, `SigProgram` (TY-04), `LawfulSig` in the
   `Forall`/`Pairwise` shape with `admitSig_ok_iff` (TY-05), and `π` for services.
2. Shape A (row 112), and **TY-01 in the same edit of `Membership.lean`**: `World.serviceTy`;
   `ServicesFit` reading it; the agreement premise in `servicesFit_map` and `fits_map`; `subN` in the
   handle arms; `fits_normalize`, `fits_subN`, `fits_join_left/right`. The module is row 132's one
   module, both changes touch it, and M6's join and loop cases need the second.
3. R2Probe's monotone family moved into `Laws`, plus C3 reflection by fold congruence (TY-04) and
   `typedProg_rows_append` with the domain bit (TY-12).
4. Red controls kept as fixtures: `prepend_not_extends`, `shadow_not_extends`,
   `typedProg_not_table_monotone`, `one_code_two_carriers`, probe A's `not_fits_join`, and probe
   D's `typedState_load_false` (proposed `E4-TYPED-CE-009`). The last two must flip under the
   amendment: `not_fits_join` to its positive form, and probe D's program to a typed load.
5. Positive controls: probe D's program loads into a typed state under the amendment (M5's first
   positive case), and probe A's `select` and annotated loop are carried through their steps.

**The inhabitance slice** (row 127; after H2 part one; sequenced with the Σ_app slice because both
edit `Program/Admission.lean`): TY-03 and TY-13, with probe B's theorems as the acceptance list.

**Data stage 1** (row 119, records):

1. TY-10's four items.
2. TY-09 as the slice's second commit, as row 128 rules.
3. The width projection's law stated at the adapter (`fits_coerce`'s shape), and width inside a
   program refused by name with a red control.
4. The R3.8 finite discipline for the `Σ_core` append, stated as what it is (§3.1).

**The M5–M7 brief**, one sentence beyond row 132's: "Membership across a join or into a loop
cursor is `fits_join_left/right` or `fits_subN`, never raw `sub`; term soundness is the named lemma
`evalTerm_fits` (TY-07); ordinary fiber operations invert by `fiber_inv` (TY-16); M5 is stated
after TY-01 lands, with probe D's program as its first positive control."

### 8.1 Proposed decisions rows (the coordinator writes the register; these are proposals)

| Proposed row | Options | Recommendation | Who |
| --- | --- | --- | --- |
| **TY-01's repair** (M5 is false through `Fits`'s raw handle arms) | (a) compare declarations in the checker's order inside `Fits` and the protocol entries, then `fits_normalize`, `fits_subN`, `fits_join_*`; (b) normalize every type the checker produces, so raw and normalized orders coincide on checker output; (c) normalize declarations at creation only | **(a)**, inside `Membership.lean` and `Residual.lean`, landing with the Σ_app slice. (b) changes the typing judgment and the printed faces (`NativeAtom.lean:21-25` refuses exactly that), and (c) leaves raw queries such as `refOf T` against a canonical declaration failing (probe A, `not_fits_cell_raw`) | owner |
| **Register probe D** as `E4-TYPED-CE-009`: "M5 loads a checked, closed, host-free program into no typed state: `Fits` compares fiber declarations in the raw order while the checker joins in the normalized order" | register now, repaired by the row above; or hold until the repair | register now, with `typedState_load_false` as the witness | coordinator |
| **DI-15's identity sentence** (TY-02) | amend to "equality of normal forms, the kernel of `subN`"; or leave | amend; one sentence | coordinator (register text) |
| **The two admission refusals' names** (TY-13), with row 127's slice | rename the `int` scan's refusal; or reuse `uninhabited` for both | rename: they refuse different things (`list int` is inhabited) | coordinator, with the slice |
| **`LawfulSig`'s shape** (TY-05), with the Σ_app slice | `Forall Local ∧ Pairwise Compatible`; or a monolithic check | the `Forall`/`Pairwise` shape, so C6 is two list lemmas and admission becomes monotone | owner, inside rows 111 and 114 |

## 9. Literature, as marked here

Each entry carries the mark this note gives it. "By name" means cited from general knowledge, not
read in this pass, with section numbers from memory.

| Work | Mark | Used for |
| --- | --- | --- |
| Pierce, *Types and Programming Languages*, 2002: ch. 13 (references, store typings), ch. 15 (subtyping; §15.2 record rules, §15.5 invariant references, §15.6 coercion semantics), ch. 16 (algorithmic subtyping and typing, joins), ch. 20–21 (recursive types) | by name | §2, §4.1, §6.2 |
| Amadio and Cardelli, "Subtyping recursive types", TOPLAS 15(4), 1993 | by name | §2.5, row 124 |
| Frisch, Castagna, Benzaken, "Semantic subtyping", JACM 2008 | assumed (type-algebra note §5.3) | §2.3 |
| Pierce 1991 (intersection and union types); Dunfield, "Elaborating intersection and union types", JFP 2014 | by name | the union rules of `sub` |
| Wand; Rémy 1994; Gaster and Jones 1996; Leijen, "Extensible records with scoped labels", TFP 2005 | by name (via the data synthesis §6.4) | §2.6: why closed records |
| Breazu-Tannen, Coquand, Gunter, Scedrov, "Inheritance as implicit coercion", I&C 1991; Luo, "Coercive subtyping", JLC 1999 | by name | §2.6: width as a boundary coercion |
| Goguen, Thatcher, Wagner, Wright 1977; Ehrig and Mahr 1985 (persistency); Goguen and Burstall, "Institutions", JACM 1992 | by name | §3.1 |
| Swierstra, "Data types à la carte", JFP 2008, §2, §6 | read (model-probe pedigree seat) | §3.3 |
| Delaware, Oliveira, Schrijvers, "Meta-theory à la carte", POPL 2013; Delaware, Keuchel, Schrijvers, Oliveira, "Modular monadic meta-theory", ICFP 2013 | by name | §3.3: conservative extension with proof reuse |
| Hyland, Plotkin, Power, "Combining effects: sum and tensor", TCS 357, 2006 | by name (as the model probe) | §3.3: equational theories |
| de Vilhena, thesis 2022 (protocols, refinement) | read (model-probe pedigree seat) | §4.1, §6.4 |
| Ahmed 2004 thesis; Appel and McAllester 2001; Iris (Jung et al. 2018) | by name | §4.1: Kripke logical relations, why no step-indexing |
| Rendel and Ostermann 2010; Matsuda and Wang 2013; Pickering, Gibbons, Wu 2017; Foster et al. 2007; McBride 2011 | by name (coherence principle's list) | §5: K2 as partial isomorphism, prism, lens |
| Miller 2006 thesis; Devriese, Birkedal, Piessens, EuroS&P 2016 | by name | §6.2: capability safety |
| Comon et al., *Tree Automata Techniques and Applications* | by name | §2.5: emptiness of regular types |

## 10. Receipt

**Base and head.** `refactor/phase1-phase3` at `ea5b28b5`; nothing committed; `git status` clean
before and after (tested). No tracked file edited.

**Commands and results** (each through the one-compiler lock,
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`, one at a time):

| Probe | Run | Result |
| --- | --- | --- |
| `TypesOrderProbe.lean` | run 1 | exit 1: `World` ambiguous between `Typed.World` and `Machine.World` (two errors; dependent theorems fell back to `sorry`; no claim taken from it) |
| | run 2 (with §5) | exit 0 |
| | run 3 (with §6) | exit 0 |
| `InhabitedProbe.lean` | run 1 | exit 1: `Fits` ambiguous with `Program.Fits` inside `simp only`; `decide` on goals with free variables (no claim taken) |
| | run 2 (final) | exit 0; every `#guard` holds; axioms below |
| `ExactByImageProbe.lean` | run 1 (final) | exit 0; every `#guard` holds; axioms below |
| `TypesOrderProbe.lean` | run 4 (with §7, final) | exit 0; every `#guard` holds; axioms below |
| `M5CounterProbe.lean` | run 1 | exit 1: `HasTy`, `check_sound`, `effTy_complete` unknown (missing import); everything else elaborated; no claim taken |
| | run 2 | exit 0 |
| | run 3 (with `typedState_load_false`, final) | exit 0; the `#guard` holds; axioms below |
| `KernelEvalProbe.lean` | runs 1–5 | scratch prints; runs 1 and 5 failed on a name; run 2 already proved `k1`, `k2` |
| | final | exit 0; axioms below |
| `RecordWorldProbe.lean` | run 1 | exit 1: a doc comment before `mutual`; every theorem else elaborated; no claim taken |
| | run 2 (final) | exit 0; axioms below |

**Axioms, verbatim from the final logs.**

```text
TypesOrderProbe.log
'Research.TypesSeat.prog3_leaf_false' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.prog3_leaf_amended' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.subN_normalize_right' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.fiberDeclaredN_normalize' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.equivN_normalize' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.fiberDeclaredN_sub' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.fiberDeclaredN_w0' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.not_fits_join' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.subN_trans' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.sub_le_subN' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.subN_equiv_iff' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.ofRaw_eq_iff' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.sub_u_factor_false' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.T_not_sub_normal' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.T_subN_equiv' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.normal_sub_T' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.fits_fiber_raw' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.not_fits_fiber_normal' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.fiber_types_equiv' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.fits_cell_normal' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.not_fits_cell_raw' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.cell_types_equiv' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.hasTy_invariant' depends on axioms: [propext, Quot.sound]

InhabitedProbe.log
'Research.TypesSeat.Inhabit.inhabited_of_fits' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.inhabited_of_hasTy' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.fits_of_inhabited_handleFree' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.inhabited_iff_handleFree' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.fiber_inhabited' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.cell_inhabited' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.promise_inhabited' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.inhabited_sub' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.prod_never_nat_canonical' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.except_never_never_canonical' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.prod_never_nat_empty' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.except_never_never_empty' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.prod_never_nat_no_hasTy' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.admit_refuses_prod_never_nat' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Inhabit.admit_refuses_except_never_never' depends on axioms: [propext, Quot.sound]

ExactByImageProbe.log
'Research.TypesSeat.Exact.readExact_le' depends on axioms: [propext]
'Research.TypesSeat.Exact.readExact_exact' depends on axioms: [propext]
'Research.TypesSeat.Exact.readExact_retract' depends on axioms: [propext]
'Research.TypesSeat.Exact.readExact_iff' depends on axioms: [propext]
'Research.TypesSeat.Exact.decodeExact_retract' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Exact.decodeExact_exact' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Exact.decodeExact_sound' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Exact.ofSchemaExact_retract' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.Exact.ofSchemaExact_exact' depends on axioms: [propext, Quot.sound]

M5CounterProbe.log
'Research.TypesSeat.M5.prog3_typed' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.M5.rootTy3_closed' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.M5.child_cert' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.M5.leaf_false' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.M5.fiber_inv' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.M5.m5_false' depends on axioms: [propext, Quot.sound]
'Research.TypesSeat.M5.typedState_load_false' depends on axioms: [propext, Quot.sound]

KernelEvalProbe.log
'k1' depends on axioms: [propext, Quot.sound]
'k2' depends on axioms: [propext, Quot.sound]
'k3' depends on axioms: [propext]

RecordWorldProbe.log
'RecWorld.raw_fits_declared' depends on axioms: [propext]
'RecWorld.raw_not_invariant' depends on axioms: [propext]
'RecWorld.amended_fits_normal' depends on axioms: [propext]
'RecWorld.normalize_idem' depends on axioms: [propext, Quot.sound]
'RecWorld.fitsN_normalize' depends on axioms: [propext, Quot.sound]
'RecWorld.fitsN_mono' depends on axioms: [propext]
```

**SHA-256 of the probes:**
`TypesOrderProbe.lean d9cbd8ad5ed950ddd2e58e64beed7945d70ff30c9d2e25ccd06b05bd777a22dd`;
`InhabitedProbe.lean 699b1c9b614cd3f19403f33231506696d8db63015ff0af613ecf37efc0b1a4de`;
`ExactByImageProbe.lean 1d2fb97f45b2620f72cd979e5de439acec268a96da3148ece7545633ab008233`;
`M5CounterProbe.lean 627b12f2d60f3fe1690b3d2ff1cfea7324ea36564a763694f0053941b37f45e7`;
`KernelEvalProbe.lean d241d5650c04841c0c84f454ae4d2fff43f7a547bd4f5fd7c327b6472139a043`;
`RecordWorldProbe.lean 077fe1317976db5f994ef260091dd4b393c3edaaf75d24583a80333c97fe11a1` (it copies lines 22–29 and 99–212
of the data synthesis model, SHA-256 `b7bdf58b5d0f031628a5aa0283d86d7d255c3f3e477d322f78eb5ef5ee2ada5e`).

**What every `#guard` checked** (tested):

- **probe A:**
  - the fork body's answer is the raw `T` and `normalize T ≠ T`;
  - the annotated loop program checks, at answer `unit`;
  - `subN` holds and raw `sub` fails on the loop's pair;
  - a `select` of two raw fiber answers types at the canonical form;
  - §7: the closed child's certificate is the raw `T`; `Api.typeOf prog3 [] = some rootTy3`,
    closed; admission accepts `prog3`;
  - §7: the loaded reference code forks the child at the empty environment and path `[0, 0, 0]`,
    and, answered as a derivation must cover, finishes with `success (fiber 1)`.
- **probe D:** admission accepts `prog3`. Its other facts are kernel theorems (`decide +kernel`),
  not guards.
- **probe B:**
  - `admitColumn` admits `never`, `union never never`, `list never`, `option never`,
    `fiberOf never never`, `exitOf never never`, `except never nat`;
  - it refuses `prod nat (except never never)` and `int`;
  - it admits `list int`, which `findInt` refuses.
- **probe C:**
  - V2: two images decode to one value;
  - the guarded decode keeps `jFailure` and refuses `jSuccess`;
  - `encode` does not give `jSuccess` back;
  - V1a: reads as `int` unguarded, refused guarded;
  - one closed product type round-trips through the guarded read.

**Read** (reading): `AGENTS.md`; `docs/core/system-map.md` §§1.1, 2, 4–8;
`docs/core/decisions.md` rows 2, 3, 21, 41–44, 56, 60, 61, 68, 95–97, 104–133; the three syntheses
and the audit named in the brief (model probe §§1–3.3, audit §§1–6, data probe §§0–9 and Appendix
A, pass synthesis by its cross-references only); `docs/DESIGN-BASIS.md` DB-01, DB-15;
`docs/DESIGN-ISSUES.md` DI-15, DI-35, DI-47, DI-62, DI-67, DI-78; `docs/core/host-boundary.md` in
full; `docs/core/coherence-principle.md` §§1–4 and its literature list;
`docs/research/2026-09-18-research-type-algebra.md` §5 and §8; `2026-09-07-lit-papers.md` Q4; the
code at every `file:line` cited above; `R2Probe.lean` in full; `Conservativity.lean` §1–2; the data
probe's `pedigree/verify-Probe.lean` §V1–V3 and the record models' declaration lists and logs.

**Not run, and why.** No `lake build`, `make`, generator, `git add` or `git commit` (the brief). I did
not rerun the other seats' probes; their results are cited as reading, with the seat that proved
them. TY-01's M5 consequence is proved (probe D). Its M6 consequence beyond M5's base is reading: I built no reachable state for a step obligation. The
literature is by name throughout except where a tree note read it (marked). Section numbers given
for TAPL and the papers are from memory and are not verified here.
