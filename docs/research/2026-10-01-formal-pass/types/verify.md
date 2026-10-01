# Verify: seat TYPES of the formal pass (2026-10-01)

Adversarial verification of `note.md` in this folder. I reran all six of the seat's probes
through the one-compiler lock and re-read every cited line and section. I checked each
"formal notion" against the definition the literature gives it, and wrote four probes of my own
(`verify-*.lean`).

## The one thing

**TY-01 is right, and it is bigger than the seat says.**

- **The capstone fails too.** The seat's program refutes M5's `typedState_load`, and it also
  refutes M6's capstone `typedState_reachable`. The note says the capstone is "not shown false".
  The empty tape reaches the loaded machine, so the capstone's statement contains M5's at
  `compileFuel = fuel`. Proved in `verify-CapstoneProbe.lean` (`capstone_implies_load`,
  `capstone_false`), at `[propext, Quot.sound]`.
- **The amendment is sufficient.** I wrote a copy of `Fits` whose fiber, cell and deferred arms
  compare declarations in the checker's order. On that copy, normalization invariance, closure
  under the checker's order and closure under joins are proved, and the M5 leaf holds through
  the join (`verify-AmendedFitsProbe.lean`, `[propext, Quot.sound]`). The seat had these as
  reading.

Two facts the coordinator needs before landing it:

1. **The repair needs an owner ruling.** It re-reads ruled and tracked text:
   - row 96's D1, "cells and deferreds compared by subtyping both ways";
   - host-boundary §4.4, "exactly the declared type" and "a subtype";
   - `E4-TYPED-CE-006`'s forced repair.
2. **The proposed ID collides.** The seat proposes `E4-TYPED-CE-009`, and the proofs seat
   proposes the same ID for a different witness (`proofs/note.md:330`, `:595`).
   `E4-TYPED-CE-007` is cited as registered but is in neither register.

## 0. Base, scope, evidence words

- **Base.** `refactor/phase1-phase3` at `ea5b28b5`. Nothing under `src/` or `Test/` has changed
  since `efd67af1` (`git diff --stat efd67af1 HEAD -- src Test` is empty). `git status` was clean
  before and after. The `.olean` files of the nine modules the probes import are newer than their
  sources (checked by modification time).
- **What I touched.** I wrote only `verify.md` and the `verify-*` files in this folder. I edited
  no tracked file and ran no `lake build`, `make`, generator, `git add` or `git commit`. I did
  not touch `/Users/pooks/Dev/lean4-effect4-slice6`. Every compile went through
  `serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`, one at a time.
- **The seat's files.** Before the rerun, the SHA-256 of all six seat probes matched the note's
  receipt. I did not modify them.
- **Evidence words.**
  - **proved**: a kernel theorem compiled here, with axioms printed at `[propext, Quot.sound]`
    or less. "proved (rerun)" means the seat's own theorem, recompiled here with axiom lines
    identical to its log.
  - **tested**: a `#guard` run here.
  - **reading**: code or notes read, not run.
  - **assumed**: not checked.
- **Literature marks.** **read**, with the note that read it; **by name**, not reread in this
  pass; **assumed**.

## 1. Verdicts

| Id | Verdict | Evidence |
| --- | --- | --- |
| TY-01 | confirmed (and strengthened) | **Reproduced.** Proved (rerun): `m5_false`, `typedState_load_false`, `T_not_sub_normal`, `not_fits_fiber_normal`, `not_fits_cell_raw`, `not_fits_join`; every probe A `#guard` holds (tested).<br>**Cause, reading.** `Fits`'s handle arms use raw `sub` (`Laws/Program/Typed/Membership.lean:25-38`). Every subsumption comparison in the checker is `sub` after `normalize` (`Laws/Program/Typing/HasTy.lean:186-187`, `:244`, `:388`; `Program/Checker.lean:185-188`, `:222`, `:369`; `Program/Typing/Rules.lean:114-117`), and every answer join is `Ty.join` (`Checker.lean:59`, `:148-167`, `:316`).<br>**Stronger than claimed.** The capstone is false as well: `capstone_false` (proved).<br>**Amendment.** `fitsN_normalize`, `fitsN_subN`, `fitsN_join_left/right` and `amended_join_holds` are proved; `tree_join_fails` is the proved red control.<br>**Corrections.**<br>(a) "Stays in one module" conflicts with its own step 3, which edits `Residual.lean` and `Assembly.lean`. In `asyncPre`'s deferred arm, `awaitAll` and `raceAll` the certificate is chosen in the derivation. Once `fits_normalize` holds, a derivation can choose the raw declared type and transport, so step 3 is not shown necessary there (reading). `CompletionStrong.ofRefGet` compares two declarations and does need `subN`; its coarse twin `CompletionOk.ofRefGet` (`World.lean:81`) is not listed.<br>(b) The cell and deferred red controls use worlds today's programs cannot reach. No checker rule produces `refOf` or `deferredOf`; native cells are `handle "Ref.Ref<number>"` (`Program/Native.lean:90-99`). The reachable instance is the fiber arm (reading).<br>(c) "The root's final exit fits neither" is inaccurate. The exit fits `fiberOf T never` (`fits_fiber_raw`) and fails only the root's canonical type.<br>(d) "gap-fundamental" holds by the brief's test, twice: two stated obligations are false. The repair is small. |
| TY-02 | partly | `T_not_sub_normal` and `normal_sub_T` proved (rerun).<br>DI-15's clause (3) already restricts identity to canonical types: "On canonical types `CTy` mutual subtyping is equality of the representatives … every store key … is taken of the canonical form" (`docs/DESIGN-ISSUES.md:87`, reading). The raw-order identity sits in row 96 D1's `Equiv`, which is TY-01, not in DI-15.<br>Naming `subN` is still worth doing. The name should record that atom arguments are compared in raw `sub` (`Program/NativeAtom.lean:103-106`, `:129`, `:305`), while rows, services, the loop cursor and snapshots use `subN`. "The checker's order" is therefore two relations. That is harmless for `Fits`, because raw `sub` implies `subN`. |
| TY-03 | confirmed | Proved (rerun): soundness for both judgments, handle-free completeness, the three handle-former witnesses, `inhabited_sub`, and the DI-67 red controls; the guards hold (tested).<br>**Closed here.** Probe B sets `ty_handle := true` without a witness. `handle_inhabited` (proved, `verify-HandleInhabitedProbe.lean`) supplies one for every target: the four internal spellings and the external-allocation case.<br>**Still owed.** One world for several handles (amalgamation), and `inhabited (normalize t) = inhabited t`. The second follows from `inhabited_sub` and the members laws, because `normalize` only distributes products, flattens unions and drops raw-`sub`-below members (`Program/Ty.lean:565-628`, reading).<br>See TY-13 for what the new refusal may be called. |
| TY-04 | partly | `SigProgram`, `SigExtends` and `cata_congr_on` are not in `src/` or `Test/` (checked).<br>Reflection is not wholly unproved. R2Probe §E proves it on the Looped fragment: `hasTy_restrict_looped` under `AgreeOnLooped`, a hand induction (`docs/research/2026-09-30-model-probe/TREE/R2Probe.lean:369-430`, reading). `SigProgram` is that premise generalised; the system map's R2 row ("reflection open") omits the fragment too.<br>The fold-congruence route is sound in principle, because the checker is one fold (`Program/Checker.lean:1-30`, reading). |
| TY-05 | partly | `LawfulSig` is absent (checked). Admission checks the whole table (`Program/Admission.lean:131-170`), and revocation under an append is tested by the pedigree verifier (`pedigree/VerifyAdmission.lean:52-65`, reading). The invented key `.duplicateKey ("", [])` is at `Admission.lean:169`. `Table.lawful` and `Table.checkLawful` are separate definitions with no agreement theorem (`Program/Table.lean:70-97`), so that arm is unreachable in fact but not proved so (reading).<br>"C6 then follows from `List.forall_append` and `List.pairwise_append`" covers only per-entry and pairwise clauses. The proposed clause "every required key typed" points from rows to services and is neither. No such check exists today. It is monotone under append, so C6 needs one more easy lemma. |
| TY-06 | partly | That C1 is the identity for Σ_app is consistent with row 111 and audit §4 (reading).<br>**Wrong literature term.** Adding a constructor to an existing sort adds new elements to that sort. The reduct of the new initial algebra is therefore not isomorphic to the old algebra, and the extension is not "persistent" in Ehrig and Mahr's sense (1985, by name). It is hierarchy-consistent (no confusion: the old term algebra embeds) but not sufficiently complete (new terms in old sorts). The missing completeness is exactly why functions with catch-all arms can change.<br>**Overstated.** "Can only be a finite gate" is too strong. The note itself says a theorem form exists that keeps copies of the old functions; DI-47's gate is the chosen form, not the only one. |
| TY-07 | confirmed | Reading: `evalTerm` appears nowhere under `Laws/Program/Typed/` (checked). The coarse twin is `evalTerm_hasTy` and `evalTerms_hasTy` (`Laws/Program/Typed.lean:971-1015`). `projectProduct` joins (`Program/NativeAtom.lean:47-56`). `fitsN_join_left/right` (proved here) unblock the `fst`/`snd` case once TY-01 lands. |
| TY-08 | confirmed | Reading: `WorldValid.cells` reads the coarse `HeapCell`, `PromiseCell` and `CompletionOk` (`Laws/Program/Typed/World.lean:68-102`; `Validity.lean:30`). `preds.HeapCell` and `preds.PromiseCell` read `Fits` (`Assembly.lean:57-62`). The deferred table has the same pair, and the merge should cover it as well. |
| TY-09 | confirmed | Tested (rerun): V1a, `ofSchema groupedInt = some .int`; V2, two images decode to one value. The normalisers are not functions in the tree (reading). The guard route must use `N_J` and `N_S`, not `id`: see TY-18. |
| TY-10 | partly | Most of the four items restate ruled design:<br>- canonical-order membership is in row 119's text;<br>- "the canonical name lists are equal" is R3.3 (data synthesis line 291);<br>- the shared field-order normaliser is design (b1) (line 513: "a named field-order normaliser on the arrows that carry order").<br>Probe E's red control (`raw_not_invariant`, proved, rerun, model) models a written-order `sub` that R3.3 already rejects.<br>New content: `record_sub_not_complete`, and `inhabited`'s record arm (conjunction). These are acceptance items (tidiness), not rigor. |
| TY-11 | confirmed | Reading: `admitAnswer` (`Program/Admit.lean:59-75`). `externalValue` requires an empty handle list (`Program/Compile.lean:1371-1382`). A handle-free value has empty `keys` (`Val.keys` is `Store.Val.handles` filtered, `Laws/Machine/Handles.lean:119-131`), so the `unknown` arm closes by `live_of_keys_nil`. The context exception and row 97's refusal are as stated. |
| TY-12 | partly | The cited `R2Probe.lean:530-545` is an `example : True` with three `#guard`s (tested there), not the theorem. The proved `typedProg_not_table_monotone` is in `TREE/verify-Probe.lean` and in the audit's `probes/VerifyTreeCurrent.lean:97-106` (`[propext, Quot.sound]` in `logs/verify-tree-current.log`, reading).<br>A component-level positive control already exists, `pointTyped_rows_append` (`R2Probe.lean:517-522`). The `TypedProg`-level control is absent, as the seat says. |
| TY-13 | partly | Tested (rerun): `admitColumn` admits `list int`, which `findInt` refuses.<br>**The name is frozen.** `Test/contracts/foundation-wave2.contract.md:217-219`: `int` "is refused only at program/table admission with `AdmitRefusal.uninhabited (at : Path)`". DI-67's ruling says the same (`docs/DESIGN-ISSUES.md:139`).<br>The refusal's path points at the `int` occurrence, which is itself empty, so the name fits what it points at.<br>**Smallest amendment.** Keep the frozen name and give the new emptiness refusal its own, for example `emptyColumn at`. A rename needs an owner ruling and a contract revision. |
| TY-14 | confirmed | Proved (rerun): `inhabited_of_hasTy`, `inhabited_of_fits`. Both wordings checked: `DESIGN-ISSUES.md:139` and contract line 217. The complete direction in DI-67's `Val.hasTy` wording is not proved by probe B; it is owed. |
| TY-15 | confirmed | Proved (rerun): `k1`, `k2`. The tree itself already kernel-evaluates the checker: `Test/Program/LoadedAdmission.lean:85-86` (`generator_checks`) and `Test/Counterexamples/Machine/Semantics/ValueMembership.lean:839` (`refProg_checks`). The comment at `Laws/Program/Template.lean:332-333` is contradicted inside the tree. |
| TY-16 | confirmed | Proved (rerun, twice: probe D and `verify-CapstoneProbe.lean`): `fiber_inv`. It is absent from the tree (checked).<br>The generic precedent is `Typed.inr_inv` (`Laws/Effects/Protocol.lean:116-125`), whose docstring says it "is what every operation arm of the step lemma starts from".<br>"Every typed-state counterexample needs one" is overstated: `E4-TYPED-CE-004`'s witness uses `store_inv`. |
| TY-17 | partly | Proved (rerun): `subN_trans`, `sub_le_subN`, `subN_equiv_iff`, `ofRaw_eq_iff`, `T_not_sub_normal`, `normal_sub_T`, `T_subN_equiv`. `subN_refl` compiles, but its axioms are not printed. The tree laws are at the cited lines (`Laws/Program/TypeAlgebra.lean:1035-1121`, reading).<br>**Unsupported: "no meets (no intersection types), so not a lattice".** Having no intersection former does not mean greatest lower bounds are missing:<br>- `never` is the bottom and `join` the least upper bound, so the common lower bounds of two types are closed under `join`;<br>- on canonical forms the order compares members, and the meet of two members can be built by structure;<br>- for example, the meet of `nat \| string` and `nat \| bool` is `nat`; for two products it is the normalized product of the meets.<br>So `CTy` appears to be a bounded lattice whose meet is a function, not a type former (reading: an argument, not a proof). TAPL §16.3 (by name) expects meets once there is a bottom type.<br>The "two joins" part is confirmed (`Program/Ty.lean:496-528`). |
| TY-18 | partly | Proved (rerun): the generic `readExact_*`, `decodeExact_*`, `ofSchemaExact_*`. The literature mapping is right (by name): Rendel and Ostermann's partial isomorphism, the two prism laws, lens get. It matches K2 laws (b) and (c) when the read is invariant under N.<br>**Both proved instances are at `N = id`**, not at the named `N_J` and `N_S` (tested, `verify-ExactNormaliserProbe.lean`):<br>- the guarded decode refuses a key-permuted image that today's decoder accepts, and that the frozen contract requires it to accept ("Object field order is immaterial", `Test/contracts/schema-codec.contract.md:26`);<br>- the guarded schema read refuses an annotated `nat` image that `ofSchema` reads back exactly;<br>- with a key-order normaliser in place of `id`, the guard keeps the permuted image and still refuses V2.<br>The premise of `readExact_iff` (the read is invariant under N) is unproved for both normalisers. |
| TY-19 | partly | The laws listed as present exist (checked: `fits_mono` :829, `fits_map` :729, `fits_sub` :837, `fits_hasTy` :269, `fits_live` :520, `flatFits_fits` :229, `fits_list_iff` :999, `fold_of` :248).<br>**Three literature corrections:**<br>(a) "`TypedProg` is de Vilhena's `Typed o Ψ w Q p` specialised" contradicts the model-probe synthesis §3.1, level 0 (read): since the slice-5 ruling the concrete judgment is its own inductive. It has four control-marker arms that the generic `Typed` (`Laws/Effects/Protocol.lean`) lacks, and shares only the protocol shape.<br>(b) Without a function type there is no arrow clause, so "logical relation" is loose. The matching object is the value interpretation `V⟦τ⟧(W)` of a Kripke model for references: a predicate per type, indexed by worlds and monotone in them (Ahmed 2004; Ahmed, Dreyer, Rossberg 2009; by name). In those models the reference case compares a declaration by its interpretation, which is the principle TY-01 restores.<br>(c) No step-indexing is needed because worlds hold syntactic types that the handle arms read as declarations (TAPL ch. 13, by name), so the world is not defined through `Fits`. "No function or recursive types" is not the reason that matters. |
| TY-20 | confirmed | Reading: consistent with rows 111–116 (read in `docs/core/decisions.md`) and with audit §4. The definitions are absent from the tree (checked). Two refinements: C3 has a proved fragment (TY-04), and C6 needs a third clause shape (TY-05). |
| TY-21 | partly | Proved (rerun, model): `fitsN_normalize`, `fitsN_mono`, `normalize_idem`, `raw_not_invariant`.<br>The claim counts "normalization invariance with the canonical-order read" among the laws `Fits` has today. `Fits` does not have it today (TY-01), and the model proves it only with the amended handle arm. The literature mapping is fine (TAPL §15.2, §15.6; lens get; row polymorphism; by name). |
| TY-22 | confirmed | Reading:<br>- `Program/Admit.lean:15-89`: `mintedIn`, `admitAnswer`, and `notExternal` when `externalRow` answers `none`;<br>- `Program/Compile.lean:1371-1382`;<br>- `World.leHost` includes `Extends` on the allocation table (`Laws/Program/Typed/Validity.lean:38-39`).<br>I looked for a mismatch at the boundary and found none. `nativeSignature.rowOf` is the normalized row view (`Program/Native.lean:314-320`), the same view as `externalRow` and the frozen S4a clause (`foundation-wave2.contract.md:40-41`). The protocol entry and the reply check read the same columns. |
| TY-23 | confirmed | Reading:<br>- `sub` terminates by `sizeOf a + sizeOf b` (`Program/Ty.lean:456`);<br>- the antichain makes a quadratic number of `sub` calls (`normalizeRow`, `Ty.lean:590-592`);<br>- inhabitance is a fold (probe B);<br>- records are factors under row 119 (d).<br>Amadio and Cardelli 1993 and TATA: by name. |

## 2. What the seat missed

1. **The capstone is refuted by the same program** (proved, `verify-CapstoneProbe.lean`).
   - `RReachable` is `∃ tape, … ∧ m = (replayR root.program fuel tape).machine`
     (`Laws/Program/Typed/Assembly.lean:81-82`).
   - `replayEval` on `[]` returns the loaded machine (`Machine/Fibers.lean:2188-2194`), and
     `ReplayResult.machine` projects it (`Laws/Machine/Approximation.lean:731-735`).
   - So `capstone_implies_load`: the capstone's statement implies M5's at
     `compileFuel = fuel`. Every M5 refutation at equal fuels refutes the capstone, and
     `capstone_false` is the seat's program.
   - The capstone's docstring already lists host-free refutations (`E4-PROV-CE-006`,
     `E4-SCHED-CE-016`). This one is independent of layers and queues, and it happens at the
     loaded state.
2. **The amendment's central lemma, proved** (`verify-AmendedFitsProbe.lean`). This turns the
   seat's step 2 from reading into a proof on a faithful copy.
   - `FitsN` is the tree's `Fits` with the three arms in `subN`. It reuses `HandleFits`,
     `ServicesFit`, `Live` and `CauseFits` unchanged; any type whose normal form is `nat` is
     raw-equivalent to `nat`, so the native spellings are unaffected.
   - Proved on it: `fitsN_live`, `fitsN_sub` (raw), `fitsN_normalize`, `fitsN_subN`,
     `fitsN_join_left/right`, and `amended_join_holds` (the M5 leaf through the join).
   - Monotonicity in the world is not affected (the arms read the same lookups; reading, not
     re-proved).
3. **Pedigree and ruled text the repair re-reads.** TY-01 is what remains of an earlier repair
   (all reading):
   - the membership note's F3 and §7 D1 (`docs/research/2026-09-30-pass/membership/note.md:185`,
     `:392`) chose `Equiv` to keep subsumption across re-spellings. They noted that "on normal
     forms the two agree", but not that the checker compares and joins after normalizing;
   - the pass synthesis's K9 (`docs/research/2026-09-30-pass/synthesis.md:380`);
   - row 96's D1, as ruled;
   - `E4-TYPED-CE-006`'s forced repair, "D1 uses subtyping both ways (Equiv)"
     (`Test/Counterexamples/REGISTER.md:201`);
   - host-boundary §4.4's table: "exactly the declared type" and "a subtype".

   All of these need the same one-line clarification: the order is `subN`, and "exactly"
   means equal normal forms. That is an owner ruling.
4. **Counterexample IDs.** The proofs seat proposes `E4-TYPED-CE-009` for `StaleCode`
   (`proofs/note.md:330`, `:595`), and the seat proposes the same ID. The live register stops at
   `E4-TYPED-CE-006`. `-007` is cited as registered (row 107, system map R9) but is in neither
   register, and `-008` is proposed under row 117. The coordinator must allocate the IDs.
5. **Probe C's guard as written breaks a frozen contract** (tested, TY-18). If stage 1 takes
   "probe C's guard" literally, it refuses key-permuted host JSON.
6. **TY-13's rename conflicts with a frozen contract**, `foundation-wave2.contract.md:217-219`,
   and with DI-67's ruling.
7. **Reflection already holds on the Looped fragment**: R2Probe §E (TY-04).
8. **The checker uses raw `sub` at atom arguments** (`Program/NativeAtom.lean:103-106`, `:129`,
   `:305`), while DI-15 makes subsumption apply there too. This is harmless for `Fits`, but it
   belongs in TY-02's naming.
9. **Only the fiber arm is live today.** Cells and deferreds are `handle` spellings with `nat`
   declarations (`Program/Native.lean:90-99`). TY-01's cell and deferred arms matter when
   generic cells land (R4 steps 3–5).
10. **A ready route for the positive control.** `typedStateF_load`
    (`Test/Counterexamples/Machine/Semantics/ValueMembership.lean:984`) already reduces M5 to
    "the loaded code is typed at every world". Under the amendment, the seat's "probe D must flip
    to a typed load" reduces to one `TypedProg` derivation for `prog3`. That derivation is owed;
    only the leaf is proved.
11. **Four literature corrections:** "persistent" (TY-06), "not a lattice" (TY-17), `TypedProg`
    as the generic `Typed` specialised, and the reason no step-indexing is needed (TY-19).
12. **TY-21 counts a law `Fits` does not have today**, and **TY-10 restates** row 119, R3.3 and
    the data synthesis's (b1).

## 3. Formal notions against the literature

| Seat's notion | Literature definition it should match | Verdict |
| --- | --- | --- |
| `Ty` as the free term algebra; `cata_ty` as its unique homomorphism | initial algebra of a signature (Goguen, Thatcher, Wagner, Wright 1977; by name) | matches |
| `(Ty, sub)` a preorder; its quotient by `subN` is `CTy` | the kernel of a preorder (two types identified when each is below the other) and its quotient poset; standard | matches (proved) |
| `CTy` a bounded join-semilattice, "no meets, so not a lattice" | a partial order with all finite joins; a lattice when meets also exist (TAPL §16.3, by name) | first half matches; second half unsupported (TY-17) |
| `sub` as algorithmic subtyping with union rules | TAPL ch. 15–16; Pierce 1991; Dunfield 2014 (by name) | matches |
| `Fits` as a Kripke unary logical relation | the value interpretation `V⟦τ⟧(W)` of a Kripke model for references, monotone in `W` (Ahmed 2004; by name) | loose: no arrow clause; the named object fits (TY-19) |
| `TypedProg` as de Vilhena's `Typed` specialised | de Vilhena 2022, protocols (read by the model-probe pedigree) | no: its own inductive since slice 5 (model-probe synthesis §3.1, level 0) |
| Σ_core growth as a persistent extension | persistency: the reduct of the free extension is isomorphic to the original (Ehrig and Mahr 1985; by name) | no: hierarchy-consistent, not sufficiently complete (TY-06) |
| K2 as a partial isomorphism or lawful prism up to N | Rendel and Ostermann 2010; the two prism laws (Pickering, Gibbons, Wu 2017; by name) | matches, given that the read is invariant under N |
| width as a boundary coercion, the get of a lens | TAPL §15.6; Foster et al. 2007 (by name) | matches |
| the minted-handle invariant as store well-formedness and capability safety | TAPL ch. 13 (store typing); Devriese, Birkedal, Piessens 2016 (by name) | matches |
| C3 by fold congruence | uniqueness of a fold: algebras that agree on a term's nodes give the same fold (Meijer, Fokkinga, Paterson 1991; by name) | matches |
| recursive types: subtyping as a greatest and inhabitance as a least fixed point | Amadio and Cardelli 1993; TATA (by name) | matches (row 124, future) |

## 4. My probes

Every probe compiled with
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs path>`, one at a
time. Each final log ends `exit=0`, and each has no axiom beyond `[propext, Quot.sound]`.

| Probe | What it settles | Runs | Axioms (final log) |
| --- | --- | --- | --- |
| `verify-CapstoneProbe.lean` (`15b67199…`) | §1 re-proves the seat's probe D (copied, so the file stands alone): `m5_false`. §2 is new: `replayR_nil_machine`, `rreachable_load`, `capstone_implies_load`, `capstone_false` | runs 1 and 2: `nomatch h, x` parsed as two match targets, in two spellings (the dependent theorems fell back to sorry; no claim taken); final: `verify-CapstoneProbe.log` | all five `[propext, Quot.sound]` |
| `verify-AmendedFitsProbe.lean` (`5401cde6…`) | `FitsN` (TY-01's amendment on a copy of `Fits`): `fitsN_live`, `fitsN_sub`, `fitsN_normalizeRow`, `fitsN_productMembers`, `fitsN_normalize`, `fitsN_subN`, `fitsN_join_left/right`, `amended_join_holds`; red control `tree_join_fails` | run 1: the same `nomatch` parse in `fitsN_members`'s `never` case (later lemmas fell back to sorry; no claim taken); final: `verify-AmendedFitsProbe.log` (= `.run2.log`) | all ten `[propext, Quot.sound]` |
| `verify-HandleInhabitedProbe.lean` (`c4f7a744…`) | `handle_inhabited`: every `handle t` has a member in some world, by the four internal spellings and an external allocation | run 1: a `decide` on a goal with a free variable and an unsolved implicit (no claim taken); final: `verify-HandleInhabitedProbe.log` | all six `[propext, Quot.sound]` |
| `verify-ExactNormaliserProbe.lean` (`cd84463b…`) | tested: today's decoder accepts a key-permuted image; probe C's guard at `id` refuses it, at the overlap type and at a plain `except`; a key-order guard keeps it and refuses V2; `ofSchema` reads an annotated `nat` image that the guard at `id` refuses | final: `verify-ExactNormaliserProbe.log` (= `.run1.log`), every `#guard` holds | no theorems (guards only) |

## 5. Reruns of the seat's probes

Each probe compiled once through the lock; logs are named `verify-rerun-<Probe>.log`.

| Probe | Exit | Axiom lines identical to the seat's `.log` |
| --- | --- | --- |
| `M5CounterProbe.lean` | 0 | yes (7) |
| `TypesOrderProbe.lean` | 0 | yes (23) |
| `InhabitedProbe.lean` | 0 | yes (15) |
| `ExactByImageProbe.lean` | 0 | yes (9) |
| `KernelEvalProbe.lean` | 0 | yes (3) |
| `RecordWorldProbe.lean` | 0 | yes (6) |

Every `#guard` in those files held, since a failing guard is an error and every exit is 0
(tested).

## 6. Receipt

- **Base and head.** `ea5b28b5` on `refactor/phase1-phase3`, both. Nothing committed.
- **Files written** (this folder only):
  - `verify.md`;
  - `verify-CapstoneProbe.lean`, its `.log` and `.run1.log`/`.run2.log`;
  - `verify-AmendedFitsProbe.lean`, its `.log` and `.run1.log`/`.run2.log`;
  - `verify-HandleInhabitedProbe.lean`, its `.log` and `.run1.log`;
  - `verify-ExactNormaliserProbe.lean`, its `.log` and `.run1.log`;
  - six `verify-rerun-*.log`.
- **Read in full or at cited lines.**
  - The seat's `note.md` and six probes.
  - `AGENTS.md`; `docs/core/system-map.md` §5 and §8; `docs/core/decisions.md` rows 96 and
    111–133; `docs/core/host-boundary.md` §4.4–4.5.
  - `docs/DESIGN-ISSUES.md` DI-15 and DI-67; `docs/DESIGN-BASIS.md` DB-01.
  - The frozen contracts `foundation-wave2` and `schema-codec`;
    `Test/Counterexamples/REGISTER.md`.
  - Model-probe synthesis §2.2 and §3.1; audit §4; pass synthesis K5–K10; the membership note's
    F3 and §7.
  - Data synthesis: lines 15–30, 285–291, 495–525.
  - `R2Probe.lean` §A–F and its `VerifyTreeCurrent` rerun; `pedigree/VerifyAdmission.lean`.
  - `proofs/note.md` (head, G3–G4, line 595); `organization/note.md` line 456.
  - Every `file:line` cited above.
- **Not done, and why.**
  - No owner-level change, and no edit to the seat's files.
  - I did not prove that `CTy` has meets (TY-17 is an argument).
  - I did not build the amended `TypedProg` derivation for `prog3`; the positive M5 control is
    owed.
  - I did not prove `fitsN_mono`; it is reading.
