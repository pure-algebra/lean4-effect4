# Effect Core v1 — EC1-S1 slice verdict

Coordinator close of slice `EC1-S1` (foundation bundle: `T001–T009` including
`T003E`, `T004S`, `T004X`, `T004RW`). Three phases ran: 13 scouts, 13
implementers, 13 breakers. This report is written from my own reruns, not from
the phase reports — three lanes misreported receipt counts, so nothing here is
taken on report.

**Verdict: the EC1-S1 gate is NOT met. Zero of nine exit conditions are fully
discharged; two are partially discharged at statement level only. No row in the
slice is closed, because no declaration in the slice exists.**

---

## 0. The finding that settles the slice

All 58 `.lean` files under `formal/effect-core-v1/` contain **zero
declarations**.

```
$ find formal/effect-core-v1 -name '*.lean' | wc -l
58
$ grep -rlE '^(theorem|def|structure|inductive|abbrev|instance|class) ' \
    formal/effect-core-v1 --include='*.lean' | wc -l
0
```

Every carrier the slice's nine rows quantify over is absent from the tree:

| Carrier | DAG id | Hits in `library/cas/Cas` + `tools` + `formal` |
| --- | --- | --- |
| `ValueTy`, `Value` | `EC1-D001/D002` | 0 |
| `ErrorRow`, `RequirementRow` | `EC1-D003/D004` | 0 |
| `PublicSurface`, `SurfaceRowKey`, `SurfaceDisposition` | `EC1-D006/D007/D008` | 0 (3 stub-docstring/import lines only) |
| `Alphabet`, `OpDesc` | `EC1-D010/D011` | 0 (3 stub-docstring/import lines only) |
| `PureExpr`, `PureDenotes`, `EnvWF` | `EC1-D012/D013` | 0 |
| `RawProgram`, `normalizeRaw`, `normalizeRow` | `EC1-D020/D026` | 0 |
| `SerializableField`, `FunctionVal`, `alphaEq` | — never proposed anywhere | 0 |

Consequence: **all thirteen implementer files declare their own carrier and
prove about that.** Thirteen green elaborations are thirteen statement-shape
results. Not one closes a proof-DAG row.

`PROOF-DAG.md:499` makes the cutover condition explicit — *"every required type
row closes its constructor/checker/semantics/classifier/lowering/red-control
edges before cutover."* Zero constructor edges are closed. `EC1-F80` ("mark a
slice cutover while one required type row has an open edge") fires on any
cutover claim for this slice. Freeze conditions **1, 3, 8, 13, 14** are all
**OPEN** and every one of them gates a row in this bundle.

All eleven S1 exit falsifiers (`F01–F03`, `F08`, `F20`, `F59`, `F60`, `F80`,
`F82`, `F86`, `F87`) remain `PENDING FALSIFIER` in `CONTRACT-PACKET.md`. None
was promoted by this slice.

---

## 1. Rerun — all 26 files, verified by me

Command form: `cd /Users/pooks/Dev/foldlab/library/cas && lake env lean <ABS-PATH>`

| Row | exit | receipts | axiom-free | w/ `Classical.choice` | errors | warnings | `sorryAx` | attack receipts |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `T001`   | 0 | 41 | 3 | 32 | 0 | 0 | 0 | 17 |
| `T002`   | 0 | 50 | 3 | 41 | 0 | 0 | 0 | 47 |
| `T003`   | 0 | 28 | 13 | 0 | 0 | 0 | 0 | 15 |
| `T003E`  | 0 | 19 | 3 | 12 | 0 | 0 | 0 | 23 |
| `T004`   | 0 | 27 | 7 | 0 | 0 | 0 | 0 | 27 |
| `T004RW` | 0 | 42 | 8 | 0 | 0 | 0 | 0 | 29 |
| `T004S`  | 0 | 39 | 12 | 16 | 0 | 0 | 0 | 27 |
| `T004X`  | 0 | 33 | 18 | 0 | 0 | 0 | 0 | 35 |
| `T005`   | 0 | 33 | 13 | 0 | 0 | 0 | 0 | 26 |
| `T006`   | 0 | 42 | 8 | 0 | 0 | 0 | 0 | 60 |
| `T007`   | 0 | 47 | 15 | 0 | 0 | 0 | 0 | 52 |
| `T008`   | 0 | 63 | 22 | 0 | 0 | 0 | 0 | 36 |
| `T009`   | 0 | 81* | 4 | 14 | 0 | 0 | 0 | 31 |

\* 77 own receipts + 4 deliberate upstream isolation prints.

**Totals: 26/26 files exit 0. 970 receipt lines; 966 own-theorem receipts.
221 axiom-free, 547 at `[propext]`/`[propext, Quot.sound]`, 202 carrying
`Classical.choice`. Zero `sorryAx` anywhere. Zero errors, zero warnings.**

`Classical.choice` appears in exactly five files and every occurrence is
inherited, not chosen:

- `T001`, `T002` — Lean core's `String` `LE`/`Decidable` instances inside the
  key comparator. (`T002`'s own attribution is *wrong in mechanism* — see
  finding M18 — but the ceiling is right.)
- `T003E`, `T004S` — `Cas.Schema.Ast.WF`, compiled by well-founded recursion.
  This is the estate's own ceiling: shipped `Cas.Schema.Described.decode_encode`
  reports the identical triple.
- `T009` — `nodup_length_le`, through core `List.length_erase_of_mem`. Also the
  estate's ceiling: `Cas.Schema.references_guarded_decidable` reports the same.

Eight files reach it not at all. This is the cleanest axis in the slice.

### Receipt discipline — audited, not accepted

```
$ comm -23 <(declared theorem names) <(receipted names)   # per file
```

Twelve of thirteen files are exactly one-to-one. **`T007` is not**: it declares
51 theorems and prints 47 receipts. `add_cancel_succ`, `lt_self_absurd`,
`normalizeRaw_def` and `shift_absurd` have no `#print axioms` line, against the
file's own claim at `T007.lean:807` ("`#print axioms` on every theorem"). All
four are used downstream so their dependencies do reach printed receipts
transitively; this is bookkeeping, not trust. Three of the four are nonetheless
named in `T007`'s reported theorem list.

I also checked and **cleared** the two files earlier flagged: `T004` and
`T004S`'s apparent gaps are line-wrapped docstring false positives. `T009`'s
apparent surplus is its four deliberate isolation prints.

### Forbidden tokens

`grep` over all thirteen files for `sorry` / `axiom` / `native_decide` /
`#eval` / `unsafe` / `partial def` / `set_option` returns **prose only**, with
one exception: `T004S.lean:72` carries
`set_option warn.classDefReducibility false` — a linter warning switch with no
semantic effect.

### Reuse, never mint — clean

```
$ grep -nE '^(structure|inductive|abbrev|def) (Sig|Prog|Handler|PProg|Refusal|Status|Word|Envelope|Ast|El|Described)\b' T0*.lean attack-T0*.lean
(no output)
```

No second signature, program carrier, handler, refusal family, schema universe
or CAS serializer was minted in 26 files. Only `T004RW` and `T004X` work inside
`Prog`/`Sig` at all, and both are rows that legitimately should. R14a holds
throughout: every other row is effect-free work on first-order data outside
`Prog`. R1 is untouched — no coinduction anywhere.

---

## 2. Gate assessment — nine conditions from `PLAN.md:299`

| # | Exit obligation | Verdict |
| --- | --- | --- |
| 1 | Module/export/member/overload closure | **NOT MET** |
| 2 | Disposition totality | **PARTIAL** (statement only) |
| 3 | Source-to-alphabet mapping | **NOT MET** |
| 4 | `El` overlap/insufficiency ledger | **NOT MET** |
| 5 | `Sig.sum` extension reuse | **PARTIAL** |
| 6 | Duplicate-free row premises | **PARTIAL** |
| 7 | No duplicate sequential body | **MET, by inspection not by theorem** |
| 8 | Decidable equality/serialization | **PARTIAL** |
| 9 | Malformed witnesses banked | **PARTIAL** (banked in Lean, unregistered) |

**1. Module/export/member/overload closure — NOT MET.** `EC1-H11` is
`PENDING HARNESS`. `formal/effect-core-v1/EffectCore/Generated/` does not exist.
No generated ledger exists in any Lean-consumable form, so `covers` and
`keysNodup` — facts *about generated data* — are discharged against nothing.
Worse, this is proved independent of the slice's work: `AttackT008`'s
`wf_does_not_imply_census_completeness` and `AttackT009`'s `F59_passes_through`
(both kernel-checked) show a ledger silently omitting
`effect/unstable/http/MultipartParser/HeadersParser` passes every theorem and
every checker the slice produced. `EC1-CE020` (`VERIFIED-TOOL`) is the live
counterexample and no row addresses it.

**2. Disposition totality — PARTIAL, statement level only.** `T008` is the
strongest single file in the slice. It proves the DAG row
(`PROOF-DAG.md:200`) is *provably equivalent to `True`* — confirmed
independently, axiom-free, as `AttackT008.the_dag_row_is_equivalent_to_True` —
and replaces it with `surface_disposition_exact` plus a two-sided decider
`checkSurface_ok_iff`, all three premises proved load-bearing, generic over any
`{κ : Type} [DecidableEq κ]`, rejecting all three `EC1-F60`/`EC1-K07` mutants by
name. I cross-checked the decider against an independent reference over a
mixed ten-ledger battery and found no disagreement. But: **neither
`PublicSurfaceWF` nor `checkSurface` decides `s.keys.Nodup`**, so a ledger whose
public universe lists one module twice is accepted
(`AttackT008.dupKeys_passes_wf_and_the_checker`) — that is `CONTRACT-PACKET.md:213`'s
failed-alias-collapse, and it is `EC1-F60`'s duplicate half landing on the very
instrument built to catch it. And there is no data to run it on.

**3. Source-to-alphabet mapping — NOT MET.** `Alphabet`, `OpDesc`, `lookup`,
`toSig` do not exist; freeze conditions 3 and 14 are OPEN, and the §17 rulings
report records condition 14 as *"no evidence"*. All four alphabet rows
(`T004`, `T004S`, `T004X`, `T004RW`) worked on locally declared stand-ins that
**disagree with each other about `lookup`'s codomain**: `T004` needs
`Option OpDesc`, `T004S` projects a `.answerTy` field, `EC1-D011` declares a
dependent type family with no lookup at all. `T004X` proves the mapping row is
`rfl` under one carrier reading and *false* under the other, so landing a
carrier does not make it provable — it decides which of two failures it is.

**4. `El` overlap/insufficiency ledger — NOT MET.**

```
$ grep -c "Schema" .staging/effect-core-v1/EXISTING-TYPES.md
0
```

`EXISTING-TYPES.md` has **zero rows for the entire `Cas.Schema.*` plane** — no
`Ast`, no `El`, no `Described`, no `Codec`. `EC1-F86`'s stated consequence
("Existing-type/bridge gate demands the `El` equivalence") names a gate with
nothing in it. Freeze condition 13 is OPEN. And `T003E`'s proposed insufficiency
boundary is **wrong on both of its excluded arms** — `Option α` and `Nat` are
each exactly representable in the shipped schema universe
(`AttackT003E.both_excluded_arms_are_representable`, kernel-checked), so the one
file that offered a route for condition 13 puts both boundary points on the
wrong side.

**5. `Sig.sum` extension reuse — PARTIAL, and the best real work in the slice.**
`T004X` proves the metadata/answer/identifier arm laws and shows the DAG's
signature equation is definitional; `T004RW` proves a genuine *uniqueness*
characterization of `stepWorded` — any function satisfying its equation set IS
`stepWorded` — and exercises `EC1-F87` mechanically rather than by inspection.
Six independent counter-models across the two files each satisfy the DAG row's
named dependencies verbatim and are still wrong. Against that: `T004RW` covers
only the worded tower and **never touches `stepRooted`/`StoreSig`, the row's
first named subject** (`stepRooted_cas_agrees` appears once in the file, inside
the quotation of the row itself); and `T004X`'s truth is decided by an OPEN
freeze condition.

**6. Duplicate-free row premises — PARTIAL, second-best in the slice.**
`T001`+`T002` deliver this genuinely: `normRow_perm_of_nodup_keys`,
`normalizeRow_canonical` with **both** premises proved load-bearing for
*opposite directions*, and the four `Canon.lean` preservation laws instantiated
at both packet carriers. The breaker then closed the one gap the implementer
declared unclosable: `AttackT002.normRow_eq_canonServices` proves the generic
construction **equals** the shipped `Cas.Backend.canonServices`, so the pin is
real, not same-laws hand-waving. Against that: under both premises the last-wins
dedup step is *provably inert*, so the row cannot distinguish last-wins from
first-wins normalization
(`AttackT002.row_bundle_minus_last_wins_does_not_pin_the_normalizer`) — the
last-wins discipline rests entirely on a law that is **not a DAG row**.

**7. No duplicate sequential body — MET, by inspection.** The mint check above
is clean across 26 files; block bodies are typed `PProg` and the shipped
`decodeProg_encodeProg` is instantiated rather than rewritten
(`EC1-XT018`, `EC1-F76` respected). But this is an inspection result, not a
theorem, and nothing in the slice would catch a future violation.

**8. Decidable equality/serialization — PARTIAL.** `T005` delivers choice-free
decidable equality of its field universe and whole raw carrier, an invertible
serialization walk, and injectivity. But the breaker proved the file's central
argument false: **invertibility does not mechanize first-orderness** — a carrier
with a genuinely function-valued field admits an equally perfect round trip
(`AttackT005.fnParse_fnFields`). The property that *does* separate them is
decidable equality, in a reduction form
(`AttackT005.decEq_fnField_decides_function_equality`, axiom-free) that `T005`
left as an unused elaboration observation.

**9. Malformed witnesses banked — PARTIAL.** The thirteen attack files bank a
large, kernel-checked adversary set. **None is registered.** They live only in
`.staging/effect-core-v1/workshop/s1/`, which `.gitignore:11` excludes, so the
bank is invisible to the packet and to every downstream slice. See §5.

---

## 3. Findings, ranked most severe first

### Blockers

**B1 — Zero declarations exist; the slice cannot cut over.** §0 above. Thirteen
green files, zero closed rows. Any cutover claim trips `EC1-F80`.
*Evidence:* `find`/`grep` in §0; `formal/effect-core-v1/EffectCore/Foundation/Alphabet.lean`
and siblings are 11-line docstring stubs; freeze conditions 1, 3, 8, 13, 14 OPEN.

**B2 — `EC1-T005` is UNDETERMINED, not vacuous, and the strike recommendation
rests on the wrong ground.** `T005` reports the row "proved verbatim and
necessarily vacuous", asserting `FunctionVal` "cannot honestly be written as
anything but the empty predicate". Over **one fixed field universe and one fixed
`SerializableField`**, two admissible readings exist — one proving the row, one
**refuting** it.
*Evidence:* `AttackT005.the_row_is_undetermined_not_vacuous`,
`row_is_false_at_the_payload_reading`, both `[propext]`.
`ALGEBRA.md:242-244` lists "dangling references" and "host-function payloads" as
*separate* deliberately-representable defects, so the packet does not identify
them the way `T005` §3 does. The strike recommendation may stand — but on
*unstatedness* (`EC1-D020` absent, field universe unfixed), never on a vacuity
the prover's own choice of predicate manufactured.

**B3 — `EC1-T004S`'s `REFUTED` disposition is wrong at packet scope.** The
refutation holds only on a carrier that **omits the descriptor clause
`ALGEBRA.md:134-135` specifies** (*"`OpDesc op` … proves that `answerTy` denotes
`Sig.Ans op`"*). On the specified carrier the row is a theorem: universally
quantified, premise-free, non-vacuous over the shipped `LlmSig` with the shipped
`Described String`. The licensing lemma offered for the transfer — "refuting the
most generous reading refutes every narrower one" — **runs backwards** for a
universal.
*Evidence:* `AttackT004S.spec_row_holds`, `spec_row_is_not_vacuous`,
`generosity_inference_is_invalid`, all kernel-checked.
**Correct disposition:** the DAG row belongs to the tautology family
`PROOF-DAG.md:203-206` already deleted twice, with the constructibility
obligation re-spelled as *data* on `OpDesc` pinned to `answerTy`. It is **not** a
counterexample-register row.

### Majors

**M1 — `T006`'s headline "EC1-F82 DISCHARGED" is false.** Its witness pair both
have `aliases = []`, so the alias stage never runs; the separation it proves is a
property of the alias-free fragment only. With a live alias map the normalizer
*identifies* a permuted duplicate-key raw pair — exactly the normalization
equivalence `CONTRACT-PACKET.md:320-323` forbids.
*Evidence:* `AttackT006.f82_is_not_discharged`, `[propext, Quot.sound]`.
`EC1-F82` is on this slice's exit list.

**M2 — `T006`'s adequacy bundle does not close the adequacy hole it claims to.**
All five preservation laws are stated relative to the already-resolved table and
**none constrains `entry`**. A second canonicalizer satisfies every §6 and §7 law
plus `EC1-T006` itself and **deletes the entry point** — `EC1-F01` in normalizer
form. The estate's own criterion (`Canon.lean:270-272`) is that the laws must
*determine* the normalizer; `T006`'s set does not.
*Evidence:* `AttackT006.section6_and_7_do_not_determine_normalizeRaw`.

**M3 — `T006`'s alias stage IS the red control it was introduced to discharge.**
`resolveRaw` is single-step, non-injective and not capture-avoiding: it resolves
a block *into a name another block already occupies*, manufacturing duplicate
keys from a duplicate-free program. `EC1-CE030`'s repair premise is therefore not
preserved across normalization and cannot be discharged upstream and reused
downstream. `TYPE-CLOSURE.md:121` lists "alias capture" as this row's red control.
*Evidence:* `AttackT006.normalizeRaw_manufactures_duplicate_keys`.

**M4 — `T009` discharges "closed" as "the profile list is non-empty".** In the
packet's own vocabulary it means admission predicates are *ordered, disjoint and
exhaustive* (`REIFICATION-CHECKLIST.md:1203`, invariant 8), and the model cannot
state that: `Profile` drops `predicateId`, `priority`, `acceptedForm`,
`rejectedFormCodes[]`. A total profile gap and an overlapping pair both pass.
`EC1-H11`'s profile-gap/overlap counters have no theorem behind them.

**M5 — `T009`'s conclusion is satisfied by a ledger in which nothing is
reified.** `Grounded`'s leaf set admits `refusal`, `target` and `pure`, so a
ledger refusing every effect-bearing row satisfies the row with zero constructive
mappings and zero handler ids; the empty ledger passes too. A green door is
silent about whether any effect reached Core.
*Evidence:* `AttackT009.allRefused_satisfies_the_row` + `allRefused_has_no_core_content`.

**M6 — `T009`'s `SurfaceRow` carries no `surfaceDisposition`.** The seven-way
disposition — the object `EC1-T008`/`EC1-D009` are about and the thing `EC1-F60`
mutates — is absent from the carrier. `EC1-F60`'s drop half is therefore **not
exercisable against this row at all**, and the `T009 → T008` DAG edge is neither
used nor dischargeable. `Profile.decision` is additionally a **dead field**:
declared, then used in no definition, clause or theorem, so a ledger in which
every decision contradicts its own mapping is admitted
(`AttackT009.decision_is_inert`).

**M7 — `T008`'s checker misses `keys.Nodup`.** Gate condition 2 above.

**M8 — `T005`'s repaired checker fails two S1-exit falsifiers and one nested
form of a third.** `EC1-F03`: a `codeTable` with two definitions sharing one
`CodeId` is accepted and slot resolution is ambiguous
(`AttackT005.dupProg_accepted`, `dupProg_resolution_is_ambiguous`). `EC1-F82`:
the verdict is invariant under permuting that table while the selected definition
changes. Nested `EC1-F08`: a callback reachable *through* a registered code body
passes `FirstOrderClosed`, which quantifies only over top-level slots
(`AttackT005.f08Nested_passes_the_target_predicate`). This directly invalidates
the recommendation to lift the §3 bundle verbatim into `EC1-D021 ProgramWF`.

**M9 — `T001`'s adequacy bundle is silent on payloads.** All four laws are
stated on the *tag*, transplanted from a service set. At the `ErrorRow` carrier
the bundle certifies tag preservation while permitting **deletion of a typed
failure arm** — a defect in the law set, not merely in the carrier reading.
*Evidence:* `AttackT001.atk_error_row_deletes_a_typed_arm`.

**M10 — `T001`'s claimed decidable-quotient payoff does not exist in the
kernel.** The `Decidable` instances resolve but `decide` gets stuck on
`mergeSort`'s well-founded recursion; with `native_decide` and `#eval` banned
there is no admissible route from instance to decision, so the checked carrier
has no computable guard. The estate's actual guard is a compiled `Bool`
(`EmitLayer.lean:225 isCanonServices`), which `T001` does not mirror.

**M11 — `T001`'s payload parameter admits function-valued payloads.** `V := Nat → Nat`
elaborates with no refusal and no diagnostic, so D0's "no function-valued
serialization field" obligation is unenforced. The parametricity sold as
generality is precisely what removes the guard.
*Evidence:* `AttackT001.atk_payload_may_be_function_valued`.

**M12 — `T003E`'s `≃` restatement is a genuine weakening, undisclosed.** Both
proved forms conclude with `Exists`, which lives in `Prop` and admits no large
elimination, so **neither can produce the transport function** the DAG's `≃`
denotes. Downstream `EC1-T004S` needs the data form to type answers. The file
argues the opposite. Cheap repair: state it `Σ`-valued — the proof is already
constructive, only its wrapper is not.

**M13 — `T003E`'s row content collapses to its carrier's own definition.** On
the supported fragment `Value τ` is definitionally `El ast`, and the row is
reprovable with **every shipped `Described` instance deleted*
(`AttackT003E.bridge_without_any_shipped_instance`). Partiality of `toAst?` is a
fact about the `none` arms and does not bear on where the conclusion lives.

**M14 — `T004`'s bridge is blind to the red control it is used to indict.**
`toSig` factors entirely through `lookup`, a lossy projection, so a forbidden
duplicate-op table and an admissible de-duplicated one produce **equal**
`toSig.Op`; `NodupOps` cannot be recovered downstream, and `Alphabet.toSig`
carries no precondition. Separately `NodupOps` is **not closed under join**, so
`EC1-T004X` cannot inherit this row's premise and the packet states no
key-disjointness side condition.
*Evidence:* `AttackT004.the_bridge_cannot_recover_the_red_control`,
`nodup_is_not_closed_under_join`.

**M15 — `T004RW`'s subsumption claim inverts the dependency it names.**
`since_cas_agrees` — the row's own named dependency — is an **input**
(hypothesis `hcasSt`) of the uniqueness theorem, and is proved load-bearing by a
counter-model satisfying everything else. The theorem sold as subsuming the
named dependencies subsumes one fact the dependency column does not name and
leaves the one it does as a premise.
*Evidence:* `EC1T004RWAttack.since_cas_agrees_is_load_bearing`.

**M16 — `T007`'s headline strengthening does not exist.** `Renames` (injective)
and `AlphaEq` (bijective) are the **same relation** at this carrier — every
injection is corrected to a bijection at the finitely many points
`applyRenaming` reads — so the row over one is inter-derivable with the row over
the other, *for every normalizer*.
*Evidence:* `AttackT007.renames_iff_alphaEq`, `row_over_renames_iff_row_over_alphaEq`.

**M17 — `T007`'s normalizer is a function of a presentation, not of the declared
carrier.** `ALGEBRA.md:235` declares `blockTable` a *finite map*; two duplicate-free
programs assigning the same block to every key get different normal forms and put
different free operation keys at the same canonical identifier. Under the map
reading `normalizeRaw` is not a function of the declared table at all. The stated
`EFFECTS-BACKEND` R4 justification is neutral between presentation-order and
reachability-order renumbering and its exemplar erases *more* presentation.
*Evidence:* `AttackT007.normalizeRaw_is_not_row_permutation_invariant`.

**M18 — grade inflation, five rows.** Each independently kernel-refuted:
`T001` PROVED-STRONGER (two of four "stronger" clauses fail — M9, M10);
`T004` ground (a) — `row_survives_any_premise` is **equivalent** to the DAG row,
not stronger, since `SerializableField` is inhabited at every field
(`AttackT005.strictly_stronger_is_actually_equivalent`);
`T004X` conjunct inflation — eight conjuncts are **six**, since two are functions
of the `sig` field alone (`AttackT004X.eight_conjuncts_are_six`);
`T004RW` — (B) and (A)-4 are derivable from their neighbours
(`guard_B_follows_from_C_publish`, `wf_conjunct_follows_from_state_conjunct`);
`T007` — M16.

**M19 — two packet ledgers have holes that make named gates empty.**
`EXISTING-TYPES.md` has zero `Cas.Schema.*` rows, so `EC1-F86`'s gate is empty
(§2 condition 4). And `Cas.Canonicalizer` — the ratified abstraction whose
`canon_idem` field **is `EC1-T001` verbatim** — appears in **no packet `.md` at
all** (`grep -rc Canonicalizer *.md` → no non-zero file), so the reuse ledger has
no row for it and `PROOF-DAG.md` §16's fifteen family rows contain no
rows/normalization family. `T001`, `T002` and `T006` all route through it with
neither a named primary route nor a named prohibited shortcut.

**M20 — `EC1-T007` is dispatched in a slice whose declaration budget lacks its
terms.** `EC1-S1` is "D0–D1"; `EC1-T007` is about `EC1-D020`/`EC1-D026`, both D2.
`EC1-T005` has the same defect and, unlike `T006`/`T007`, is re-listed in **no**
later slice. This is a ledger defect that forced the carrier invention above,
not an agent choice.

**M21 — `T003`'s premise refutation does not carry the deletion it is cited
for.** `no_unary_env_premise_totalises` proves only *non-totality*, with its
`EnvWF` binder unused; non-totality does not obstruct the adequacy iff, and the
premised row is inhabited under an arbitrary unary predicate
(`AttackT003.premised_row_is_inhabited_under_every_unary_predicate`). The
deletion still stands — it is forced by the intrinsic carrier, not by §2. `T003`
is additionally **blind to the scalar primitives**: an equality primitive
answering `true` on `1 = 2` passes full two-sided adequacy
(`AttackT003.the_row_is_blind_to_the_scalar_primitive`).

**M22 — `T002` is blind to the dedup discipline.** Gate condition 6 above.

### Minors

**m1** — `T007` receipt discipline: 51 theorems, 47 receipts (§1).
**m2** — `T009`'s and `T007`'s "dead premise" results are eta-expansions
(`AttackT009.dead_premise_is_eta`), not strengthenings; neither licenses deleting
the `T009 → T008` DAG edge.
**m3** — `T009`'s `handlersNodup` merges two id namespaces the schema keeps
separate, so it **false-refuses** a ledger invariant 10 permits
(`AttackT009.subcalcCollision_refused_on_handlersNodup_alone`).
**m4** — `T009` returns one bit where invariant 25 requires seven separately
reported zero counters; `EC1-CE031`'s repair is satisfied only in its second half.
**m5** — `T004S`'s `describedAddr32` erases the tag `Cas/Schema/El.lean:16-18`
states must be retained (`EC1-F86` shape), and its only row-satisfying alphabet
is built over a **minted** signature — so the non-vacuity control does not run
over a shipped one.
**m6** — `T004`'s `AnsCode.interp` duplicates the inhabited `El .str` meaning and
puts `Nat` beside `SafeInt`; scoped and disclosed, but "nothing is minted" is not
true as written.
**m7** — `T006`'s `normalizeRaw_ladder_coherent`, elevated as "the reviewable
obligation", constrains only the alias field and is cleared by a block-discarding
stage (`AttackT006.the_coherence_obligation_admits_a_discarding_ladder`).
**m8** — `T009`'s disclosed exponential caveat is not testable with `decide`
(the elaborator's whnf cache memoises); the shipped memoised variant
(`Guarded.lean:449/468`) is confirmed untransplanted, and any constant-fuel
harness false-refuses (`chain12_falsely_refused_when_underfuelled`).
**m9** — `T004S`'s `field_repair_is_a_projection`, backing its recommended
replacement, never mentions an answer-code table and is a content-free tautology
(`AttackT004S.field_repair_needs_no_alphabet`); the honest form is proved as
`honest_field_repair_is_a_projection`.
**m10** — one anchor drift: `T004.lean` cites `PROOF-DAG.md:207` twice for the
deleted-tautology sentence, which is at :203-204; :207 is blank. Every other
anchor I spot-checked resolves exactly (`Canonicalize.lean:53/55/64/81/155/160`,
`Canon.lean:259/266/278/288/297/313`, `Sig.lean:13`, `El.lean:178`,
`Described/Core.lean:16`, `Guarded.lean:378/421`, `Admission.lean:60`).
**m11** — no host/TypeScript evidence exists anywhere in the slice. The mirror
half of `EC1-F60` and the generator join are untouched by all thirteen rows.

---

## 4. What is now owed

**No row came back REFUTED as a statement — every file elaborates and every
theorem in it is true.** What is owed is that no row is *closed*, six carry
inflated grades, and four carry claims that are false.

### Owed before any EC1-S1 cutover

| Row | Status after breakers | What would close it |
| --- | --- | --- |
| `T001` | Proved on local carrier; grade PROVED-STRONGER **not supported** | Rule §17.1/§17.8. Add a payload-preservation law (M9). Mirror the estate's compiled `Bool` guard (M10). Refuse function-valued payloads (M11). |
| `T002` | Proved with both premises; **blind to dedup discipline** | Promote the last-wins law to a DAG row. Register the backward falsifier. Adopt `AttackT002.normRow_eq_canonServices` as the pin. |
| `T003` | Proved premise-free at intrinsic carrier; **three narrative claims must be amended** | Re-attribute the deletion to the intrinsic carrier (M21). Add a scalar-primitive confronting instrument. Ship `PureDenotes`'s independence as an enforceable review condition. |
| `T003E` | PROVED-WEAKER, correctly labelled; **`≃` is Prop not data** | Restate `Σ`-valued (M12). Redo the insufficiency boundary — both excluded arms are representable. Rule §17.13. Add `Cas.Schema.*` rows to `EXISTING-TYPES.md`. |
| `T004` | Restatement sound; **ground (a) refuted; bridge blind** | Rule freeze conditions 3 and 14. Put `NodupOps` on `toSig` as a precondition (M14). State the key-disjointness side condition `T004X` needs. |
| `T004S` | **Its own `REFUTED` disposition is refuted** | Reclassify: delete the DAG row as a tautology; move the obligation to `OpDesc` data pinned to `answerTy`. Do **not** file a register row for it. |
| `T004X` | `rfl` on one carrier, false on the other; **six conjuncts not eight** | Rule condition 14. Enforce `Sig.sum` retention at admission — §8's real content is that the constraint is load-bearing, not that the row is undecided. |
| `T004RW` | Real uniqueness result; **rooted tower absent** | Restate at `stepRooted`/`StoreSig` — the row's first named subject. Add the two missing necessity rungs. Drop (B) and (A)-4 as derived. |
| `T005` | **UNDETERMINED, not vacuous** | Fix the field universe (needs `EC1-D020`). Then strike on unstatedness. Do **not** lift the §3 bundle into `ProgramWF` until it is reachability-closed and duplicate-free (M8). |
| `T006` | DAG row genuinely proved; **F82 discharge false; adequacy hole open** | Retract the F82 claim (M1). Add the `entry` law (M2). Make alias resolution capture-avoiding and chain-closed (M3). Freeze the stage order — the row's truth depends on it. |
| `T007` | Row proved; **strengthening refuted; carrier mismatch** | Decide presentation-order vs map semantics (M17). Re-sequence into `EC1-S2` (M20). Restate the premise honestly as bijective. |
| `T008` | **Strongest row; statement level only** | Add the `keys.Nodup` clause (M7). Validate the two unrouted diagnostics. Run `EC1-H11` and produce the ledger. |
| `T009` | Real decidability result; **"closed" is not what was proved** | Model profile predicates (M4). Wire `decision` in (M6). Add `surfaceDisposition` to the row carrier. Split the verdict into invariant 25's seven counters. Transplant the memoised door. |

### Owed at packet level

1. **Land `D0–D1` in `formal/effect-core-v1/`.** Nothing in this slice is closed
   until the constructor edges exist. This is the whole gate.
2. **Rule freeze conditions 1, 3, 8, 13, 14.** Five of the nine gate conditions
   are downstream of a *ruling*, not of a proof. No further Lean effort moves
   `T001`, `T003E`, `T004`, `T004S`, `T004X` or `T004RW` until they close.
3. **Add `Cas.Schema.*` rows to `EXISTING-TYPES.md`** — `EC1-F86` currently
   names an empty gate.
4. **Add `Cas.Canonicalizer` to the reuse ledger and a rows/normalization family
   row to `PROOF-DAG.md` §16** — three rows route through an abstraction the
   packet has never mentioned.
5. **Fix the slice ledger.** `EC1-T005` and `EC1-T007` are owed by `EC1-S1`
   while depending on D2; `EC1-T005` appears in no other slice's exits.
6. **Run `EC1-H11`.** Two gate conditions and three rows are blocked on a
   harness that has never run.

---

## 5. Proposed counterexample-register rows

**Proposed only — I have not edited `COUNTEREXAMPLES.md`. The packet author owns
the register.** Highest existing id is `EC1-CE052`; ids below are placeholders.
Every witness is kernel-checked, `sorryAx`-free, and reruns with:

```
cd /Users/pooks/Dev/foldlab/library/cas && \
  lake env lean /Users/pooks/Dev/foldlab/.staging/effect-core-v1/workshop/s1/<FILE>
```

Note: these witnesses currently live under a `.gitignore`d path
(`.gitignore:11`). **Registering them requires promoting the files to a tracked
location first** — otherwise the register cites evidence the repository does not
carry. That promotion is itself owed.

| ID | Statement defeated | Witness | Owner | State / forced repair |
| --- | --- | --- | --- | --- |
| `EC1-CE053` | `NodupKeys r -> norm r = norm s -> rowEq r s` for keyed rows. | `r = norm [c,c]`, `s = [c,c]`, one key written twice; the equation comes from idempotence, the premise from `norm`'s nodup closure. | `workshop/s1/T002.lean`: `backward_premise_is_necessary`; independently at both packet carriers in `attack-T002.lean`: `errorRow_forward_premise_is_necessary`, `requirementRow_forward_premise_is_necessary`. | `VERIFIED-KERNEL`; both premises of `EC1-T002` are load-bearing, for **opposite** directions. `EC1-CE030` justifies only the forward one. Axioms `[propext, Classical.choice, Quot.sound]`. |
| `EC1-CE054` | Idempotence plus preservation pins a keyed-row normalizer's dedup discipline. | A first-occurrence-wins normalizer satisfies `T001`, `T002`, `T002a/b/c` and is a different function; under both premises the dedup step is inert. | `attack-T002.lean`: `row_bundle_minus_last_wins_does_not_pin_the_normalizer`, `normRowFirst_violates_last_wins`, `row_premises_collapse_norm_to_mergeSort`. | `VERIFIED-KERNEL`; the last-wins law (`Canon.lean:278` analogue) must become a DAG row. |
| `EC1-CE055` | A stable non-deduplicating raw sort prevents a duplicate-key normalization equivalence. | Two duplicate-key, permuted, distinct raw programs with a live alias map normalize equal; alias resolution is a second deduplication channel. | `attack-T006.lean`: `f82_is_not_discharged`, `separation_holds_only_on_the_alias_free_fragment`. | `VERIFIED-KERNEL`; **retracts `T006` §7's `EC1-F82` discharge.** Forced repair: constrain the alias stage, or move the F82 defence to admission. |
| `EC1-CE056` | Idempotence plus the four preservation laws determines `normalizeRaw`. | `forgetEntry` satisfies idempotence, PRESERVE-exact/count/elements, `KeySorted`, alias discharge and duplicate separation — and deletes the entry point. | `attack-T006.lean`: `section6_and_7_do_not_determine_normalizeRaw`, `forgetEntry_deletes_the_target_block`, `entry_has_a_block_is_preserved`. | `VERIFIED-KERNEL`; add an `entry` law. `EC1-F01` in normalizer form. |
| `EC1-CE057` | Single-step alias resolution preserves duplicate-free block keys. | A `Nodup`-keyed program whose alias resolves a block into an occupied name; the normal form has duplicate keys. | `attack-T006.lean`: `normalizeRaw_manufactures_duplicate_keys`, `ce030_premise_is_not_preserved_by_normalizeRaw`. | `VERIFIED-KERNEL`; `EC1-CE030`'s premise is not preserved across normalization. Alias resolution must be capture-avoiding and chain-closed. |
| `EC1-CE058` | A renaming-stable normalizer can preserve block identifiers. | Any normalizer that is renaming-stable and never invents or loses an identifier returns an empty table; survives restriction to well-formed inputs. | `workshop/s1/T007.lean`: `preserve_keys_is_incompatible_with_the_row`; strengthened in `attack-T007.lean`: `preserve_keys_obstruction_survives_wf_restriction`. | `VERIFIED-KERNEL`; the `Canon.lean` PRESERVE bundle **does not transfer** to a bound namespace. Adequacy must be stated on the free namespace, on structure, or modulo renaming. |
| `EC1-CE059` | Top-level slot-resolution closure is first-order closure. | A continuation slot reachable through a registered code body passes `FirstOrderClosed`; and a duplicate `CodeId` table is accepted with ambiguous resolution, invariant under permutation. | `attack-T005.lean`: `f08Nested_passes_the_target_predicate`, `topLevelClosed_is_strictly_weaker`, `dupProg_accepted`, `dupProg_permutation_is_invisible`. | `VERIFIED-KERNEL`; nested `EC1-F08`, plus `EC1-F03` and `EC1-F82` landing. Any `ProgramWF` clause must be reachability-closed and duplicate-free. |
| `EC1-CE060` | A surface-ledger well-formedness predicate constrains the public key universe. | A ledger whose `keys` lists one module twice satisfies `PublicSurfaceWF` and is accepted by the checker. | `attack-T008.lean`: `dupKeys_passes_wf_and_the_checker`, `accepted_key_count_overstates`, `the_repair_separates_them`. | `VERIFIED-KERNEL`; `EC1-F60`'s duplicate half on the instrument built to catch it. One decidable clause repairs it. |
| `EC1-CE061` | Mapping groundedness witnesses that effects reached Core. | A ledger refusing every effect-bearing row, and the empty ledger, both satisfy the row with zero constructive mappings and zero handler ids. | `attack-T009.lean`: `allRefused_satisfies_the_row`, `allRefused_has_no_core_content`, `emptySurface_wf`. | `VERIFIED-KERNEL`; groundedness is a consistency property, never a coverage one. |
| `EC1-CE062` | A profile-mapping well-formedness bundle detects census defects. | Duplicate row keys, an omitted deep public module, and decisions contradicting their own mappings all pass unmodified. | `attack-T009.lean`: `dupRowKey_wf`, `F59_passes_through`, `decision_is_inert`, `incoherentDecision_wf`. | `VERIFIED-KERNEL`; `EC1-F59` and `EC1-F60` pass through. Invariant 25's counters need their own clauses. |
| `EC1-CE063` | `Nat` and top-level `Option` are outside the `Cas.Schema.El` supported overlap. | Both are exactly representable: `Option α` by a one-optional-field struct, `Nat` by `.arr .null`; both satisfy the shipped `Described` class including `Ast.WF`. | `attack-T003E.lean`: `describedOption`, `describedNat`, `both_excluded_arms_are_representable`. | `VERIFIED-KERNEL`; `Instances.lean:5-7` is instance **policy**, not a limit of the schema universe. §17.13's boundary must be redrawn. |
| `EC1-CE064` | Pure-evaluator adequacy constrains atom meanings or scalar primitives. | Two atom tables with identical signatures, each fully adequate, denote different values for one program; an equality primitive answering `true` on `1 = 2` also passes. | `workshop/s1/T003.lean`: `atom_meaning_is_unconstrained`; `attack-T003.lean`: `same_program_two_atom_meanings`, `the_row_is_blind_to_the_scalar_primitive`. | `VERIFIED-KERNEL`; `ALGEBRA.md` §3 clause 5 cannot be inherited from `EC1-T003`. A separate confronting instrument is owed. |
| `EC1-CE065` | An alphabet's `toSig` bridge can witness a duplicate-operation table. | A forbidden duplicate-op table and its de-duplicated counterpart have pointwise-equal lookups and an **equal** `toSig.Op`; `NodupOps` is unrecoverable downstream and is not closed under join. | `attack-T004.lean`: `the_bridge_cannot_recover_the_red_control`, `nodup_is_not_closed_under_join`, `join_drops_an_arm`. | `VERIFIED-KERNEL`; `Alphabet.toSig` needs the premise as a precondition, and `EC1-T004X` needs a key-disjointness side condition the packet does not state. |
| `EC1-CE066` | A flat-table alphabet carrier can satisfy `extend a b |>.toSig = a.toSig ⊕ₛ b.toSig`. | On overlapping arms concatenation collapses the shared operation while `Sig.sum` keeps both tagged; the right arm's routing is silently discarded. | `workshop/s1/T004X.lean`: `Derived.T004X_false_at_the_derived_carrier`, `Derived.derived_right_arm_metadata_is_lost`; `attack-T004X.lean`: `Derived.derived_extend_is_order_sensitive`. | `VERIFIED-KERNEL`; the `Sig.sum`-retention clause of freeze condition 14 is **load-bearing** and must be enforced at admission. |
| `EC1-CE067` | The `EC1-T004RW` dependency column pins the worded extension. | Six total step functions satisfy `since_cas_agrees` and `stepWorded_preserves_wf` verbatim, plus the strengthened CAS import, and are each wrong — refuted only by a right-arm projection. | `workshop/s1/T004RW.lean`: `imported_laws_do_not_pin_the_extension`; `attack-T004RW.lean`: `three_further_adversaries`. | `VERIFIED-KERNEL`; the column names two consequences and omits the projections that carry the weight. `publish` and `listRoots` have **no** projection law in the estate at any depth. |

Rows I explicitly recommend **NOT** filing:

- **`T004S`'s "answer bridge is not a theorem".** Refuted at packet scope (B3).
  It is a tautology-deletion, not a counterexample.
- **`T005`'s "row is vacuous".** Undetermined, not vacuous (B2).

---

## 6. Summary

- **Rows proved (on locally declared carriers): 13/13.** Every file elaborates;
  every theorem in it is true. Nothing was weakened silently to get a green check
  — I checked each grade against its own theorem text.
- **Rows closed against the proof DAG: 0/13.** No carrier exists.
- **Rows whose reported grade is refuted: 6** — `T001`, `T004`, `T004S`,
  `T004X`, `T005`, `T007`.
- **Rows carrying a claim that is false: 4** — `T006` (F82 discharge, adequacy
  bundle), `T004S` (disposition), `T005` (vacuity), `T003` (premise attribution).
- **Verified receipts: 970 lines / 966 own theorems** across 26 files. Zero
  `sorryAx`, zero errors, zero warnings. 221 axiom-free; `Classical.choice` in
  five files, every occurrence inherited from Lean core or the estate's own
  ceiling.
- **Blockers: 3** — B1 (no declarations exist), B2 (`T005` undetermined),
  B3 (`T004S` disposition wrong).
- **Gate: NOT MET.** 0 of 9 exit conditions fully discharged; 5 partial, 1 met by
  inspection only, 3 not met. All 11 S1 exit falsifiers remain `PENDING`.
  `EC1-H11` has never run.

The honest reading: this slice produced a large amount of genuinely good
statement-shape work — `T008`'s decider, `T009`'s `checkB_iff`, `T004RW`'s
uniqueness theorem, and the `T001`/`T002` normalizer pin are all real results
that will survive — and it produced **no assurance about Effect Core v1**,
because Effect Core v1 has no declarations. Five of the nine gate conditions are
blocked on rulings rather than proofs. The next slice should not treat any row
here as discharged; it should treat this bundle as a set of *candidate
statements with their adversaries already banked*, and land `D0–D1` first.
