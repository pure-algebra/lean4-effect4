The note misses where the typed state pins services by itself: `ServicesOk` reads `nativeServiceTy` directly (Typed/Admission.lean:32-34), and Codex's in-flight item E re-pins it as `ServicesFit` over flat carriers only; with that route included, R1 before M5–M7 is still cheap (about 22 mechanical declarations if the service table is a world component), and the soundness theorems need no restatement at all (proved: typing survives every signature extension, rows by append and services with fresh keys, and `meaning_typed`/`run_sound` carry to any table and service list as corollaries).

# Seat TREE: ground truth and feasibility probes for R1-R9

Status: done, 2026-09-30. Research only; no tracked file edited.

- Note under review: `docs/research/2026-09-30-full-program-model-requirements.md` (committed at
  `7cae243a`; its stated base `74b526d4`).
- Tree at HEAD `7cae243a` on `refactor/phase1-phase3`. `git diff 74b526d4 7cae243a --stat`
  touches only `docs/STATE.md` and the note, so every code claim made at the base holds or fails
  identically at HEAD.
- Evidence words: **proved** (a kernel theorem I ran), **tested** (a finite check I ran),
  **reading** (read in code or notes, not run), **assumed**.
- Probes compile against the oleans in `.lake/build` through the lock script. Some oleans predate
  HEAD's last source commits (`git log --since="2026-09-24 01:10" -- src/` touches
  `Laws/Api/Supervision`, `Laws/Machine/StoresLaws`, `Laws/Program/LayerSharing`, `Laws/Run`,
  `Machine/Stores` (memoComplete) and `Program/Checker` (comments only)). No declaration a probe
  uses changed in those commits (reading).

## 1. The note's factual claims against the tree

Each row: the claim, the verdict, the command or file:line that settles it.

### 1.1 Counts

| Claim (note line) | Verdict | Evidence |
| --- | --- | --- |
| "188 `sig : Signature` binders in the proof graph" (:109) | **confirmed, with a qualifier** | `grep -rno "(sig : Signature" src/Effect4/Laws \| wc -l` = 188 (explicit binders, 18 files). Counting implicit binders too, `grep -rno "sig : Signature" src/Effect4/Laws \| wc -l` = 219 (188 explicit + 31 `{sig : Signature`), 19 files. `variable (sig : Signature Op)` lines count once but bind a whole section, so the number of signature-generic statements is larger than either count. (tested) |
| "89 uses in 15 proof files" (:111) | **confirmed as a grep count; it undercounts the pinning** | `grep -rn "nativeSignature" src/Effect4/Laws \| wc -l` = 89 lines (one occurrence each), `grep -rln … \| wc -l` = 15. Two of the 89 are the lemma name `nativeSignature_row_closed` (MeaningSound.lean:681 and its definition). The count misses the other routes to the built-in signature: `nativeServiceTy` read directly (Typed/Admission.lean:33), `Api.typeOf` (= `typeOfProgram (nativeSignature table)`, Api.lean:96) in Assembly.lean:149 and :226, and `admitProgram`/`AdmittedProgram` in Laws/Run.lean (7 lines) and Laws/Program/CheckedTyping.lean (4 lines). (tested) |
| "ten places (`Typed/Admission` 1, `Assembly` 2, `Residual` 3, `ForkSource` 4) … mostly through `ProgramSource`" (:216-217) | **counts confirmed; "mostly through `ProgramSource`" corrected** | `grep -c nativeSignature` per file gives 1/2/3/4. Six of the ten read `root.table`/`src.table` (Admission.lean:95; Assembly.lean:45-46; Residual.lean:53, 111-112). The four in ForkSource (ForkSource.lean:32, 47, 53, 68) are `nativeSignature` at its default, the **empty** table, on a bare `root : NativeEff`, not a `ProgramSource`. The typed modules also reach the built-in signature in three places the count misses: `ServicesOk` reads `nativeServiceTy` (Admission.lean:32-34), and the M5/M6 statements read `Api.typeOf root.program root.table` (Assembly.lean:149, :226). Corrected total: 13 places in the same four modules (Admission 2, Assembly 4, Residual 3, ForkSource 4). (tested) |
| "runtime admission in three (`Program/Admission.lean:90, 108, 191`)" (:218) | **confirmed** | `grep -n nativeSignature src/Effect4/Program/Admission.lean` = 90, 108, 191. (tested) |

### 1.2 File:line references and what the named things state

| Claim | Verdict | Evidence (reading unless marked) |
| --- | --- | --- |
| `Signature Op` at `Program/Typing/Rules.lean:49` carries `rowOf`, `atomOf`, `scopeKey`, `serviceTy` (:107) | **confirmed, incomplete** | Rules.lean:49-66. It also carries `dom` (:62, default all) and `constAtom` (:66, default none). The checker reads `rowOf`/`dom` (Checker.lean:133-134), `serviceTy` (:216, :219), `scopeKey` (:209, :332, and through `bodyRequires`), `atomOf`/`constAtom` through `argTy` (Rules.lean:88-98). |
| `AdmittedProgram` extends `TypedProgram (nativeSignature table)` (`Program/Admission.lean:90`) | **confirmed** | Admission.lean:89-95. |
| `MeaningSound` and `LoopSound` stated at `effTy nativeSignature` (`LoopSound.lean:298`, `:307`) | **confirmed for LoopSound; MeaningSound's own lines are elsewhere; the pin is empty in substance** | LoopSound.lean:298, :307, :530-547. MeaningSound's statements are MeaningSound.lean:518-521 (`sound`) and :738-762 (`meaning_typed`, `meaning_never_wrong`, `meaning_stores`, `run_typed`), all at the empty table (its own header says so, :33-34). Both fragments exclude every node that reads the parts of the signature R1 opens: `Straight` and `Looped` refuse `.service`, `.provideService`, `.provideLayer` (Fragment.lean:44-46; DenoteB.lean:147-149) and every `perform` whose op is not `.sync` (Fragment.lean:28-31; DenoteB.lean:130-133), and `NativeOp.kind (.external _) = .program` (Native.lean:127). So no straight or looped program can mention a host row or a service key; see §3.4 for the corollary that carries both theorems to any table and service list without reproof. |
| `ProgramSource` carries a program and a row table only (`Typed/Admission.lean:84-86`), "and the typed state reads the signature through it" | **lines confirmed; the second half corrected** | Admission.lean:84-86. The typed state also reads the built-in service table directly, not through the source: `ServicesOk w services := ∀ key sv sty, services.getV key = some sv → nativeServiceTy key = some sty → …` (Admission.lean:32-34), reached from `HandlesFit`'s context arm (:57), hence from `StrongValue` (:61-62), `StrongCause`, `StrongExit`, `EnvTyped` and everything typed by them; and from `preds.ServiceOk` (Assembly.lean:56), `CaptureTyped` (:47), `fiberPre .setContext` (Residual.lean:121). |
| "`nativeSignatureWith` … only the layer checker uses it" | **confirmed** | `grep -rn nativeSignatureWith src/ Test/` = 9 lines in 2 files: its definition (Services.lean:42-55) and `Test/Program/AuthorContract.lean:281-292`, where it is passed to `Api.checkLayer` (Api.lean:540-541 takes any `sig`) and `ServiceDef.Agrees`. (tested) |
| "Building, admitting and running refuse a seventh carrier (probe of 2026-09-30: `serviceCarrier … signature none`)" | **confirmed; the cited probe is a scratchpad file, not in the tree** | The probe is the coordinator's `scratchpad/demo/ServiceDemo.lean` (code 12). Building refuses at `disagreeingService` (Api/Author.lean:46-50, refusal :39). Admitting refuses because `admitProgram` checks at `nativeSignature table` (Admission.lean:108), whose `serviceTy` is `nativeServiceTy` (Native.lean:288-293, six codes at :277-279). Running needs a `Built` (`Run.open`, Run.lean:100) or `HostSession.start`, which calls `admitProgram` (HostSession.lean:136). Re-tested in my R1 probe (§2). |
| `interpret_pinned` (§1) | **exists, in the `effects` dependency** | `.lake/packages/effects/Effects/Algebra/Universal.lean:243`. Not in `src/`. |
| `Protocol.sum` (§1, R2) | **exists; it is over the `Effects` operation signature, not the typing signature** | Laws/Effects/Protocol.lean:83-95; `Typed.inl` :97. See §1.3. |
| `provide_closed`, `merge_rows_comm` in `Program/Provision.lean` | **confirmed** | Provision.lean:98, :138. |
| `replay_unique`, `journal_replays` (K5) | **confirmed** | Laws/Api/Runner.lean:157; Laws/Run.lean:184. |
| `denoteR` | **confirmed** | Laws/Program/DenoteR.lean:797. |
| `composeAt` "typing closure is derivable; its meaning laws are future work (system map §6)" | **confirmed as prose** | `composeAt` is defined only in `docs/core/system-map.md:154`; no Lean declaration (`grep -rn composeAt src Test .lake/packages` is empty). |

### 1.3 Status words and the model claims

| Claim | Verdict | Evidence |
| --- | --- | --- |
| R2 "rows: additive by construction. The theorems quantify over the row table, and `interpret_pinned` and `Protocol.sum` are per operation" | **half right; the reason given is the wrong one** | Two different signatures are in play. `Program.Signature Op` is the *typing* signature (Rules.lean:49). `interpret_pinned` and `Protocol.sum` are over `Effects.Signature`, the *operation* signature of the reference interpreter: `RSig = StoreSig ⊕ FiberSig` (Laws/Program/Sched.lean:194-206; StoreSig at Laws/Program/Denote.lean:41), 31 store and 40 fiber operations. A host row is not an operation of `RSig`: every host row goes through one fiber operation, `FiberOp.async (register : EffName) (request : Val)` (Sched.lean:105), whose protocol entry reads the row table (`asyncPre … .external op _`, Residual.lean:110-112). So adding a row adds no `RSig` operation and no `Protocol.sum` summand; rows are additive because the table is a parameter of `nativeSignature` and of `ProgramSource`. Whether typing is preserved under a longer table is not stated anywhere in the tree (no lemma relates two signatures or two tables: `grep -rnE "sig'\|sig₁\|sig₂\|Signature\.(le\|extends\|sub\|mono)" src Test` is empty). §3 proves it for appended rows and refutes it for prepended ones. |
| R2 "services: fixed (six type codes)" | **confirmed** | Native.lean:277-279, :288-293. |
| R2 "cells: fixed at `number`" | **confirmed for the rows and the store decoders; the type language and the world are already generic** | Rows: `refTy := .handle "Ref.Ref<number>"` (Native.lean:90-91), `deferredTy` at `<number, number>` (:97-99), `refMake : nat → refTy` (:156). Decoders: `syncOpOf refMake (Val.nat n)` only, `deferredSucceed/Fail` on `Val.nat` only (Native.lean:232, :248-251). Generic already: `Ty.refOf`, `Ty.deferredOf` (Admission.lean:41-42 uses them), the world's `Ρ : RefKey → Option Ty` and `Π` (Typed/World.lean:48-57). Details in §4 (R4). |
| R2 "data types: `Ty` is closed" | **confirmed** | `Ty` has no record or variant constructor (the constructor list is visible in `findInt`, Program/Admission.lean:30-41). Row 2 rules annotation-carried names now and `Ty.record`/`Ty.variant` later (decisions.md:23). |
| R4 "The typed world: proved (row 44)" | **"ruled and defined" is the right word, not "proved"** | Row 44 is a ruling (decisions.md:91, "ruled 2026-09-19"). The world is defined at every type (World.lean:52-57) and its order laws are proved (World.lean:394-406), but the typed-state milestone over it (M5, M6) is declared, not proved (`#proof_wanted`, Assembly.lean:235-257). |
| R4 "Type constructors and the template calculus: landed (steps 1–2)" | **confirmed** | Row 42's status cell (decisions.md:89); `rowTy` matches the row's request template (Rules.lean:111-115). |
| R4 "the rows, the store and the faces: open (steps 3–5)" | **confirmed**; what remains is itemized in §4 | |
| R4 "Bridge … row 96's D2 reads the native spellings as cells declared at `nat`" | **confirmed** | decisions.md:189 (D2); `HandleFits` in `docs/research/2026-09-30-pass/membership/note.md` §2. |
| R6 "Parked by the owner on 2026-09-30" | **consistent with row 95's go-ahead** | decisions.md:188: M6 counts only runs whose tape applies no host answer. |
| Source "the author seat's receipt C2 … row 21" | **confirmed** | Row 21 (decisions.md:52): keep the declaration-site check "until an application needs a seventh carrier — threading changes `Built`, `HostSession.start`, `Run.open` and both soundness statements". |


## 2. R1 by probe: the typed-state source with a service table

Probe: `R1Probe.lean` (this folder); log `R1Probe.log`. Command:
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs>/R1Probe.lean`,
exit 0. Every theorem prints `[propext, Quot.sound]` or less. No `sorry`, `native_decide`,
`axiom`, `partial`, `unsafe` (`grep -c` = 0).

### 2.1 What elaborates (proved and tested)

- `Source` = `ProgramSource` plus `services : List (ServiceKey × Ty) := []`, with
  `Source.sig := nativeSignatureWith src.table src.services`. At the empty list it is the tree's
  signature, `rfl` (`Source.sig_ofProgramSource`), and its row, domain, atom and scope halves are
  the tree's for every service list, `rfl` (`Source.sig_rowOf` … `sig_scopeKey`). **proved**
- Design B's chain `ServicesOkB`, `HandlesFitB`, `StrongValueB`, `StrongCauseB`, `StrongExitB`,
  `EnvTypedB`, each taking the static service table, with connectors to the tree's judgments at
  `nativeServiceTy` (`servicesOkB_native`, `handlesFitB_native` by induction on `Ty`,
  `strongValueB_native`, `envTypedB_native`). **proved**
- `PointTypedB` (checker at `src.sig`, environment at `src.sig.serviceTy`) and `BodyTypedB`; at
  the empty list `PointTypedB ↔ PointTyped` (`pointTypedB_ofProgramSource`). **proved**
- The M5 premise over the source: `typeOfProgram (Source.ofProgramSource src).sig src.program =
  Api.typeOf src.program src.table` is `rfl`. **proved**
- `AdmittedProgramB program table services` and `admitProgramB`, beside the tree's; a certificate at
  the empty list is the tree's certificate and back (`AdmittedProgramB.toTree_ofTree`, `rfl`).
  **proved**
- The seventh carrier (the coordinator's demo key, `⟨⟨12⟩, ⟨12⟩⟩ : string`): **tested**
  - the tree refuses it at every stage: `Api.typeOf greetProgram [] = none`;
    `admitProgram greetProgram []` is `.error .illTyped`; `Api.check` refuses at the root with
    `serviceUnknown`; `Api.Author.build` refuses with `serviceCarrier k12_12 string none`;
  - over the source's signature it types and admits, closed, at `⟨string, never, empty⟩`;
  - the module already carries the table R1 needs: `Module.serviceTypes`
    (Program/Authoring.lean:332-333) equals the probe's service list.
- Not `rfl`: `termTy (nativeSignatureWith t s) env x = termTy (nativeSignature t) env x` does not
  elaborate as `rfl` (tested, `R1Probe-run1.log`); it is proved by induction in R2Probe §A.

### 2.2 What would change its statement, measured

The typed state reads the built-in signature through two routes, not one:

1. **The source route** (rows already threaded): `ProgramSource` (Admission.lean:84-86) gains the
   field; the bodies of `PointTyped` (:95), `CaptureTyped` (Assembly.lean:45-46), `storePre`'s
   `memoGet` arm (Residual.lean:52-53) and, for uniformity only, `asyncPre`'s `external` arm
   (:110-112, the row half does not see services) read the source's signature. Statements that
   change: `source_fork_extension` and `fork_source_extension` (ForkSource.lean:28-68, today at the
   empty table on a bare `NativeEff`), `M3bAssembly.typedState_load` (Assembly.lean:148-150) and
   `M6Ledger.typedState_reachable` (:225-227), whose premise is `Api.typeOf root.program
   root.table`. **About 9 declarations.** (reading; the shapes elaborate in the probe)
2. **The value route, which the note does not mention.** `ServicesOk` reads `nativeServiceTy`
   directly (Admission.lean:32-34). It is reached from `HandlesFit`'s context arm (:57), so from
   `StrongValue`, `StrongCause`, `StrongExit`, `EnvTyped`, `CompletionStrong`, and everything typed
   by them. Two shapes:
   - **A. a static world component.** `World` (World.lean:52-57) gains `serviceTy : ServiceKey →
     Option Ty := nativeServiceTy`; `World.le` (:131-136) gains `w.serviceTy = newer.serviceTy` as a
     last conjunct; `order_refl`/`order_trans` (:394-406) and the six `*_extension` proofs (:411,
     :519, :531, :605, :692, :710) gain one component each (`rfl`); `ServicesOk`'s body reads
     `w.serviceTy`; `initialWorld` (Validity.lean:41) takes the source's table; `TypedState`
     (Assembly.lean:67) or `WorldValid` (Validity.lean:19) gains `w.serviceTy = root.sig.serviceTy`.
     **About 13 declarations, all mechanical, and one test edit**: the field has a default, so no
     world is rebuilt; the positional projections at World.lean:433, :437, :754, Residual.lean:339,
     Validity.lean:149 reach conjuncts before the new last one, but `order_trans` (World.lean:406)
     and `token_replacement_refused` (Test/Audit/TypedStateDecl.lean:294) project today's last
     conjunct (`.2.2.2.2.2`) and gain a `.1`. (reading; `grep -rn "\.2\.2\.2\.2\.2"`)
   - **B. a parameter of the judgments**, as the probe's `…B` chain does. Measured with
     `measure.py` (`measure-designB.txt`): **59 declarations name one of the seven judgments in
     their statement and 18 more in their body** (src 39 + 11, Test 20 + 7). (tested count)
3. **Item E is re-pinning the value route now.** Brief addendum 2 item E (row 96, in flight in
   the slice 6 worktree) replaces `ServicesOk` by `ServicesFit`, which reads `nativeServiceTy` and
   types a service value by `FlatFits` (`docs/research/2026-09-30-pass/membership/Fits.lean:75-91`).
   Its comment states the premise: "the service table's types are scalars and non-context
   handles … so this needs no recursion". `FlatFits` is `False` at every other type. An open
   service table therefore needs one of: carriers restricted to flat types (a decidable check on
   the table at admission), or `ServicesFit` at the full `Fits`, which recurses through a context
   value into service values whose types are not subterms of the context's type (not structural
   on `Ty`). Shape A is untouched by E's renames (it edits `ServicesFit`'s body); shape B would be
   paid on E's ~77 declarations a second time unless folded into E's cut-over. (reading)

Runtime admission and the run path (row 21's list), measured by reading:

| File | Declarations whose statement changes |
| --- | --- |
| `Program/Admission.lean` | 10 of 16: `AdmittedProgram`, `admitProgram`, `AdmittedStraightProgram`, `admitStraightProgram`, and the six theorems at :150-212 (the four `findInt*` scanners and the two refusal types stay) |
| `Api/Built.lean` | `Built` (one field, the certificate's index) |
| `Api/Author.lean` | `Built.typed` (:82) only; `build` (:55) and `disagreeingService` (:46) change bodies (admit at `m.serviceTypes`; the refusal becomes a conflict check) |
| `Api/HostSession.lean` | `Session` and `start` if the service table is a session field (the certificate indexed by it); 15 if it is a session index (every declaration of the 28 that mentions the table or the session, `Header` and `Call` included, except `Refusal`) |
| `Run.lean` | `Run.open`'s body if a session field; `Run` and its readers if an index |
| `Api.lean` | `Typed` and `check` (:443-456) if `Built.typed` keeps producing a `Typed`; the ~20 `(table : RowTable := [])` entry points (:96-241) gain a defaulted service list, so call sites do not move |
| Laws | `admitted_unique`, `admitProgram_certificate`, `open_total` (Laws/Run.lean:207, :218, :230); `Laws/Program/CheckedTyping.lean` (4 lines); the faces' entry theorems in `Laws/Codegen/{Checked,Admit}.lean` and `Laws/Api/{ModuleReadable,Codegen}.lean` (22 `nativeSignature` lines) |
| `MeaningSound.lean`, `LoopSound.lean`, `TypedRun.lean` | **none**: carried over by corollary (§3.4) |

None of the runtime rows is on the M5–M7 path: M5 and M6 are stated over `ProgramSource` and
`TypedState`, not over `AdmittedProgram`, `Built` or `Session` (Assembly.lean:148-227).

**Does any proof depend on the six codes beyond reading the signature?** In the proof graph, no:
`nativeServiceTy` appears in `src/Effect4/Laws` only in `ServicesOk`'s definition and a comment
(`grep -rn nativeServiceTy src/` gives Admission.lean:29, :33 and no proof). Outside it,
`disagreeingService` (Api/Author.lean:48) is a definition; the printer and reader read
`sig.serviceTy` generically (Codegen/PrintLeaf.lean:300-307, Codegen/Read.lean:346-361, :864-867).
Tests pin the codes concretely and stay true at the empty list (`natKey_ty`,
Test/Program/LoadedAdmission.lean:115; `nativeServiceTy_profile`, Test/Codegen/ReadContract.lean:35;
`Test/Api/AcquireHandleContract.lean:26-27`). The one dependence on the codes' *shape* is item E's
`FlatFits` (above). (reading)

## 3. R2 by probe: does typing survive a larger signature?

Probe: `R2Probe.lean`; log `R2Probe.log`. Same command, exit 0, 29 theorems, every one at
`[propext, Quot.sound]` or less. The tree has no lemma relating two signatures or two tables
(§1.3), so everything here is new.

### 3.1 The general law (proved)

`SigExtends s s'`: same `atomOf`, `constAtom`, `scopeKey`; every operation `s` admits, `s'` admits
at the same row; every key `s` types, `s'` types at the same carrier.

- `argTy_congr`, `termTy_congr`, `causeTy_congr`: the term and cause typers read only `atomOf` and
  `constAtom` (mutual induction on `Term`/`Terms`).
- `hasTy_ext`, `stmtsHasTy_ext`, `effsHasTy_ext`, `actionHasTy_ext`, `layerHasTy_ext`,
  `layersHasTy_ext`: all six judgments are preserved along `SigExtends`, by structural recursion on
  the derivation, one line per rule (63 rules: 26 + 7 + 2 + 17 + 9 + 2).
- `check_ext` (the checker at every path, through `check_sound`/`check_complete`), `effTy_ext`,
  `typeOfProgram_ext`, `checkLayer_ext`. `SigExtends.refl`/`trans`.

### 3.2 Rows (proved; red control kept)

- `rows_append t t'`: `nativeSignature t` ⊆ `nativeSignature (t ++ t')`. A program typed under a
  table keeps its type, at every path, when rows are appended.
- **What fails: prepending.** `prepend_not_extends`: `[rowB] ++ [rowA]` does not extend `[rowA]`.
  **tested:** `yield* A.a()` (`.perform (.external 0) unit`) answers `nat` under `[rowA]` and
  `string` under `[rowB] ++ [rowA]`; under `[rowA] ++ [rowB]` it still answers `nat`. External
  indices are positions, so prepending re-points every call. `Package.install` prepends package
  rows (Program/Authoring/Services.lean:184-187); that is harmless only because `Row.call` resolves
  positions at elaboration, after installing. An elaborated program needs append, or a reindexing
  (a renaming of operations) carried with it.
- The typed state's source admission is monotone in the table: `pointTyped_rows_append`.
- **Red control for the typed state (tested, kept):** `asyncPre … .external op _`
  (Residual.lean:110-112) reads `rowOf op` without `dom op`. Outside the table the row is the
  placeholder (Native.lean:118-120) whose columns are `never`, below every type (Ty.lean:440), so
  the entry holds at every certificate; with a longer table the same index constrains. So
  `TypedProg` is not monotone in the table unless the entry also requires `dom op = true` (or an
  invariant says every registered host row is in the table).

### 3.3 Services (proved; red control kept)

- `services_append t s s' fresh`: appending a service list is an extension when no appended key is
  already typed (`nativeServiceTyWith s entry.1 = none` for each entry). Corollaries:
  `native_into_with` (the tree's signature into `nativeSignatureWith` with fresh keys),
  `rows_and_services` (both at once), `native_into_greet` (code 12, freshness by `decide +kernel`).
- **What fails: shadowing.** `shadow_not_extends`: an entry at a key the six codes already type
  (`⟨⟨100⟩, ⟨4⟩⟩`, a number) is not an extension. **tested:** `yield* key` answers `nat` under the
  tree's signature and `bool` under `nativeSignatureWith [] [(key, bool)]`. `nativeServiceTyWith`
  (Services.lean:42-45) lets a declared entry override the six codes; conservativity needs the
  freshness premise. The key module already frames keys as typed by their code relative to a
  supplied universe (`ServiceUniverse`, Machine/Key.lean:43-81, :331-390); a per-code table extended by
  fresh codes would make freshness a property of the codes alone.

### 3.4 The soundness theorems carry over without restatement (proved)

A looped program (hence a straight one) names no host row and no service, layer, scope or fork
(`Looped`, DenoteB.lean:125-152; `Straight`, Fragment.lean:22-49; `NativeOp.kind (.external _) =
.program`, Native.lean:127). So:

- `hasTy_restrict_looped`: a looped program's typing under `s'` is a typing under `s` whenever the
  two agree on atoms and on the rows of synchronous operations; `agree_native t s`: every
  `nativeSignatureWith t s` agrees so with `nativeSignature`.
- Corollaries, each a short proof through the tree's theorem: `meaning_typed_any`, `run_typed_any`, `meaningB_typed_any`;
  `restrictCertificate` (a `TypedProgram (nativeSignatureWith t s) e` for a looped `e` is a
  `TypedProgram nativeSignature e` at the same type) and with it `run_sound_any`,
  `run_soundB_any` — the "both soundness statements" of row 21 and receipt C2
  (Laws/Program/TypedRun.lean:83, :112).

So the note's "`MeaningSound` and `LoopSound` follow" is right in a stronger form than it says:
they need no restatement at all, and the premise shared by row 21, receipt C2 and the findings
ledger's 4B (`docs/research/2026-09-17-scout-findings-ledger.md:294-300`: threading "changes …
the soundness statements (`MeaningSound`, `LoopSound` are stated at `nativeSignature table`)") is
wrong; they are in fact stated at the empty table. (proved)

### 3.5 Not probed

- Atom extension: `SigExtends` fixes `atomOf` and `constAtom`. A new atom name is additive, but
  marking an existing name const-generic changes the literal rule (`litArgTy`, Rules.lean:68-81), so atoms are
  additive only for fresh names.
- Data types and cell types: `Ty` is a closed inductive; adding a constructor is not a signature
  extension but a change of the type language (§4 and R3).

## 4. R4: what remains of rows 42–43 steps 3–5 at HEAD

Source of the steps: `docs/research/2026-09-18-rows-42-43-plan.md` §1 (design), §2 (order), §2b
(probe of 3–5), §2c (the push's L1–L7), §2d (re-cuts), §2e (the pause). Status of each piece at
HEAD, by reading unless marked.

**Already landed** (so not "remaining"): steps 1–2 (row 42's status cell, decisions.md:89);
L1, `Term` below the machine (Machine/Term.lean:100-107, namespace `Effect4.Program`); L3's atoms
`ite`, `optSome`, `optNone`, `mul`, the list atoms, `natSub/Div/Mod`, `strConcat`
(Machine/Term.lean:147-164); §2d's `templateAdmissible` and `Row.wellScoped`
(Laws/Program/Template.lean:268, :288); N1's root sets (`ocaml/gen/roots.json` exists); the type
printer's `refOf`/`deferredOf` arms (Codegen/Types.lean:302-305); the typed state's per-cell world
(`Ρ`, `Π` at any `Ty`, Typed/World.lean:48-57), which the plan's step 4 did not have yet.

**Step 3 (L4): rows as templates and function-taking rows — open.**

| Piece | Where it stands |
| --- | --- |
| Ref and Deferred rows over `var 0`/`var 1` | Rows still at the spelled handles: `refTarget`/`refTy` (Native.lean:90-91), `deferredTarget`/`deferredTy` (:98-99); 13 Ref rows (:156-189), 6 Deferred rows (:190-207). |
| `deferredMake (value error : Ty)` | Constructor has no arguments (Native.lean:64); `deferredTypeArgs` is spelled (:97). |
| Function-taking rows by binder terms | Eight constructors carry `FnName` (Native.lean:56-63); their `SyncOp` twins too (Machine/Stores.lean:255-270); `refStep` applies the name (:878-919) through `FnName.total/partialUpdate/modify/modifySome` (:852-875); `FnName` itself (:61-72), `fnSpelling` (Native.lean:109), `fnNames`/`NativeOp.all` (:295-304). 31 files mention `FnName` (15 in `src/`, one of them generated; 7 Lean files and 4 baseline fixtures in `Test/`; 5 in `tools/`, two of them generator inputs), e.g. Laws/Program/Progress.lean (23 lines), Laws/Machine/StoresLaws.lean (20), Laws/Machine/Handles.lean (17), the generated `Store/Domain/Derived/Program.lean` (42), `OCaml5/Lcnf/Externs.lean` (5). |
| Store ops at any value | `syncOpOf` decodes `refMake` on `Val.nat` only (Native.lean:232) and `deferredSucceed/Fail` on `Val.nat` only (:248-251). The stores themselves are generic (`SyncOp.refMake (initial : Val)`, Stores.lean:245; `RefHeap := List Val`). |
| Typing the term | `Row.fn` and `Signature.termOf` do not exist (`Signature`, Rules.lean:49-66); `rowTy` types no term (:111-115). |
| Anchored inference for a repeated variable (`Ref.setAndGet`'s `prod (refOf (var 0)) (var 0)`; plan §2d L4) | No `collect`/`solve` in Ty.lean or Template.lean. |
| `Eff.scopedAt`'s `perform` arm | Still ignores the operation (`eff_perform := fun _ a1 n => a1.scoped n`, Program/Scoped.lean:26); wrong once an operation carries a term (plan §2d L4; fix in `tools/Effect4Gen/Authoring.lean`). |
| `Val.hasTy`'s cell and promise arms | Still compare the spelled targets (Program/Typed.lean:45-50); row 96's D2 now reads them as declared at `nat`. |
| Service code 7 at `refOf nat` | Still `NativeOp.refTy` (Native.lean:278); the TS profile projects it as `handle "Ref.Ref<number>"` (`ts/eff/profile.gen.ts:111`). |
| `Progress` per instantiation | `FnName.*_hasTy_nat` (Laws/Program/Progress.lean:86, :92, :110, :117) stand in. |
| Generators over terms | `Test/Program/Gen.lean`, `Test/Machine/Fuzz.lean` still draw names. |

**Step 4 (L2): the per-cell world in the straight and looped soundness — open, and partly
superseded.** `Val.hasTyWith` does not exist; `MeaningSound`'s invariant still carries
`Stores.HeapNat` (`TypedAt.heap`, MeaningSound.lean:297; `meaning_stores`, :751-756;
`meaningB_stores`, LoopSound.lean:545-550). The M5–M7 typed state already has the per-cell
tables, so step 4's original target is now only the two fragment theorems.

**Step 5 (L6): the faces — open.** `Row.typeArgs` is spelled (Eff.lean:213; Native.lean:97), not
derived; binder terms have no printer or reader (`LambdaShape`, `lambdaShape : FnName → …`,
`lambdaAtom`, Codegen/Forms.lean:127-138; `atom?`, Codegen/Styles.lean:129); the TS profile is
generated at the spelled handles and the five names (`ts/eff/profile.gen.ts:111`); OCaml `eff_*`
and the corpus `.ty` goldens move with them (plan §2 step 5). Not verified: whether the TS reader
already accepts `Ref.Ref<A>` generics (assumed open, per plan §2b step 5).

**L7 is R1 for services.** The plan's own table (§2c) lists "L7, user service carriers: the six
type codes become a service table beside the program, as the row table is", after L6. The note
does not cite this; it is the pedigree of R1-for-services and of the order question.

**What step 3 would reopen in M6.** The store protocol `Ψ_S` (Typed/Residual.lean:34-80) is already
stated at any cell type for `refMake/Get/Set/GetAndSet/SetAndGet` and the deferred rows (it reads
`Ρ`/`Π`). Only the eight read-modify-write rows carry `FnName` content: their `storePre`
(:41-43) and `storePost` arms (:63-66; `refModify`'s post is `∃ n, ans = Val.nat n`, :66).
So M6 store arms proved before step 3 would be restated for those eight rows (and wherever
`syncOpOf`'s `nat` decode is used), not for all 31. (reading)

## 5. Cost of each, and whether R1 before M5–M7 is as cheap as the note says

Counts are declarations whose statement changes (bodies listed where they matter), from §2–§4.

| Requirement | What it costs | Evidence |
| --- | --- | --- |
| R1, typing layer | **0** existing declarations. Already over any `Signature`. | proved (R2Probe uses only the tree's generic lemmas) |
| R1, `MeaningSound`/`LoopSound`/`TypedRun` | **0** restated. Five corollaries and one restriction lemma (~70 lines in the probe). | proved (§3.4) |
| R1, typed state, source route | **~9**: `ProgramSource` (+field), `PointTyped`, `CaptureTyped`, `storePre.memoGet`, `asyncPre` (bodies), the two ForkSource statements, `typedState_load`, `typedState_reachable`. | elaborates (R1Probe §A, §C); count by reading |
| R1, typed state, value route (missed by the note) | **A: ~13** mechanical (world field, order, eight order proofs, `ServicesOk`/`ServicesFit` body, initial world, one `TypedState` conjunct), one test projection edit. **B: 77** (59 statements + 18 bodies, 27 of them tests), or the same set again after item E lands. Plus a ruling on non-flat carriers (`FlatFits`). | B's chain elaborates with connectors (R1Probe §B); counts `measure-designB.txt` (tested count) and reading |
| R1, runtime admission and run path (row 21) | **~15–20** in the cheap shape (the service table a field of `Built` and `Session`, an index of the certificate: Admission 10, `Built`, `Built.typed`, `Session`, `start`, three Laws/Run theorems) plus the defaulted entry points of `Api.lean` and the faces' entry theorems (22 `nativeSignature` lines). **~45** if the session is indexed. None is on the M5–M7 path. | reading; `admitProgramB` elaborates (R1Probe §D) |
| R2 | **0** existing declarations; a new lemma family (the probe's §A–§C, ~30 declarations). Two side conditions to state, both shown necessary: rows only by append (or a reindexing), services only with fresh keys. One typed-state repair if `TypedProg` must be table-monotone: `asyncPre` reads the domain bit. | proved and tested (§3) |
| R4 (rows 42–43 steps 3–5) | The largest: 31 files name `FnName`; ~19 rows, `SyncOp`, `refStep`, `syncOpOf`, the checker's term typing (`Row.fn`/`termOf`), anchored inference, `scopedAt`, `Val.hasTy`'s handle arms, Progress, two generators, the faces (printer, reader, TS profile, OCaml `eff_*`, corpus goldens), regeneration through LCNF. In M6 it reopens only the eight read-modify-write arms of `Ψ_S`. | reading (§4) |

**Verdict on the order claim.** The note says R1 "belongs after Codex's H items and before the
M5–M7 brief" and that "the cost is statement-level, because the checker already takes any
signature".

- **Cheaper than claimed for the soundness theorems.** They need no restatement (proved), so row
  21's and receipt C2's "threading changes … both soundness statements" is wrong, and so is the
  note's "`MeaningSound` and `LoopSound` follow" if it is read as a restatement.
- **Wider than claimed for the typed state.** "`ProgramSource` carries the service table …
  `PointTyped` checks under `nativeSignatureWith`" covers the source route only. The value route
  (`ServicesOk`, and from item E `ServicesFit` with `FlatFits`) also reads the six codes, and
  ForkSource is pinned to the empty table, rows included.
- **Still cheap with shape A, and cheapest before M5–M7.** With the service table as a static
  world component the whole typed-state change is ~22 mechanical declarations. After M5–M7 it
  would also touch every M6 proof that builds a world-order witness by hand (one more `rfl`
  component each) and M5's initial world; the steps themselves never change `w.serviceTy`. With
  shape B, doing it after M5–M7 reopens every M6 proof that mentions `StrongValue`/`Fits`; doing
  it during item E costs one pass instead of two.
- **The runtime threading (row 21) is independent of M5–M7** and can follow the milestone
  without reopening it: M5 and M6 are stated over `ProgramSource`, not over `AdmittedProgram`,
  `Built` or `Session`.
- **Generic cells before the M6 store arms** is right, and narrower than "the store arms": the
  eight read-modify-write rows are what step 3 restates.

## 6. Other status claims checked

| Claim | Verdict | Evidence |
| --- | --- | --- |
| R3 "the design is ready: a mutual spine `Ty`/`Fields` (type algebra note §1.3)" | confirmed as a design | `docs/research/2026-09-18-research-type-algebra.md:144-152` |
| R3 "Recursive types … no register row covers them" | confirmed | `grep -in "recursive type" docs/core/decisions.md docs/DESIGN-ISSUES.md` is empty |
| R3 "The basis refuses `Err.value` (language cut §3)" | confirmed | `docs/core/language-cut.md:59-64`; `docs/DESIGN-BASIS.md:655` |
| R6 "Exists: the session and the interim rule" | **half at HEAD** | The session exists (Api/HostSession.lean:84-138). Of row 97's interim rule only the reply side is in the tree (`externalValue`, Program/Compile.lean:1353-1365; `externalHandleTarget`, Program/Typed.lean:17-18); the table-admission half (refuse internal handle kinds in host rows' columns) is not in `Table.lean` or `admitProgram`; it is slice 6 work (row 97, go-ahead 2026-09-30). |
| §1 "Build totality was proved in the 2026-09-04 workshop spike only" | **corrected** | `build_total` was proved in the tree (`Program/Provision.lean`, commit `f182d2b3`, 2026-09-04) and cut on 2026-09-18 (`b08f3b58`: "Cut: … Provision's build_total/buildAll_total"). `grep -rn build_total src/ Test/` now finds only the module docstring, which still says it is "proved once over the algebra" (Provision.lean:35-40): a stale claim in the tree. |
| §1 "`Ψ_S ⊕ Ψ_F` … verified separately" | confirmed as structure | `TypedProg` keeps the two halves as separate arms (`store`, `fiber`, Residual.lean:186-200); `Protocol.sum` and its lifts are stated generically (Protocol.lean:83-120) and as obligations (Typed/ProtocolObligations.lean:30-49), not used to build `TypedProg`. |
| R7 "Row 82's design is not settled" | confirmed | decisions.md row 82: "open; lifting the entire machine Capture record is not the design" |
| R8 "`journal_replays` is proved" (row 98) | confirmed; row 98 itself is "open, recommended (API migration)" | Laws/Run.lean:184 |

## 7. Decisions at the owner's boundary (options and recommendation)

1. **Where the typed state reads the service table.** (A) a static component of the world, fixed
   by the world order and tied to the source in `TypedState`; (B) a parameter of the value
   judgments. *Recommend A*: ~13 mechanical declarations, untouched by item E's renames, and the
   M1 kickoff's world already splits persistent tables from exclusive contents
   (`docs/research/2026-09-20-m1-kickoff-confidence-and-design-representations.md` §3, :253-257). B is
   the more literal parameterization and costs 77 declarations, or a fold into item E's cut-over.
2. **Which carriers an application may declare.** (a) flat only: `unit`, `nat`, `bool`, `string`,
   a non-context handle, checked on the table at admission; (b) any `Ty`, which needs `Fits` at
   the carrier and so a recursion that is not structural on `Ty`. *Recommend (a) now*: it is item
   E's `FlatFits` premise made a rule, and it fits the `ServiceDef` pattern (a carrier handle plus
   rows on it). Open a register row for structured carriers beside R3's records.
3. **Freshness of declared keys.** `nativeServiceTyWith` lets a declaration override a key the
   six codes type; that is not conservative (proved). *Recommend*: admission refuses a declared
   key the built-in table already types at another carrier (what `disagreeingService` becomes
   under R1), or move to per-code tables extended by fresh codes (`ServiceUniverse`'s framing).
4. **`asyncPre`'s domain bit.** *Recommend* the host-row protocol entry also require
   `dom op = true` before M6 is proved against it, so `TypedProg` is monotone in the table.
5. **Rows extend by append.** *Recommend* R2 for rows be stated as append (or a reindexing
   carried with the program); `Package.install`'s prepend stays harmless because positions are
   resolved after it.

Proposed register rows (for the coordinator; this seat does not edit `decisions.md`):
- "Service carriers under an open service table: flat only (admission check) or full membership."
- "Declared service keys must be fresh against the built-in table, or the table is per code."
- "`asyncPre` requires the row's domain bit (typed-state monotonicity in the table)."
- Amend row 21's consequence: threading does not change the soundness statements (R2Probe §3.4).

## 8. Receipt

- **Base / head:** `7cae243a` (HEAD, `refactor/phase1-phase3`); the note's base `74b526d4`
  differs only in `docs/STATE.md` and the note. No commit, no `git add`, no tracked file touched.
- **Files written** (all in `docs/research/2026-09-30-model-probe/TREE/`): `note.md`,
  `R1Probe.lean`, `R1Probe.log`, `R1Probe-run1.log` (the first run's errors, kept as the evidence
  that the term typer's move is not `rfl`), `R2Probe.lean`, `R2Probe.log`, `measure.py`,
  `measure-designB.txt`. Scratch: `scratchpad/tree/Names.lean` (lemma-name check, not evidence).
- **Commands and results:**
  - `bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <abs>/R1Probe.lean`
    → exit 0; 10 `#print axioms` lines, all `[propext, Quot.sound]` or `[propext]`; 8 `#guard`s pass.
  - same for `R2Probe.lean` → exit 0; 29 `#print axioms` lines, all `[propext, Quot.sound]` or no
    axioms; 8 `#guard`s pass.
  - `python3 measure.py . ServicesOk,HandlesFit,StrongValue,StrongCause,StrongExit,EnvTyped,CompletionStrong`
    → 59 statement + 18 body declarations (`measure-designB.txt`).
  - Counting greps as quoted in §1.1 and §4.
- **Trust:** `grep -c "sorry\|native_decide\|axiom \|partial \|unsafe "` on both probes = 0.
  `decide +kernel` is used for three finite facts about `nativeServiceTy` (as
  `Test/Program/LoadedAdmission.lean:115` does).
- **Bounded or host-only evidence:** the `#guard`s are finite tests on single programs (tested,
  not proved). The probes compile against `.lake/build` oleans, some older than HEAD's last
  source commits; none of the declarations used changed in those commits (reading).
- **Open obligations:** none of the probes is landed; landing R2's lemma family would put it in
  `Laws/Program/Typing/` with a `Test` fixture for each red control (`prepend_not_extends`,
  `shadow_not_extends`). Not probed: the TS reader on `Ref.Ref<A>`; atom extension; the runtime
  threading beyond `admitProgramB`.
