# effect4_eff — the Eff program IR as an OCaml library

`Eff`, the Effect program IR of this repository (`src/Effect4/Program/`), reified in OCaml:
a typed embedding you author programs in, the canonical byte wire Lean decodes, the JSON
printer, and the typing judgement as a checker. An OCaml program written through the typed
surface erases to bytes that the Lean fiber machine loads, re-checks and runs.

Standard library only. OCaml 5.1.1 / dune 3.24 (opam switch `effect4`).

## Layout

| file | lines | kind | what it is |
| --- | ---: | --- | --- |
| `eff_frame.ml` | 209 | hand | the framing kernel: `emit_*`/`decode_*` for the ten tags, base-256 naturals, UTF-8 validation |
| `eff_json_text.ml` | 61 | hand | JSON string escaping and number/array/object assembly for the printer |
| `eff_types.ml` | 471 | **generated** | one OCaml variant/record per Lean inductive/structure, constructor order pinned, `ctor_index_*` / `ctor_name_*` / `ctor_names_*` per family |
| `eff_wire.ml` | 978 | **generated** | `encode_*` / `decode_*` per family, `*_exact` at the top level |
| `eff_json.ml` | 187 | **generated** | `print_*` per family (a printer only — there is no JSON parser anywhere) |
| `eff_native.ml` | 184 | **generated** | the atom typing table (`atom_ty`), the 53 op values (`all_ops`) and their rows (`row_of`), `scope_key`, the handle types |
| `eff_typing.ml` | 369 | hand | the typing judgement of `Typing.lean` as `type_of : eff -> (eff_ty, error) result`, `well_typed`, `print_type`, and `Ty.join` |
| `eff_typed.ml` / `.mli` | 393 / 254 | hand | the GADT surface indexed by the Eff type, and `erase` to the untyped carrier |
| `eff_manifest.txt` | 23 | **generated** | one line per family: name, OCaml type, constructors and their carriers, in order |
| `goldens/` | 113 files | **generated** | `<name>.bin` (canonical bytes), `<name>.json`, `<name>.ty` for 37 programs, plus `corpus.txt` and `coverage.txt` |
| `test/test_eff.ml` | 466 | hand | the golden battery, the GADT corpus, the constructor pins, the wire kernel |
| `test/prop_wire.ml` | 184 | hand | the wire property test on random untyped values |
| `test/test_lean_wire.ml` | 180 | hand | the differential against Lean's own encoder (`ocaml/goldens/eff/*.hex`) |
| `tools/*.sh` | — | hand | build / test / signature-inference drivers for WSL |

## Build and test

From inside `ocaml/eff` (its own project root, so its `_build` does not contend with the
`ocaml/` workspace):

```
eval $(opam env --switch=effect4 --set-switch)
cd ocaml/eff && dune build --root . && dune test --root .
```

or `cd ocaml && dune build eff` from the workspace root. On Windows the same through WSL:
`wsl -e bash ocaml/eff/tools/test.sh`.

## Regenerating

The four generated modules, the manifest and the goldens all come from one Lean tool that
reads the families out of the environment. From the repository root:

```
lake env lean -M4096 --run src/OCaml5/Tools/EffGen.lean ocaml/eff
```

It writes `eff_types.ml`, `eff_wire.ml`, `eff_json.ml`, `eff_native.ml`, `eff_manifest.txt`
and `goldens/`. Each generated file carries a `GENERATED … Do not edit.` header; a fix to a
generated file belongs in `EffGen.lean`. (The header inside the files spells the command
without `-M4096`; the cap is this repository's build hygiene rule, not the tool's.)

The Lean-side hex goldens the differential compares against are a different tool:

```
lake env lean -M4096 --run src/OCaml5/Tools/EffWire.lean ocaml/goldens/eff
```

## The wire

Canonical bytes, as `src/Effect4/Store/Canonical.lean` frames every stored value:
`framed tag payload = tag :: be64 (length payload) ++ payload`, `be64` eight big-endian
bytes.

| value | bytes |
| --- | --- |
| `Unit` | `framed 9 []` |
| `Bool b` | `framed 1 [b ? 1 : 0]` |
| `Nat n` | `framed 2 (base-256 digits, big-endian, no leading zero; 0 = empty payload)` |
| `String s` | `framed 3 (utf8 bytes)` |
| `List xs` | `framed 4 (concat (encode x))` |
| `Option none` / `some x` | `framed 6 []` / `framed 7 (encode x)` |
| `a × b` | `framed 5 (encode a ++ encode b)` |
| constructor `i`, args `a₁…aₙ` | `framed 10 (encode (i : Nat) ++ encode a₁ ++ … ++ encode aₙ)` |
| a structure (one constructor) | as constructor 0 with its fields in declaration order |

`i` is the constructor's 0-based index in declaration order as the Lean environment reports
it. `Var` is a `Nat`. The list families (`Terms`, `Stmts`, `Effs`) are inductives: `nil` = 0,
`cons head tail` = 1. `Op` is `NativeOp` throughout.

Decoding is length-directed — every frame is self-delimiting — and **exact**: trailing bytes,
a wrong tag, an out-of-range constructor index, a short payload, a non-canonical natural (a
leading zero digit), a bool byte other than 0/1, and invalid UTF-8 are all refusals, never
repairs. `decode_program` returns `(value, bytes consumed)`; `decode_program_exact` refuses
anything left over.

Naturals are OCaml `int`: encoding refuses a negative, and decoding refuses more than eight
digits or eight digits above `max_int` (2⁶² − 1 on a 64-bit host). Lean's `Nat` is unbounded,
so a program carrying a literal above 2⁶² − 1 is outside this library's range and is refused
rather than truncated.

## Constructor index tables

From `eff_manifest.txt` (0-based, in Lean declaration order). A `(carrier)` suffix is the
constructor's argument types.

| family | OCaml type | constructors |
| --- | --- | --- |
| `Ty` | `ty` | never unit nat int string bool handle option list prod except exitOf causeOf fiberOf union |
| `Lit` | `lit` | unit nat bool str |
| `Term` | `term` | var lit app |
| `Terms` | `terms` | nil cons |
| `CauseTerm` | `cause_term` | fail die interrupt both |
| `MaskMode` | `mask_mode` | interruptible uninterruptible inherit |
| `ForkOptions` | `fork_options` | *(structure)* startImmediately daemon maskMode |
| `ObserverMode` | `observer_mode` | awaitValue joinEffect |
| `FinalizerStrategy` | `finalizer_strategy` | sequential parallel |
| `FnName` | `fn_name` | incr double zeroWhenPositive noChange takeAndBump |
| `NativeOp` | `native_op` | refMake refGet refSet refGetAndSet refSetAndGet refUpdate refGetAndUpdate refUpdateAndGet refUpdateSome refGetAndUpdateSome refUpdateSomeAndGet refModify refModifySome deferredMake deferredIsDone deferredPoll deferredSucceed deferredFail deferredAwait scopeMake |
| `Eff` | `eff` | succeed fail failCause yieldError sync suspend perform bind gen catchCause matchCause onExit exit uninterruptible interruptible branch whileLoop yieldNow callback awaitFiber withFiber scoped acquireRelease choose |
| `Stmt` | `stmt` | bindYield yieldDiscard ret ifElse whileTrue breakLoop |
| `Stmts` | `stmts` | nil cons |
| `Effs` | `effs` | nil cons |
| `ActionTerm` | `action_term` | fork forkIn forkScoped runIn interrupt interruptScoped interruptAll awaitAll awaitAllFailFast snapshotChildren awaitNewChildren raceAll setContext getContext getId closeScope |
| `RowKind` | `row_kind` | sync async program |
| `RowShape` | `row_shape` | call value |
| `ServiceName` / `ServiceTypeCode` / `ServiceKey` / `Row` / `EffTy` | *(structures)* | see `eff_manifest.txt` for the field order |

Tags: `bool=1 nat=2 string=3 list=4 pair=5 none=6 some=7 bytes=8 unit=9 ctor=10`.

## Properties per module

Each module's header states its own; in short.

* `eff_frame` — every frame is self-delimiting; every decoder is exact; a non-canonical
  natural, an invalid UTF-8 string and an out-of-range bool are refusals. *tested*
* `eff_wire` — `decode_*_exact (encode_* v) = Some v`, and `decode_*` never reads past the
  frame it was given. *generated from the rule; tested on 37 goldens, 8 Lean-side goldens and
  1 250 random values*
* `eff_json` — a printer only; `print_eff` of every golden is the Lean printer's output byte
  for byte. *tested*
* `eff_native` — `atom_ty` is `nativeAtomTy` and `row_of` is `NativeOp.row`, both checked
  against Lean by evaluation at generation time. *by construction, plus tested pins*
* `eff_typing` — agrees with Lean's `typeOf`/`wellTyped` on the whole corpus, well-typed and
  ill-typed alike. *tested*
* `eff_typed` — an ill-typed program cannot be constructed; `erase` then `encode` is byte for
  byte what Lean encodes. *tested on the 27 well-typed programs; the Lean theorem is open,
  see "The two open theorems" below*

## Authoring a program

```ocaml
open Eff_typed

(* fun () -> let x = 1 in x + 1, as an Eff program *)
let p : (empty, nat, (never, never) union) eff =
  Bind (Succeed (nat 1), Succeed (Succ v0))

let bytes = encode p                       (* the canonical bytes Lean decodes *)
let json  = Eff_json.print_eff (erase p)   (* the human form *)
let ty    = Eff_typing.print_type (erase p)
```

`v0`/`v1`/… are de Bruijn indices counted from the newest binding; `erase` converts them to
Lean's position from the oldest. The error index is a syntactic `union` tree whose `to_ty` is
Lean's canonical `Ty.join`. (That example is the `pBind` golden: 199 bytes, and its JSON and
type are the golden's.)

---

# Evidence

Everything below is the state of a run on 2026-09-04, reproducible by the commands named.

## Regeneration is reproducible

Regenerating into a scratch directory and comparing SHA-256 against the checked-in tree:
`eff_types.ml`, `eff_wire.ml`, `eff_json.ml`, `eff_native.ml`, `eff_manifest.txt` — all five
identical; 113 golden files compared, 0 differences, 0 missing, 0 extra. The tree on disk is
exactly what `EffGen.lean` produces at HEAD, so the regenerate command above is verified, not
merely documented.

## Test results

`cd ocaml/eff && dune build --root . && dune test --root . --force`

| executable | checks | failures |
| --- | ---: | ---: |
| `test_eff` — goldens, GADT corpus, pins, wire kernel | 607 | 0 |
| `prop_wire` — the wire on 1 250 random values, 5 properties each | 6 250 | 0 |
| `test_lean_wire` — the differential against `Effect4.Program.Wire` | 64 | 0 |
| **total** | **6 921** | **0** |

### Per program: the goldens (all 37)

Each row is ten checks: decode exactly, re-encode byte for byte, JSON equals the Lean
printer's, type equals Lean's `typeOf`, the well-typed flag, `decode` reports the whole length
as consumed, a trailing byte refused by `decode_exact` and not consumed by `decode`,
truncation refused, a flipped tag refused, a length past the end refused.

| program | bytes | decode | re-encode | JSON | `typeOf` |
| --- | ---: | --- | --- | --- | --- |
| p42 | 66 | ok | identical | equal | `nat` / `never` |
| pBind | 199 | ok | identical | equal | `nat` / `never` |
| pFork | 290 | ok | identical | equal | `exitOf nat never` / `never` |
| pTwo | 599 | ok | identical | equal | `exitOf nat never` / `never` |
| pAwait | 159 | ok | identical | equal | `nat` / `nat` |
| pGen | 274 | ok | identical | equal | `nat` / `never` |
| pWhile | 351 | ok | identical | equal | `unit` / `never` |
| pCatch | 151 | ok | identical | equal | `nat` / `never` |
| pStr | 76 | ok | identical | equal | `string` / `never` |
| pFailCause | 313 | ok | identical | equal | `never` / `nat` |
| pYieldError | 67 | ok | identical | equal | `never` / `bool` |
| pSync | 202 | ok | identical | equal | `nat` / `never` |
| pSuspend | 74 | ok | identical | equal | `unit` / `never` |
| pMatch | 267 | ok | identical | equal | `bool` / `never` |
| pOnExit | 114 | ok | identical | equal | `nat` / `never` |
| pExit | 86 | ok | identical | equal | `exitOf never nat` / `never` |
| pMasks | 104 | ok | identical | equal | `nat` / `never` |
| pBranch | 200 | ok | identical | equal | `nat` / `nat` |
| pCallback | 159 | ok | identical | equal | `nat` / `nat` |
| pJoin | 291 | ok | identical | equal | `nat` / `never` |
| pScoped | 320 | ok | identical | equal | `fiberOf nat never` / `never` |
| pAcquire | 168 | ok | identical | equal | `handle Ref.Ref<number>` / `never`, requires ⟨0,0⟩ |
| pChoose | 161 | ok | identical | equal | `nat` / `never` |
| pPair | 270 | ok | identical | equal | `nat` / `never` |
| pStmts | 599 | ok | identical | equal | `nat` / `never` |
| pActions | 1836 | ok | identical | equal | `nat` / `never`, requires ⟨0,0⟩ |
| pOps | 2667 | ok | identical | equal | `nat` / `nat` |
| pIll | 135 | ok | identical | equal | ill-typed |
| pIllRet | 209 | ok | identical | equal | ill-typed |
| pIllReq | 86 | ok | identical | equal | ill-typed |
| pIllBreak | 75 | ok | identical | equal | ill-typed |
| pIllBranch | 199 | ok | identical | equal | ill-typed |
| pIllJoin | 199 | ok | identical | equal | ill-typed |
| pIllVar | 45 | ok | identical | equal | ill-typed |
| pIllCallback | 168 | ok | identical | equal | ill-typed |
| pIllStep | 303 | ok | identical | equal | ill-typed |
| pIllInterruptor | 95 | ok | identical | equal | ill-typed |

### Per program: the GADT corpus (the 27 well-typed programs)

Each is rebuilt through `Eff_typed`'s constructors, erased, and encoded. For all 27 — p42,
pBind, pFork, pTwo, pAwait, pGen, pWhile, pCatch, pStr, pFailCause, pYieldError, pSync,
pSuspend, pMatch, pOnExit, pExit, pMasks, pBranch, pCallback, pJoin, pScoped, pAcquire,
pChoose, pPair, pStmts, pActions, pOps — the run reports *identical to golden* / *well-typed:
yes* / *answer and error both agree with the erased witness*. That is the proof that OCaml
authors exactly what Lean would.

The ten `pIll*` programs are not in the GADT corpus and cannot be: that they are
unconstructible is the point. The test pins the two lists against each other.

## The Lean-side differential

`ocaml/goldens/eff/*.hex` are the canonical bytes of eight programs written by
`src/OCaml5/Tools/EffWire.lean` through `Effect4.Program.Wire` — Lean's own implementation of
the byte rule, independent of the one `EffGen.lean` derives this library from. This library's
decoder reads them and re-encodes:

| program | bytes | decode | re-encode | vs `goldens/<name>.bin` |
| --- | ---: | --- | --- | --- |
| p42 | 66 | ok | identical | **identical** |
| pAwait | 159 | ok | identical | **identical** |
| pBind | 199 | ok | identical | **identical** |
| pFork | 290 | ok | identical | **identical** |
| pCatch | 206 | ok | identical | differs at byte 8 (`8e` vs `c5`) — different programs, same name |
| pGen | 484 | ok | identical | differs at byte 8 (`09` vs `db`) — different programs, same name |
| pLoop | 343 | ok | identical | no golden of that name |
| pScope | 234 | ok | identical | no golden of that name |

* All eight decode **exactly** and re-encode byte for byte. That is the strongest evidence
  this lane can give that the OCaml wire is Lean's wire — including on `pLoop` (a `whileLoop`
  over `refUpdate`) and `pScope` (`scoped`/`acquireRelease`/`interruptAll`), which the OCaml
  corpus does not shape the same way.
* The four names that denote the *same* Lean term in both corpora (`p42`, `pBind`, `pFork`,
  `pAwait`, read off `Wire.lean` §Corpus against `EffGen.lean` §Corpus) are byte for byte
  equal. That is asserted, not merely reported.
* `pCatch` and `pGen` are different Lean *definitions* sharing a name across the two corpora
  (`Wire.Corpus.pCatch` catches `both(fail 1, interrupt none)` and returns unit;
  `EffGen.Corpus.pCatch` catches `fail 1` and returns `0`). The test proves the byte
  difference is a program difference and not a wire difference, by checking that the two
  decoded programs differ too. The differences begin at offset 8 — the last byte of the outer
  frame's `be64` length — which is what a different-sized payload looks like, not a framing
  disagreement.
* `test_lean_wire` also checks Lean's own manifest against this library's constructor tables
  (16 lines: 15 families plus the tag numbers), and that a trailing byte on Lean's bytes is
  refused.

The Lean goldens are outside this dune project (`ocaml/goldens/eff` is a sibling of
`ocaml/eff`), so they cannot be a tracked dune dependency: the test reaches them by a relative
path that is the same from either build root, or takes the directory as `argv(1)`, and prints
`SKIPPED` rather than passing silently if it is absent.

## What is not covered, and why

**Constructors: nothing is missing.** `goldens/coverage.txt` counts every constructor of every
family across the 37-program corpus and every count is ≥ 1: all 24 `Eff` arms, all 6 `Stmt`,
all 16 `ActionTerm`, all 4 `CauseTerm`, all 4 `Lit`, all 3 `Term`, all 20 `NativeOp`, all 5
`FnName`, all 3 `MaskMode`, both `ObserverMode`, both `FinalizerStrategy`, and the `nil`/`cons`
of `Terms`/`Stmts`/`Effs`.

**Ops.** All 53 op *values* (11 with no payload, 8 × 5 `FnName`, 1 × 2 `FinalizerStrategy`) are
enumerated in `Eff_native.all_ops` and each is pinned against its Lean row (name, request,
answer, error, sync/async), as is the typed `op` GADT's own signature for each. Of the 53, 21
are actually *performed* by a golden program (`pOps`: one per constructor plus both scope
strategies); the other 32 differ from one that is only in the `FnName` payload, which the wire
encodes as a nested constructor frame already exercised.

**Atoms.** The table has 10. Six appear in golden programs (`succ`, `isZero`, `add`, `lt`,
`pair`, `fst`). `pred`, `not`, `eq`, `snd` appear in none — the Lean corpus never used them.
They are covered here instead by direct `atom_ty` row checks and by a program built through
the GADT (`Not (Eq (Pred (Snd (Pair …))))`) that is erased and put to the checker. So they have
E1 evidence but not E2: no Lean-authored byte string exists for them. Four lines added to
`EffGen.Corpus` plus a regeneration would close that.

**Types.** As a program's answer or error the `.ty` goldens exercise `never`, `unit`, `nat`,
`string`, `bool`, `handle`, `exitOf`, `fiberOf`. Not exercised as a program type: `int`,
`option`, `list`, `prod`, `except`, `causeOf`, and a residual `union`. `prod` and `causeOf` do
occur inside the run (op requests such as `refSet : ref × nat`, and the cause bound by
`catchCause`/`matchCause`); `union` is always canonicalised away by `Ty.join` because every
corpus program's two error branches collapse to one type — a program whose error is a genuine
two-member union would be a worthwhile addition. `Ty.int`, `Ty.option`, `Ty.list` and
`Ty.except` have `ty` witnesses in the typed surface for `to_ty` completeness, but no `term` or
`eff` constructor produces a value of them: Eff is first-order and has no list or option
literal atom, so a `list` only enters through a variable (`Snapshot_children` binds one and
`Await_all` consumes it, which `pActions` does).

**Requirements.** The native alphabet has one service key (`scope_key = ⟨0,0⟩`). Two corpus
programs carry it (`pAcquire`, `pActions`); `pScoped` discharges it with `scoped`. The
`req_of_list`/`req_union` algebra (ascending, deduplicated) is tested directly.

**`RowKind.program`** is a constructor of the type but no `NativeOp` row uses it; the test pins
that `deferredAwait` is the single `async` row and the rest are `sync`.

**Deliberately out of scope.** No JSON *parser* anywhere — the JSON side is a printer only. No
TypeScript printing: Lean owns `Api.print`. No evaluator: this library authors, checks and
serialises programs; running them is the Lean fiber machine and the `ocaml/avatar` lane. No
`Obj`, no `Marshal`, no polymorphic compare on abstract types.

**Bound.** OCaml naturals are `int`, so literals and variable indices above 2⁶² − 1 are refused
rather than encoded; Lean's `Nat` is unbounded. A program from Lean carrying such a literal
would be refused by this decoder — a refusal, not a truncation, but a real gap against the
Lean type.

## The typed surface's signature

The authority is `eff_typed.mli` (254 lines) — read it there rather than from a copy. Its
shape, in one paragraph: five families of phantom value types (`never nat int_ ref_number
deferred_number scope context unknown`, plus the injective compounds `except exit cause_of
fiber union`); `'a ty`, the witness that maps a phantom back to Lean's `Ty` (`Union` through
`Ty.join`); `empty` and `('env,'a) ix` for the type-level environment and de Bruijn index;
`('env,'a) term` with one arm per literal and per native atom; `('env,'e) cause`;
`('req,'ans,'err,'kind) op` with the twenty `NativeOp` rows written into the constructor
types; the witnesses `join_answer`, `merge_ret`, `gen_answer`, `observer`, `in_loop`; the
mutual `('env,'a,'e) eff` / `('env,'r,'e,'l) stmts` / `('env,'a,'e) effs` /
`('env,'a,'e) action` with one constructor per Lean arm in Lean's order; `program` as the
existential of a closed program with its two witnesses; and then `handle_target`, `to_ty`, the
`erase_*` family (each taking the environment depth, because an OCaml index counts from the
newest binding and Lean's `Var` from the oldest — the Lean index is `depth - 1 - index`),
`erase`, `encode`, and the conveniences `v0..v3`, `nat`, `unit_`, `bool`, `str`,
`fork_options`.

## The two open theorems

Both are about the Lean side and are stated so a Lean seat can pick them up directly. Neither
is proved; both are pinned by tests over the corpus.

### T1 — erasure of the typed surface is well-typed

Transcribe `eff_typed.mli`'s families into Lean as an inductive family indexed by the typing
judgement's data, with the same witnesses:

```lean
/-- The OCaml GADT `('env, 'a, 'e) Eff_typed.eff` as a Lean family. `Γ : TyEnv` replaces the
    type-level snoc list; the phantom-to-`Ty` map `to_ty` is the identity here because the
    indices are already `Ty`. A `union` index becomes `Ty.join`, and the `join_answer` /
    `merge_ret` witnesses become `EffTy.joinAnswer` / `GenTy.joinAnswer` equations. -/
inductive TEff : TyEnv → Ty → Ty → Type
  | succeed {Γ a}       : TTerm Γ a → TEff Γ a .never
  | bind {Γ a b e₁ e₂}  : TEff Γ a e₁ → TEff (a :: Γ) b e₂ → TEff Γ b (Ty.join e₁ e₂)
  | …                   -- one arm per line of the .mli, in the same order

def TEff.erase {Γ a e} : TEff Γ a e → Eff NativeOp := …   -- transcription of erase_eff
def TEff.requires {Γ a e} : TEff Γ a e → List ServiceKey := …

/-- **T1.** Everything the typed surface can build type-checks in Lean, at exactly the indices
    the surface carries. -/
theorem TEff.typeOf_erase {Γ : TyEnv} {a e : Ty} (p : TEff Γ a e) :
    Typing.check Γ p.erase = some { answer := a, error := e, requires := p.requires }

/-- The closed corollary the OCaml header claims (E1). -/
theorem TEff.wellTyped_erase {a e : Ty} (p : TEff [] a e) : Api.wellTyped p.erase = true
```

`requires` is the one piece of the judgement the OCaml GADT deliberately does not track in its
indices (`scoped` discharges `scope_key`; `perform`/`callback` add their row's `requires`;
everything else is the union of its children), so it has to be a function of the derivation
rather than an index. The proof is by induction on `p`, each case `simp [Typing.check, erase]`
plus the corresponding witness lemma. The interesting cases are `gen` (the statement list's
return type must be threaded, so the induction is mutual with a `TStmts` lemma) and
`whileLoop` (the step term is typed two environments deeper).

Evidence today: the 27 well-typed corpus programs are each built through the GADT, erased, and
the checker's answer and error compared with `to_ty` of the indices — plus one extra program
for the four atoms no golden uses. Not proved.

### T2 — the wire is exact

In `src/Effect4/Program/Wire.lean`, with `encodeProgram : Eff NativeOp → Bytes` and
`decodeProgram : Bytes → Option (Eff NativeOp)`:

```lean
/-- **T2a** (round trip). -/
theorem decodeProgram_encodeProgram (p : Eff NativeOp) :
    decodeProgram (encodeProgram p) = some p

/-- **T2b** (exactness / canonicity): every byte string the decoder accepts is the encoding of
    the program it produces — so there is exactly one byte string per program, and a decode
    never repairs. -/
theorem encodeProgram_decodeProgram {b : Bytes} {p : Eff NativeOp} :
    decodeProgram b = some p → b = encodeProgram p
```

T2b is the load-bearing half: with it, `decodeProgram` is a partial inverse whose domain is
exactly the image of `encodeProgram`, which makes trailing bytes, a leading-zero natural digit,
an out-of-range constructor index and a short payload refusals *by construction* rather than by
case analysis. The route: prove the framing lemma first — for `Store/Canonical.lean`'s
framing, `readFrame (framed t p ++ r) = some (t, p, r)` and conversely
`readFrame b = some (t, p, r) → b = framed t p ++ r` — then lift it through the mutual
`encEff`/`decEff` recursion, with a `natOfDigits`/`digits` canonicity lemma for the `Nat` case.

Evidence today: `Wire.lean` already `#guard`s T2a and the two refusal corollaries on its
eight-program corpus. On the OCaml side the same statements are tested on 37 goldens, on the 8
Lean-authored byte strings, and on 1 250 random values at seed 42 — plus injectivity of
`encode` on the random sample, the finite shadow of T2b. Not proved.

A third statement is what the differential actually measures, and is *not* a Lean theorem
because one side is OCaml code: for every `p : Eff NativeOp`,
`Effect4.Program.Wire.encodeProgram p` and `Eff_wire.encode_program (ocaml_of p)` are equal.
It is discharged empirically by `test_lean_wire` on the eight programs Lean has published
bytes for; widening `Wire.Corpus` is the cheapest way to strengthen it.

## What remains owed

* T1 and T2 are open.
* `pred`, `not`, `eq`, `snd` and a genuinely two-member `union` error have no Lean-authored
  golden bytes; four short additions to `EffGen.Corpus` plus a regeneration would fix it.
* `Wire.Corpus` (Lean's own eight) does not cover `gen` with `whileTrue`/`breakLoop`,
  `matchCause`, `choose`, `raceAll` or the fiber-action alphabet; widening it would widen the
  strongest evidence this lane has.
* Naturals above 2⁶² − 1 are refused, not encoded.
