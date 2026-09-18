# The `effTy` callers slice — plan (2026-09-18)

The owner's ask: land the move of `effTy`'s consumers onto the fold checker cleanly and
efficiently, then look at what can be cut. This note is the probe: what consumes the block, how,
and the order that keeps every commit green.

## 1. What consumes the block

The block is `effTy`/`layerTy`/`layersTy`/`stmtsTy`/`effsTy`/`actionTy` (`Program/Typing.lean`
282-556, 275 lines). Its consumers, by kind:

| kind | where | count |
| --- | --- | --- |
| black box, through the sound/complete lemmas (`effTy_sound`, `effTy_eq_hasTy`, `wellTyped_iff`, `hasTy_unique`, `hasTy_weaken`; namespace `Conform.Effect4.Typing`) | `Laws/Program/{TypedRun,MeaningSound,LoopSound,CheckedTyping}.lean`, `Laws/Codegen/Checked.lean`, `Laws/Program/Typing/{Check,HasTy}.lean` | 7 files |
| black box, evaluated (`#guard`, `decide`, `Api.typeOf`, `wellTyped`) | 8 test files, `Api.lean`, `Codegen` | fine under any definition |
| **unfolding the equations** — completeness (`simp_all [effTy]`) | `Laws/Program/Typing/Sound.lean` | 63 sites |
| **unfolding** — the fifty inversion lemmas (`aesop` with `attribute [aesop norm simp] effTy …`) | `Laws/Program/Typing/Inversion.lean` | 50 lemmas |
| **unfolding** — `build_total`/`buildAll_total` (`simp [layerTy, …] at ht`) | `Program/Provision.lean` (core) | 24 sites; **no users** |
| **unfolding** — the weakening block (`effTy_weaken` and siblings, mutual) and `effTy_provideService_twice` | `Program/Typing.lean` 677-775 (core) | 10 sites; `effTy_weaken` used by `Forms.lean`, `Schema/Transform.lean`, `typeOf_weaken`; `provideService_twice` **no users** |
| **unfolding** — specific arms in proofs about forms and transforms | `Laws/Codegen/Forms.lean` (5), `Schema/Transform.lean` (4, core, wipe list §3), `Laws/Program/ScopedTyping.lean` (4, by `rfl`) | 13 sites |
| generated `@[spec]` reflect lemmas | `Laws/Program/Typing/Specs.lean` (1635 lines, group `specs`) | **no users** (`mvcgen` is used once, elsewhere, on `ofVal_spec`) |

## 2. The one obstacle: the path

`check sig env p e` threads the blame path; a child is checked at `p ++ [i]`. A proof that
relates a child's `effTy` to its parent's (every completeness arm, every inversion, Forms,
Transform, Provision) therefore meets `(check sig env (p ++ [0]) first).toOption` on one side
and `effTy sig env first = (check sig env [] first).toOption` on the other. The equation between
them — the success projection does not depend on the path — is exactly today's `check_eq`
(`Typing/Agreement.lean`, 600 lines of structural recursion). It is also a two-line corollary
of soundness and completeness *stated for `check` at every path*: an `ok` at one path derives
`HasTy`, which completeness gives back at any path. So the order is forced: **the proof graph
moves to `check` first, and `check_eq` is then deleted, not kept.**

Core cannot import Laws, so a core theorem that needs path independence (Provision's
`build_total`, `effTy_provideService_twice`, `Schema/Transform`'s inline proofs) either moves
to Laws or goes. All three have no users or are on the wipe list.

## 3. The end state

- `Checker.check` is the one checker. `effTy sig env e := (check sig env [] e).toOption` and the
  five siblings likewise (`layersTy` under `LayerTy.mergeNonempty`), as definitions in the
  `Typing` facade; `typeOf`, `typeOfProgram`, `WellTyped`, `WellTypedLayer` unchanged.
- `Program/Typing.lean` splits: `Typing/Rules.lean` is everything the fold needs (the type
  algebra, `termTy`, `argTy`, `causeTy`, the weakening lemmas of terms and causes) and
  `Typing.lean` re-exports it plus `Checker` and defines the projections, so every
  `import Effect4.Program.Typing` keeps working. `Checker.lean`, `Blame.lean`, `Terms.lean`
  import `Rules`.
- Laws: `check_sound`/`check_complete` and the four siblings (`Sound.lean`, restated for
  `check` at every path; the arms are the same three lines each), the inversions for `check`
  (`Inversion.lean`, `aesop` with `attribute [aesop norm simp] Checker.check …` and the
  `Except` laws), and the corollaries under their old names in `Conform.Effect4.Typing`:
  `effTy_sound`, `effTy_complete`, `effTy_eq_hasTy`, `wellTyped_iff`, `hasTy_unique`,
  `hasTy_weaken` — one line each through `toOption_eq_some`. Plus `check_toOption : (check sig
  env p e).toOption = effTy sig env e` (path independence), which the arm-specific sites use.
- The weakening block restated for `check` at equal paths (`check_weaken`, core, same 60
  lines), `effTy_weaken` its corollary, `typeOf_weaken` unchanged.
- Forms (5 sites) and ScopedTyping (4) rewrite with `[effTy, Checker.check, toOption_bind,
  toOption_pure, check_toOption, …]` — the arm equation is derived inline, no named equation
  set.
- `Agreement.lean` keeps `refusal_none_iff`, the mode-flag and list-sort lemmas, the term
  typer agreement, `explain_none_iff`; `check_eq` and its 600 lines go.

## 4. Cuts this slice makes or enables

| what | lines | why it goes |
| --- | --- | --- |
| `check_eq` (`Typing/Agreement.lean`) | ~600 | corollary of sound + complete for `check` |
| `Typing/Specs.lean` + group `specs` (`EmitSpecs`, `specs.json`, Makefile/`generate.py` entries, `GENERATED.md` row) | 1635 generated | no consumer; `mvcgen` is not used on the checker |
| `Laws/Program/Typing/Check.lean` (`checkTyping`, `TypingGap`, `assessTyping`) | 58 | no consumer; `Api.checkTyping` is the one in use |
| `Provision.lean` `build_total`/`buildAll_total` | ~170 | no consumer; if kept, moves to Laws restated for `checkLayer` |
| `effTy_provideService_twice` | ~30 | no consumer |
| `Schema/Transform.lean` + `Laws/Schema/Transform.lean` + `Schema/Endpoint.lean` | 98 + 18 + 383 | wipe list (`ontology.md` §3); imported only by `Api` (re-exports) and each other |

## 5. Order, each step green

1. **S2 (parallel files, no deletion):** `Laws/Program/Typing/CheckInversion.lean` (the fifty
   inversions for `check`, `aesop`), `Laws/Program/Typing/CheckSound.lean` (`check_sound`,
   `check_complete`, siblings; `check_toOption`). The old files stay. Build the two modules.
2. **S1 (the flip, one commit):** split `Typing.lean`; the projections; delete the block, the
   old `Sound.lean`/`Inversion.lean` bodies (the corollaries take the old names), `check_eq`;
   restate the weakening block; rewrite Forms/ScopedTyping sites; move or cut Provision's
   totality theorems; cut Specs, Check.lean, Transform/Endpoint. Build both roots and
   `Test.All`; regenerate nothing (the `specs` group is removed from the manifest).
3. Docs: census note §7.8, `STATE.md`, `GENERATED.md`, `decisions.md` rows 3/26 as touched.

`termTy`/`termsTy` (the term typer) follow the same pattern in a later slice.
