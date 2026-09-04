# OCaml5 and the avatar: state of the chain and the paths forward

Status: 2026-09-04, for the grill. Everything below is committed on `main` at or after
`bba637f` (Mac and PC in sync). Numbers are what the coordinator reproduced, not what a seat
reported, except where marked "seat".

## 1. The chain, edge by edge

```
Lean Flow / Deep.RunMachine ──(A3, not started)──▶ avatar program in OCaml 5 effects
   avatar rows = rc.112 rows on 34 goldens ×3 masks and 158 adversarial programs (executed)
OCaml5.Term ──(P4: executed on corpus, compile_correct stated)──▶ OCaml5.Code
OCaml5.Term ──(O1+P1: proved)──▶ Machine (native runtime) ══(P3: 57/64 arms proved)══ MachineJ (effect.js)
OCaml5.Code ──(O2+P2: knot closed, dominators open)──▶ CPS output ──generate.ml (trust)──▶ JS
OCaml5.Term ◀──(P5: proved faithful on corpus)── Lean renders OCaml ── ocamlc (trust)
```

| Edge | Object | Proved | Executed | Stated only |
| --- | --- | --- | --- | --- |
| Term → native machine | `Effect.lean`, `Invariant.lean` | 258 theorems: `WF`/`step_wf` over 65 arms, run induction, one-shot, chain discipline, handler in parent, trap survival, both `Unhandled` routes, exit fires one handler, Stdlib corollaries about source terms for the resume family | 15 witnesses × 3 hosts | `Safe` residue: what the program hands `%resume`/`%runstack`/`%reperform` (a decidable `Term` predicate); `deepMatchWith`/`Shallow` prefix |
| native ≈ jsoo discipline | `EffectJsoo.lean` | `rel_start`, `forward`, `backward`, `rows_agree_start` at `propext`/`Quot.sound`, 57/64 arms outright | 15 witnesses on `MachineJ` = jsoo host rows | 7 pairs (`SpecialPairs`), each an exact goal with 2–3 documented attempts; `HypH` excludes 3 executed host divergences |
| Term → Code | `Compile.lean`, `compile/` | 6 theorems (pure fragment) | 35 agreement guards on the witness corpus (Term vs Code vs CPS), 39 dump guards against real jsoo pre-transform IR of 4 witnesses | `compile_correct` for the effect arms; no report (seat stopped) |
| Code → CPS | `Cps.lean`, `CpsProof.lean` | 77 theorems: split_blocks, callback transparency, every emitted shape, the relation `R` incl. dominator half, `KSoundAt` (the FSCD §5 knot) closed, `LookLemmas`, `ScopeAtJump` modulo `DominatorSound` | 3,500-program harness, 0 disagreements; 4 real dumps reproduced | `DominatorSound` (CHK correctness, pure graph theory, decomposition written); the whole-program assembly |
| values | `Value.lean` | — | 215 facts, 38 differ native/jsoo, 34 JS representation probes | — |
| Promise host | `Promise.lean` | — | 11 executed orders; OCaml `Await` resuming from a microtask under jsoo | 3 theorems |
| the avatar | `avatar/` | — | 102/102 + 75/75 golden pairs across 5 families = rc.112 = Lean goldens; 158 adversarial programs 435/435 vs rc.112 after 4 avatar fixes, 12 classified divergences; 40+158 programs byte-identical on 3 hosts | the RunFiber ↔ avatar relation (A3) |
| Lean → OCaml text | `Render.lean`, `Fuzz.lean` | field mangling injective | 13 witnesses + 1,300 fuzzed programs, 0 Lean-vs-host disagreements; 5 Deep carriers render byte-identical to the hand-written avatar; 220-program generated corpus typechecks both sides | — |

Trust boundaries, unchanged: `ocamlc`, `ocamlopt`, js_of_ocaml's `parse_bytecode.ml` and
`generate.ml`, the JavaScript engine, the OCaml runtime's C outside the transcribed arms.

## 2. What the work found (the part that is already useful)

- **js_of_ocaml 5.7.1**: no `caml_drop_continuation` (fuzz shows one *silent* wrong answer);
  `%reperform` drops `last_fiber`; a 2-arg closure has JS `length` 3 under `--enable effects`;
  the constant folder saturates `int_of_float` where emitted code truncates; a `perform` inside a
  callback invoked from JS is `Unhandled`, so JS may enter OCaml only at a fiber boundary.
- **OCaml 5.1.1 runtime**: the continuation `%reperform` takes at the root leaks one-shot in
  native and jsoo (bytecode alone nulls it); resuming a stack already on the running chain makes
  a cycle in the C. Neither is reachable through `Stdlib.Effect`.
- **The Lean Deep machine** (`Effect4/Deep/Fibers.lean`), found by the avatar corpus:
  `Fiber.awaitAll` answers in argument order where `countdownPark` collects in completion order;
  the cross-dispatcher flush order recorded as an assumption at `Fibers.lean:1130` is observable;
  interrupting a `raceAll` host interrupts its entrants in rc.112, the Deep `Race` has settle-time
  cleanup only. Plus `E4-SEM-CE-011` reproduced from an independent implementation.
- **The OCaml workspace** (`effect4_of_ocaml`): `PromiseHostProofs.v` never compiled; its 42
  theorems are statements.

## 3. The paths, priced

**Path B, the avatar becomes Effect4's runtime representation (recommended first).**
The cleanup inventory on the PC names the gap: Deep has no runtime behind the host. The avatar
is that runtime, already at 100% on every golden and on 158 adversarial programs, byte-identical
on three hosts, with a Lean machine (P1) underneath it. What it needs:
1. **A3**: `AvatarRelation.lean`, `RunFiber` ↔ avatar record field by field, `frame.current`/
   `.stack` related through `OCaml5.Machine`, the two-bound shape (command fuel + per-fiber op
   counter) A0 §19 states; `interruptRecord` and `exitFiber` proved to preserve it. P1's table is
   the starting point; P5's generator makes the record side derived rather than typed.
2. **Fix the three Deep gaps** in `Effect4/Deep/Fibers.lean` against rc.112, with the corpus
   programs as the register rows.
3. **A1**: the avatar as a gate face in `check-trace-host.sh`, stamped. Cheapest packet; stops
   the result rotting.
4. **Generate, do not hand-write**: P5 renders the carriers; the remaining hand-written part
   is the handler arms (`RunInterp` as code, divergence 5), which is exactly the part the
   relation has to cover.
Cost: three or four packets. Value: a proved-shape, executed-at-scale runtime representation,
and the Deep bugs fixed.

**Path A, close the theorem chain on the fragment.** `DominatorSound` (P2, decomposition
written), the P2 assembly, the seven P3 pairs, `compile_correct` (P4), the `Safe` residue and
the `deepMatchWith` prefix (P1). Every one is an exact stated goal with attempts recorded.
Cost: one round each for P2/P1/P4, unknown for P3's seven. Value: "proved JS for the effect
fragment" modulo the named compilers. Runs in parallel with B, disjoint files.

**Path C, the lowering targets the avatar.** Effect4's lowering emits OCaml (or TypeScript
that calls the jsoo-compiled avatar) so `Flow → OCaml → jsoo → JS` becomes the deliverable
pipeline, with O3 as the value boundary and P6 as the Promise host. Needs B's relation first,
and a ruling on the target. Value: the actual "verified JS via OCaml" product.

**Path D, landing.** Move `workshop/OCaml5` to its permanent home, contracts, batteries,
register rows, the OCaml5 docs' `workshop/Deep` citations repointed to `Effect4/Deep`. Needed
before any of it is cited by a package; blocks on nothing; no new knowledge.

## 4. Rulings the grill has to take

1. **Home.** Deep was just promoted into `Effect4/Deep`. Does the avatar live beside it
   (`Effect4/Avatar`, an Effect-specific runtime) with only the OCaml5 machine/jsoo model in a
   sibling package, or does everything under `workshop/OCaml5` go to one sibling package?
2. **Is the avatar the runtime representation?** If yes, DESIGN-BASIS and TRACE-DAG gain the
   avatar as the object the `host` edge is stated against, and A3 is the theorem that closes it.
3. **Lowering target.** TypeScript against rc.112 (today), OCaml against the avatar, or both.
4. **Trust boundaries accepted** for the claim: `ocamlc`, `parse_bytecode`, `generate.ml`,
   engine. Or does one of them get its own model next (generate.ml is the smallest).
5. **The three Deep gaps.** Fix Deep to rc.112 now, or record as refusals.
6. **Corpus as gate.** 158 + 220 programs: which become standing gates (stamped) and which stay
   research artefacts.
