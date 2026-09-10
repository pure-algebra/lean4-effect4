# The faces of one `Eff` program

Slice S1b, 2026-09-09 (DI-50). This packet is a **statement of what is claimed and by what
evidence**, not a red battery: every battery it names already exists and none is added here
(v1 DI-50: "cite the batteries that exist; add none"). `docs/DESIGN-MAP.md` §L4 is the prose;
this is the packet the map says the layer lacks.

Evidence words are `docs/DESIGN-MAP.md`'s four, and **several may apply to one claim**
(DI-32): *proved* (a Lean theorem, with its premises), *reproduced* (a gate that regenerates
and compares bytes), *tested* (a golden, differential, property or metamorphic corpus under a
named observer — `tsc` and `#guard` are finite checker runs and count here), *stamped* (a
verifying trace of the inputs a projection was cut from).

---

## 1. The nine faces

One program has nine representations that must agree. Each row says what the face *is*, what
holds it, and where the battery is.

| # | face | what it is | evidence | where |
| --- | --- | --- | --- | --- |
| 1 | the Lean printer | `Api.print` / `Api.printModule`: an `Eff` to one TypeScript expression, or a declaration block with one `const L_<path>` per hoisted layer | proved (§2), tested | `src/Effect4/Codegen/Print.lean`; `Test/Codegen/PrintContract.lean` |
| 2 | the Lean reader | `Api.readModule` / `readEff`: the partial inverse, with a closed refusal alphabet | proved (§2), tested | `src/Effect4/Codegen/Read.lean`; `Test/Codegen/ReadContract.lean`, `Test/Codegen/ReadAxiomReport.lean` |
| 3 | the TypeScript printer-image reader | `ts/eff/read.ts`: a third implementation of face 2's relation, in the target language | tested (byte equality against Lean-cut oracles over the generated corpus), reproduced (its head union is generated, so `tsc` holds head coverage) | `ts/eff/read.ts`, `ts/eff/check.ts`; `ts/eff/test/read.test.ts`, `tables.test.ts`; `scripts/check-ts-eff-corpus.sh` |
| 4 | the foreign recognizer `ck` | `ts/eff/ingest/ck.ts` over the TypeScript compiler API: an island recognizer of a sub-language of rc.112 | tested (agreement with face 5; equality with Lean where an oracle exists) | `ts/eff/ingest/ck.ts`; `ts/eff/ingest/test/foreign.test.ts`, `gate.test.ts`, `refusals.test.ts` |
| 5 | the foreign recognizer `oxc` | `ts/eff/ingest/oxc.ts` over oxc 0.147.0, sharing **no** recognition code with face 4 | tested (the same) | `ts/eff/ingest/oxc.ts`; the same batteries |
| 6 | the canonical wire | the byte encoding of a program, in three implementations: `Effect4.Program.Wire`, `ts/eff/wire.gen.ts`, `ocaml/eff/eff_wire.ml` | proved (`decode_encode`, `decode_exact`, `encode_injective`), reproduced (goldens), tested | `src/Effect4/Program/Wire.lean`; `ocaml/goldens/eff`; `ts/eff/test/wire.test.ts`, `ocaml/eff/test/test_lean_wire.ml`, `prop_wire.ml` |
| 7 | the JSON projection | the same program as JSON, in three implementations: `OCaml5.Eff.effV.json`, `ts/eff/json.gen.ts`, `ocaml/eff/eff_json.ml` | reproduced (byte comparison against the Lean-cut oracle), tested | `src/OCaml5/Eff/Goldens.lean`; `ts/eff/json.gen.ts`; `ocaml/eff/test/test_eff.ml` |
| 8 | the executed image on rc.112 | the truth harness: the printed module *run* under the pinned host, its exit and observable schedule compared with the Lean machine's | tested (a bounded differential over a frozen corpus), reproduced (the gate regenerates the modules, the result and the tapes and compares bytes), stamped | `harness/truth/`; `scripts/check-truth.py`; the `#guard`s of `harness/truth/Truth.lean` |
| 9 | the OCaml conformance face | `ocaml/eff`: a second implementation of the families, the wire, the JSON and the typing, checked against goldens the Lean side cuts | reproduced (goldens), tested (`dune-tests`), stamped | `ocaml/eff/`; `bash scripts/check-ocaml.sh dune-tests`; `src/OCaml5/Tools/EffGen.lean` |

**Not a face of this layer.** The runtime coverage census is the traceability matrix for
rc.112's runtime, not a representation of an `Eff` program (`docs/DESIGN-MAP.md` §L4).

---

## 2. The two round-trip laws, with their side conditions

Both are theorems in `src/Effect4/Codegen/Read.lean`, and both carry premises that are part of
the claim.

**Law R1 — a readable program that prints comes back as itself.**

```
read_print (hl : LawfulSpelling sig spell) (e : Eff Op)
  (hr : readable sig spell n e = true) (hp : print sig n e = .ok x)
  : readEff sig spell n x = .ok e                                    -- Read.lean:1692
roundTrip_eq … : roundTrip sig spell n e = .ok e                     -- Read.lean:3032
read_print_native (table) (h : LawfulTable table = true) …           -- Read.lean:3024
```

Side conditions, each of which is a real restriction:

1. `LawfulSpelling sig spell` — the signature's spellings invert. For the native profile it is
   discharged by `nativeLawful table h` from `LawfulTable table = true`, decided.
2. `readable sig spell n e = true` — **the program must be in the reader's image.**
   `readable` is *print reconstruction*, not executable validity: a program can be well typed,
   admitted and runnable and still not readable (`pAwait` is the standing example — settlement
   v2 R2c). This is why the law is not "every program round-trips".
3. `print sig n e = .ok x` — the printer may refuse (§5.1's refused row of `Print.lean`).
4. `n` is the environment length; the law is stated at every `n`, not only at 0.

**Law R2 — what the reader accepts prints back to exactly the tree it read.**

```
read_exact (hl : LawfulSpelling sig spell) (h : readEff sig spell n x = .ok e)
  : print sig n e = .ok x                                            -- Read.lean:2829
read_exact_native (table) (ht : LawfulTable table = true) …          -- Read.lean:3038
```

Side condition: the same `LawfulSpelling`. R2 needs no `readable` premise — acceptance by the
reader is itself the hypothesis. Together R1 and R2 make printer and reader a **partial
isomorphism**, not a bijection: the domain of R1 is `readable`, the domain of R2 is the
reader's acceptance, and neither is all of `Eff`.

**What the round trip does not say.** Nothing about faces 3–5: the TypeScript reader and the
two foreign engines implement the same relation but are held by byte comparison and mutual
agreement, not by these theorems.

---

## 3. The two ingest contracts, and the inclusion property

The printed image and the foreign language are read by **different contracts**, and the
difference is a ruling, not an implementation detail (DI-37). The two differ on exactly three
axes:

| axis | the printed contract (`readPrintedSource`) | the foreign contract (`recognizeSource`) |
| --- | --- | --- |
| the admitted language | exactly what `Api.print` emits: one expression, the reserved heads, the row spellings, the pure atoms | a sub-language of rc.112 as people write it, including spellings the printer never emits and excluding shapes it does |
| the refusal discipline | a printed module that does not read is a **defect of the printer or the reader** and fails the gate | a refusal is an ordinary verdict with a code from a closed, exhaustive, injectively coded taxonomy (`src/Effect4/Ingest/Taxonomy.lean`), and the two engines must agree on it |
| the service-key numbering | the ordinals Lean minted, carried through the printed `Context.Service<T>("k<name>_<service>")` | renumbered from 4 in first-seen order (`ck.ts` and `oxc.ts`, `this.keys.length + 4`) |

**The inclusion property.** *The printed image is a sub-language of the foreign one*: every
printed module the foreign contract admits lifts to the program the printed oracle names, **up
to the service-key renumbering**. Checked by `bun ts/eff/ingest/check-corpus.ts inclusion
<printed corpus>`, wired into `bash scripts/check-ingest.sh`: each printed expression is
wrapped in the `effect` import header and one `export const main`, recognized by both engines,
and its lift compared with the printed oracle after canonically renumbering every
`{name,service}` key node on both sides. A module that lifts to a *different* program is a
contradiction and fails; a module the foreign contract refuses is counted and named by its
code, because the two contracts differ on the admitted language by design — that count is the
measurement the mode publishes. Evidence: tested.

---

## 4. The truth claim, and its quantifiers

The claim held by face 8 is bounded on five axes, and every one of them is part of it
(DI-23; the same text is in `harness/truth/Truth.lean`'s tape section).

1. **Single-fiber.** A tape is the list of package-row completions rc.112 gave one program on
   one run, consumed in file order. It is a faithful oracle only while every row of a program
   is made by one fiber. Every fixture with a tape is single-fiber; there is no fork-using
   host fixture. The first one inherits multi-fiber consumption order as a **named
   obligation**, not an extension: rows would have to be selected per fiber, and nothing in
   the harness detects a violation.
2. **`compareSchedules` is untouched by tapes.** The compared schedule is
   `started`/`forked`/`parked`/`resumed`/`ran`/`exited` over fiber indices in first-seen
   order, and is not a function of the tape. A tape decides what a row answered, never when a
   fiber ran.
3. **A pinned host.** `effect@4.0.0-rc.112` and `@effect/sql-sqlite-bun@4.0.0-rc.112` on bun;
   `scripts/check-truth.py` refuses to run without them. The claim is about those bytes.
4. **24 programs, 6 tapes.** The corpus is frozen and listed in `harness/truth/Truth.lean`;
   six programs perform package rows and have tapes. The gate re-records all six on every run
   and refuses a byte that moved, so a committed tape is the answer rc.112 just gave.
5. **It is a differential, not a bisimulation.** Exits are compared exactly for a success
   value and a `fail` payload, and by kind for a `die` and an `interrupt`; schedules are
   compared row by row with `scheduled` rows dropped on both faces. Nothing here claims
   denotational equivalence for all programs.

Since DI-59 a sixth quantifier is worth stating with them: **one error value.** A row whose
declared error column is the DB-15 pair projects at the adapter, before the printed program
sees it, so the value a printed handler observes, the value on the tape and the value the Lean
machine replays are one value (`harness/truth/prelude.ts` `toPair`; the recorder's
`taggedPair` is the same function).

---

## 5. The `ocaml/eff` conformance relation

`ocaml/eff` is not a second semantics; it is a **conformance suite** for the data faces.
Precisely, for each of the families the closed world names:

- **structure**: the OCaml types are generated from `OCaml5.Eff.World`, so a constructor or a
  field that moves in Lean moves there or the generator refuses;
- **bytes**: `eff_wire.ml` must produce the bytes `Effect4.Program.Wire` produces, on the
  goldens `src/OCaml5/Tools/EffWire.lean` cuts (`ocaml/goldens/eff`), and must decode them
  back exactly;
- **JSON**: `eff_json.ml` must produce the bytes `OCaml5.Eff.effV.json` produces;
- **typing**: `eff_typing.ml` is hand-written and must agree with `effTy` on the corpus it is
  given; it is the one part of the OCaml face that is not generated, and it is where the two
  typing faces can only be compared by goldens;
- **reachability**: the generator refuses to write when the corpus fails to reach a
  constructor (`src/OCaml5/Tools/EffGen.lean`), which is the acceptance model DI-19 asks the
  OCaml engine's own test to follow.

Evidence: reproduced (the goldens, byte for byte) and tested (`bash scripts/check-ocaml.sh
dune-tests`); never proved — no theorem relates an OCaml function to a Lean one.

---

## 6. Non-guarantees this packet does not remove

- No contract packet covers the printer, either reader, the ingest or the OCaml face; this one
  states the claims and cites their batteries, which is not the same as a red battery per law.
- A program with a non-empty Lean requirement row prints untyped (DI-24). Measured 2026-09-09:
  the four sqlite truth programs are in that class in Lean and yet have `R = never` on rc.112,
  because `effTy`'s `.scoped` arm passes the requirement row through while rc.112's
  `Effect.scoped` is `Exclude<R, Scope>`.
- The refusal taxonomy's classification is a function of rule order rather than of the input
  (DI-48).
- The printed image is type-checked only for the truth corpus (DI-49,
  `harness/truth/tsconfig.json`); the generated printed corpus is executed and parsed but not
  type-checked, and it is deliberately not all well typed (152 of 400).
