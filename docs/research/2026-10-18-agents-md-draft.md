# AGENTS.md, one page: a draft for the owner

Status: draft for the owner's review. The live `AGENTS.md` is unchanged until the owner approves.

The current file is 320 lines, plus an 845-line writing rulebook. It lists procedures and gates
and never states the abstractions the work must serve. This draft leads with the abstractions,
then keeps only the rules that protect them. Everything it drops stays findable in the authority
documents it points to.

---

# Effect4 — agent rules

Effect4 is a verified, agent-first platform for authoring and running programs. An agent writes a
program as data, checks it, runs it and stores it. Every answer it gets is defined once in Lean.

## The core abstractions

Each abstraction has one owner. New work deepens one of them or it does not land.

| Abstraction | Owner | Its law |
| --- | --- | --- |
| `Eff`: the one program, as first-order data | `src/Effect4/Program` | one free object per sort (`Eff`, `Ty`, `Term`, `Val`); every traversal is a fold |
| The machine: what a program does | `src/Effect4/Machine`, `src/Effect4/Run` | a run is its journal; replaying the journal gives the run (`replay_unique`) |
| `Canonical α`: data as bytes | `src/Effect4/Store/Domain` | write, then read, gives the value back; a read accepts only the canonical print (exact embedding) |
| The store: content-addressed nodes | `Store/Domain/Cas.lean` | commits are atomic; nodes only grow; a head moves only from the head it names; one result per query |
| The checker: `Check.run`, `Oracle`, `Memo` | `src/Effect4/Program/Check.lean` | every oracle equals `run`; a memo changes cost, never an answer |
| The document, fills and runs | `Program/Typing/SourceDocument.lean`, `FillSet.lean`, `src/Effect4/Live` | a document is its origin and accepted actions; fills are certified at one snapshot |
| The tool: `Tool.serve` | `src/Effect4/Tool` | requests and replies are data; an accepted action appends once; a refusal or a query changes nothing |
| Faces: the Lean driver, the native shell, the TypeScript face | `tools/Drivers`, `ocaml/`, `ts/` | a face owns only text and IO; its semantics is generated from Lean, never copied by hand |

## How to build well here

- **One owner per fact.** A second copy of a rule, a list or a table is a defect. Derive it, or delete it.
- **Make illegal states unrepresentable.** Seal a checked value: a private constructor and a proof field in Lean, an abstract type in OCaml.
- **Refusals are values.** Each one names where and why. A cache miss, fuel exhaustion and an unanswered choice are not refusals.
- **Persist accepted actions, never derived state.** Loading replays them through the one interpreter.
- **Deep modules.** Give each module a small interface over a lot of function. Delete pass-through wrappers.
- **Build in parallel, then cut.** A new representation lands beside the old one with its agreement theorem. Then the callers move, and the old one is deleted in the same push.
- **Hold to the literature.** Name the construction you transcribe and its source. An Effect behaviour cites its line in `vendor/`.

## Hard rules

- **Trust:**
  - Never use `partial`, `unsafe`, `native_decide`, `axiom`, `extern` or `implemented_by`.
  - `sorry` appears only as a planned goal (`proof_goal`).
  - Every declaration audits at `[propext, Quot.sound]`.
  - Every warning is an error.
- **Proofs:**
  - Write no `simp_all`, `first |` or `try`; a hand `simp` is `simp only [...]`.
  - Search with `aesop` in `Laws`.
  - A theorem names its claim and its consumer before it is worked (`docs/core/semantics.md`).
- **Landing:**
  - Run the narrow build of the touched modules.
  - Run `#axiom_audit` over them.
  - Run the one behaviour gate the change reaches: `check-ocaml` or `check-ts`.
  - Nothing else: no `lake build Test`, `make build`, `make check-full` or `make gen-semantics` unless the owner asks.
- **Builds:**
  - Run Lean through `python3 /private/tmp/seams-lean-one.py`, which allows one build per worktree.
  - Run OCaml through `opam exec --switch=effect4`.
  - Run TypeScript through tsgo 7 only.
- **Git:**
  - Commit by explicit paths.
  - Add `docs/research` with `-f`.
  - Never push or merge without the owner.
- **Coordinator's files:** `docs/core/decisions.md` and `lakefile.toml`. An agent proposes a row in its receipt instead.

## Where things are

| Need | Read |
| --- | --- |
| What is true at HEAD, what is next | `docs/STATE.md`, `make status` |
| The layers and requirements R1–R14 | `docs/core/system-map.md` |
| The judgments and their properties | `docs/core/semantics.md` |
| Open decisions | `docs/core/decisions.md`, `docs/DESIGN-ISSUES.md` |
| The source tree and its boundaries | `docs/ARCHITECTURE.md` |
| Generated files and their producers | `docs/GENERATED.md` |
| The OCaml estate | `ocaml/README.md`, `ocaml/STANDARDS.md` |
| Writing rules for documents | `docs/core/controlled-english.md` |

Write plainly. Use one idea per sentence and the active voice. Back every number with a command.
