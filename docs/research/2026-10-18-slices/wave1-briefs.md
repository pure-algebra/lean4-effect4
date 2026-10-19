# Wave 1: three seat briefs

Coordinator: the main session, 2026-10-18. Base: `refactor/phase1-phase3` at `4a81cc034`. The
plan is [README.md](README.md), amended by its §9 (the owner's rulings after Codex's review). The
review is [codex-review/README.md](codex-review/README.md). Each seat reads both, then its own
section below.

## Rules for every seat

- Work only in your worktree, on your branch. Commit there by explicit paths. Never push, never
  merge. End each commit message with `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- `.lake/packages` is already copied into your worktree. Do not copy it again.
- Run Lean only as `python3 /private/tmp/seams-lean-one.py lake ...` from your worktree. Run dune
  only as `opam exec --switch=effect4 -- dune ...`.
- Never run `lake build Test`, `make build`, `make check-full` or `make gen-semantics`.
- A landing owes three things:
  - the narrow build of the modules it touches, with `make batteries-touched BASE=4a81cc034`;
  - `#axiom_audit` over each touched `src` or `Test` module;
  - `make check-ocaml` when a change reaches OCaml or a generated file.
- Regenerate what you reach:
  - `python3 scripts/generate.py --only <family>` for a generated Lean family;
  - `make gen-lcnf` for the lowered OCaml.

  Commit generated files beside their sources.
- Do not edit `docs/core/decisions.md`, `AGENTS.md` or `lakefile.toml`; propose changes in your
  receipt. `python3 scripts/check-docs.py --fix` also rewrites `decisions.md`; revert that file.
- In proofs, write no `simp_all`, `first |` or `try`. Every warning is an error. Prefer `aesop`
  in `src/Effect4/Laws/**`. Place each new theorem by `AGENTS.md`'s five items.
- Greenfield until release (ruling 1): change a wire shape or a digest when the slice needs it.
  Write no compatibility reader, and say what moved in the receipt.
- Start no subagent. Leave `tools/view/make_videos.py` alone.
- Write your receipt as `docs/research/2026-10-18-slices/receipt-<seat>.md` in your worktree, and
  force-add it with your last commit. It opens with the one thing the coordinator must know
  before merging. Then it gives:
  - the base and head commits;
  - each slice's commit, with the files changed;
  - each command and its result;
  - the axiom output;
  - what moved on the wire;
  - what is open.

Generated files (`ocaml/gen/api_gen.ml`, the derived codecs) will conflict between seats. The
coordinator never merges them by hand: it regenerates them after merging the sources.

## Seat 1: refusals and the method table (`/Users/pooks/Dev/wt-w1-refusals`, branch `seat/w1-refusals`)

**Slice 1a. Located refusals** (plan A1, amended by Codex's R1.1 and ruling 2).
- Add `structure Located (Site Reason : Type)` with `site` and `reason`, `Located.mapSite` and
  `mapSite_comp`, in one small core module. A new core module follows decisions row 200.
- Give the program's refusal the form `Located (List Nat) TypeReason`, and keep churn small.
  A projection may keep the old field name where callers read it.
- Each judgment keeps its own reason alphabet. Do not add a generic `Judgment` record.
- `AddRefusal.notCertified (why : FeedRefusal)`: `FillSetInternal.addEntry` stops discarding the
  feed's refusal.
- `AdmitRefusal.illTyped (why : TypeRefusal)`.
- One relocation rule: the feed answers absolute program addresses (`p ++ q` at the call
  boundary). Remove the second relocation in `Suggest.suggestOne`.
- Split `TypeReason.term` into its causes: an unbound variable, an unknown atom, refused argument
  types, and a literal outside the alphabet. Keep the more specific record, tuple and fold reasons.
- A `rootRefused` refusal, located at the document's root, that names `draft` as the remedy.
- Red control (Codex R1.1): fill `[1]` with `.succeed (.var 1)` where one variable exists. The
  edit route and the pending-fill route must report the same absolute address and the
  unbound-variable reason. A second prefix fails. Signature admission still refuses before
  program typing when both fail.

**Slice 1b. Hole hygiene** (plan A1 and P6, amended by R3.1).
- The document's view lists each declared hole that the program never performs, and each hole's
  exact `perform` term (`Sketch.hole`).
- Suggestions drop the target hole itself, and enclosing programs that only reproduce it.
- No change to `Eff`, `Term` or `Ty` (decisions row 288).
- Red control: with one application row, `external 0` is not hole zero, and the view says so.

**Slice 1c. One method table** (plan C2 and A3, amended by R5.1).
- Generate a finite `MethodKey` from `Action`'s and `Query`'s constructors. Spell the exception
  `open_` → `open` once, at its constructor.
- `methodDescriptor : MethodKey → MethodDescriptor`: name, kind, versions, argument and result
  shapes, description, `readOnly`.
- Descriptions are an exhaustive function of the key. A missing description fails the Lean build,
  with no fallback to an empty string.
- `supportedMethods`, `Request.method` and the names in `Methods.descriptions` become projections
  of the descriptor. Prove `method_name_agrees`, `query_hint` and `hinted_readOnly` (from
  `serve_query`).
- MCP tools:
  - each tool carries `annotations`: `readOnlyHint` from the classification; destructive,
    idempotent and open-world hints set explicitly, never inferred from `serve_query`;
  - each tool carries `outputSchema`: a closed schema of `Wire.Envelope Reply`, the actual
    `structuredContent`;
  - `describe` has its own schema.
- `scripts/check-mcp-protocol.py` validates an enveloped response against the emitted schema. A
  bare-`Reply` schema must fail that check, as a red control.

Files you own: `src/Effect4/Program/Typing/*`, `src/Effect4/Program/Admission.lean`,
`src/Effect4/Tool/*`, their laws and batteries, `ocaml/engine/kit/kit_mcp.ml`,
`scripts/check-mcp-protocol.py`. The `Admission` change reaches many modules: batch 1a's
constructor changes into one build.

## Seat 2: install metadata and model tests (`/Users/pooks/Dev/wt-w1-estate`, branch `seat/w1-estate`)

Read the OCaml probe first: `docs/research/2026-10-18-ocaml-tooling-probe/README.md`, §2.2, §5
(slices 1 and 4), and its `probes/consumer` and `probes/stm`.

**Slice 2a. Install metadata, no release** (plan E1, amended by ruling 4 and R6.2).
- Add packages and `public_name` for `effect4_engine`, `effect4_bytes`, `effect4_engine_cas` and
  `effect4_kit`, and for the `eff` executable.
- Generate the opam files (`generate_opam_files`), declaring `zarith`, `yojson` and `conf-gmp`.
- `dune build @install` installs them into a scratch prefix.
- Add an outside-consumer check, run from `dune test` or a script that `make check-ocaml` runs.
  It is a project outside `ocaml/` that links the installed kit and checks one program. Its red
  control: a test library is not nameable.
- Mark every package unstable in its synopsis. Names may change when seat 3's manifest lands.
- Another seat edits the `modules` line of `ocaml/engine/kit/dune`. Touch only the package lines
  there.

**Slice 2b. Parallel model tests** (plan E2).
- Land `probes/stm/stm_mailbox.ml` as a test of `E4_mailbox`. Keep its two red controls: an
  off-by-one bound, and a mailbox with no lock.
- Then `E4_inbox`, `E4_sched`'s admission, the disk writer, and the native tool session. Each gets
  a model, sequential and parallel runs, and a red control that fails.
- qcheck-stm 0.10 is installed in the switch. Report host-only evidence as such.

Files you own: the `dune` and `dune-project` files under `ocaml/` (package lines only in
`engine/kit/dune`), new test directories under `ocaml/engine/test/`, and new opam files.

## Seat 3: export classes and the name manifest (`/Users/pooks/Dev/wt-w1-names`, branch `seat/w1-names`)

Read Codex's R6.1 and R6.2 in full, and the estate plan's §2.2 and ruling D-11
(`docs/research/2026-10-17-ocaml-estate-review/plan.md`).

**Slice 3a. Typed export classes** (R6.1, step 1).
- Give every root of `ocaml/gen/roots.json` one class: `public`, `linkage`, `coverage` or
  `internal`. Read the recipe into a typed `ExportPlan` in Lean (`src/OCaml5/`).
- The plan checker refuses a root with two contradictory classes. Never resolve one by order.
- Freeze the current public and linkage roots.
- State `facade_resolves` and `public_excludes_coverage` as finite checks of the plan.

**Slice 3b. The public-name manifest** (R6.2, the naming slice).
- `publicName : Lean.Name → Except NameRefusal PublicName`, from the Lean declaration before LCNF
  changes its name:
  - namespace components become modules;
  - a type is `t` in its owner's module;
  - a constructor is capitalized at its owner;
  - an OCaml keyword is escaped by one fixed rule.
- A collision refuses generation and names both Lean declarations. Red control: `aB` and `a_b`.
- Generate the manifest of every public root as a committed, generated file, marked so. An
  append-only check refuses a manifest that moves or drops an earlier public path.
- Generate a public facade module over the closure from the manifest, with type equalities, so a
  client writes `Effect4.Program.Eff.t` and `Effect4.Run.Tree.of_program`.
- Facades are additive: keep today's `Api_gen` names, and do not change `globalName` for existing
  output.
- Check that a project outside `ocaml/` compiles against the facade and cannot name a coverage
  root through it. A sealed package (`Built`, `Prepared`, `Checked`, the tool `Session`) stays
  abstract through every alias.
- Do not start C5 (one shared closure). It is the next wave.

Files you own: `src/OCaml5/**`, `ocaml/gen/roots.json`, the generated manifest and facade, and
their checks.
