# library/effects — lane routing

The Effect-TS host of the store language and one adapter profile of the larger
effectful interface. Semantics flow FROM the Lean estate: interaction and
schema/interop semantics originate in `library/cas`, while stable portable
IDs, canonical bytes, and profile membership belong to the future
language-neutral `library/effect-protocol/` manifest. Generated surfaces here
(`src/cas/generated/` and the future generated effect-protocol bindings) are
byte-gated projections — never authoritative homes (R7: programs are content,
hosts are code). Effect TypeScript is the first host profile, not the protocol
authority and not the only permitted consumer.

## Spec corpus

Indexed with decision record in [docs/SPECS.md](../../docs/SPECS.md).
Binding: [EFFECTS-BACKEND.md](../cas/EFFECTS-BACKEND.md),
[SCHEMA-MATERIALIZATION.md](../cas/SCHEMA-MATERIALIZATION.md).
Distribution and release posture: [PACKAGING.md](PACKAGING.md) (what
the package is as a distributable, what flips at publish time, the
Windows honesty list) and [RELEASING.md](RELEASING.md) (the gate
sequence a release runs).
Active designs touching this lane:
[PLAIN-LANGUAGE](../../.staging/operational-structure/PLAIN-LANGUAGE.md)
(emitter inventory E1–E6),
[INGESTION-HARNESS](../../.staging/operational-structure/INGESTION-HARNESS.md)
(the harness map and program-ingestion path).
The pre-grade [Effect Core v1 packet](../../.staging/effect-core-v1/README.md)
owns the full public-surface/reification study. Its
[reification checklist](../../.staging/effect-core-v1/REIFICATION-CHECKLIST.md)
requires recursive export/member/overload closure, profile-specific proof
rows, and exact TS7 `@effect/tsgo` file-set coverage. Language-service output
is source-hygiene evidence only; it never defines the Lean semantics.
The neutral manifest likewise contains no proof status, source census, LSP
result, or runtime claim. Those facts live in generated sidecars keyed by its
digest. AGENTS files remain authored routers and are never generated from a
sidecar.
Serving plane (how `cas serve` and `cas daemon` are run, secured, and
observed): [SERVING.md](SERVING.md) — Category 1 since decision 32(b),
and it lives here rather than under `docs/lab-core/`; the wire
authority remains [PROFILE-CAS-HTTP-0.md](PROFILE-CAS-HTTP-0.md).

## Lane rules

- Effect 4 idioms to their fullest; code quality and interaction
  semantics are paramount — a tool teaches by use.
- Tests run through the configured runner: `bun run test` (vitest).
  Never bare `bun test` on vitest files.
- Generated files are edited only by their Lean emitters; a hand edit
  to `src/cas/generated/**` is a defect.
- Future generated effect-protocol bindings are edited only through the
  neutral-manifest materializer; a host may not rewrite their IDs or bytes.
- Effect Core work uses the clean packet-baseline/integration and per-slice
  breaker-builder-reviewer worktree protocol in the staged packet. Work begins
  with file stubs only, then a broad surface/profile/edge sweep, and only then
  deepens one proof-closed type row at a time.
- An `ensuring` adapter must preserve the body's resulting state across typed
  error or refusal so cleanup can begin with that state. This state-outside-error
  requirement is an information contract, not a mandated transformer stack;
  ordinary bind or any layout that discards state on error is inadequate.
