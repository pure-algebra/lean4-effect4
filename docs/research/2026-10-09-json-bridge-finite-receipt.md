# The JSON bridge above 2^1024 — receipt, 2026-10-09

Base `c4b6b795` (`refactor/phase1-phase3`), branch `claude/json-bridge-exact`. Finding F1 of
`docs/research/2026-10-09-mcp-code-mode-design.md` (seat MCP, probe MCP-2).

## The defect

`binary64OfNat` writes the biased exponent `1023 + e` into the pattern without a bound, so from
2^1024 up it leaves its eleven bits: 2^1024 gets `+Infinity`'s pattern `0x7FF0000000000000`, and
2^2048 gets `-1.0`'s `0xBFF0000000000000`. `natCandidate` divides the whole word by 2^52, sign bit
included, so it read those patterns back as 2^1024 and 2^2048. `natOfBinary64` checked only that
round trip, so the session tool's bridge (`Tools.JsonBridge.ofLeanJson`) admitted both naturals,
and the reader read the number `-1.0` as the natural 2^2048. The docstring of `binary64OfNat`
("truncates toward zero above 2^53") was false above 2^1024.

## Placement (written before the proof)

- Concept `exact-codecs`; claim `json-read-exact` (role compatibility, pointer
  `Canonical.ofJson_exact`); requirement R14.
- `natOfBinary64_finite`, a step of the claim: whatever `natOfBinary64` reads is a non-negative
  finite binary64 pattern (below `binary64Infinity`), and its natural is below 2^1024.
  `natCandidate_lt` is its step. Reach: every `UInt64`. Consumer: `Tools.JsonBridge.ofLeanJson_num`,
  so the session tool (`Tools.Session.programFrom?`) and the MCP face.
- Not established: the retraction, that every natural binary64 holds exactly reads back. The
  claim leaves the round trip out, and `JsonNumber.lean` names that theorem as owed. Nothing of
  how a host parses the datum's text.

## The change

- `src/Effect4/Data/JsonNumber.lean`: `binary64Infinity` (`0x7FF0000000000000`); the docstrings of
  the module and of `binary64OfNat` state the domain: a binary64 datum only below 2^1024, exact
  for at most 53 significant bits (every natural up to 2^53), truncated toward zero otherwise,
  and no binary64 of the natural from 2^1024 up.
- `src/Effect4/Store/Domain/ShapeRead.lean`: `natOfBinary64` reads only a pattern below
  `binary64Infinity`; its docstring states its domain and the MCP face's profile (naturals up to
  2^53).
- `src/Effect4/Laws/Store/ShapeRead.lean`: the placement bullet, `natCandidate_lt`,
  `natOfBinary64_finite`; `natOfBinary64_exact` takes the second conjunct.
- `tools/Tools/JsonBridge.lean`: `ofLeanJson_num` now also gives the datum's finiteness and the
  bound; the module docstring says the bridge refuses a natural from 2^1024 up.
- `Test/Program/JsonFormControls.lean`: controls (the two patterns, both refused) and the
  profile's top, 2^53, read back.

## Commands and results

| Command | Result |
| --- | --- |
| `scratch/lean-slot.sh lake build Effect4.Data.JsonNumber Effect4.Store.Domain.ShapeRead Effect4.Laws.Store.ShapeRead Tools.JsonBridge Tools.Session Test.Program.JsonFormControls Test.Audit.LandingPlanControls` | green, 914 jobs |
| `#print axioms` (scratch) | `natOfBinary64_finite`, `natCandidate_lt`, `Canonical.ofJson_exact`: `[propext, Quot.sound]`; `natOfBinary64_exact`: none. `ofLeanJson_num` reaches `Classical.choice`, as `ofLeanJson` itself already did (Lean's JSON types); `Tools.*` is outside the gate's audit |
| `lake env lean docs/research/2026-10-09-mcp-code-mode/JsonBridgeProbe.lean` | before (`JsonBridgeProbe.out.txt`): `none true true true (some true) false`; after: `none true false false none false` — 2^1024 and 2^2048 are refused, 2^53 + 2 is still admitted, `-1` still refused |

The probe is a finite probe. The design note's F1 row and the MCP-1 probe's comment about
non-finite patterns describe the tree before this commit.
