# LeanServer adoption record

Status: formal adoption landing, 2026-08-27, operator-directed. The
ratifications this lands were made earlier the same day (workflow §14:
the R1 acceptance ruled LeanServer a first-class differential
conformance peer; the layer-design record's rider adopted it for real
server semantics). This note materializes the adoption: the pinned
clone, the byte-level verification, the claim boundaries, and the
integration roadmap. It makes no conformance claim about LeanServer
and grades none of its theorems.

## Identity and pin

- Repository: <https://github.com/AfonsoBitoque/LeanServer>
- Adopted revision: `24b916aaa6ae4a20732536494904d0699fac7ec7`
  (merge "chore/lean2.29.1") — the same pin the transport-standards
  survey audited and its receipt records
  (`.reference/provenance/receipts/remote-transport-standards-and-lean-models.json`,
  entry `leanserver`).
- License: Apache-2.0 (LICENSE at the pin).
- Toolchain: `leanprover/lean4:v4.29.1` — BEHIND the estate's 4.33.1.
  Consequence: LeanServer runs as an externally built, pinned tool
  under its own toolchain (elan resolves it per its `lean-toolchain`),
  never as an in-tree Lake dependency of the effects package.
- Local materialization: `.reference/clones/leanserver` (gitignored,
  like every study clone). Re-materialize with:
  `git clone <repo> && git checkout 24b916aaa6ae4a20732536494904d0699fac7ec7`.

## Verification at adoption

The receipt pins three audited protocol files by SHA-256 and byte
length. Verified at this landing against the materialized clone —
**at the git blob level**, all three match exactly:

| File | sha256 (blob) | bytes |
| --- | --- | --- |
| `LeanServer/Protocol/GRPC.lean` | `0aa65bca8bd2f4252cc6582bfd4dfc5576ba3c8081070ad8e3a4ad078c8ba1c7` | 9254 |
| `LeanServer/Protocol/HTTP2.lean` | `f16685587f0c5fa7019678c5adc7cd72799b3fa25b9dbd2c8f84086558195bf3` | 59072 |
| `LeanServer/Protocol/WebSocket.lean` | `ed577eec5acb988f09b4413d85bb370f1238194b8d55c1a44c48ef7cf5f9cecd` | 19736 |

Caution recorded for future verifiers on Windows: hashing the WORKING
COPY disagrees for two of the three files because checkout
materializes CRLF; verification must hash the raw blobs
(`git cat-file blob <rev>:<path>`), which is what the table reflects.

## What was adopted, and as what

LeanServer is an executable Lean 4 HTTPS server: TLS 1.3, HTTP/2,
HTTP/3 (QUIC), WebSocket, and gRPC, with its own crypto stack and C
FFI. The project's own README claims ~32,000 lines of Lean, 81
modules, and 935 compiler-checked theorems with zero `sorry`. Those
are the project's claims, reported here with attribution only — see
the claim boundary below.

Two adopted roles, both ratified in the workflow's §14:

1. **Differential conformance peer** (TOOLS.md row): an independent
   executable networking stack run beside the effects adapter in the
   remote conformance suites, differences adjudicated against the
   pinned standards and the Lean model. Suites bind an ABSTRACT peer
   interface (`ConformancePeer`); LeanServer is one binding among
   several, so no suite couples to it.
2. **Real-server-semantics substrate** (layer-design rider): the
   adopted basis for building real server-side realizations for the
   conformance harnesses — planned for absolutely, landing at its own
   slice, not necessarily the current or next one.

## Claim boundary (C5)

- LeanServer is **never a standards oracle**. Agreement with it
  proves nothing by itself; only the pinned standards and the
  estate's own Lean model adjudicate.
- Its theorem count is **not estate evidence**. The transport survey's
  source audit found totality-shaped vacuous propositions
  (`parse_total : ∀ data, True`) and heavy reliance on
  `native_decide`, which sits outside the effects library's accepted
  formal-core proof posture. No gate G0–G6 attaches to any LeanServer
  theorem; anything borrowed from it must be restated and reproved in
  the estate's own judgment.
- The survey's audited implementation gaps are ADOPTED as **named
  detection targets** — the differential suites must detect them, and
  a run in which the divergence goes unnoticed fails (harness docket
  V5). At the pin:
  - gRPC: `grpc-status`/`grpc-message` placed in ordinary response
    headers rather than trailers; message decoder does not require
    exact consumption of the input remainder.
  - HTTP/2: request constructed at the first DATA frame rather than
    the stream's message-completion boundary; DATA/CONTINUATION
    aggregation incomplete; cites superseded RFC 7540.
  - WebSocket: endpoint-role masking, reserved bits, minimal length
    encodings, and the full fragmentation/control-frame state machine
    not enforced; continuation handling loses the message kind.

## Integration roadmap

Its own slice, sequenced by the operator (earliest: after the R2
correction pass). Shape when it lands: build LeanServer with its own
pinned toolchain as an external tool; bind it behind the existing
`ConformancePeer` interface; decide the first wire lane (the
`cas-http/0` profile over its HTTP stack, or a gRPC lane) as a Pass A
question, never a packet-level guess; carry its expected-divergence
list (the detection targets above) in the binding. Runtime admission
for gated use is already in place as the TOOLS.md row; any expansion
of role beyond the two adopted ones is a new ratification.
