# Remote transport standards and Lean models

Status: conception research (G0), 2026-08-27. This report records the
standards/source ledger, transport obligations, bounded Lean prior-art survey,
and an unratified conformance architecture. It does not claim that the effects
implementation, a host transport, or any Lean model conforms to these
standards. Any such claim remains pending an exact judgment, implementation
refinement, and conformance evidence.

The transport question is narrower than CAS correctness. A conforming HTTP,
gRPC, SSE, or WebSocket exchange can still return the wrong bytes, stale
metadata, or a false statement about remote durability. Conversely, a CAS
address check does not establish that redirect credentials, retry semantics,
message framing, or stream termination were handled correctly. The remote
boundary therefore needs two explicit admissions:

1. **Transport completion:** the selected transport says that one response,
   RPC, event, or message completed without a framing or protocol failure.
2. **CAS admission:** the completed application payload passes the canonical
   decoding, address recomputation, and store/replay checks required by the CAS
   contract.

Only the second admission may produce a trusted CAS value. Protocol validators,
HTTP entity tags, digest fields, gRPC statuses, SSE event IDs, and WebSocket
message boundaries are inputs to that decision, not substitutes for it.

## Executive finding

Generic conformance theorems are feasible, but the reusable theorem boundary
is not “the server implements HTTP.” It is a relational refinement from a
versioned protocol trace into the existing remote-CAS command/event machine.
The recommended stack is:

```text
real client and hostile/ordinary server
  -> raw versioned transcript
  -> protocol adapter and validator
  -> normalized operation observations
  -> Effects.Remote machine
  -> canonical decode, address verification, and CAS admission
```

The bounded Lean search found reusable labeled-transition-system and weak-trace
machinery, and usable Lean runtime implementations, but no package combining
current HTTP, gRPC, SSE, and WebSocket semantics, concurrent server/failure
dynamics, refinement theorems, and a proved bridge to a real transport. The
protocol-specific models and the adapter relations therefore remain Foldlab
obligations. This is an absence result only for the named repositories and
search routes in this report, not a claim about all Lean code.

For the product design, HTTP and gRPC are the natural CAS data planes. SSE and
WebSocket are better defaults for advisory invalidation, progress, and
availability notifications. Either can carry CAS bytes, but neither provides
operation acknowledgements, durable replay, deduplication, or CAS admission;
an application subprotocol would have to supply and test those semantics.

The current working-tree remote model is already on the right side of one
important boundary: `OpId` is a logical client-assigned identifier and
`MachineState.inFlight` is a map, so concurrent operations are not identified
by fiber, connection, or HTTP/2 stream identity. Future retry work needs a
separate attempt identity and explicit processing evidence; it should not
repurpose `OpId`.

## Standards and source ledger

### Pin policy and standing

RFC Editor publications are immutable numbered editions; their RFC number and
publication date are the source pin. The WHATWG HTML Standard is a living
standard, so both the rendered section and an exact repository commit are
recorded. gRPC's protocol documents and proposals are project specifications,
not IETF standards, so exact repository commits and each proposal's stated
status are recorded. JSON-RPC 2.0 is a working-group specification rather than
an IETF standard; the fetched representation is therefore content-hashed.

Unless a row says otherwise, RFC text is published by the IETF Trust under the
[IETF Trust Legal Provisions](https://trustee.ietf.org/documents/trust-legal-provisions/)
and has the standards-track standing shown in the RFC header. The ledger uses
only the official RFC Editor, WHATWG, gRPC, and JSON-RPC sources.

| Pin | Standing and license | Normative sections used here | Relevance to a remote CAS client |
|---|---|---|---|
| [RFC 9110, *HTTP Semantics*](https://www.rfc-editor.org/rfc/rfc9110.html), June 2022 | Internet Standard, STD 97; IETF Trust | [§§4.2–4.3](https://www.rfc-editor.org/rfc/rfc9110.html#section-4.2), [§8.6](https://www.rfc-editor.org/rfc/rfc9110.html#section-8.6), [§8.8](https://www.rfc-editor.org/rfc/rfc9110.html#section-8.8), [§9.2](https://www.rfc-editor.org/rfc/rfc9110.html#section-9.2), [§10.2.3](https://www.rfc-editor.org/rfc/rfc9110.html#section-10.2.3), [§11](https://www.rfc-editor.org/rfc/rfc9110.html#section-11), [§13](https://www.rfc-editor.org/rfc/rfc9110.html#section-13), [§14](https://www.rfc-editor.org/rfc/rfc9110.html#section-14), [§15](https://www.rfc-editor.org/rfc/rfc9110.html#section-15) | Common HTTP semantics: origin and authority, representation metadata, safety/idempotency, authentication, conditionals, ranges, redirects, and status codes. Applies across HTTP/1.1, HTTP/2, and HTTP/3. |
| [RFC 9111, *HTTP Caching*](https://www.rfc-editor.org/rfc/rfc9111.html), June 2022 | Internet Standard, STD 98; IETF Trust | [§§3–5](https://www.rfc-editor.org/rfc/rfc9111.html#section-3) | Storage eligibility, incomplete responses, freshness, validation, authenticated responses, `Vary`, `Age`, and cache-control directives. |
| [RFC 9112, *HTTP/1.1*](https://www.rfc-editor.org/rfc/rfc9112.html), June 2022, as updated by RFC 9931 | Internet Standard, STD 99; IETF Trust | [§2](https://www.rfc-editor.org/rfc/rfc9112.html#section-2), [§§6–9](https://www.rfc-editor.org/rfc/rfc9112.html#section-6), [§11](https://www.rfc-editor.org/rfc/rfc9112.html#section-11) | HTTP/1.1 octet parsing, content-length and transfer-coding precedence, completeness, connection reuse, and message-smuggling defenses. |
| [RFC 9931, *Security Considerations for Optimistic Protocol Transitions in HTTP/1.1*](https://www.rfc-editor.org/rfc/rfc9931.html), March 2026 | Standards Track; updates RFC 9112 and RFC 9298; IETF Trust | [§6.2](https://www.rfc-editor.org/rfc/rfc9931.html#section-6.2), [§7](https://www.rfc-editor.org/rfc/rfc9931.html#section-7), [§8](https://www.rfc-editor.org/rfc/rfc9931.html#section-8) | Current prohibition and security treatment for optimistic bytes during protocol upgrades and proxy `CONNECT`; material to WebSocket handshakes. |
| [RFC 9113, *HTTP/2*](https://www.rfc-editor.org/rfc/rfc9113.html), June 2022 | Standards Track; IETF Trust | [§§4–8](https://www.rfc-editor.org/rfc/rfc9113.html#section-4), [§10](https://www.rfc-editor.org/rfc/rfc9113.html#section-10) | Stream/message framing, flow control, resets, `GOAWAY`, malformed messages, connection errors, and retry-relevant processing boundaries. |
| [RFC 9114, *HTTP/3*](https://www.rfc-editor.org/rfc/rfc9114.html), June 2022 | Standards Track; IETF Trust | [§§3–8](https://www.rfc-editor.org/rfc/rfc9114.html#section-3) | HTTP over QUIC streams, stream termination, cancellation, request rejection, `GOAWAY`, field compression, and HTTP/3 error scope. |
| [RFC 8470, *Using Early Data in HTTP*](https://www.rfc-editor.org/rfc/rfc8470.html), September 2018 | Standards Track; IETF Trust | [§5.1](https://www.rfc-editor.org/rfc/rfc8470.html#section-5.1), [§5.2](https://www.rfc-editor.org/rfc/rfc8470.html#section-5.2) | `425 Too Early`, replay exposure, and the rule that a retry after `425` is not sent in early data. |
| [RFC 9530, *Digest Fields*](https://www.rfc-editor.org/rfc/rfc9530.html), February 2024 | Standards Track; obsoletes RFC 3230; IETF Trust | [§§2–6](https://www.rfc-editor.org/rfc/rfc9530.html#section-2) | `Content-Digest`, `Repr-Digest`, request negotiation fields, partial representations, and integrity/security limitations. |
| [RFC 9457, *Problem Details for HTTP APIs*](https://www.rfc-editor.org/rfc/rfc9457.html), July 2023 | Standards Track; obsoletes RFC 7807; IETF Trust | [§§3–5](https://www.rfc-editor.org/rfc/rfc9457.html#section-3) | Typed HTTP problem responses, extension handling, status duplication, and disclosure cautions. |
| [RFC 6455, *The WebSocket Protocol*](https://www.rfc-editor.org/rfc/rfc6455.html), December 2011 | Standards Track; updated by RFCs 7936, 8307, and 8441; IETF Trust | [§§4–7](https://www.rfc-editor.org/rfc/rfc6455.html#section-4), [§§9–10](https://www.rfc-editor.org/rfc/rfc6455.html#section-9) | HTTP/1.1 opening handshake, masking, frame grammar, fragmentation, control frames, closing, extensions, origin/security checks, and implementation limits. |
| [RFC 7692, *Compression Extensions for WebSocket*](https://www.rfc-editor.org/rfc/rfc7692.html), December 2015 | Standards Track; IETF Trust | [§§4–8](https://www.rfc-editor.org/rfc/rfc7692.html#section-4) | `permessage-deflate` negotiation, RSV1 use, window/context parameters, decompression, and compression security. |
| [RFC 7936, *Clarifying Registry Procedures for the WebSocket Subprotocol Name Registry*](https://www.rfc-editor.org/rfc/rfc7936.html), July 2016 | Standards Track; updates RFC 6455; IETF Trust | [§2](https://www.rfc-editor.org/rfc/rfc7936.html#section-2) | Confirms that WebSocket subprotocol identifiers are case-sensitive and updates registry procedure. |
| [RFC 8307, *Well-Known URIs for the WebSocket Protocol*](https://www.rfc-editor.org/rfc/rfc8307.html), January 2018 | Standards Track; updates RFC 6455; IETF Trust | [§§3–4](https://www.rfc-editor.org/rfc/rfc8307.html#section-3) | Optional `/.well-known/` discovery for `ws` and `wss`; relevant only if CAS endpoint discovery adopts it. |
| [RFC 8441, *Bootstrapping WebSockets with HTTP/2*](https://www.rfc-editor.org/rfc/rfc8441.html), September 2018 | Standards Track; updates RFC 6455; IETF Trust | [§§3–5](https://www.rfc-editor.org/rfc/rfc8441.html#section-3) | Extended `CONNECT`, enablement setting, HTTP/2-specific handshake fields, and mapping of WebSocket framing to an HTTP/2 stream. |
| [RFC 9220, *Bootstrapping WebSockets with HTTP/3*](https://www.rfc-editor.org/rfc/rfc9220.html), June 2022 | Standards Track; IETF Trust | [§§2–4](https://www.rfc-editor.org/rfc/rfc9220.html#section-2) | HTTP/3 enablement and extended `CONNECT` mapping, including QUIC stream closure and reset behavior. |
| [WHATWG HTML, *Server-sent events* §§9.2.2–9.2.6](https://html.spec.whatwg.org/multipage/server-sent-events.html#server-sent-events), rendered 2026-08-27; source pin [`whatwg/html@9ead9de8f6751ccb98e91972e580ed6e3314c64a`](https://github.com/whatwg/html/tree/9ead9de8f6751ccb98e91972e580ed6e3314c64a) | WHATWG Living Standard. Text licensed CC BY 4.0; source-code portions BSD-3-Clause, per the pinned repository `LICENSE`. | [EventSource processing model](https://html.spec.whatwg.org/multipage/server-sent-events.html#the-eventsource-interface), [parsing](https://html.spec.whatwg.org/multipage/server-sent-events.html#parsing-an-event-stream), [interpretation](https://html.spec.whatwg.org/multipage/server-sent-events.html#interpreting-an-event-stream) | Fetch mode, credentials, status/media-type checks, reconnection, `Last-Event-ID`, UTF-8 event-stream parsing, event dispatch, and terminal `204`. |
| gRPC [`PROTOCOL-HTTP2.md`](https://github.com/grpc/grpc/blob/7ef6a9efc3a1518d838dfb250cffe520a59185ac/doc/PROTOCOL-HTTP2.md), [`http-grpc-status-mapping.md`](https://github.com/grpc/grpc/blob/7ef6a9efc3a1518d838dfb250cffe520a59185ac/doc/http-grpc-status-mapping.md), and [`connection-backoff.md`](https://github.com/grpc/grpc/blob/7ef6a9efc3a1518d838dfb250cffe520a59185ac/doc/connection-backoff.md), pin `grpc/grpc@7ef6a9efc3a1518d838dfb250cffe520a59185ac`, 2026-08-27 | Official gRPC project protocol documents, Apache-2.0; project specification, not an IETF standard | Request/response grammar, length-prefixed messages, compression, trailers and statuses, HTTP fallback mapping, reset mapping, and connection backoff | Defines the actual gRPC-over-HTTP/2 envelope and distinguishes HTTP status from final gRPC status. |
| gRPC proposal [`A6-client-retries.md`](https://github.com/grpc/proposal/blob/59404cb421b52ecc563dfe51db3917aaa5ced410/A6-client-retries.md), pin `grpc/proposal@59404cb421b52ecc563dfe51db3917aaa5ced410`, last updated 2024-08-23 | Official gRPC design proposal, status **Implemented**, Apache-2.0; project specification | Retry commitment, transparent and configured retries, throttling, pushback, deadline, buffering, backoff, and attempt accounting | Normative design basis for distinguishing reconnect, call retry, and retry suppression after commitment. |
| gRPC proposal [`G2-http3-protocol.md`](https://github.com/grpc/proposal/blob/59404cb421b52ecc563dfe51db3917aaa5ced410/G2-http3-protocol.md), same repository pin, last updated 2021-08-25 | Official gRPC design proposal, status **Implemented: grpc-dotnet**, Apache-2.0; project specification with narrower implementation standing than the HTTP/2 protocol document | gRPC mapping to HTTP/3 and HTTP/3 error translation | Candidate HTTP/3 gRPC lane. RFC 9114 remains authoritative where the proposal references an older HTTP/3 draft. |
| [JSON-RPC 2.0 Specification](https://www.jsonrpc.org/specification), published 2010-03-26, updated 2013-01-04; fetched 2026-08-27; response-body SHA-256 `8fe1edfdca511d309e712e47447457ea5159b728ec02071a84593aed692aefeb` | JSON-RPC Working Group specification; grants implementation and verbatim copying/commentary with retained copyright notice; not an IETF standard | §§4–7: request, notification, response, error, and batch objects | Transport-neutral request/response correlation and batch behavior. It does not define HTTP status mapping, retry safety, authentication, streaming, or CAS error meanings. |

### Source-use cautions

- HTTP semantics are common, but framing and retry evidence are not. HTTP/1.1
  connection closure, HTTP/2 `END_STREAM`/`RST_STREAM`/`GOAWAY`, and HTTP/3
  QUIC stream completion/error codes must remain separate conformance lanes.
- The WHATWG pin freezes the researched text. An implementation that claims
  conformance to a later living-standard snapshot needs a new pin and delta
  review.
- gRPC repository documents are the project's protocol contract. They do not
  raise gRPC itself to IETF-standard standing, and `G2-http3-protocol.md` has a
  narrower implementation-status claim than the HTTP/2 protocol document.
- JSON-RPC is transport agnostic. HTTP, WebSocket, or another carrier does not
  acquire retry, authentication, or streaming semantics merely by carrying a
  JSON-RPC envelope.

## Transport obligations

### Common HTTP semantics

#### Authority, TLS identity, redirects, and credentials

[RFC 9110 §4.3](https://www.rfc-editor.org/rfc/rfc9110.html#section-4.3)
defines an origin from scheme, host, and port. The CAS client should carry that
authority, plus any application namespace or tenant, in its operation identity;
an ambient base URL is insufficient evidence for cache or credential reuse.
For HTTPS, service identity verification is part of authenticated origin
establishment, not an optional CAS integrity check.

Redirect handling is an explicit state transition:

- `307` and `308` preserve the method. Historical handling of `301` and `302`
  can rewrite a `POST` to `GET`, so the remote layer must not treat all 3xx
  responses as method-preserving.
- On a redirect, connection-specific and proxy-authentication fields are
  recomputed or removed. Origin credentials such as `Authorization` and
  `Cookie` are not forwarded outside their valid scope. User-supplied sensitive
  fields also need an allow/deny policy rather than blind replay.
- The client needs a redirect bound and cycle detection. For a CAS operation,
  crossing origin or namespace should require an explicit policy decision,
  followed by ordinary content verification at the destination.

Conformance cases should cover same-origin and cross-origin redirects, every
method-changing status, loops, relative locations, userinfo rejection,
credential stripping, proxy credentials, and a redirect to an address whose
payload fails the final CAS check.

#### Method safety, idempotency, retry, and early data

[RFC 9110 §9.2](https://www.rfc-editor.org/rfc/rfc9110.html#section-9.2)
distinguishes safe from idempotent methods. `GET` and `HEAD` are safe; safe
methods and `PUT` are idempotent at the HTTP semantic level. A client does not
automatically retry a non-idempotent request unless it knows the application
operation is idempotent or has evidence that the original request was not
applied. A failed automatic retry is not itself an invitation to retry
indefinitely.

The CAS API must state operation semantics independently of the chosen verb.
An exact-address upload can be application-idempotent if the server verifies
the address and repeated success has no additional effect, but that is an API
obligation; the spelling `POST` or `PUT` alone does not prove it. Conversely,
an idempotent HTTP method may still consume a one-shot authorization token or
interact with an implementation quota.

The retry state should retain:

- operation identity and method semantic class;
- attempt count and one deadline spanning all attempts;
- request bytes sent and whether the server could have processed them;
- response headers observed and protocol-specific commitment evidence;
- configured maximum attempts, backoff, jitter, and server pushback;
- the last transport error and whether its processing status is known,
  unprocessed, or indeterminate.

`Retry-After` can be either an HTTP date or delay-seconds
([RFC 9110 §10.2.3](https://www.rfc-editor.org/rfc/rfc9110.html#section-10.2.3)).
It is scheduling input, not permission to replay a non-idempotent operation.
For `425 Too Early`, a retry is sent after leaving early data
([RFC 8470 §5.2](https://www.rfc-editor.org/rfc/rfc8470.html#section-5.2)).
The default CAS policy should confine 0-RTT to operations whose replay effects
are explicitly acceptable.

Tests should inject disconnects before request bytes, during upload, after the
server processes a request but before the response, after response headers,
and during response content. They should assert both the retry decision and
the absence of duplicate semantic commitment.

#### Status and typed error mapping

HTTP status remains distinct from the domain result. A useful minimum mapping
preserves rather than collapses these cases:

| HTTP observation | Remote-CAS classification to consider | Required caution |
|---|---|---|
| `401` | authentication required/invalid | Keep separate from authorization denial; process the applicable challenge and credential scope. |
| `403` | authenticated or anonymous principal denied | Do not rewrite to absence. |
| `404` | address or endpoint absent | Absence can be cached by generic HTTP caches; the CAS layer should default to no semantic negative cache unless the API contract supplies scope and freshness. |
| `408`, `429`, `502`, `503`, `504` | transient candidate | Retry still depends on method/application idempotency, deadline, attempt budget, and `Retry-After`; status alone is insufficient. |
| `409`, `412` | conflict/precondition failure | Preserve the validator or concurrency meaning; do not call it transport failure. |
| `413`, `431` | content or field budget rejected | Terminal unless policy or request shape changes. |
| `416` | unsatisfied range | Validate local range arithmetic and representation identity before retrying. |

For `application/problem+json`, the problem `type` URI is the stable problem
identifier. The body's `status` member is advisory duplication; the actual
HTTP status drives generic HTTP handling. Clients should ignore unrecognized
extension members and must not branch on human-readable `title` or `detail`
([RFC 9457 §§3–4](https://www.rfc-editor.org/rfc/rfc9457.html#section-3)).
Problem responses and logs may contain sensitive data, so conformance fixtures
need a redaction boundary as well as a decoder boundary.

#### Validators, ranges, resume, and digest fields

Entity tags are opaque validators, not CAS addresses. Weak and strong tags
have different comparison rules. `If-Range` requires a strong validator; a
weak entity tag cannot safely bind range resumption. Conditional requests must
also preserve the distinction between `If-Match`, `If-None-Match`, and date
validators rather than reducing them to a Boolean cache hit.

Range processing has several non-obvious requirements from
[RFC 9110 §14](https://www.rfc-editor.org/rfc/rfc9110.html#section-14):

- byte ranges address the selected encoded representation, not necessarily the
  decoded CAS bytes;
- a `206` recipient inspects `Content-Range` and, for multipart responses, each
  part's fields;
- a server may coalesce, reorder, or return fewer ranges than requested;
- partial responses may be recombined only when their validators establish one
  representation, normally with a common strong validator;
- large decimal lengths and range offsets need overflow-safe parsing;
- a completed reassembly still undergoes canonical decoding and CAS address
  verification before admission.

`Content-Digest` covers HTTP content, while `Repr-Digest` can describe the
whole selected representation and is therefore more useful alongside a range.
The `Want-*` fields are negotiation preferences, not guarantees. Digest fields
can support early rejection and diagnostics, but absent a separate authentic
channel an attacker can remove or replace them. They do not displace TLS
authentication or the CAS address check
([RFC 9530 §§2–6](https://www.rfc-editor.org/rfc/rfc9530.html#section-2)).

Range conformance should include ignored range requests returning `200`, valid
single and multipart `206`, reordered/coalesced parts, overlapping ranges,
`416`, changed validators between attempts, weak `If-Range`, content codings,
truncated parts, integer overflow, a correct HTTP digest with the wrong CAS
address, and a correct CAS object transported without optional digest fields.

#### HTTP caching versus semantic CAS caching

RFC 9111 permits caches to store more than successful complete `200`
responses. Negative responses can be reusable, and an incomplete `200` or
`206` may be stored if the cache records it as incomplete and handles later
ranges correctly. It must not serve an incomplete response as complete.
Authenticated requests, `Vary`, freshness, revalidation, `Age`, and
`Cache-Control` all affect reuse.

The remote library should therefore keep two caches conceptually separate:

- an HTTP cache, governed by RFC 9111 and keyed by the selected representation;
- a semantic CAS cache, containing only values that completed transport and
  passed CAS admission.

A conservative semantic key includes authority, tenant/namespace, CAS address,
representation format, and content-coding assumptions. A `304` or partial
`206` updates transport representation state but cannot directly mint an
admitted CAS value. Negative semantic caching should be opt-in with explicit
scope and freshness; otherwise transient authorization, replication, or
eventual-consistency behavior can be misreported as stable absence.

Tests should place a hostile or merely RFC-conforming intermediary before the
CAS endpoint and exercise stale responses, `Vary`, authenticated responses,
incomplete stored responses, `304` revalidation, collapsed concurrent misses,
and negative cache entries. The invariant under test is that no HTTP cache path
bypasses CAS admission.

#### Body, header, decompression, and concurrency budgets

HTTP does not supply the application's acceptable body size. The client must
enforce explicit budgets for response fields, declared content length,
transport bytes, decoded bytes, decompressed bytes, range count, multipart
parts, concurrent streams, redirects, and queued consumer data. Declared
length permits an early rejection but cannot replace streaming byte counts.
Content codings are decoded before application parsing and can expand far past
their encoded size.

Budget failure should be a typed event containing the stage, observed amount,
and configured bound, followed by cancellation of the underlying stream.
It must not leave an apparently reusable partial semantic object. Flow control
and backpressure reduce buffering pressure, but neither establishes an
application size limit.

### HTTP/1.1 framing lane

HTTP/1.1 message completeness is an adversarial parser boundary. Under
[RFC 9112 §§6–8](https://www.rfc-editor.org/rfc/rfc9112.html#section-6):

- transfer coding takes framing precedence over `Content-Length`; a message
  carrying both is suspicious and must not be normalized into an ordinary CAS
  response;
- invalid or conflicting content lengths are unrecoverable framing errors
  (identical repeated values are a separately defined case);
- a content-length response that closes early is incomplete;
- chunked content is complete only after the terminal zero-size chunk and its
  trailer section;
- close-delimited response bodies are inherently ambiguous when the connection
  fails;
- bytes following a complete response cannot be treated as a second response;
- a connection is reusable only after the complete response body is consumed
  or deliberately handled according to the protocol.

For WebSocket and other protocol transitions, no application-protocol bytes
are sent before the successful upgrade response. RFC 9931 makes the optimistic
transition security problem explicit, while RFC 6455 already requires the
WebSocket client to wait for the handshake response.

The HTTP/1.1 hostile-server suite should emit byte-exact cases for short and
long bodies, conflicting and duplicated `Content-Length`, `Transfer-Encoding`
plus `Content-Length`, malformed chunk sizes, chunk extensions, missing zero
chunk, trailers, extra response bytes, premature TLS close, upgrade rejection,
and a server that waits to verify that no optimistic WebSocket bytes arrive.
No such failure may deliver or cache a partial CAS value.

### HTTP/2 stream lane

HTTP/2 DATA frame boundaries are transport artifacts and do not delimit CAS or
RPC messages. A response finishes at `END_STREAM`, including a trailing HEADERS
frame when present. A mismatch between declared content length and received
DATA length is a malformed message, and clients do not accept malformed
responses ([RFC 9113 §8](https://www.rfc-editor.org/rfc/rfc9113.html#section-8)).

The model must distinguish stream-local from connection-wide failures:

- `RST_STREAM` terminates one stream and carries an error code;
- `GOAWAY` carries the last stream identifier the peer might have processed;
  streams above that boundary can be treated as unprocessed, while streams at
  or below it may have been processed;
- automatic replay after either signal still depends on operation idempotency
  unless the protocol gives unprocessed evidence;
- connection and stream flow-control windows constrain sending, and a receiver
  continues processing control frames promptly, but flow control is not a CAS
  content budget;
- peer settings such as maximum concurrent streams belong in scheduling state,
  not in the semantic CAS state.

Conformance cases should split and coalesce application prefixes across DATA
frames, omit `END_STREAM`, reset mid-body, send trailers, mismatch content
length, interleave many streams, cancel consumers, stall flow-control windows,
and send `GOAWAY` with stream identifiers on both sides of the current request.
The expected output includes retry classification and completeness, not merely
the host library's exception text.

### HTTP/3 stream lane

HTTP/3 carries each request/response exchange on a QUIC bidirectional stream.
It has no HTTP/1.1 `Transfer-Encoding`; stream termination and HTTP/3 frames
provide the message boundary. A partial response following cancellation is not
usable as a complete response
([RFC 9114 §4](https://www.rfc-editor.org/rfc/rfc9114.html#section-4)).

Retry evidence is version-specific:

- `H3_REQUEST_REJECTED` states that the request was not processed by the
  application and is retry-relevant unprocessed evidence;
- `H3_REQUEST_CANCELLED`, resets, and ambiguous connection loss do not by
  themselves prove non-processing;
- an HTTP/3 `GOAWAY` identifier bounds requests that might have been accepted;
  requests at or above its threshold are treated differently from earlier
  requests;
- QPACK or critical-stream failures can be connection-wide even if one CAS
  request first observes them.

The suite should exercise clean FIN versus reset, request rejection versus
cancellation, incomplete responses, `GOAWAY` boundaries, blocked field
decoding, critical stream failure, cancellation races, and 0-RTT rejection.
QUIC migration, loss, and connection recovery can be implementation-level
fixtures, but their normalized result still must preserve whether the request
was unprocessed, processed, or indeterminate.

### gRPC over HTTP/2 and HTTP/3

#### Envelope and completion

The official HTTP/2 protocol document defines a gRPC call as an HTTP `POST`
with `content-type: application/grpc`, a case-sensitive path, and
`te: trailers`. Each gRPC message has a one-byte compressed flag, a four-byte
unsigned big-endian length, and that many message bytes. HTTP DATA frames do
not align with this five-byte prefix or the message body.

The compressed flag and negotiated encoding must agree, and decompression
needs its own budget. Compression context is per message under the base
protocol. A length that exceeds the application limit is rejected before
allocation, even if the unsigned value is representable by the host runtime.

A normal response consists of initial headers, zero or more length-prefixed
messages, and trailers; a trailers-only response is also valid. Final
`grpc-status` is required even when it is zero. HTTP `200` therefore does not
mean gRPC success. The client must wait for the final gRPC status before
admitting an RPC result. If a non-gRPC response or missing `grpc-status`
requires an HTTP-to-gRPC fallback mapping, the mapping is used only in that
absence case; it must not overwrite an explicit gRPC status.

If `grpc-status-details-bin` is present, its encoded status code must not
contradict `grpc-status`. Header and trailer budgets remain necessary; the
protocol document suggests an 8 KiB default calculation but does not make that
an adequate universal application limit.

#### Retry and backoff

The implemented A6 proposal separates connection backoff from retrying one
RPC. Configured retries retain one call deadline, a maximum-attempt count,
backoff and jitter, retryable gRPC statuses, and optional server pushback.
Negative or unparseable `grpc-retry-pushback-ms` suppresses retry rather than
inventing a delay.

A call becomes committed once response headers are received or the outgoing
message exceeds the retry buffer. After commitment, configured retries stop.
Transparent retry is reserved for evidence of non-processing such as an
HTTP/2 `REFUSED_STREAM` or a stream beyond a `GOAWAY` processing boundary.
The service method's idempotency still belongs in the application contract;
gRPC framing does not make all calls replay-safe.

The HTTP/3 gRPC proposal maps the same message and status model onto RFC 9114.
Its stated implementation status is currently limited to grpc-dotnet, so a
generic effects API should expose HTTP/3 as a capability rather than silently
assuming every gRPC backend provides it. `H3_REQUEST_REJECTED` can map to an
unavailable/unprocessed path; cancellation remains potentially ambiguous.

#### gRPC conformance matrix

The transport suite should cover:

- a five-byte prefix split at every boundary and multiple messages coalesced
  into one DATA chunk;
- truncated prefixes and bodies, oversized unsigned lengths, invalid compressed
  flags, absent or unsupported encodings, corrupt compressed data, and
  decompression expansion;
- trailers-only success and failure, missing status, malformed status,
  contradictory status details, HTTP error with no gRPC status, and HTTP `200`
  with nonzero gRPC status;
- stream reset, connection loss, and `GOAWAY` before and after the processing
  boundary;
- retry-buffer commitment, headers commitment, retry pushback, attempt budget,
  one deadline across attempts, and cancellation during backoff;
- equivalent HTTP/3 cases for request rejection, cancellation, reset, and
  `GOAWAY`.

An RPC that yields bytes for a CAS object is not complete until those bytes
also pass the CAS decoder and address check.

### JSON-RPC 2.0 envelope

A JSON-RPC 2.0 request carries the exact version string `"2.0"`, a method,
optional structured parameters, and an optional identifier. A response carries
the same identifier and exactly one of `result` or `error`. Notification
requests omit the identifier, and the server sends no response; they are
therefore inappropriate for CAS operations whose success, durability, or
returned value must be observed.

Batch responses may be returned in any order and operations may be processed
concurrently. Correlation is strictly by identifier, never array position. An
empty batch is invalid, while an all-notification batch produces no response.
The specification does not define duplicate-identifier handling robustly
enough for a client to rely on duplicates, so an implementation should generate
unique outstanding identifiers and reject ambiguous responses.

Conformance cases should include reordered batch responses, duplicate,
unknown, missing, and mismatched identifiers, wrong version, both or neither
of `result`/`error`, invalid error objects, empty batch, all-notification batch,
batch count and byte limits, and cancellation with late responses. The CAS RPC
profile must separately define method idempotency, typed error codes,
authorization scope, and whether an accepted upload is durable.

### Server-sent events

EventSource accepts a successful event stream only from an HTTP `200` response
with a supported `text/event-stream` media type. Its fetch uses `no-store`
cache mode. The default constructor does not include cross-origin credentials;
`withCredentials: true` changes the credential mode. HTTP `204` tells the
client to stop reconnecting.

An SSE stream is UTF-8 and uses a line parser with CRLF, bare CR, and bare LF
terminators. The first BOM is ignored. A line beginning with `:` is a comment;
otherwise the parser splits at the first colon and removes at most one leading
space from the value. Field names are case-sensitive. Repeated `data` fields
are joined with newline characters. An event is dispatched only on a blank
line; an unterminated event at EOF is discarded. An `id` containing NUL, LF,
or CR is not installed, and a `retry` value changes reconnection time only when
it is entirely decimal digits.

On reconnection, a nonempty last event ID is sent in `Last-Event-ID`. This is a
cursor, not proof that the server retained every event or that an event was
processed exactly once. The model should permit duplicates and gaps unless a
separate CAS notification protocol supplies and tests stronger replay rules.
Redirect and credential-scope rules still apply to reconnects.

SSE has no application-level consumer acknowledgement or bounded-retention
guarantee. It is consequently a good fit for advisory invalidation, availability
hints, or change notifications. CAS bytes received in SSE data remain
untrusted, bounded input and require normal decoding and address admission.

The suite should split the byte stream at every possible UTF-8 and line
boundary; cover BOM, CR/LF variants, comments, empty and repeated data, unknown
and case-variant fields, embedded NUL, invalid `retry`, incomplete EOF,
terminal `204`, redirect/authentication, reconnect delay, `Last-Event-ID`,
duplicates, gaps, and a slow consumer with a bounded queue and cancellation.

### WebSocket over HTTP/1.1, HTTP/2, and HTTP/3

#### Handshake variants

For HTTP/1.1, the client sends a `GET` upgrade request with WebSocket version
13 and a freshly random 16-byte `Sec-WebSocket-Key`, then waits. It accepts
only a valid `101` response with the required upgrade fields and the correct
`Sec-WebSocket-Accept`. A subprotocol or extension not offered by the client is
a handshake failure. Subprotocol matching is case-sensitive. No WebSocket
frame is sent before successful transition.

HTTP/2 uses RFC 8441 extended `CONNECT` only after the server advertises the
enablement setting. The request supplies `:protocol` as `websocket` plus the
HTTP/2 scheme, authority, and path fields. It does not use the HTTP/1.1
`Connection`, `Upgrade`, `Host`, key, or accept fields; success is status `200`,
after which RFC 6455 frames travel on that stream.

HTTP/3 uses the analogous RFC 9220 extended `CONNECT` after HTTP/3 enablement.
QUIC FIN and reset behavior must be mapped to WebSocket closure without
pretending an abrupt transport reset supplied a clean WebSocket Close frame.

#### Frames, fragmentation, and control

Clients mask every frame with a fresh unpredictable 32-bit mask. Server frames
are not masked; a client that receives a masked server frame fails the
connection. Length encodings are minimal, and the most significant bit of the
64-bit length is zero. Reserved bits and opcodes are accepted only under a
negotiated extension.

Control frames are at most 125 bytes and are never fragmented. Data messages
can be fragmented through continuation frames, with control frames interleaved;
receivers must process that interleaving. Text messages require valid UTF-8.
A CAS binary protocol should use binary messages and still enforce stateful
fragment assembly and whole-message limits.

A Ping elicits a Pong carrying the same application data as soon as practical,
including while a fragmented message is in progress. Close begins a state
transition: after sending Close, the endpoint sends no more data frames;
receiving Close normally prompts a Close response. The model must distinguish
clean close, peer-reported close code/reason, transport EOF, reset, timeout,
and local cancellation.

#### Extensions, limits, and backpressure

RFC 6455 requires implementations to protect themselves with frame and
reassembled-message limits. The CAS client additionally needs decompressed
message and queued-consumer limits. WebSocket supplies ordered delivery on one
connection but no application acknowledgement, durable replay, or stream
multiplexing contract for CAS operations; those must be designed above it.

If `permessage-deflate` is enabled, its parameters and context-takeover choices
are negotiated exactly. RSV1 applies to the first data frame of a compressed
message, not every continuation frame. Compression creates decompression-bomb
and cross-message context risks; disabling it is a defensible default for CAS
bytes, while enabling it requires separate compressed/decompressed budgets and
tests. CAS hashing applies to the defined application representation after the
agreed protocol decoding, not to arbitrary on-wire compressed fragments.

WebSocket conformance should cover handshake statuses and fields, incorrect
accept values, unsolicited protocols/extensions, optimistic-data rejection,
masked server frames, client mask freshness, nonminimal and huge lengths,
unknown RSV/opcodes, invalid continuation sequences, fragmented control frames,
control payloads over 125 bytes, invalid UTF-8, interleaved Ping/Pong, Close
races, abrupt EOF, compression negotiation and bombs, slow consumers, and the
distinct HTTP/1.1, HTTP/2, and HTTP/3 bootstrap rules.

### Abstract command/event boundary implied by the standards

The effect-side protocol core should consume normalized events rather than host
exceptions or arbitrary callback timing. One possible vocabulary, still
unratified, is:

| Direction | Candidate forms | Standards evidence retained |
|---|---|---|
| Commands | `startHttp`, `sendBody`, `cancel`, `openRpc`, `openSse`, `openWebSocket`, `sleepUntilRetry` | Operation ID, authority/namespace, method semantic class, deadline, limits, credential policy, validator/range state, offered protocols/extensions, last SSE event ID. |
| HTTP events | `responseHeaders`, `bodyChunk`, `trailers`, `messageEnd`, `redirect`, `authChallenge`, `retryAfter`, `rangePart` | HTTP version, status, fields, received byte counts, completeness, strong/weak validator identity. |
| Failure/control events | `streamReset`, `connectionGoAway`, `transportClosed`, `timeout`, `budgetExceeded` | Error scope, stream/request boundary, clean versus incomplete close, attempt, processing evidence, stage and observed limit. |
| gRPC events | `rpcMessage`, `rpcTrailers`, `rpcStatus`, `retryPushback` | Prefix/compression validation, headers-commit boundary, final status, details consistency, retry commitment. |
| SSE events | `sseOpen`, `sseEvent`, `sseReconnect`, `sseStopped` | Parsed event ID/type/data, retry delay, redirect authority, EOF versus `204`, duplicate/gap-tolerant cursor. |
| WebSocket events | `wsAccepted`, `wsFrame`, `wsMessage`, `wsPing`, `wsPong`, `wsClose` | Bootstrap version, negotiated subprotocol/extensions, masking and fragmentation validation, clean/abnormal closure. |

Each operation needs an explicit state such as `requesting`, `headers`, `body`,
`trailers`, `transportComplete`, `casAdmitted`, `rejected`, `cancelled`, or
`indeterminate`. `bodyChunk`, `rpcMessage`, `sseEvent`, and `wsMessage` are
untrusted observations. Only `transportComplete` followed by `casAdmitted` can
publish or semantically cache a CAS value.

Fiber-local state can carry cancellation scope, deadline, trace context, and a
handle to an in-flight operation, but origin, operation identity, retry attempt,
processing evidence, and admission state must be explicit machine data. Making
those facts ambient would make replay and cross-fiber conformance traces harder
to state and would risk credential or validator leakage between operations.

### Generic and real-transport conformance shape

The standards suggest a two-step refinement boundary:

```text
raw transport transcript
  -> versioned protocol adapter
  -> normalized commands/events
  -> remote/CAS abstract machine
  -> transport-complete candidate
  -> canonical decode and CAS admission
```

The generic theorem target should range over normalized events and state the
conditions under which an admitted CAS value can be produced, when retry is
permitted, and how cancellation or incomplete input leaves no admitted prefix.
Separate executable suites then drive hostile and ordinary HTTP/1.1, HTTP/2,
HTTP/3, gRPC, SSE, and WebSocket servers and check that each adapter emits the
expected normalized trace.

Passing those real-transport tests would be evidence about the pinned host
runtime and adapter; it would not by itself prove full RFC conformance or remote
durability. A conformance claim therefore needs to name the runtime/backend,
version, TLS stack, protocol version, exercised fixture set, and the exact
abstract trace relation.

## Lean 4 model and implementation survey

### Reuse decisions

| Source and exact pin | What exists | Decision for Foldlab |
|---|---|---|
| [PolyFun `bb7e1003544b8461e3d484fc51c61b2ff865250f`](https://github.com/Verified-zkEVM/PolyFun/tree/bb7e1003544b8461e3d484fc51c61b2ff865250f), Apache-2.0, Lean/Mathlib 4.33.1 | `Control.LTS` with silent and visible steps; strong, delay, and weak simulation; weak bisimulation; finite weak traces; trace-inclusion and trace-equality theorems; interaction trees and handler simulation | **Reuse or adapt the small LTS/trace kernel.** `IsWeakSimulation.weakTrace` and `traces_subset` have the right shape for a protocol-adapter bridge. Admit the dependency separately or copy only the owned semantic kernel so the effects package can remain Mathlib-free. Use its full interaction trees only if infinite reconnecting/streaming sessions become an approved requirement. |
| [Lean `Std.Http` at `lean4@819816b2e0a3bf405af45ae5c7af2491d8f5bee6`](https://github.com/leanprover/lean4/tree/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Std/Http), Apache-2.0, Lean 4.33.1 | Direction-indexed executable HTTP/1.1 reader/writer machine, transport class, TCP implementation, and bidirectional in-memory mock | **Reuse as a runtime and harness seam, not a standards model.** The targeted scan found only small local theorems and no RFC refinement for the H1 state machine. Relate its events to an independent standards-derived model. |
| [lean-grpc `v1.1.0`, `0887548b7fdfea9fe76d645514f42e8206cee270`](https://github.com/RileyBetts/lean-grpc/tree/0887548b7fdfea9fe76d645514f42e8206cee270), Apache-2.0, Lean 4.32.1 | Pure-Lean HTTP/2, HPACK, and gRPC runtime; scoped codec/framing proofs; h2spec and official interop fixtures documented with explicit exclusions | **Use as a runtime/interop peer and possible wire adapter.** Its own proof document excludes the connection state machine, full flow control, FFI/TCP, end-to-end sessions, and parts of HPACK. Interop results are observational evidence until related to the Foldlab trace judgment. |
| [Veil `300c305e945750ab3fb62de4a79c23161b24da39`](https://github.com/verse-lab/veil/tree/300c305e945750ab3fb62de4a79c23161b24da39), Apache-2.0, Lean 4.28.0 | Relational and executable transition systems, reachability, traces, invariant checking, and bounded model-checking workflow | **Adapt the safety/counterexample pattern.** Do not make it the default dependency while its solver dependencies, Lean version, and Mathlib posture differ from this package. Model checking remains bounded evidence; checked theorem terms carry the proof claim. |
| Mathlib 4.33.1, `0df444a360eaa60ab8c11dca51a86af692955474` | Deterministic state-transition reachability/evaluation utilities and streams with a bisimulation/coinduction principle | **Utility reuse only.** The deterministic `StateTransition` carrier is too weak for an open, nondeterministic, concurrent protocol environment. |
| [Telltale `d5bed45ea0e5b3ad1be032f113e644121879c61a`](https://github.com/hxrts/telltale/tree/d5bed45ea0e5b3ad1be032f113e644121879c61a), MIT | Multiparty session types, async buffered configurations, explicit transport outcomes, normalized runtime observations, and differential fixtures | **Adapt selected patterns.** Its bridge inventory and `ok`/blocked/disconnected/timeout/error result split are useful. Do not import the MPST stack unless fixed roles, FIFO channels, and endpoint projection become domain requirements. |
| [HITrees `3ddf725488a8b2e83af391a1c6ad77796c904865`](https://git.ista.ac.at/plv/hitrees/-/tree/3ddf725488a8b2e83af391a1c6ad77796c904865), BSD-3-Clause | Reified higher-order effects, handlers, thread pool, yield, nondeterministic selection, kill, and continuations | **Pattern only for explicit scheduler semantics.** It shows how fibers can be modeled without making logical CAS state ambient. |
| ZipperGen `b8f0b068df395f7c07882ef3fede44faaf638aea`; Leslie `58e58b2502b2a570e4ce4fdb6b40748c3cb30e5d`; LeanLTL `d5473f06ab9d0ea652a51b2e78b11089731c4b6c`; LeanearTemporalLogic `24796b51e00ae61e09163dd8a9ff8ce10127f7a3` | Endpoint projection, fairness/refinement shapes, and temporal statement patterns | **Pattern only.** Missing licenses, version drift, mutable dependencies, admitted gaps, or weak bridges prevent direct use. In particular, liveness needs explicit infinite-trace and fairness assumptions. |

No credible theorem package was found for SSE processing, WebSocket framing and
session state, or current gRPC-over-HTTP/2 server dynamics. The reservoir and
repository search did find executable networking packages, but none covered
the whole standards-to-transport refinement boundary.

### LeanServer: valuable implementation, not the oracle

[LeanServer at `24b916aaa6ae4a20732536494904d0699fac7ec7`](https://github.com/AfonsoBitoque/LeanServer/tree/24b916aaa6ae4a20732536494904d0699fac7ec7)
is a serious and useful Lean networking implementation. It is Apache-2.0,
targets Lean 4.29.1, contains executable HTTP/2, gRPC, and WebSocket code, and
has enough surface area to become a useful hostile-fixture client/server or
differential-test peer. The correct conclusion is not to discard it; it is to
avoid treating its code or theorem count as the standards oracle.

The source audit found concrete mismatches that a Foldlab conformance layer
should catch:

- `Protocol/GRPC.lean` puts `grpc-status` and `grpc-message` in ordinary
  response headers, while the gRPC protocol requires final status in trailers,
  including status zero. Its message decoder consumes one framed message but
  does not require exact consumption of the input remainder.
- `Protocol/HTTP2.lean` constructs a request at the first DATA frame rather
  than waiting for the stream's message-completion boundary, and it does not
  model all DATA/CONTINUATION aggregation requirements. It cites superseded RFC
  7540 rather than current RFC 9113.
- `Protocol/WebSocket.lean` does not enforce endpoint-role masking, reserved
  bits, minimal lengths, or the complete fragmentation/control-frame state
  machine. Continuation handling loses the original text/binary kind.
- The targeted theorem scan found local round trips and concrete fixtures, but
  no protocol-to-RFC trace refinement. `parse_total : forall data, True` is a
  totality-shaped but vacuous proposition, and the tree relies heavily on
  `native_decide`, which is outside the effects library's accepted formal-core
  proof posture.

Those observations make LeanServer an especially good regression target: run
the same malformed/truncated/interleaved cases against it and other runtimes,
normalize what each runtime observed, and check the model's expected result.
Any borrowed decoder or framing idea still needs an exact-consumption and
protocol-refinement proof in Foldlab's own judgment.

### Closest end-to-end proof architecture is currently outside Lean

Two Coq projects supply technique prior art rather than reusable Lean code:

- Koh et al., [*From C to Interaction Trees: Specifying, Verifying, and
  Testing a Networked Server*](https://doi.org/10.1145/3293880.3294106),
  layers a linear service specification, network-aware concurrent behavior,
  executable interaction trees, C refinement, and model-based testing.
- Zhang et al., [*Verifying an HTTP Key-Value Server with Interaction Trees
  and VST*](https://doi.org/10.4230/LIPIcs.ITP.2021.32), with its
  [published artifact](https://doi.org/10.5281/zenodo.4697379), verifies a
  defined HTTP/1.1 subset and bridges socket events through the user/kernel
  boundary.

Their important lesson is the layered bridge, not their prover or exact HTTP
subset: service semantics, network semantics, executable implementation, and
real observations are separate relations.

## Proposed open-system model

### State and transitions

The protocol model should be an open labeled transition system:

```lean
-- Candidate shapes only; names and carriers are not frozen.
structure ProtocolState where
  clients : ClientId → ClientState
  server : ServerState
  network : NetworkState

inductive Move where
  | client ... | server ... | network ... | environment ...

Step : ProtocolState → Move → Option ProtocolObs → ProtocolState → Prop
```

The server is permitted to be nondeterministic or adversarial within the
protocol model. This is enough to establish client-side safety properties; an
implementation proof of the remote server is not a prerequisite. Network and
environment moves cover fragmentation, coalescing, delay, loss, close/reset,
duplication at retry boundaries, redirects, cancellation, `GOAWAY`, and
scheduler choices. Internal buffering, parsing, backoff, and scheduling moves
are silent observations.

Protocol traces should relate to the abstract remote machine through a
relation, not a total decoder:

```lean
Realizes : List ProtocolObs →
  List (OpId × Effects.Remote.MInput K B) → Prop
```

The relation is necessary because several frames can yield one application
event, one frame can contain several messages, and many protocol actions yield
no remote event. A local weak-step simulation is therefore the default bridge.
Trace equality or bisimulation is stronger than the CAS client needs and would
incorrectly constrain buffering, backoff, or harmless internal actions.

### Unratified theorem docket

The following are candidate judgment shapes, not landed claims:

| Candidate | Exact judgment shape | What it would establish |
|---|---|---|
| `adapter_step_refines` | Given an implementation/model state relation, every executable adapter step is matched by zero or more silent model steps and at most one visible weak step, ending in related states. | Local bridge premise. |
| `adapter_traces_subset` | `AdapterTrace t -> exists u, Realizes t u ∧ u ∈ Model.traces`. | Every admitted executable finite observation has a modeled abstract schedule. |
| `incomplete_excludes_completion` | If a protocol trace terminates with incomplete framing, its normalized trace contains no transport-complete event for that attempt. | A prefix, reset, missing trailer, or abrupt EOF cannot masquerade as completion. |
| `completion_precedes_admission` | Every `cached` or `returned` decision in the composed trace is preceded for the same operation and attempt by protocol completion and standard CAS admission. | Links transport completion to existing RMT-001 rather than replacing it. |
| `retry_requires_authority` | A retry command implies either application idempotency or protocol evidence classified as known-unprocessed, plus remaining deadline/attempt budget. | Rules out status-only and exception-only retry. |
| `operation_isolation` | Projecting a concurrent trace to operation `i` is unchanged by steps for distinct operation `j`, except declared shared capacity/scheduling observations. | No cross-stream response or batch substitution. |
| `cross_transport_agreement` | If two protocol traces realize the same abstract input schedule, deterministic `Effects.Remote.run` produces equal abstract results, decisions, and commands. | HTTP/gRPC/SSE/WebSocket implementations agree at the service boundary; it does **not** assert wire-trace equality. |
| `generated_scenario_denotes_trace` | Every generated finite scenario has a witness in the standards model. | Generator cases are meaningful model cases. It does not state bounded completeness unless a separate theorem does. |

Safety and liveness remain separate. Finite traces can exclude bad admission,
cross-operation substitution, illegal retry, and publication of a partial
object. Eventual response, reconnect, or acknowledgement needs infinite traces
and hypotheses for delivery, server availability, scheduler fairness, and
consumer progress. No bounded conformance run can discharge those hypotheses.

## Fit to the current Effects remote model

The current working-tree snapshot already provides useful semantic anchors:

- `MInput.request` and `MInput.fromWire` carry an `OpId`; `inFlight` maps IDs
  to independent load/upload states; commands and decisions are ID-tagged.
- `RMT_001_no_cache_or_return_without_admission` covers both cache and caller
  delivery at the abstract event boundary.
- RMT-002's current Lean theorem covers declared-length and local upload-size
  rejection. Actual streamed, decoded, and decompressed byte budgets are still
  transport-adapter obligations.
- `RMT_003_rejection_monotone` and `RMT_003_terminal_over_run` make integrity
  rejection temporal over the model run, rather than a one-step fixture.

That is a meaningful R1 semantic suite, but it is not yet a real-transport
suite. Its manifest rows start at already-normalized `Event` values, so they do
not exercise response framing, actual streamed byte counts, gRPC trailers,
SSE parsing, WebSocket role/fragment state, TLS authority, or retry commitment.
The strongest current design choices are the relational AGREEMENT boundary,
comparison of commands as well as outcomes, operation-correlated schedules,
and the temporal RMT-003 theorem. The principal rigor gap is now the missing
protocol-adapter relation and transcript evidence below `Event`, not another
large collection of abstract example rows.

This review did not run the build or transport tests. It assesses declarations,
theorem shapes, workflow text, and source snapshots only; current compilation
and runtime status are separate evidence.

The standards review exposes the next model gaps:

1. Add an `AttemptId` below logical `OpId`. A connection stream ID is
   session-local and cannot replace either identifier.
2. Carry processing evidence such as `knownUnprocessed` versus
   `possiblyProcessed`; do not infer it from a generic reset or status code.
3. Refine `.ok declared bytes`: a protocol adapter must witness exact framing
   completion and actual byte counts. Declared length alone is useful for early
   rejection, not for successful completion.
4. Keep version-specific status, trailers, redirect, credential, range,
   validator, and completeness data in the protocol trace. The abstract
   `.redirected` and `.rateLimited Nat` events are too coarse to establish
   credential stripping or `Retry-After` date/delay normalization by
   themselves.
5. Make retry commitment explicit. For gRPC this includes response headers and
   retry-buffer overflow; for HTTP/2 and HTTP/3, only named protocol conditions
   provide known-unprocessed evidence.
6. Define cancellation as an operation/attempt transition. A fiber may own the
   cancellation scope, but ambient fiber state is not semantic operation
   identity and must not carry origin, credentials, retry entitlement, or CAS
   admission.

## Effect v4 boundary and developer experience

The existing deep seam remains the ergonomic one:

```text
CasStore service
  -> semantic-admission adapter (proof obligations pending)
  -> versioned remote transport
  -> Effect HttpClient / RPC / stream runtime
```

The Effect APIs should hide resource mechanics while leaving semantic choices
visible:

- `Layer` provides one configured endpoint/namespace; `LayerMap` provides a
  keyed family for roots, tenants, or authorities. Secrets remain layer
  dependencies, never keys or CAS identity.
- `HttpClient` performs raw exchanges. Generic `retryTransient` and redirect
  combinators must not make semantic retry/credential decisions invisibly;
  the remote machine chooses, then the shell executes one declared command.
- `Stream` enforces incremental transport, decoded, decompressed, and queued
  byte budgets with backpressure. `Scope` owns response bodies, sockets,
  WebSockets, SSE subscriptions, and cancellation cleanup.
- `RequestResolver` batches and deduplicates genuine backend operations.
  `Cache` stores only CAS-admitted successes; neither presence nor a complete
  HTTP response is enough.
- `PartitionedSemaphore`-style host/tenant limits belong in the shell's
  scheduler. Capacity observations may feed the model without making runtime
  scheduling part of content identity.
- `Graph` is appropriate after nodes are independently admitted, for checked
  materialization, cycle rejection, traversal, and child-before-parent upload.
  It is not a wire trust boundary and its allocation-index snapshot is not CAS
  identity.

The user-facing transport error should retain operation and attempt identity,
stage, authority with secrets redacted, completion/processing classification,
status or close code, byte counts, and retry decision. Users should not have to
decode host exception strings to learn whether a request was rejected,
possibly processed, incomplete, or CAS-invalid.

## Executable real-transport conformance plan

Use the same finite `Scenario` language for every transport, then give each
adapter a protocol-specific realization:

1. Lean enumerates or accepts a scenario containing operations, interleaving,
   fragmentation, faults, and cancellation points, and computes the permitted
   normalized outcomes.
2. A hostile server or raw-frame peer enacts the HTTP/1.1, HTTP/2, HTTP/3,
   gRPC, SSE, or WebSocket realization. Ordinary reference servers provide a
   second lane.
3. The Effect or Lean client emits a redacted transcript with `OpId`,
   `AttemptId`, authority, connection/stream correlation, framing terminal,
   statuses/trailers, actual byte counts, and normalized observations.
4. An executable Lean checker validates trace membership at the normalized
   boundary. If the runtime adapter later receives a weak-simulation proof,
   the same observations support the stronger trace-inclusion judgment.
5. Every found defect becomes a named, deterministic manifest vector. Shrinker
   output enters the suite only after the shrink relation has been reviewed or
   proved to retain the failing semantic condition.

Supplementary ecosystem suites can increase observational coverage: WPT for
EventSource behavior, Autobahn for WebSocket framing, h2spec for HTTP/2, and
official gRPC interoperability cases. Their labels never substitute for the
Foldlab trace relation, and live remote servers provide evidence about the
observed deployment only.

The highest-value first slice is HTTP/1.1 unary load over `Std.Http.Transport`
and its in-memory mock: complete content-length response, truncated body,
chunked response missing its zero chunk, reset/close ambiguity, over-budget
stream, wrong CAS address, and cancellation. Follow with gRPC unary load using
lean-grpc and LeanServer as differential peers, then SSE notifications and
WebSocket control/subprotocol cases. HTTP/2/3 concurrency and retry commitment
should land before any claim that generic remote retries are safe.

## Counterexamples that constrain the contract

- Equal wire traces across transports are neither expected nor required;
  agreement is over normalized service results and decisions.
- HTTP digest fields do not authenticate a peer and are not CAS identity.
- SSE `Last-Event-ID` does not provide exactly-once processing or bounded
  retention.
- A WebSocket reset or lost Close handshake can leave the last application
  send semantically ambiguous.
- gRPC `UNAVAILABLE`, HTTP `503`, and an arbitrary host exception do not prove
  that a side effect was not applied.
- Eventual response or reconnection is false without delivery, availability,
  and fairness hypotheses.

## Provenance and claim standing

The exact research pins and fetched-content identities are recorded in
`.reference/provenance/receipts/remote-transport-standards-and-lean-models.json`.
Promotion into the canonical Source Lock remains pending. This report is
research input only: the model vocabulary, theorem docket, Effect API, and
staging order require Pass A ownership and ratification before implementation.
