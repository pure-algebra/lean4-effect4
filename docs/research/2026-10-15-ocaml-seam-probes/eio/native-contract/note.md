# Target native Eio interfaces directly

The finite probe supplies actual Eio source, sink, and stream-socket provider dictionaries.
Standard Eio consumers use them without conversion to another interface.
The same generic clients also consume standard Eio providers.
This gives a concrete native-interface target for generation and a future mathematical model.

**Role:** native interface model research and executable controls.
**Evidence:** installed Eio source, actual OCaml compilation, finite execution, and deliberate compiler refusals.
**Scope:** OCaml 5.1.1, Eio 1.2, and the source hashes in `sources.json`.
**Limit:** no Eio theorem, generated provider, Effect4 machine run, or network-backend test.

## The actual types

[Eio resources](https://ocaml-multicore.github.io/eio/eio/Eio/Resource/index.html) combine an existential carrier with its method dictionary.
The installed `resource.mli` exposes this shape:

```ocaml
type -'tags t = T : ('state * ('state, 'tags) handler) -> 'tags t
```

The dictionary's methods retain that exact hidden state type.
Interface tags constrain callers, and provider-interface keys select the methods.
This is richer than a record of serialized requests and replies.

| Native component | What the interface model must represent |
| --- | --- |
| `Resource.t` | An existential carrier and its compatible method dictionary |
| `Resource.pi` | An extensible typed method key, preserving carrier and implementation types |
| `Flow.Pi.SOURCE` | A first-class module with abstract `t`, `read_methods`, and `single_read` |
| `Flow.Pi.SINK` | The same carrier equation across `single_write` and `copy` |
| `Cstruct.t` | A mutable buffer view, its backing storage, offset, length, and aliases |
| `Net.Pi.STREAM_SOCKET` | Shared source, sink, shutdown, close, and platform-tag types |

The [Flow provider API](https://ocaml-multicore.github.io/eio/eio/Eio/Flow/Pi/index.html) packages those source and sink modules directly.
The probe uses `Flow.Pi.source`, `Flow.Pi.sink`, and `Net.Pi.stream_socket`.
It also adds a typed `Read_count` method through `Resource.pi`.
Standard Flow consumers accept that richer resource without knowing the extra method.

The [Net API](https://ocaml-multicore.github.io/eio/eio/Eio/Net/index.html) adds interfaces and platform tags to the same resource mechanism.
The tested stream-socket provider is an in-memory mock.
Its native interface matches Eio's provider module type.
That fact does not establish TCP, datagram, connection, or backend semantics.

The hosted documentation can describe a newer Eio release.
The installed `.mli` and implementation hashes bind every probe to Eio 1.2.
For example, current hosted Net error constructors differ from those installed here.

## What the interoperability probe does

The generic transfer client has only standard source and sink arguments.
It calls `Eio.Flow.copy` unchanged.
The generic line client calls standard `Eio.Buf_read` unchanged.

| Control | Observed result |
| --- | --- |
| Custom source to standard buffer sink | The exact binary payload arrives |
| Standard string source to custom sink | The exact binary payload arrives |
| Both custom, then both standard | The same transfer client works unchanged |
| Custom source with one-byte reads | Standard buffered reading reconstructs the line |
| Standard source | The same buffered client reconstructs the line |
| Custom sink with short writes | Standard copying retries until the payload is written |
| Vectored write with short writes | Standard writing retains vector order and retries |
| Read into a buffer slice | Only the returned prefix changes |
| `read_exact` reaches EOF early | Earlier bytes remain written in the destination |
| Additional typed method | Standard Flow copying and custom count lookup both work |
| Stream-socket provider | Standard Flow copy, shutdown, and Net close dispatch correctly |
| Missing native source method | The compiler rejects the provider module |
| Sink supplied as a source | The compiler rejects the missing read capability |

`probe.log` and `type-controls.log` retain the observations and compiler diagnostics.
The providers deliberately perform partial reads and writes.
The tests therefore exercise the standard retry paths, rather than only whole-buffer completion.

## A supported mathematical interface

The useful target has two parts: native type structure and method behavior.
The type structure should represent abstract types, existential packages, module equations, interface tags, labels, and native buffer types.
The behavior should relate method calls, host state, and mutable buffer observations.

For an initially readable source, relate its native state to an abstract unread byte sequence.
A successful read returns a positive count bounded by the destination view.
It writes that prefix, advances the unread sequence, and leaves the remaining destination bytes unchanged.
EOF is a separate outcome when no more bytes can be read.
Short reads remain permitted.

For a writable sink, relate its state to the bytes it has accepted.
A successful write can accept a positive prefix when the input vectors contain bytes.
The standard `write` operation repeats that method until all vectors are consumed.
The current API discourages concurrent writes to the same flow because their bytes can interleave.
Any proposed serial observation needs that client condition or an explicit interleaving model.

The [Flow contract](https://ocaml-multicore.github.io/eio/eio/Eio/Flow/index.html) supplies these partial-I/O distinctions.
The model must also retain state and buffer mutations before a later exception.
The finite EOF control demonstrates why treating failure as an unchanged state is wrong.

Method execution can suspend, fail, or finish.
Its mathematical description therefore needs a state-transition relation, rather than only a pure request-to-answer function.
Cancellation, cleanup, borrowed buffers, and backend errors require their own method contracts.
`Read_source_buffer` additionally forbids retaining borrowed views after its callback returns.
This probe advertises no borrowed-buffer method.

## What generation can claim

Generate the actual native module interfaces and provider dictionaries for a named supported Eio profile.
Retain Eio's abstract type equalities and native method types.
A data-row method returning bytes is insufficient to represent `single_read`, which mutates a caller-supplied buffer.
Such an implementation needs the buffer-mutation connector too.

A future verification result can connect a generated provider's modeled methods to its native interface contract.
That would let standard Eio consumers call it through the standard interface.
Conversely, generated clients can accept existing Eio providers directly.
Their behavioral guarantees remain conditional on those providers meeting the same contract.
Static type compatibility alone does not certify every existing native implementation.

The earlier resource probe also shows why dictionary construction must be controlled.
An arbitrary public `Resource.T` value can claim a tag without supplying its method.
The generated public factory should expose only validated dictionaries.
Native resources, buffers, and method closures remain runtime objects outside stored `Eff` syntax.

This proposal uses the existing host-protocol, state, and finalization concepts under R6, R8, and R11.
It adds no general LCNF lowering obligation while decisions rows 391 and 392 remain in force.
The next useful research slice models native SOURCE and SINK contracts, then generates this exact provider shape from that description.

## Reproduce

Run `sh docs/research/2026-10-15-ocaml-seam-probes/eio/native-contract/run.sh`.
Run `sh docs/research/2026-10-15-ocaml-seam-probes/eio/native-contract/check-types.sh`.
Run `python3 docs/research/2026-10-15-ocaml-seam-probes/eio/native-contract/capture.py` to refresh provenance.

The scripts compile copied files in temporary directories.
They install nothing and run no repository build.
The original Eio packet and concurrent production edits remain untouched.
