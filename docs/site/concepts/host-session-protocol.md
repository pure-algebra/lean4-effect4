# Host session protocol and boundary

This page explains the host session protocol and boundary in Effect4. It covers the four-state protocol automaton, keyed call correlation, at-most-once reply application, and external host assumptions.

## The runtime concept {#runtime-concept}

Effect programs perform external operations by dispatching asynchronous requests to the host platform and awaiting responses. In Effect rc.112, fibers pause until external listeners resolve or reject promises.

Effect4 formalizes this boundary through a keyed host session (`Session`, `src/Effect4/Api/HostSession.lean`). External completions enter as host answers submitted and applied through strict protocol steps.

This architecture isolates external side effects from internal deterministic machine steps.

## Literature foundations {#literature}

The metatheory adapts session types from Wadler (2012) and Honda, Vasconcelos, and Kubo (1998). Structured session protocols track communication states and dual message exchanges.

Labeled transition systems and protocol automata adapt Lynch and Vaandrager (1995).

Mathematical models of external hosts adapt comodels from Plotkin and Power (2008), Uustalu (2015), and Ahman and Bauer (2020).

## What Effect4 keeps and what it cuts {#adaptations-and-cuts}

Effect4 governs host interaction using a four-state protocol automaton (`idle`, `awaitingAsync`, `parked`, `terminated`) in `Protocol` (`src/Effect4/Api/HostProtocol.lean`).

Host replies enter through explicit call correlation. Envelope fields (session, call identifier, key, and row) match responses to waiting operations.

Effect4 enforces at-most-once reply application (`applyReply`):
- Each correlation key is bound, submitted, and applied at most once.
- Applying a reply prepares the answer and resumes the waiting fiber once.
- A retired key cannot be applied again (`session_keys_once`).

Effect4 cuts internal handle transmission (decisions row 97, `E4-HOST-CE-007`). Host rows carrying internal handles like cells or scopes are rejected at table admission.

Host progress is an external driver assumption, not an internal proof obligation (`docs/core/host-boundary.md`).

## How to read the claims {#reading-claims}

The claims under this concept state that host communication adheres to protocol transitions and that admitted replies fit expected continuation types.

Key properties to inspect:
- [`keys-once`](#claim:keys-once): A reached run binds, submits, and applies each correlation key at most once.
- [`allows-answer`](#claim:allows-answer): Asynchronous response delivery is an allowed protocol transition from the awaiting state.
- [`host-progress`](#claim:host-progress): Eventual response arrival is recorded as an external assumption.

The table of claims on this page gives each claim's status and its statement.
