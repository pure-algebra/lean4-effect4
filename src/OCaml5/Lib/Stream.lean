import OCaml5.Lib.Sexp

/-!
# `OCaml5.Lib.Stream` — the explicit pull/push carriers

Status: seat W4 of the 2026-09-04 wave. Plan: `docs/research/2026-09-04-ocaml-packages-plan.md`
§4.2: "streaming as explicit pull/push carriers matching `Effect4/Channel`'s shapes". Report:
`docs/research/2026-09-04-seat-w4-library-carriers.md`.

**This module is the shape W2's daemon streams its replies in. It is written first and on
purpose: a streaming reply is a `Channel Sexp ε` — a finite sequence of `emit` chunks and
`pause` turns, terminated by exactly one `halt`, and nothing else.** `Stream.replyOfChunks`
builds one; `Runner` consumes one against a bounded buffer, which is where back-pressure lives.

## The state of `Effect4/Channel` (checked, 2026-09-04)

There is no `Effect4/Channel/`. The only `Channel` modules in the tree are
`git:c407ab7:vendor/foldlab/pinned/tree/formal/effect-core-v1/EffectCore/Channel/Core.lean` and
`.../Channel/Stream.lean`, both of which are **reserved empty module boundaries** — eleven lines
of docstring, `namespace EffectCore.Channel`, `end`. The only other trace of the shapes is the
rc.112 census in `src/Effect4/StdLib/Rc112.lean:32-34,1301-…`, which pins the digests of
`src/Stream.ts`, `src/Sink.ts` and `src/Channel.ts` and lists their exports. So the shapes here
are taken from **rc.112's own vocabulary** (`Take`, `Pull`, `Channel`, `Sink`, `Stream`), not
from an existing Lean carrier, and this module is the first Lean carrier for them.

## Named properties (theorem names are stable; cite these)

* `Runner.pipeline_invariant` — **FIFO and no loss and no duplication, in one equation**:
  `emitted = delivered ++ buffer ++ pending`, preserved by every step.
* `Runner.delivered_prefix_step` — `delivered` only ever grows by appending: an element is
  delivered **at most once**, and in emission order.
* `Runner.delivered_prefix_emitted` — what has been delivered is a prefix of what was emitted.
* `Runner.backpressure_bound` — **the bounded buffer**: `buffer.length ≤ capacity` is preserved
  by every step, and the producer step is the one that blocks (`Runner.step_blocks_when_full`).
* `Runner.terminator_once` — `ending` is written at most once: **exactly one terminator**, and
  once set it never changes.
* `Runner.terminator_only_at_halt` — and it is written only by the source's `halt`.
* `Channel.pull_halt_stable` — a halted channel keeps answering the same terminator.

## What each definition stands for

| here | rc.112 (`effect` rc.112, pinned in `src/Effect4/StdLib/Rc112.lean`) | Eio / Core |
| --- | --- | --- |
| `Take` | `Take.ts`: `Chunk` / `End` / `Failure`, plus `pending` for "the pull's effect has not resolved" | — |
| `Channel` | `Channel.ts`: a program that emits chunks downstream and terminates once | Eio's `Flow.source` (covered: `emit` is a `read`, `halt none` is `End_of_file`) |
| `Channel.pull` | `Stream.toPull` / `Stream.fromPull` (`Stream.ts:554,576`) | — |
| `Stream` | `Stream.ts`: a `Channel` with no input (`Stream.toChannel`, `:656`) | — |
| `Sink` | `Sink.ts`: the consuming end, here a **bounded** buffer | Eio's `Flow.sink` (covered for the write side; its `Buf_write` is not) |
| `Runner` | the driver that connects the two, fuel-bounded | — |

## Refusals

* **`Core.Sequence`.** `Sequence.t` is a closure pair (`state`, `step`) — higher-order, and its
  `Sequence.unfold` cannot be a first-order carrier. Anything the daemon or the avatar streams
  must be a `Channel`, not a `Sequence`. Refusal row `W4-STREAM-SEQUENCE`.
* **`Eio.Stream` (the bounded queue between fibers).** It is a *concurrency* object: two fibers,
  a mutex and a condition. Its carrier is the `Runner`'s buffer plus `OCaml5.Lib.Eio`'s fork,
  and the interleaving of the two fibers is the OCaml5 machine's, not this module's. Only the
  buffer bound is claimed here. Refusal row `W4-STREAM-EIO-STREAM`.
* **`Eio.Buf_read` / `Buf_write`.** Byte-level buffering with parser combinators; no carrier.
  Refusal row `W4-STREAM-EIO-BUF`.
* **At-least-once.** No retry model is defined, so **no at-least-once property is claimed**: a
  `Runner` whose fuel runs out has delivered a prefix and nothing is re-sent. A daemon that
  needs redelivery must carry an acknowledgement alphabet, which this carrier does not have.
  Refusal row `W4-STREAM-NO-RETRY`.
* **Chunk boundaries as semantics.** `emit [a, b]` and `emit [a]; emit [b]` deliver the same
  elements in the same order; nothing here distinguishes them, and no consumer may. Refusal row
  `W4-STREAM-CHUNK-BOUNDARY`.
-/

set_option autoImplicit false

namespace OCaml5.Lib

universe u

/-! ## The pull face -/

/-- rc.112's `Take` (`Take.ts`), plus `pending` for a pull whose effect has not resolved. -/
inductive Take (α ε : Type u) : Type u where
  /-- `Take.Chunk`. -/
  | chunk (xs : List α)
  /-- `Take.End`. -/
  | done
  /-- `Take.Failure`. -/
  | fail (e : ε)
  /-- The pull suspended: one scheduler turn passes and nothing is taken. -/
  | pending
deriving Repr

/-- A channel program (rc.112 `Channel.ts`), first-order: a finite sequence of chunk emissions
and scheduler turns, ending in exactly one terminator. A `Stream` is a `Channel` with no input
(`Stream.toChannel`, `Stream.ts:656`), which is this same type. -/
inductive Channel (α ε : Type u) : Type u where
  /-- Emit one chunk downstream, then continue. -/
  | emit (chunk : List α) (next : Channel α ε)
  /-- Yield one scheduler turn, then continue. -/
  | pause (next : Channel α ε)
  /-- Terminate: `none` is `Take.End`, `some e` is `Take.Failure e`. -/
  | halt (err : Option ε)
deriving Repr

/-- A `Stream` is a `Channel` with no input. -/
abbrev Stream (α ε : Type u) := Channel α ε

namespace Channel

variable {α ε : Type u}

/-- One pull: rc.112's `Stream.toPull` (`Stream.ts:554`). A halted channel stays halted. -/
def pull : Channel α ε → Take α ε × Channel α ε
  | .emit xs next => (.chunk xs, next)
  | .pause next => (.pending, next)
  | .halt none => (.done, .halt none)
  | .halt (some e) => (.fail e, .halt (some e))

/-- **A halted channel keeps answering the same terminator**: the terminator is stable, which is
what makes "exactly one terminator" observable at any pull. -/
theorem pull_halt_stable (e : Option ε) :
    (pull (Channel.halt (α := α) e)).2 = Channel.halt e := by
  cases e <;> rfl

/-- Everything a channel will ever emit. -/
def emitted : Channel α ε → List α
  | .emit xs next => xs ++ emitted next
  | .pause next => emitted next
  | .halt _ => []

/-- The terminator a channel will reach. -/
def terminator : Channel α ε → Option ε
  | .emit _ next => terminator next
  | .pause next => terminator next
  | .halt e => e

/-- A channel from a list of chunks, ending in `End`. -/
def ofChunks : List (List α) → Channel α ε
  | [] => .halt none
  | xs :: r => .emit xs (ofChunks r)

theorem emitted_ofChunks : ∀ cs : List (List α), (ofChunks (ε := ε) cs).emitted = cs.flatten
  | [] => rfl
  | xs :: r => by simp [ofChunks, emitted, emitted_ofChunks r]

end Channel

/-! ## The push face: a bounded sink -/

/-- rc.112's `Sink.ts`, as a **bounded** buffer: `capacity` is the back-pressure bound, `buffer`
is what is held, `delivered` is everything the consumer has taken, in order, and `ending` is the
one terminator. -/
structure Sink (α ε : Type u) : Type u where
  /-- The back-pressure bound. -/
  capacity : Nat
  /-- Held, FIFO: head is next out. -/
  buffer : List α := []
  /-- Taken by the consumer, in order. -/
  delivered : List α := []
  /-- `none` while open; `some none` is `End`, `some (some e)` is `Failure e`. -/
  ending : Option (Option ε) := none
deriving Repr

namespace Sink

variable {α ε : Type u}

/-- An empty sink of the given capacity. -/
def make (capacity : Nat) : Sink α ε := { capacity }

/-- Is there room for one more? -/
def hasRoom (s : Sink α ε) : Bool := s.buffer.length < s.capacity

/-- Accept one element at the tail (FIFO). -/
def enqueue (s : Sink α ε) (x : α) : Sink α ε := { s with buffer := s.buffer ++ [x] }

/-- The consumer takes one element from the head. -/
def consume (s : Sink α ε) : Sink α ε :=
  match s.buffer with
  | [] => s
  | x :: r => { s with buffer := r, delivered := s.delivered ++ [x] }

/-- Write the one terminator. Writing twice is refused: the first wins. -/
def close (s : Sink α ε) (e : Option ε) : Sink α ε :=
  match s.ending with
  | some _ => s
  | none => { s with ending := some e }

theorem capacity_enqueue (s : Sink α ε) (x : α) : (s.enqueue x).capacity = s.capacity := rfl
theorem capacity_consume (s : Sink α ε) : s.consume.capacity = s.capacity := by
  cases hb : s.buffer with
  | nil => simp [consume, hb]
  | cons x r => simp [consume, hb]
theorem capacity_close (s : Sink α ε) (e : Option ε) : (s.close e).capacity = s.capacity := by
  cases he : s.ending with
  | some v => simp [close, he]
  | none => simp [close, he]

/-- **The terminator is written at most once.** -/
theorem close_idem (s : Sink α ε) (e e' : Option ε) : (s.close e).close e' = s.close e := by
  cases he : s.ending with
  | some v => simp [close, he]
  | none => simp [close, he]

end Sink

/-! ## The driver -/

/-- The fuel-bounded driver: a source, the chunk it is part-way through, and the sink. `emitted`
is the ghost accumulator the conservation law is stated against. -/
structure Runner (α ε : Type u) : Type u where
  /-- The remaining source program. -/
  source : Channel α ε
  /-- The tail of the chunk currently being handed to the sink. -/
  pending : List α := []
  /-- Everything pulled out of the source so far, in order. -/
  emitted : List α := []
  /-- The consuming end. -/
  sink : Sink α ε
deriving Repr

namespace Runner

variable {α ε : Type u}

/-- Start a run of `c` into a sink of capacity `n`. -/
def start (c : Channel α ε) (n : Nat) : Runner α ε := { source := c, sink := Sink.make n }

/-- One step. The producer moves while the sink has room; when it is full the consumer runs
instead — that is the back-pressure. With nothing pending, the source is pulled; once the source
has halted, the sink drains. -/
def step (r : Runner α ε) : Runner α ε :=
  match r.pending with
  | x :: rest =>
    match r.sink.hasRoom with
    | true => { r with pending := rest, sink := r.sink.enqueue x }
    | false => { r with sink := r.sink.consume }
  | [] =>
    match r.sink.ending with
    | some _ => { r with sink := r.sink.consume }
    | none =>
      match r.source.pull with
      | (.chunk xs, next) => { r with source := next, pending := xs, emitted := r.emitted ++ xs }
      | (.pending, next) => { r with source := next }
      | (.done, next) => { r with source := next, sink := r.sink.close none }
      | (.fail e, next) => { r with source := next, sink := r.sink.close (some e) }

/-- Run for at most `n` steps. -/
def run : Nat → Runner α ε → Runner α ε
  | 0, r => r
  | n + 1, r => run n (step r)

/-! ### The laws -/

/-- The conservation invariant: what was pulled is exactly what has been delivered, plus what is
buffered, plus what is still being handed over. -/
def Conserves (r : Runner α ε) : Prop :=
  r.emitted = r.sink.delivered ++ r.sink.buffer ++ r.pending

/-! The five shapes a step can take, as equations, so every law below is a case analysis. -/

theorem step_move (r : Runner α ε) {x : α} {rest : List α} (hp : r.pending = x :: rest)
    (hroom : r.sink.hasRoom = true) :
    step r = { r with pending := rest, sink := r.sink.enqueue x } := by
  simp [step, hp, hroom]

theorem step_block (r : Runner α ε) {x : α} {rest : List α} (hp : r.pending = x :: rest)
    (hroom : r.sink.hasRoom = false) :
    step r = { r with sink := r.sink.consume } := by
  simp [step, hp, hroom]

theorem step_drain (r : Runner α ε) (hp : r.pending = []) {e : Option ε}
    (he : r.sink.ending = some e) :
    step r = { r with sink := r.sink.consume } := by
  simp [step, hp, he]

theorem step_chunk (r : Runner α ε) (hp : r.pending = []) (he : r.sink.ending = none)
    {xs : List α} {next : Channel α ε} (hs : r.source.pull = (.chunk xs, next)) :
    step r = { r with source := next, pending := xs, emitted := r.emitted ++ xs } := by
  simp [step, hp, he, hs]

theorem step_pause (r : Runner α ε) (hp : r.pending = []) (he : r.sink.ending = none)
    {next : Channel α ε} (hs : r.source.pull = (.pending, next)) :
    step r = { r with source := next } := by
  simp [step, hp, he, hs]

theorem step_done (r : Runner α ε) (hp : r.pending = []) (he : r.sink.ending = none)
    {next : Channel α ε} (hs : r.source.pull = (.done, next)) :
    step r = { r with source := next, sink := r.sink.close none } := by
  simp [step, hp, he, hs]

theorem step_fail (r : Runner α ε) (hp : r.pending = []) (he : r.sink.ending = none)
    {e : ε} {next : Channel α ε} (hs : r.source.pull = (.fail e, next)) :
    step r = { r with source := next, sink := r.sink.close (some e) } := by
  simp [step, hp, he, hs]

/-- Every step is one of the seven shapes. -/
theorem step_cases (r : Runner α ε) :
    (∃ x rest, r.pending = x :: rest ∧ r.sink.hasRoom = true) ∨
    (∃ x rest, r.pending = x :: rest ∧ r.sink.hasRoom = false) ∨
    (r.pending = [] ∧ ∃ e, r.sink.ending = some e) ∨
    (r.pending = [] ∧ r.sink.ending = none) := by
  cases hp : r.pending with
  | cons x rest =>
    cases hroom : r.sink.hasRoom
    · exact Or.inr (Or.inl ⟨x, rest, rfl, rfl⟩)
    · exact Or.inl ⟨x, rest, rfl, rfl⟩
  | nil =>
    cases he : r.sink.ending with
    | some e => exact Or.inr (Or.inr (Or.inl ⟨rfl, e, rfl⟩))
    | none => exact Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))

/-- **FIFO, no loss, no duplication.** One `step` preserves the conservation invariant. -/
theorem pipeline_invariant (r : Runner α ε) (h : Conserves r) : Conserves (step r) := by
  unfold Conserves at *
  rcases step_cases r with ⟨x, rest, hp, hroom⟩ | ⟨x, rest, hp, hroom⟩ | ⟨hp, e, he⟩ | ⟨hp, he⟩
  · rw [step_move r hp hroom]
    simp only [Sink.enqueue]
    rw [h, hp]; simp
  · rw [step_block r hp hroom]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; rw [h, hb]
    | cons y b' => simp only [Sink.consume, hb]; rw [h, hb]; simp
  · rw [step_drain r hp he]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; rw [h, hb]
    | cons y b' => simp only [Sink.consume, hb]; rw [h, hb]; simp
  · cases hs : r.source.pull with
    | mk t next =>
      cases t with
      | chunk xs => rw [step_chunk r hp he hs]; rw [h, hp]; simp
      | pending => rw [step_pause r hp he hs]; exact h
      | done => rw [step_done r hp he hs]; simp only [Sink.close, he]; exact h
      | fail e => rw [step_fail r hp he hs]; simp only [Sink.close, he]; exact h

theorem run_pipeline_invariant : ∀ (n : Nat) (r : Runner α ε), Conserves r → Conserves (run n r)
  | 0, _, h => h
  | n + 1, r, h => run_pipeline_invariant n (step r) (pipeline_invariant r h)

theorem start_conserves (c : Channel α ε) (n : Nat) : Conserves (start c n) := rfl

/-- **Delivered only ever grows by appending**: an element is delivered at most once, and in
order. -/
theorem delivered_prefix_step (r : Runner α ε) :
    r.sink.delivered <+: (step r).sink.delivered := by
  rcases step_cases r with ⟨x, rest, hp, hroom⟩ | ⟨x, rest, hp, hroom⟩ | ⟨hp, e, he⟩ | ⟨hp, he⟩
  · rw [step_move r hp hroom]; exact List.prefix_rfl
  · rw [step_block r hp hroom]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; exact List.prefix_rfl
    | cons y b' => simp only [Sink.consume, hb]; exact ⟨[y], rfl⟩
  · rw [step_drain r hp he]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; exact List.prefix_rfl
    | cons y b' => simp only [Sink.consume, hb]; exact ⟨[y], rfl⟩
  · cases hs : r.source.pull with
    | mk t next =>
      cases t with
      | chunk xs => rw [step_chunk r hp he hs]; exact List.prefix_rfl
      | pending => rw [step_pause r hp he hs]; exact List.prefix_rfl
      | done =>
        rw [step_done r hp he hs]; simp only [Sink.close, he]; exact List.prefix_rfl
      | fail e =>
        rw [step_fail r hp he hs]; simp only [Sink.close, he]; exact List.prefix_rfl

/-- **What has been delivered is a prefix of what was emitted.** -/
theorem delivered_prefix_emitted (r : Runner α ε) (h : Conserves r) :
    r.sink.delivered <+: r.emitted := by
  rw [h]
  exact ⟨r.sink.buffer ++ r.pending, by simp⟩

/-- **The bounded buffer.** `buffer.length ≤ capacity` is preserved by every step. -/
theorem backpressure_bound (r : Runner α ε) (h : r.sink.buffer.length ≤ r.sink.capacity) :
    (step r).sink.buffer.length ≤ (step r).sink.capacity := by
  rcases step_cases r with ⟨x, rest, hp, hroom⟩ | ⟨x, rest, hp, hroom⟩ | ⟨hp, e, he⟩ | ⟨hp, he⟩
  · rw [step_move r hp hroom]
    have hlt : r.sink.buffer.length < r.sink.capacity := by
      simpa [Sink.hasRoom] using hroom
    simp only [Sink.enqueue, List.length_append, List.length_cons, List.length_nil]
    omega
  · rw [step_block r hp hroom]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; simp [hb] at h ⊢
    | cons y b' => rw [hb] at h; simp only [Sink.consume, hb]; simp at h ⊢; omega
  · rw [step_drain r hp he]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; simp [hb] at h ⊢
    | cons y b' => rw [hb] at h; simp only [Sink.consume, hb]; simp at h ⊢; omega
  · cases hs : r.source.pull with
    | mk t next =>
      cases t with
      | chunk xs => rw [step_chunk r hp he hs]; exact h
      | pending => rw [step_pause r hp he hs]; exact h
      | done => rw [step_done r hp he hs]; simp only [Sink.close, he]; exact h
      | fail e => rw [step_fail r hp he hs]; simp only [Sink.close, he]; exact h

theorem run_backpressure_bound : ∀ (n : Nat) (r : Runner α ε),
    r.sink.buffer.length ≤ r.sink.capacity →
    (run n r).sink.buffer.length ≤ (run n r).sink.capacity
  | 0, _, h => h
  | n + 1, r, h => run_backpressure_bound n (step r) (backpressure_bound r h)

/-- The producer is the step that blocks when the buffer is full: nothing is enqueued and nothing
new is pulled, the consumer runs instead. -/
theorem step_blocks_when_full (r : Runner α ε) {x : α} {rest : List α}
    (hp : r.pending = x :: rest) (hfull : r.sink.hasRoom = false) :
    (step r).pending = r.pending ∧ (step r).emitted = r.emitted := by
  rw [step_block r hp hfull]
  exact ⟨rfl, rfl⟩

/-- **Exactly one terminator.** Once `ending` is set, no step changes it. -/
theorem terminator_once (r : Runner α ε) (e : Option ε) (h : r.sink.ending = some e) :
    (step r).sink.ending = some e := by
  rcases step_cases r with ⟨x, rest, hp, hroom⟩ | ⟨x, rest, hp, hroom⟩ | ⟨hp, e', he⟩ | ⟨hp, he⟩
  · rw [step_move r hp hroom]; simpa [Sink.enqueue] using h
  · rw [step_block r hp hroom]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; exact h
    | cons y b' => simp only [Sink.consume, hb]; exact h
  · rw [step_drain r hp he]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; exact h
    | cons y b' => simp only [Sink.consume, hb]; exact h
  · rw [he] at h; cases h

theorem run_terminator_once : ∀ (n : Nat) (r : Runner α ε) (e : Option ε),
    r.sink.ending = some e → (run n r).sink.ending = some e
  | 0, _, _, h => h
  | n + 1, r, e, h => run_terminator_once n (step r) e (terminator_once r e h)

/-- **And the terminator is written only by the source's `halt`.** While anything is pending, or
while the source's pull is a chunk or a pause, `ending` stays `none`. -/
theorem terminator_only_at_halt (r : Runner α ε) (h : r.sink.ending = none)
    (hne : (step r).sink.ending ≠ none) :
    r.pending = [] ∧
      ((r.source.pull).1 = Take.done ∨ ∃ e, (r.source.pull).1 = Take.fail e) := by
  rcases step_cases r with ⟨x, rest, hp, hroom⟩ | ⟨x, rest, hp, hroom⟩ | ⟨hp, e', he⟩ | ⟨hp, he⟩
  · exact absurd (by rw [step_move r hp hroom]; simpa [Sink.enqueue] using h) hne
  · refine absurd ?_ hne
    rw [step_block r hp hroom]
    cases hb : r.sink.buffer with
    | nil => simp only [Sink.consume, hb]; exact h
    | cons y b' => simp only [Sink.consume, hb]; exact h
  · rw [he] at h; cases h
  · refine ⟨hp, ?_⟩
    cases hs : r.source.pull with
    | mk t next =>
      cases t with
      | chunk xs =>
        exact absurd (by rw [step_chunk r hp he hs]; exact h) hne
      | pending =>
        exact absurd (by rw [step_pause r hp he hs]; exact h) hne
      | done => exact Or.inl rfl
      | fail e => exact Or.inr ⟨e, rfl⟩

end Runner

/-! ## The daemon's streaming reply shape (for W2)

A streaming reply **is** a `Channel Sexp ε`: chunks of sexps, terminated by exactly one `halt`.
`replyOfChunks` builds the common case. The daemon writes each `emit`'s chunk as
`OCaml5.Lib.Sexp.print` of each element and the `halt` as one terminator line; a reader turns
that back into a `Channel` and gets `Runner`'s laws for free. -/

namespace Stream

variable {ε : Type}

/-- A finished reply: these chunks, then `End`. -/
def replyOfChunks (cs : List (List Sexp)) : Channel Sexp ε := Channel.ofChunks cs

/-- A reply that fails after these chunks. -/
def replyFailing : List (List Sexp) → ε → Channel Sexp ε
  | [], e => .halt (some e)
  | xs :: r, e => .emit xs (replyFailing r e)

theorem replyOfChunks_terminator (cs : List (List Sexp)) :
    (replyOfChunks (ε := ε) cs).terminator = none := by
  induction cs with
  | nil => rfl
  | cons xs r ih => simpa [replyOfChunks, Channel.ofChunks, Channel.terminator] using ih

theorem replyFailing_terminator (cs : List (List Sexp)) (e : ε) :
    (replyFailing cs e).terminator = some e := by
  induction cs with
  | nil => rfl
  | cons xs r ih => simpa [replyFailing, Channel.terminator] using ih

end Stream

end OCaml5.Lib
