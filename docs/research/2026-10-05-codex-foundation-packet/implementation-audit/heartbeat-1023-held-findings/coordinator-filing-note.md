# Codex's held findings of 2026-10-06: the coordinator's filing note

Status: history, not authority. Codex watched the sessions while the coordinator's screen was
locked, and it held five notes. The owner pasted Codex's relay into the coordinator's session
on 2026-10-06 (`relay.txt`). The coordinator filed the advisories and the reviews that hold
their evidence, without the packets' copies of tracked sources and without their hash files.

| File here | From Codex's packet |
| --- | --- |
| `pending-advisory.md`, `review.md`, `carryforward.txt` | the heartbeat of 10:23 |
| `pending-advisory-0923.md` | the heartbeat of 09:23, which lists the five notes |
| `cards/` | the heartbeat of 07:23: the Cache finding, with a finite Python model |
| `host/` | the heartbeat of 07:23: the keyed lane's aggregate |
| `refs/review.md` | the heartbeat of 09:53: a helper for seat REFS, and the install rule's guard |

Do not run a script of this folder in place.

## What the coordinator did with each note

1. **Cache's count of awaiters had no owner after a key left the map.** The card is
   corrected (`docs/research/2026-10-05-claude-lead/module-cards/cache.md`, section 3). The
   cell has a second list, the detached records: each entry that left the map while its lookup
   was pending. The coordinator took the retained records and not a `Ref` for each entry: each
   step then stays one update of one cell. Codex's control is the probe's case CP9. It ran on
   both builds, for an eviction and for an invalidation, and each run gave the same answer
   (tested, one schedule each). Commit `8b471a8a`. No ruling changed.
2. **The keyed lane's aggregate counted a ledger's prediction as the host's observation.** It
   is two aggregates now: `noEntryWaits`, and `wholeObservationOnHost` in the strict reading
   (`harness/truth/session/check-keyed.ts`). The second is false for all four scenarios.
   Commit `34db7582`; `make check-host-protocol` passes.
3. **Seat MOVE's comparison held the two removal wrappers by their types only.** A
   coordinator's note in the receipt keeps the two kinds of evidence apart. The coordinator
   checked both bodies by `rfl`, with one red control of the same type. Commit `d61522d3`.
   Seat PUB puts the two lines into a battery of the Queue.
4. **The authoring comments promised more than `var_push_minted` gives.** Three docstrings
   and the generator's comment now promise a variable's reading, under that lemma's premises.
   Commit `1b2679f6`.
5. **The mask probe's two summary words said too much.** The report says
   `base constant while live` and `last two cuts equal`, and its header says what neither
   shows. Commit `d61522d3`.

Two notes needed no act.

- **The helper for seat REFS.** The seat found the same route alone: its step 2 landed
  `foldList_subset_of_at` with the proof of the top theorem (`00a37ffc` on `seat/refs`).
- **The install incident** is recorded already, and it is not opened again.
