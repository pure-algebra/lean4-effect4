# Lane X notes — the Char room

Running notes of lane X (`workshop/Cas/LANDING.md`, "X — the Char room"). One dated entry per
module: what is retyped, what is deleted, what is generated, what is open. Times are the
machine clock (`Get-Date`).

## 2026-09-05 10:57 — start; state of the machine, and the plan the reading forced

Read in the given order: `LANDING.md` (the X section, "The one lake, by lock" with its
`LEAN_NUM_THREADS` paragraph, "Layout after the landing"), `BRIEF.md`, the facts note §5
(Q1–Q8, Q3 and Q4 closely) and §6a, the plan §3 (the kind table) and §5 (the lane rows),
`NOTES-L1.md` (all five entries and the "Open" list), `REPORT-S1.md`, `REPORT-S2.md`; then
`src/Effect4/Store/{Canonical,Digest,Node,Kind,Genesis}.lean`, `Store/PinDerived.lean` (the
generated model, with its `--kind` line at 168), `scripts/generate-derived.ps1` (the manifest
and the invocation), and the whole Char room.

Machine: no `lean.exe`/`lake.exe`, no `LAKE.lock`; `LAKE.log` shows lane U released at
10:56:52 with exit 0, so this lane runs alone. `git status` shows U's seven `Surface/*.lean`
files and nothing of mine.

Facts checked before writing a line:

- Nothing outside the room consumes it: the only importers of `Effect4.Evidence.Char.*` are
  `src/Effect4.lean:166-169` (four import lines, unchanged by this lane) and the room's own
  modules. There is no `Test/Evidence/Char/` directory, so plan §5's "the batteries re-pinned"
  (lane Y's row) is empty at the landing.
- The Queue room names no address: a grep for `digestOf|addr|address|Canonical|Store.|json|hex|
  Digest` over `Evidence/Char/Queue/**` and over `Core.lean` matches only two prose lines in
  `Core.lean` (30, 397). So the Queue changes not at all, as the landing expects.
- `digestOf` no longer exists (L1's `Store/Digest.lean` is the spike's); `Canonical.digest` is
  the payload digest and `address` the node address. `address` is declared under `variable
  [Content Document]` (`Store/Node.lean:330,363`), so every module that calls it must have
  `Effect4.Store.Genesis` in its import closure (`instContentDocument`, `Genesis.lean:36`).
- `Ref α` is a plain structure over `Digest` (`Store/Node.lean:53`) and needs **no** instance to
  be named in a field type; only `instCanonicalRef` (line 102) needs `[Content α]`. That is what
  makes the retypings possible before `Char/Derived.lean` exists.

### The four ordering facts that shaped the layout

1. A generated `Canonical T` for a carrier with a `Ref β` field needs `Content β` **first**, and
   `--kind` emits `Content` right after that type's `Canonical` (the PinDerived model). So one
   generated file can carry the whole room if its type list is in dependency order.
2. `Evidence.fixture (… ) (receipt : Ref Receipt)` names `Receipt`, which `Conformance/
   Consume.lean` declares. To keep the field **typed** (the landing's wording; `AnyRef` is the
   escape only "where a `Ref` needs a type parameter the room cannot name"), `Evidence.lean`
   now imports `Conformance/Consume.lean`. No cycle: `Consume.lean` never mentions `Evidence`
   (its `asFixtureEvidence` answers refs, not an `Evidence`).
3. The generic hand instances must exist **before** `Consume.lean` (`receiptOf` addresses a
   `Fact`) and before `Surface.lean` (`Characterized.ofParts` addresses a `VectorSet` and a
   `Receipts`). So `src/Effect4/Evidence/Char/Canonical.lean` sits between `Conformance/
   Vector.lean` and `Conformance/VectorSet.lean`, and `Derived.lean` reaches it transitively —
   the landing's "imported by Derived" holds.
4. `Cell.lean` is the room's worked instance: it builds a `Target` and calls
   `Characterized.ofParts`, so it needs `Content Target` and `Content Implementation`, which are
   generated. So `Cell.lean` imports `Char/Derived.lean` and is the one module of the room below
   it. Its own alphabet `Label` therefore cannot be generated (the generated file would have to
   import `Cell.lean` to see it, and `Cell.lean` imports the generated file); its instance is
   hand, written in the generator's shape. Recorded as a departure.

### The import order after this lane

`Core → Conformance/{GSet, Vector} → Char/Canonical → Conformance/{VectorSet, Generators,
Compose, Consume} → Evidence → Manifest → Conformance/Surface → Char/Derived →
Conformance/Cell → Conformance` (the doc root). `Queue/*` hangs off `Core` and is untouched.
