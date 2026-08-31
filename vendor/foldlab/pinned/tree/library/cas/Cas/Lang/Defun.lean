import Cas.Lang.Representation
import Cas.Grammar.Sorts

/-!
# Defunctionalized code points — F3, first bite (grammar ruling 4)

The Reynolds move: a straight-line store program becomes a finite table
of first-order nodes. `PLine` is one code point — a `put` whose operands
name a literal address or the i-th earlier answer POSITIONALLY (no
binders), or a `load` of such an operand. `PProg` is the table; the
designated result is the last answer.

Three faces, tied by theorems:

- `embed` is the host-level program a table denotes — a `Prog CasSig`
  that resolves `ans i` against the growing answer history and refuses
  (`failWith`) on a dangling index or an empty table;
- `runP` is the DIRECT interpreter: it walks the table over the word
  calling the SAME machinery `step` uses — `putWord` is now literally
  the reference handler's `put` clause under a local name (R10: meaning
  lives in one place, so the clause is not spelled twice), and load is
  `Word.find`, exactly `step`'s load case;
- `encodeLine`/`decodeLine` put the code points INTO the store: a line
  is a `Node` at wire tag 14 (step nodes; tag 15 is the table node) —
  the reserved registry rows another agent is landing — and `encodeProg`
  lays the table out children-first as a `Word` whose final binding is
  the tag-15 table node referencing every line. The program IS content.

## Theorem statements (the designed set)

Proved below:

- `step_put_putWord` — a corollary of `step_handle` (`Handler.lean`)
  since the handler bridge landed: `putWord` IS the reference handler's
  put clause, so the direct interpreter cannot drift from `step` on
  puts, by construction rather than by a coincidence of two bodies.
- `runPFrom_embedFrom` — the packaged induction: over any word and any
  answer history, running the embedding with fuel `p.length + 1` equals
  the direct interpreter, status AND word.
- `runP_embed_agree` — AGREEMENT (the heart, F1's pattern):
  `run H (p.length + 1) (embed p) w = runP H p w`. The fuel is exact:
  one step per line (each line is one vis node on the executed path)
  plus one closing step (the final `pure`, or the refusal vis).
- `runP_preserves_wf` — the direct interpreter preserves word
  admission (L7, inherited through the agreement).
- `runPFrom_halts` / `runP_halts` — the direct interpreter always
  reports a halted status, which is what makes it a gate.
- `ObsEq_embed_of_runP` — the word gate READ as a stratum-3 equality:
  tables whose direct runs agree at every word denote observationally
  equal programs. R5's observation and R14's `ObsEq` are one thing,
  through the R10 bridge.
- `readPIn_encodePIn`, `readPRef_encodePRef` — operand and typed-ref
  round trips over the shared byte primitives (`nat32`, `readChunk`).
  UN-PARKED 2026-08-29: rolled back on 2026-08-28 for kernel-memory
  exhaustion, restored by staging the proofs against abstract byte
  strings (see the staging note above `readPIn_zero`).
- `decodeLine_encodeLine` — the code-point round trip:
  `decodeLine (encodeLine l) = some l` for well-formed lines. UN-PARKED
  2026-08-29 by the same decomposition; this is the theorem whose
  monolithic proof caused the OOM-killed builds.
- `encodeProg_wf` — the encoded table ADMITS as a word
  (`Word.wf (encodeProg H p) = true`) for EVERY address function `H`,
  hash-lattice Level 0: line nodes carry no references and the table
  node's references resolve against the line bindings laid down first.

- `readPIn_exact`, `readPRef_exact`, `readLine_exact`, `decodeLine_exact`
  — EXACTNESS (owed item, discharged 2026-08-29): the decoder accepts
  nothing outside the encoder's image, in the style of the codec's
  `readFrame_exact`. A successful read proves its input was an encoding
  AND proves the well-formedness the forward direction demands.

- `decodeProg` / `decodeProg_encodeProg` — THE TABLE-LEVEL DECODER
  (owed item, discharged 2026-08-29): `Word → Option PProg`, reading the
  word `encodeProg` laid down back to exactly the table. Two premises,
  both triaged at the decoder's section note: `hwf` (the encodability
  condition the line round trip already carries) and `hsep` (the address
  function separates the table's lines — NECESSARY, not convenient, and
  strictly weaker than `Function.Injective H`).
- `runP_decodeProg_encodeProg`, `ObsEq_decodeProg_encodeProg` — THE
  CAPABILITY ROUND TRIP: a table stored as content and recovered from
  that content runs identically, and denotes an observationally equal
  program. The program IS content, as one theorem.

- `PProg.envelope` and THE SANDWICH (2026-08-29) — the table's static
  analysis, and the proof that a run stays inside it. The envelope is
  computed from the table alone (reads, put shapes, the answer-index
  dataflow DAG); `runPFrom_puts_sound` bounds the word a run leaves by
  the declared put shapes IN ORDER, `PProg.resolve_sound` and
  `runPFrom_absent_sound` bound the addresses it consults,
  `runPFrom_load_absent`/`runPFrom_load_present` give the lower bound so
  it is not vacuous, and `runPFrom_done_answers` proves DESIGN.md §2.1's
  hash-determined dataflow: given `H`, the answer history is a pure
  recursion on the table. Where the over-approximation lives is stated
  and exhibited rather than hidden — see that section's triage note.
- `runP_no_dangling` — a refusal class the envelope decides WITHOUT
  running: a table whose dataflow DAG is closed cannot refuse for a
  dangling answer index, at any word.
- `envelope_decodeProg_encodeProg` — the store content determines the
  envelope: a table recovered from its own bytes analyses identically.

- `PLine.HashDetermined` and `PLine.hashDetermined` — HD-1
  (2026-08-29): the BOUNDARY, named. The property `PLine.answer`
  already computes — a total function from an operation's arguments to
  the address it answers that no handler may contradict — defined, and
  discharged for `CasSig` out of `putWord_answer` (put half, Level 0)
  and `PIn.resolve` (load half, `rfl`). The definition's docstring
  carries the ruling the boundary decides: inside it, no trace store;
  outside it, `(out, deps, recipe)` from `Persistable`. The closing
  witness of this module exhibits the outside.
- `PProg.answersFrom_prefix`, `runPFrom_append_done`,
  `runPFrom_frame_sound`, `runP_frame_sound` — FRAME-1 (2026-08-29):
  the frame condition for EVERY run and not only `done` ones, which is
  what `Fragments.lean`'s interop claim 1 states. The history a run
  reaches a line in is `answersFrom` up to that line
  (`runPFrom_append_done`), that history is a prefix of the whole
  table's (`answersFrom_prefix`), and so every address any reached line
  consults lies in `reads ∪ answersFrom` — refusing runs included.

Owed (stated, not yet proved — named follow-ups, not weakened):

- (discharged 2026-08-29) wire tags 14/15 were registry RESERVATIONS
  mirrored here as literals. They are now the `Ty.step` and `Ty.cont`
  sorts, with forms in `Cas.Grammar.manifestV0` witnessed by
  `encodeLine` and `tableNode`; this module writes the sorts' own tags.

This module is the APPLICATIVE-STRENGTH rung of the fragment tower.
`Cas/Lang/Fragments.lean` states the whole ladder and the interop
contract each rung offers another effect system; read it before coding
against a table.
-/

namespace Cas.Lang

open Cas.Grammar (schemeVersion)

/-- Wire tag of a step (code-point) node — `REGISTRY.md` row 14,
the `step` sort, 0x0E. An abbreviation for `Ty.step.wireTag`, kept so
this module's theorem statements read in its own vocabulary. -/
abbrev stepWireTag : UInt8 := Cas.Grammar.Ty.step.wireTag

/-- Wire tag of a table (continuation) node — `REGISTRY.md` row 15,
the `cont` sort, 0x0F. An abbreviation for `Ty.cont.wireTag`. -/
abbrev contWireTag : UInt8 := Cas.Grammar.Ty.cont.wireTag

/-! ### The reconciliation debt, DISCHARGED 2026-08-29

Rows 14 and 15 were spelled here as bare `UInt8` defs, OUTSIDE
`Cas.Grammar.Ty`'s registry, while growing `Ty` was still F3's own
unscheduled slice. Two guards held the reservation open: they pinned
the literals against `REGISTRY.md`, and they pinned `Ty.ofTag`'s
REFUSAL of both tags, so that the day the rows were ratified this
file's build would go red and this would be the site that had to
follow.

That day was 2026-08-29 (G3 of the reification-substrate growth order).
The rows are sorts: `Ty.step` and `Ty.cont`, with forms in
`Cas.Grammar.manifestV0` witnessed by `encodeLine` and `tableNode`
below. The refusal guards went red exactly as designed and are gone —
a reservation cannot be pinned once it is spent. The names survive as
abbreviations of the sorts' own tags, so nothing downstream churns and
no literal is written twice: `Ty.wireTag` is now the only place either
number appears. -/

/-- A positional operand: a literal address, or the i-th earlier
answer. No binders — the Reynolds defunctionalization keeps every code
point first-order. -/
inductive PIn where
  | lit (a : Addr32)
  | ans (i : Nat)
  deriving DecidableEq

/-- Operand well-formedness: an answer index fits the 32-bit wire
field. -/
def PIn.WF : PIn → Prop
  | .lit _ => True
  | .ans i => i < 4294967296

/-- One straight-line code point: admit a node whose references name
operands, or load an operand. -/
inductive PLine where
  | put (version tag : UInt8) (payload : Bytes) (refs : List (UInt8 × PIn))
  | load (src : PIn)
  deriving DecidableEq

/-- A defunctionalized program: a finite table of code points. The
designated result is the last answer. -/
abbrev PProg := List PLine

/-- Line well-formedness: byte-bound fields (matching `Node.WF`'s
bounds) and well-formed operands. -/
def PLine.WF : PLine → Prop
  | .put _ _ payload refs =>
      payload.length < 4294967296 ∧ refs.length < 4294967296 ∧
        ∀ r ∈ refs, r.2.WF
  | .load src => src.WF

/-- Resolve an operand against the answer history (absolute
indexing: `ans i` is the i-th line's answer). -/
def PIn.resolve (env : List Addr32) : PIn → Option Addr32
  | .lit a => some a
  | .ans i => env[i]?

/-- Resolve a line's operand references into typed references. -/
def resolveRefs (env : List Addr32) (refs : List (UInt8 × PIn)) :
    Option (List Ref) :=
  refs.mapM fun r => (r.2.resolve env).map (Ref.mk r.1)

/-! ## The embedding — what a table denotes -/

/-- The host-level program a table denotes, from a given answer
history: resolve each line's operands, perform the operation, extend
the history with the answered address (a load answers its source
address into the history), and finish at the last answer. A dangling
index or an empty table refuses. -/
def embedFrom (env : List Addr32) : PProg → Prog CasSig Addr32
  | [] =>
    match env.getLast? with
    | some a => .pure a
    | none => failWith "defun: empty program"
  | .put v t payload refs :: rest =>
    match resolveRefs env refs with
    | some rs =>
      .vis (.put ⟨v, t, payload, rs⟩) fun (a : Addr32) => embedFrom (env ++ [a]) rest
    | none => failWith "defun: dangling answer index"
  | .load src :: rest =>
    match src.resolve env with
    | some a => .vis (.load a) fun _ => embedFrom (env ++ [a]) rest
    | none => failWith "defun: dangling answer index"

/-- The host-level program a table denotes. -/
def embed (p : PProg) : Prog CasSig Addr32 := embedFrom [] p

/-! ## The direct interpreter — the same machinery `step` calls -/

section Interp

variable (H : Bytes → Addr32)

/-- The interpreter's put case as a function over the word — the NAME
of the reference handler's `put` clause, not a second spelling of it.
Meaning lives in exactly one place (R10, `Handler.lean`), so the
duplicated body that used to stand here retired with the bridge; what
remains is a local abbreviation for the table walker's benefit. -/
def putWord (n : Node) (w : Word) : Except Refusal (Addr32 × Word) :=
  (referenceHandler H).handle (.put n) w

/-- The bridge, now a corollary: `putWord` IS `step`'s put case,
because both are the reference handler's clause (`step_handle` at
`op = .put n`). The direct interpreter cannot drift from the
interpreter on puts — by construction rather than by coincidence. -/
theorem step_put_putWord {A} (n : Node) (k : Addr32 → Prog CasSig A)
    (w : Word) :
    step H (.vis (.put n) k) w
      = match putWord H n w with
        | .ok (a, w') => (.running (k a), w')
        | .error r => (.refused r, w) := by
  have h := step_handle H (.put n) k w
  unfold putWord
  cases hh : (referenceHandler H).handle (CasE.put n) w with
  | ok aw =>
    obtain ⟨a, w'⟩ := aw
    simp only [hh] at h ⊢
    exact h
  | error r =>
    simp only [hh] at h ⊢
    exact h

/-- The direct interpreter, answer history explicit: execute each line
over the word through `putWord` (puts) and `Word.find` (loads —
exactly `step`'s load case), threading the history. -/
def runPFrom (env : List Addr32) :
    PProg → Word → Status CasSig Addr32 × Word
  | [], w =>
    match env.getLast? with
    | some a => (.done a, w)
    | none => (.refused (.failed "defun: empty program"), w)
  | .put v t payload refs :: rest, w =>
    match resolveRefs env refs with
    | some rs =>
      match putWord H ⟨v, t, payload, rs⟩ w with
      | .ok (a, w') => runPFrom (env ++ [a]) rest w'
      | .error r => (.refused r, w)
    | none => (.refused (.failed "defun: dangling answer index"), w)
  | .load src :: rest, w =>
    match src.resolve env with
    | some a =>
      match Word.find w a with
      | some _ => runPFrom (env ++ [a]) rest w
      | none => (.refused (.noObject a), w)
    | none => (.refused (.failed "defun: dangling answer index"), w)

/-- The direct interpreter: walk the table over the word. -/
def runP (p : PProg) (w : Word) : Status CasSig Addr32 × Word :=
  runPFrom H [] p w

/-- The packaged induction behind the agreement: over ANY answer
history and ANY word, running the embedding with fuel `p.length + 1`
equals the direct interpreter — status and word. Each executed line is
one vis node (one fuel); the closing step (the final `pure` or the
refusal vis) is the `+ 1`. -/
theorem runPFrom_embedFrom (env : List Addr32) (p : PProg) :
    ∀ w : Word,
      run H (p.length + 1) (embedFrom env p) w = runPFrom H env p w := by
  induction p generalizing env with
  | nil =>
    intro w
    simp only [embedFrom, runPFrom, List.length_nil]
    cases env.getLast? with
    | some a => simp [run, step]
    | none => simp [run, step, failWith]
  | cons line rest ih =>
    intro w
    cases line with
    | put v t payload refs =>
      simp only [embedFrom, runPFrom, List.length_cons]
      cases hr : resolveRefs env refs with
      | none => simp [run, step, failWith]
      | some rs =>
        have hstep := step_put_putWord H ⟨v, t, payload, rs⟩
          (fun (a : Addr32) => embedFrom (env ++ [a]) rest) w
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | ok aw =>
          obtain ⟨a, w'⟩ := aw
          rw [hp] at hstep
          simp only [hp]
          calc run H (rest.length + 1 + 1)
                (.vis (.put ⟨v, t, payload, rs⟩)
                  fun (a : Addr32) => embedFrom (env ++ [a]) rest) w
              = run H (rest.length + 1) (embedFrom (env ++ [a]) rest) w' :=
                run_step_running H hstep (rest.length + 1)
            _ = runPFrom H (env ++ [a]) rest w' := ih (env ++ [a]) w'
        | error r =>
          rw [hp] at hstep
          simp [run, hstep, hp]
    | load src =>
      simp only [embedFrom, runPFrom, List.length_cons]
      cases hr : src.resolve env with
      | none => simp [run, step, failWith]
      | some a =>
        cases hf : Word.find w a with
        | some n =>
          have hstep : step H
              (.vis (.load a) fun _ => embedFrom (env ++ [a]) rest) w
              = (.running (embedFrom (env ++ [a]) rest), w) := by
            simp [step, hf]
          simp only [hf]
          calc run H (rest.length + 1 + 1)
                (.vis (.load a) fun _ => embedFrom (env ++ [a]) rest) w
              = run H (rest.length + 1) (embedFrom (env ++ [a]) rest) w :=
                run_step_running H hstep (rest.length + 1)
            _ = runPFrom H (env ++ [a]) rest w := ih (env ++ [a]) w
        | none =>
          have hstep : step H
              (.vis (.load a) fun _ => embedFrom (env ++ [a]) rest) w
              = (.refused (.noObject a), w) := by
            simp [step, hf]
          simp [run, hstep, hf]

/-- AGREEMENT (the heart of F3's first bite, F1's proof pattern): the
direct interpreter and the embedded program agree — status AND final
word — with fuel exactly the line count plus one. -/
theorem runP_embed_agree (p : PProg) (w : Word) :
    run H (p.length + 1) (embed p) w = runP H p w :=
  runPFrom_embedFrom H [] p w

/-- The direct interpreter preserves word admission — L7, inherited
through the agreement rather than re-proved. -/
theorem runP_preserves_wf (p : PProg) {w : Word}
    (hw : Word.wf w = true) : Word.wf (runP H p w).2 = true := by
  rw [← runP_embed_agree]
  exact run_preserves_wf H _ _ hw

/-- The direct interpreter always halts, from any answer history: it
walks a finite table and every clause reports `done` or `refused`. -/
theorem runPFrom_halts (env : List Addr32) (p : PProg) (w : Word) :
    (runPFrom H env p w).1.isRunning = false := by
  induction p generalizing env w with
  | nil => cases hg : env.getLast? <;> simp [runPFrom, hg, Status.isRunning]
  | cons line rest ih =>
    cases line with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none => simp [runPFrom, hr, Status.isRunning]
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error r => simp only [runPFrom, hr, hp]; rfl
        | ok aw =>
          obtain ⟨a, w'⟩ := aw
          simp only [runPFrom, hr, hp]
          exact ih _ _
    | load src =>
      cases hs : src.resolve env with
      | none => simp [runPFrom, hs, Status.isRunning]
      | some a =>
        cases hf : Word.find w a with
        | none => simp only [runPFrom, hs, hf]; rfl
        | some n =>
          simp only [runPFrom, hs, hf]
          exact ih _ _

/-- `runP` reports a HALTED status, always — which is what makes it a
gate rather than an approximation. -/
theorem runP_halts (p : PProg) (w : Word) :
    (runP H p w).1.isRunning = false := runPFrom_halts H [] p w

/-- THE WORD GATE, as a stratum-3 equality: two tables whose DIRECT
runs agree at every starting word denote observationally equal
programs. `runP` is what the emitter's gate executes, at the exact fuel
`p.length + 1`; `ObsEq` is R14's stratum-3 equation over `interpretRef`.
This corollary — the bridge (`run_interpretRef_agree`) applied through
`runP_embed_agree` — is what makes R5's word observation and that
equation ONE thing rather than two claims that resemble each other.

Note what the hypothesis compares and the conclusion does not: `runP`
agreement includes the refusal WORD, `ObsEq` does not carry it. The
gate therefore decides `ObsEq` by checking something strictly finer;
the implication runs only in this direction, and `ObsEq.run_refused`
(`Representation.lean`) is the exact statement of the shortfall. -/
theorem ObsEq_embed_of_runP {p q : PProg}
    (h : ∀ w : Word, runP H p w = runP H q w) :
    ObsEq H (embed p) (embed q) :=
  ObsEq.of_run H fun w =>
    ⟨p.length + 1, q.length + 1,
      by rw [runP_embed_agree, runP_embed_agree, h w],
      by rw [runP_embed_agree]; exact runP_halts H p w⟩

end Interp

/-! ## Content encoding — the program as store nodes -/

/-- Encode an operand: `0x00` then the 32 address bytes, or `0x01`
then the index as `nat32`. -/
def encodePIn : PIn → Bytes
  | .lit a => 0 :: a.val
  | .ans i => 1 :: nat32 i

/-- Read one operand. -/
def readPIn : Bytes → Option (PIn × Bytes)
  | [] => none
  | b :: rest =>
    if b = 0 then
      match readChunk 32 rest with
      | some (c, rest') =>
        if h : c.length = 32 then some (.lit ⟨c, h⟩, rest') else none
      | none => none
    else if b = 1 then
      match readNat32 rest with
      | some (i, rest') => some (.ans i, rest')
      | none => none
    else none

/-! ### The operand round trip, staged

The 2026-08-28 rollback died of ONE cause, and `NodeCodec.lean` had
already measured it: "two-stage proofs check instantly; three-stage
exhausts the kernel". The parked proofs rewrote the byte primitives
straight into the CONCRETE encoding term under a nested `match` motive,
so every stage multiplied the motive the kernel re-checked.

The cure is the same one the node codec uses: each `match` scrutinee is
discharged against an ABSTRACT byte string in its own lemma, and the
concrete encoding meets the reader only at the final `exact`. The
motives stay one stage wide and the kernel never sees the composition. -/

/-- The reader's literal-address arm, at an abstract tail. -/
theorem readPIn_zero (r : Bytes) :
    readPIn (0 :: r) =
      match readChunk 32 r with
      | some (c, rest') =>
        if h : c.length = 32 then some (PIn.lit ⟨c, h⟩, rest') else none
      | none => none := rfl

/-- The reader's answer-index arm, at an abstract tail. -/
theorem readPIn_one (r : Bytes) :
    readPIn (1 :: r) =
      match readNat32 r with
      | some (i, rest') => some (PIn.ans i, rest')
      | none => none := rfl

/-- OPERAND ROUND TRIP (un-parked): the operand reader recovers a
well-formed operand and consumes exactly its encoding. -/
theorem readPIn_encodePIn (x : PIn) (h : x.WF) (rest : Bytes) :
    readPIn (encodePIn x ++ rest) = some (x, rest) := by
  cases x with
  | lit a =>
    show readPIn (0 :: (a.val ++ rest)) = _
    rw [readPIn_zero, readChunk_append rest a.property]
    dsimp only
    rw [dif_pos a.property]
  | ans i =>
    show readPIn (1 :: (nat32 i ++ rest)) = _
    rw [readPIn_one, readNat32_nat32 i h rest]

/-- Encode one typed operand reference: the expected kind tag byte,
then the operand. -/
def encodePRef (r : UInt8 × PIn) : Bytes := r.1 :: encodePIn r.2

/-- Read one typed operand reference. -/
def readPRef : Bytes → Option ((UInt8 × PIn) × Bytes)
  | [] => none
  | t :: rest =>
    match readPIn rest with
    | some (i, rest') => some ((t, i), rest')
    | none => none

/-- TYPED-REF ROUND TRIP (un-parked): the kind tag passes through and the
operand round trip carries the rest. -/
theorem readPRef_encodePRef (r : UInt8 × PIn) (h : r.2.WF) (rest : Bytes) :
    readPRef (encodePRef r ++ rest) = some (r, rest) := by
  obtain ⟨t, i⟩ := r
  show readPRef (t :: (encodePIn i ++ rest)) = _
  rw [show readPRef (t :: (encodePIn i ++ rest))
      = match readPIn (encodePIn i ++ rest) with
        | some (x, rest') => some ((t, x), rest')
        | none => none from rfl,
    readPIn_encodePIn i h rest]

/-- `readN` under a membership-relative round trip: the counted-
sequence reader recovers a list whose ELEMENTS satisfy the reader's
premise. The codec's `readN_encode` quantifies its hypothesis over all
values; the encoding here round-trips only on well-formed operands, so
the induction is repackaged with the premise carried by membership.
Its consumer is `decodeLine_encodeLine`, which was rolled back on
2026-08-28 and restored here on 2026-08-29; this lemma is what the
restored proof reuses instead of re-proving. -/
theorem readN_encode_of {α : Type} {p : Bytes → Option (α × Bytes)}
    {e : α → Bytes} {P : α → Prop}
    (hp : ∀ a, P a → ∀ rest, p (e a ++ rest) = some (a, rest)) :
    ∀ (xs : List α), (∀ a ∈ xs, P a) → ∀ rest : Bytes,
      readN p xs.length ((xs.map e).flatten ++ rest) = some (xs, rest) := by
  intro xs
  induction xs with
  | nil => intro _ rest; simp [readN]
  | cons a t ih =>
    intro hP rest
    have h1 := hp a (hP a List.mem_cons_self) ((t.map e).flatten ++ rest)
    have h2 := ih (fun b hb => hP b (List.mem_cons_of_mem a hb)) rest
    simp only [List.length_cons, List.map_cons, List.flatten_cons,
      List.append_assoc, readN, h1, h2]

/-- Encode a line's body: `0x00`, version, tag, framed payload, ref
count as `nat32`, then the typed operand references — all through the
shared byte primitives; or `0x01` then the operand for a load. -/
def encodeLineBody : PLine → Bytes
  | .put v t payload refs =>
      0 :: v :: t ::
        (frame payload ++
          (nat32 refs.length ++ (refs.map encodePRef).flatten))
  | .load src => 1 :: encodePIn src

/-- Read one line body, consuming the whole byte string. -/
def readLine : Bytes → Option PLine
  | [] => none
  | b :: rest =>
    if b = 0 then
      match rest with
      | v :: t :: body =>
        match readFrame body with
        | some (payload, r1) =>
          match readNat32 r1 with
          | some (cnt, r2) =>
            match readN readPRef cnt r2 with
            | some (refs, []) => some (.put v t payload refs)
            | _ => none
          | none => none
        | none => none
      | _ => none
    else if b = 1 then
      match readPIn rest with
      | some (src, []) => some (.load src)
      | _ => none
    else none

/-- A code point as a store node: wire tag 14, the line body as
payload, no references — the opaque-payload discipline of the v0 step
sort (operand references live in the payload because they name
ANSWERS, which have no address until the table runs). -/
def encodeLine (l : PLine) : Node :=
  ⟨schemeVersion, stepWireTag, encodeLineBody l, []⟩

/-- Decode a step node back to its code point. -/
def decodeLine (n : Node) : Option PLine :=
  if n.tag = stepWireTag then readLine n.payload else none

/-! ### The code-point round trip, staged

This is the theorem whose monolithic proof exhausted kernel memory on
2026-08-28. `readLine`'s put arm is a FOUR-stage nested match (frame,
count, counted refs, trailing-empty), and the parked proof drove all
four stages simultaneously through the concrete encoding term in one
`simp only`. Per `NodeCodec.lean`'s measured determination that is the
shape that does not check.

The two lemmas below are the decomposition: each takes its stage
scrutinees as HYPOTHESES over abstract byte strings, so the match
motives are one stage wide and mention no encoding at all. The concrete
encoding is supplied once, at the call site, as three already-proved
byte-primitive facts. -/

/-- The line reader's put arm, driven by its three stage results over an
abstract body. -/
theorem readLine_put_of (v t : UInt8) {body payload r1 r2 : Bytes}
    {cnt : Nat} {refs : List (UInt8 × PIn)}
    (h1 : readFrame body = some (payload, r1))
    (h2 : readNat32 r1 = some (cnt, r2))
    (h3 : readN readPRef cnt r2 = some (refs, [])) :
    readLine (0 :: v :: t :: body) = some (.put v t payload refs) := by
  rw [show readLine (0 :: v :: t :: body)
      = match readFrame body with
        | some (payload, r1) =>
          match readNat32 r1 with
          | some (cnt, r2) =>
            match readN readPRef cnt r2 with
            | some (refs, []) => some (PLine.put v t payload refs)
            | _ => none
          | none => none
        | none => none from rfl, h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [h3]

/-- The line reader's load arm, driven by its one stage result over an
abstract body. -/
theorem readLine_load_of {r : Bytes} {src : PIn}
    (h : readPIn r = some (src, [])) :
    readLine (1 :: r) = some (.load src) := by
  rw [show readLine (1 :: r)
      = match readPIn r with
        | some (src, []) => some (PLine.load src)
        | _ => none from rfl, h]

/-- CODE-POINT ROUND TRIP (un-parked): a well-formed line, encoded as a
step node, decodes back to itself. -/
theorem decodeLine_encodeLine (l : PLine) (h : l.WF) :
    decodeLine (encodeLine l) = some l := by
  rw [show decodeLine (encodeLine l) = readLine (encodeLineBody l) from
    if_pos rfl]
  cases l with
  | put v t payload refs =>
    obtain ⟨hpay, hcnt, hrefs⟩ := h
    have h3 : readN readPRef refs.length ((refs.map encodePRef).flatten)
        = some (refs, []) := by
      have := readN_encode_of
        (fun a ha rest => readPRef_encodePRef a ha rest) refs hrefs []
      simpa using this
    exact readLine_put_of v t
      (readFrame_frame payload hpay _)
      (readNat32_nat32 refs.length hcnt _) h3
  | load src =>
    have h1 : readPIn (encodePIn src) = some (src, []) := by
      have := readPIn_encodePIn src h []
      simpa using this
    exact readLine_load_of h1

/-! ### Exactness — the decoder accepts nothing outside the image

The second direction, in the style of the codec's `readFrame_exact` and
`parseNode_exact`: a successful read PROVES its input was an encoding,
and proves the well-formedness the forward direction demands. Together
with the round trips above this is what "one byte representation per
code point" means for the step sort.

`readN_exact_of` is the exactness dual of `readN_encode_of` and is
carried for the same reason: the codec's `readN_exact` recovers the
splitting but drops the per-element property, and a line's admission
condition quantifies over its operand references. -/

/-- `readN` under a membership-relative exactness: the counted reader
recovers the splitting, the count, AND the reader's per-element
property. The dual of `readN_encode_of`. -/
theorem readN_exact_of {α : Type} {p : Bytes → Option (α × Bytes)}
    {e : α → Bytes} {P : α → Prop}
    (hp : ∀ b a rest, p b = some (a, rest) → b = e a ++ rest ∧ P a) :
    ∀ (n : Nat) (b : Bytes) (as : List α) (rest : Bytes),
      readN p n b = some (as, rest) →
      b = (as.map e).flatten ++ rest ∧ as.length = n ∧ ∀ a ∈ as, P a := by
  intro n
  induction n with
  | zero =>
    intro b as rest h
    simp only [readN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨has, hrest⟩ := h
    subst has; subst hrest
    simp
  | succ k ih =>
    intro b as rest h
    unfold readN at h
    split at h
    next a b' hpb =>
      split at h
      next as' b'' hrn =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨has, hrest⟩ := h
        obtain ⟨hb', hlen, hall⟩ := ih b' as' b'' hrn
        obtain ⟨hb, hPa⟩ := hp b a b' hpb
        subst has; subst hrest
        refine ⟨by rw [hb, hb']; simp [List.append_assoc], by simp [hlen], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hPa
        · exact hall x hx
      next => simp at h
    next => simp at h

/-- Operand exactness: a successful operand read proves its input was an
operand encoding, and proves the operand well-formed. -/
theorem readPIn_exact {b : Bytes} {x : PIn} {rest : Bytes}
    (h : readPIn b = some (x, rest)) : b = encodePIn x ++ rest ∧ x.WF := by
  match b with
  | [] => simp [readPIn] at h
  | c :: r =>
    by_cases h0 : c = 0
    · subst h0
      rw [readPIn_zero] at h
      split at h
      next cc rr hc =>
        split at h
        next hlen =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hx, hrest⟩ := h
          subst hx; subst hrest
          exact ⟨by rw [(readChunk_exact hc).1]; rfl, trivial⟩
        next => simp at h
      next => simp at h
    · by_cases h1 : c = 1
      · subst h1
        rw [readPIn_one] at h
        split at h
        next i rr hi =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hx, hrest⟩ := h
          subst hx; subst hrest
          obtain ⟨hb, hlt⟩ := readNat32_some _ _ _ hi
          exact ⟨by rw [hb]; rfl, hlt⟩
        next => simp at h
      · rw [show readPIn (c :: r) = none from by
          simp only [readPIn, if_neg h0, if_neg h1]] at h
        simp at h

/-- Typed-reference exactness. -/
theorem readPRef_exact {b : Bytes} {r : UInt8 × PIn} {rest : Bytes}
    (h : readPRef b = some (r, rest)) :
    b = encodePRef r ++ rest ∧ r.2.WF := by
  match b with
  | [] => simp [readPRef] at h
  | t :: rr =>
    rw [show readPRef (t :: rr)
        = match readPIn rr with
          | some (x, rest') => some ((t, x), rest')
          | none => none from rfl] at h
    split at h
    next x rest' hx =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hr, hrest⟩ := h
      subst hr; subst hrest
      obtain ⟨hb, hwf⟩ := readPIn_exact hx
      exact ⟨by rw [hb]; rfl, hwf⟩
    next => simp at h

/-- READLINE EXACTNESS (owed item, discharged): a successful line read
proves its input was a line encoding, and proves the line well-formed.
The decoder's image is exactly the encoder's. -/
theorem readLine_exact {b : Bytes} {l : PLine} (h : readLine b = some l) :
    b = encodeLineBody l ∧ l.WF := by
  match b with
  | [] => simp [readLine] at h
  | c :: r =>
    by_cases h0 : c = 0
    · subst h0
      match r with
      | [] => simp [readLine] at h
      | [_] => simp [readLine] at h
      | v :: t :: body =>
        rw [show readLine (0 :: v :: t :: body)
            = match readFrame body with
              | some (payload, r1) =>
                match readNat32 r1 with
                | some (cnt, r2) =>
                  match readN readPRef cnt r2 with
                  | some (refs, []) => some (PLine.put v t payload refs)
                  | _ => none
                | none => none
              | none => none from rfl] at h
        split at h
        next payload r1 hf =>
          split at h
          next cnt r2 hn =>
            split at h
            next refs hrn =>
              simp only [Option.some.injEq] at h
              subst h
              obtain ⟨hb1, hplen⟩ := readFrame_exact hf
              obtain ⟨hb2, hclt⟩ := readNat32_some _ _ _ hn
              obtain ⟨hb3, hlen, hall⟩ :=
                readN_exact_of (fun _b _a _rest hh => readPRef_exact hh)
                  cnt r2 refs [] hrn
              subst hlen
              refine ⟨?_, ?_, ?_, hall⟩
              · rw [hb1, hb2, hb3]
                simp [encodeLineBody]
              · exact hplen
              · omega
            next => simp at h
          next => simp at h
        next => simp at h
    · by_cases h1 : c = 1
      · subst h1
        rw [show readLine (1 :: r)
            = match readPIn r with
              | some (src, []) => some (PLine.load src)
              | _ => none from rfl] at h
        split at h
        next src hs =>
          simp only [Option.some.injEq] at h
          subst h
          obtain ⟨hb, hwf⟩ := readPIn_exact hs
          exact ⟨by rw [hb]; simp [encodeLineBody], hwf⟩
        next => simp at h
      · rw [show readLine (c :: r) = none from by
          simp only [readLine, if_neg h0, if_neg h1]] at h
        simp at h

/-- Step-node exactness, lifted to the node: `decodeLine` accepts only
step nodes carrying a line encoding. -/
theorem decodeLine_exact {n : Node} {l : PLine} (h : decodeLine n = some l) :
    n.tag = stepWireTag ∧ n.payload = encodeLineBody l ∧ l.WF := by
  unfold decodeLine at h
  split at h
  next ht => exact ⟨ht, (readLine_exact h).1, (readLine_exact h).2⟩
  next => simp at h

/-! ## The table as a word — the program IS content -/

/-- The content address of a line's step node under `H`. -/
def lineAddr (H : Bytes → Addr32) (l : PLine) : Addr32 :=
  H (encodeNode (encodeLine l))

/-- The table node: wire tag 15, the line count as payload, one typed
reference per line to its step node, in program order. -/
def tableNode (H : Bytes → Addr32) (p : PProg) : Node :=
  ⟨schemeVersion, contWireTag, nat32 p.length,
    p.map fun l => ⟨stepWireTag, lineAddr H l⟩⟩

/-- The table laid out children-first as a word: every step node, then
the table node referencing them all. -/
def encodeProg (H : Bytes → Addr32) (p : PProg) : Word :=
  (p.map fun l => Binding.mk (lineAddr H l) (encodeLine l))
    ++ [Binding.mk (H (encodeNode (tableNode H p))) (tableNode H p)]

/-- A word of reference-free bindings passes the admission scan from
any prefix. -/
theorem wfFrom_of_refs_nil :
    ∀ (w prior : Word), (∀ b ∈ w, b.node.refs = []) →
      Word.wfFrom prior w = true := by
  intro w
  induction w with
  | nil => intro prior _; rfl
  | cons b rest ih =>
    intro prior h
    obtain ⟨a, n⟩ := b
    have hn : n.refs = [] := h _ List.mem_cons_self
    simp only [Word.wfFrom, hn, List.all_nil, Bool.true_and]
    exact ih _ fun x hx => h x (List.mem_cons_of_mem _ hx)

/-- The encoded table ADMITS as a word, for EVERY address function —
hash-lattice Level 0, no injectivity anywhere: step nodes carry no
references, and each table reference resolves against the step
bindings laid down first (whatever binding `find` answers, it is a
step binding, so it carries tag 14). -/
theorem encodeProg_wf (H : Bytes → Addr32) (p : PProg) :
    Word.wf (encodeProg H p) = true := by
  have hlines : Word.wf
      (p.map fun l => Binding.mk (lineAddr H l) (encodeLine l)) = true := by
    refine wfFrom_of_refs_nil _ [] fun b hb => ?_
    obtain ⟨l, _, rfl⟩ := List.mem_map.mp hb
    rfl
  refine Word.wf_snoc hlines ?_
  intro r hr
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hr
  have hmem : Binding.mk (lineAddr H l) (encodeLine l)
      ∈ p.map fun l => Binding.mk (lineAddr H l) (encodeLine l) :=
    List.mem_map.mpr ⟨l, hl, rfl⟩
  have hsome := Word.find_isSome_of_mem hmem
  cases hf : Word.find
      (p.map fun l => Binding.mk (lineAddr H l) (encodeLine l))
      (lineAddr H l) with
  | none => rw [hf] at hsome; simp at hsome
  | some m =>
    have hm := Word.find_mem hf
    obtain ⟨l', _, heq⟩ := List.mem_map.mp hm
    have htag : m.tag = stepWireTag := by
      have hnode := congrArg Binding.node heq
      simp only at hnode
      rw [← hnode]
      rfl
    exact Word.resolvesIn_iff.mpr ⟨m, hf, htag⟩

/-! ## The table-level decoder — the program recovered from content

The missing direction of the applicative capability. `encodeProg` lays a
table down as a word; `decodeProg` reads one back. The word's LAST
binding is the table node (that is how `encodeProg` builds it), its
references name the step nodes in program order, and each one resolves
through `Word.find` and decodes through `decodeLine`.

### The premise, triaged

`encodeProg_wf` needs no premise on `H` at all — admission is Level 0.
RECOVERY is not, and the reason is worth stating plainly rather than
importing `Function.Injective H` out of habit:

    hsep : ∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l'

— the address function SEPARATES the table's lines. This premise is not
a convenience of the proof; it is NECESSARY, and the `example` below
`decodeProg_encodeProg` CHECKS that rather than asserting it: under a
degenerate `H` two distinct lines share an address, `encodeProg` lays
down two bindings there, both of the table node's references name it,
and `Word.find` answers the FIRST for both — so the recovered table
repeats one line where `p` had two. Note what the witness also shows:
the word still ADMITS. The store has not malfunctioned; it has
deduplicated, which is content-addressing working as designed, and no
decoder can undo it.

It is stated at the table's lines rather than as `Function.Injective H`
deliberately, per CAS-003: it is strictly weaker (it constrains `H` only
on the finitely many preimages this table actually lays down, and is
vacuous for tables of fewer than two lines), and it is exactly where the
obligation bites. `Function.Injective H` discharges it, but nothing here
needs the full strength.

`hwf : ∀ l ∈ p, l.WF` is the other premise, and it is the same admission
condition `decodeLine_encodeLine` already carries — a line whose fields
overflow their wire scalars was never encodable. -/

/-- Recover a table from a word: the last binding must be a table node,
and each of its references must resolve to a decodable step node. -/
def decodeProg (w : Word) : Option PProg :=
  match w.getLast? with
  | some b =>
    if b.node.tag = contWireTag then
      b.node.refs.mapM fun r => (Word.find w r.addr).bind decodeLine
    else none
  | none => none

/-- Under separation, each line's binding is what `find` answers at that
line's address within the step-node prefix. -/
theorem find_lineAddr (H : Bytes → Addr32) :
    ∀ p : PProg,
      (∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l') →
      ∀ l ∈ p,
        Word.find (p.map fun l => Binding.mk (lineAddr H l) (encodeLine l))
          (lineAddr H l) = some (encodeLine l) := by
  intro p
  induction p with
  | nil => intro _ l hl; simp at hl
  | cons a rest ih =>
    intro hsep l hl
    by_cases hae : lineAddr H l = lineAddr H a
    · have hla : l = a := hsep l hl a List.mem_cons_self hae
      subst hla
      simp [Word.find]
    · have hlr : l ∈ rest := by
        rcases List.mem_cons.mp hl with rfl | hm
        · exact absurd rfl hae
        · exact hm
      simp only [List.map_cons, Word.find, if_neg hae]
      exact ih (fun x hx y hy =>
        hsep x (List.mem_cons_of_mem a hx) y (List.mem_cons_of_mem a hy)) l hlr

/-- The same lookup inside the whole encoded word: the step bindings come
first, so the table binding appended after them cannot shadow one. -/
theorem find_encodeProg (H : Bytes → Addr32) (p : PProg)
    (hsep : ∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l') :
    ∀ l ∈ p,
      Word.find (encodeProg H p) (lineAddr H l) = some (encodeLine l) :=
  fun l hl => Word.find_append_of_some _ (find_lineAddr H p hsep l hl)

/-- The table node's reference list, read elementwise, is the table. -/
theorem mapM_lineRefs (H : Bytes → Addr32) (f : Ref → Option PLine) :
    ∀ p : PProg, (∀ l ∈ p, f ⟨stepWireTag, lineAddr H l⟩ = some l) →
      (p.map fun l => (⟨stepWireTag, lineAddr H l⟩ : Ref)).mapM f = some p := by
  intro p
  induction p with
  | nil => intro _; rfl
  | cons a rest ih =>
    intro h
    simp only [List.map_cons, List.mapM_cons, h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem a hx))]
    rfl

/-- THE PROGRAM IS RECOVERABLE FROM CONTENT (owed item, discharged): the
word `encodeProg` lays down reads back to exactly the table it encoded.
Both premises are triaged in the section note above — `hwf` is the
encodability condition `decodeLine_encodeLine` already carries, and
`hsep` is NECESSARY, not convenient. -/
theorem decodeProg_encodeProg (H : Bytes → Addr32) (p : PProg)
    (hwf : ∀ l ∈ p, l.WF)
    (hsep : ∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l') :
    decodeProg (encodeProg H p) = some p := by
  have hlast : (encodeProg H p).getLast?
      = some (Binding.mk (H (encodeNode (tableNode H p))) (tableNode H p)) :=
    List.getLast?_concat
  rw [show decodeProg (encodeProg H p)
      = (if (tableNode H p).tag = contWireTag then
          (tableNode H p).refs.mapM fun r =>
            (Word.find (encodeProg H p) r.addr).bind decodeLine
        else none) from by rw [decodeProg, hlast],
    if_pos (show (tableNode H p).tag = contWireTag from rfl)]
  exact mapM_lineRefs H _ p fun l hl => by
    rw [find_encodeProg H p hsep l hl, Option.bind_some,
      decodeLine_encodeLine l (hwf l hl)]

/-- Why `hsep` cannot be dropped, in the style of `Address.lean`'s
Level-2 witness: under a degenerate address function two DISTINCT lines
share an address, so the table node names that one address twice,
`Word.find` answers the first binding both times, and recovery returns
one line where the program had two. Every line here is well-formed and
the word still admits (`encodeProg_wf` needs no premise) — what fails is
recovery alone. The separation premise is NECESSARY, not a convenience
of the proof. -/
example :
    ∃ (H : Bytes → Addr32) (p : PProg),
      (∀ l ∈ p, l.WF) ∧
        Word.wf (encodeProg H p) = true ∧
        decodeProg (encodeProg H p) ≠ some p :=
  ⟨fun _ => ⟨List.replicate 32 0, by simp⟩,
    [.load (.ans 0), .load (.ans 1)],
    by
      intro l hl
      rcases List.mem_cons.mp hl with rfl | hl
      · show (0 : Nat) < 4294967296; omega
      · rcases List.mem_cons.mp hl with rfl | hl
        · show (1 : Nat) < 4294967296; omega
        · simp at hl,
    encodeProg_wf _ _,
    by decide⟩

/-! ## The capability round trip — a stored program runs identically

The sentence the product vision speaks, as one theorem: a table put into
the store and recovered from it is the same program, so it computes the
same thing. `decodeProg_encodeProg` composed with the direct
interpreter — cheap, because the recovery is an EQUALITY of tables, not
a simulation between them. -/

/-- THE CAPABILITY ROUND TRIP: a table stored as content and recovered
from that content runs identically — same status, same final word, at
every starting word. -/
theorem runP_decodeProg_encodeProg (H : Bytes → Addr32) (p : PProg)
    (hwf : ∀ l ∈ p, l.WF)
    (hsep : ∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l')
    {q : PProg} (hq : decodeProg (encodeProg H p) = some q) (w : Word) :
    runP H q w = runP H p w := by
  rw [decodeProg_encodeProg H p hwf hsep] at hq
  exact congrArg (fun r => runP H r w) (Option.some.inj hq).symm

/-- The same statement at stratum 3: a stored-and-recovered table denotes
an OBSERVATIONALLY EQUAL program. R14's equation, reached through the
word gate — the program is content, and the content is the program. -/
theorem ObsEq_decodeProg_encodeProg (H : Bytes → Addr32) (p : PProg)
    (hwf : ∀ l ∈ p, l.WF)
    (hsep : ∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l')
    {q : PProg} (hq : decodeProg (encodeProg H p) = some q) :
    ObsEq H (embed q) (embed p) :=
  ObsEq_embed_of_runP H fun w =>
    runP_decodeProg_encodeProg H p hwf hsep hq w

/-! ## THE EFFECT ENVELOPE — what a table can do, without running it

The applicative-strength half of the fragment tower (`Cas/Lang/Fragments.lean`).
The envelope is what `possibleOps` names in the selective literature (SAF
§3.2) and what DESIGN.md §5.5 mints as **effect envelope**: the object a
GRANT is written against. It is computed from the table ALONE — no word,
no store, no `H`, no fuel — so every definition below is a plain function
on first-order data, exactly R14a-P1. Nothing here enters `Prog`.

Three components, per the design's ask:

- **reads** — the literal addresses the table can consult. A `load`'s
  source is one; so is every reference of a `put`, because admission
  CONSULTS each reference for presence and kind (`checkRefs`) before it
  admits anything. Answer-valued operands contribute no literal: their
  address is not known until the table runs, and the dataflow edge is
  what accounts for them.
- **puts** — the put SHAPES, in program order: version, kind tag,
  payload bytes, and the expected kind tag of each reference. Everything
  about the admitted node except the reference ADDRESSES, which are the
  only part the answer history supplies.
- **dataflow** — the answer-index DAG, edges `(i, j)` reading "line `i`
  consumes line `j`'s answer". Already implicit in `resolveRefs`; here it
  is the graph, read off.

### What statement triage changed

Four findings, each of which moved a statement:

1. **DESIGN.md §3.1's table calls L-A's analysis "exact:
   `over = under = actual`". That is refuted.** A run executes only the
   prefix before its first refusal, so a table whose first line refuses
   still has an envelope naming every later put. The first `example`
   below exhibits it. L-A is over-approximate for exactly the reason
   every rung is: refusal.
2. **A SECOND source of over-approximation, at the word, that the design
   note does not name: `put`'s DUPLICATE outcome.** A put line that
   executes performs its operation but appends no binding when the node
   is already stored. So the word projection of the envelope is a
   `Sublist`, never a prefix, even on runs that never refuse — the
   second `example` exhibits it. This is F2's deduplication seen from the
   envelope side, and it is why `runPFrom_puts_sound` concludes
   `List.Sublist`.
3. **"Actual" cannot be a trace here without a second spelling of
   meaning.** `runPFrom` reports a status and a word, not an operation
   list, and adding an instrumented walk would put the run's meaning in
   two places (R10). So the sandwich is stated at the two places the run
   is genuinely OBSERVABLE — the word it leaves (`runPFrom_puts_sound`)
   and the address a refusal names (`runPFrom_absent_sound`) — plus the
   per-operand statement that covers every consultation
   (`PProg.resolve_sound`). No trace semantics is introduced.
4. **The "answers" half is not run data at all — it is a pure recursion,
   and saying so is the theorem.** DESIGN.md §2.1's *hash-determined
   dataflow* claims that, given `H`, a table's whole answer environment
   is a function of the table. `PProg.answersFrom` computes it with no
   word and no store, and `runPFrom_done_answers` proves the direct
   interpreter threads exactly that history. That is what lets the read
   half say "an earlier answer" without quantifying over runs. Note the
   honest converse: `answersFrom` is store-free, so it keeps computing
   past a refusal a store would have raised — it over-approximates in
   exactly the same place the envelope does, and nowhere else. -/

/-- The operation kind of a code point — the first thing the envelope
reads off a line. -/
inductive PKind where
  | put
  | load
  deriving DecidableEq

/-- Which operation a line performs. -/
def PLine.kind : PLine → PKind
  | .put .. => .put
  | .load _ => .load

/-- A line's operand references, in order: a put's reference operands, or
a load's single source. This is the line's whole dependence on the
outside world — there is nowhere else for an address to come from. -/
def PLine.operands : PLine → List PIn
  | .put _ _ _ refs => refs.map Prod.snd
  | .load src => [src]

/-- The statically determined shape of a put: everything about the node a
put line admits that does NOT depend on the answer history — scheme
version, kind tag, payload bytes, and each reference's expected kind tag.
What the history supplies is only the reference ADDRESSES. -/
structure PutShape where
  version : UInt8
  tag : UInt8
  payload : Bytes
  refKinds : List UInt8
  deriving DecidableEq

/-- The shape a node exhibits — the run-side projection the put-soundness
theorem compares the envelope against. -/
def PutShape.ofNode (n : Node) : PutShape :=
  ⟨n.version, n.tag, n.payload, n.refs.map Ref.expectedTag⟩

/-- The literal addresses a table can READ: every operand naming an
address outright, over every line — a load's source, and every reference
of a put, since admission consults each one. -/
def PProg.reads (p : PProg) : List Addr32 :=
  p.flatMap fun l => l.operands.filterMap fun
    | .lit a => some a
    | .ans _ => none

/-- The puts a table performs, in program order, by shape. -/
def PProg.puts (p : PProg) : List PutShape :=
  p.filterMap fun
    | .put v t payload refs => some ⟨v, t, payload, refs.map Prod.fst⟩
    | .load _ => none

/-- The answer-index dataflow from a starting line index. Spelled with an
explicit index accumulator rather than through `List.zipIdx` so that the
closure theorem below inducts along the same recursion the table does. -/
def PProg.dataflowFrom (i : Nat) : PProg → List (Nat × Nat)
  | [] => []
  | l :: rest =>
    (l.operands.filterMap fun
      | .ans j => some (i, j)
      | .lit _ => none) ++ PProg.dataflowFrom (i + 1) rest

/-- The answer-index dataflow: an edge `(i, j)` says line `i` consumes
line `j`'s answer. The dependency DAG, read off the table. -/
def PProg.dataflow (p : PProg) : List (Nat × Nat) := PProg.dataflowFrom 0 p

/-- THE EFFECT ENVELOPE: what a table can do, computed from the table
alone. Stratum-1 data — decidable, hashable, addressable — so an envelope
is itself a thing a grant can be written against and a store can hold. -/
structure Envelope where
  reads : List Addr32
  puts : List PutShape
  dataflow : List (Nat × Nat)
  deriving DecidableEq

/-- The envelope of a table. -/
def PProg.envelope (p : PProg) : Envelope :=
  ⟨PProg.reads p, PProg.puts p, PProg.dataflow p⟩

/-- How many puts the envelope declares — the count half of the put
shape. -/
def Envelope.putCount (e : Envelope) : Nat := e.puts.length

/-- Dataflow closure relative to a starting answer-history length. -/
def PProg.dataflowClosedFrom (i : Nat) (p : PProg) : Bool :=
  (PProg.dataflowFrom i p).all fun e => decide (e.2 < e.1)

/-- The dataflow is CLOSED when every edge names a STRICTLY EARLIER line.
Absolute indexing makes this decidable on the table alone, and
`runP_no_dangling` proves it is exactly the condition under which no line
can refuse for a dangling answer index — a refusal class the envelope
decides without running. -/
def Envelope.dataflowClosed (e : Envelope) : Bool :=
  e.dataflow.all fun edge => decide (edge.2 < edge.1)

/-- The envelope's closure predicate is the table's, at history zero. -/
theorem dataflowClosed_eq (p : PProg) :
    (PProg.envelope p).dataflowClosed = PProg.dataflowClosedFrom 0 p := rfl

/-! ### Resolution — what the operands can name

The three facts about `PIn.resolve`/`resolveRefs` the sandwich rests on,
each stated over an abstract history so the theorems above them never
re-derive the `mapM`. -/

/-- A literal operand resolves to itself, at every history. -/
theorem PIn.resolve_lit {env : List Addr32} {a b : Addr32}
    (h : (PIn.lit a).resolve env = some b) : a = b := by
  simpa [PIn.resolve] using h

/-- An answer operand resolves only inside the history. -/
theorem PIn.resolve_ans {env : List Addr32} {j : Nat} {a : Addr32}
    (h : (PIn.ans j).resolve env = some a) : a ∈ env := by
  simp only [PIn.resolve] at h
  exact List.mem_of_getElem? h

/-- Resolution changes only the ADDRESSES: the expected kind tags come
from the table, so an admitted node exhibits exactly the reference kinds
the envelope declared. -/
theorem resolveRefs_kinds : ∀ {refs : List (UInt8 × PIn)} {env : List Addr32}
    {rs : List Ref}, resolveRefs env refs = some rs →
      rs.map Ref.expectedTag = refs.map Prod.fst := by
  intro refs
  induction refs with
  | nil => intro env rs h; simp [resolveRefs] at h; subst h; rfl
  | cons r rest ih =>
    intro env rs h
    simp only [resolveRefs, List.mapM_cons] at h
    cases hx : (r.2.resolve env) with
    | none => simp [hx] at h
    | some a =>
      simp only [hx, Option.map_some] at h
      cases hrest : resolveRefs env rest with
      | none =>
        have h0 : (rest.mapM fun q => (q.2.resolve env).map (Ref.mk q.1)) = none := hrest
        rw [h0] at h; simp at h
      | some rs' =>
        have : (rest.mapM fun q => (q.2.resolve env).map (Ref.mk q.1)) = some rs' := hrest
        simp only [this] at h
        have hrs : rs = ⟨r.1, a⟩ :: rs' := by simpa using h.symm
        subst hrs
        simp [ih hrest]

/-- Every resolved reference came from an operand: the addresses a put
carries into admission are exactly the resolutions of the operands the
envelope read off. -/
theorem resolveRefs_mem : ∀ {refs : List (UInt8 × PIn)} {env : List Addr32}
    {rs : List Ref}, resolveRefs env refs = some rs → ∀ r ∈ rs,
      ∃ x ∈ refs.map Prod.snd, x.resolve env = some r.addr := by
  intro refs
  induction refs with
  | nil => intro env rs h r hr; simp [resolveRefs] at h; subst h; simp at hr
  | cons q rest ih =>
    intro env rs h r hr
    simp only [resolveRefs, List.mapM_cons] at h
    cases hx : (q.2.resolve env) with
    | none => simp [hx] at h
    | some a =>
      simp only [hx, Option.map_some] at h
      cases hrest : resolveRefs env rest with
      | none =>
        have h0 : (rest.mapM fun z => (z.2.resolve env).map (Ref.mk z.1)) = none := hrest
        rw [h0] at h; simp at h
      | some rs' =>
        have hr' : (rest.mapM fun z => (z.2.resolve env).map (Ref.mk z.1)) = some rs' := hrest
        simp only [hr'] at h
        have hrs : rs = ⟨q.1, a⟩ :: rs' := by simpa using h.symm
        subst hrs
        rcases List.mem_cons.mp hr with rfl | hm
        · exact ⟨q.2, by simp, hx⟩
        · obtain ⟨x, hx', hres⟩ := ih hrest r hm
          exact ⟨x, by simp at hx' ⊢; exact Or.inr hx', hres⟩

/-- A put's reference list resolves whenever each of its operands does. -/
theorem resolveRefs_isSome : ∀ {refs : List (UInt8 × PIn)} {env : List Addr32},
    (∀ x ∈ refs.map Prod.snd, (x.resolve env).isSome) →
      (resolveRefs env refs).isSome := by
  intro refs
  induction refs with
  | nil => intro env _; simp [resolveRefs]
  | cons q rest ih =>
    intro env h
    have hq : (q.2.resolve env).isSome := h q.2 (by simp)
    have hrest := ih (env := env) fun x hx => h x (by simp at hx ⊢; exact Or.inr hx)
    cases hx : (q.2.resolve env) with
    | none => rw [hx] at hq; simp at hq
    | some a =>
      cases hy : resolveRefs env rest with
      | none => rw [hy] at hrest; simp at hrest
      | some rs =>
        have hy' : (rest.mapM fun z => (z.2.resolve env).map (Ref.mk z.1)) = some rs := hy
        simp [resolveRefs, List.mapM_cons, hx, hy']

/-! ### THE SANDWICH (a) — soundness at the operand

`actual ⊆ possible`, stated where every consultation happens: an operand.
A table cannot name an address it did not either write down (a literal
the envelope holds) or compute (an entry of the answer history). There is
no third source, because `PIn` has two constructors. -/

/-- SOUNDNESS, read half, at the operand: every address a line consults
resolves either to a literal the envelope names among the table's reads,
or to a member of the answer history the run has built. -/
theorem PProg.resolve_sound {p : PProg} {l : PLine} (hl : l ∈ p)
    {x : PIn} (hx : x ∈ l.operands) {env : List Addr32} {a : Addr32}
    (h : x.resolve env = some a) :
    a ∈ PProg.reads p ∨ a ∈ env := by
  cases x with
  | lit b =>
    left
    have : b = a := PIn.resolve_lit h
    subst this
    refine List.mem_flatMap.mpr ⟨l, hl, ?_⟩
    exact List.mem_filterMap.mpr ⟨PIn.lit b, hx, rfl⟩
  | ans j => exact Or.inr (PIn.resolve_ans h)

/-- The addresses a line consults under a given answer history — the
line's contribution to the frame condition. -/
def PLine.touches (env : List Addr32) (l : PLine) : List Addr32 :=
  l.operands.filterMap (PIn.resolve env)

/-- THE FRAME CONDITION, per line: at whatever history the run is in when
it reaches a line, everything that line touches lies in the envelope's
literal reads together with that history. `runPFrom_done_answers` below
identifies the history itself, so the two theorems together are "this
program touches only these addresses". -/
theorem PProg.touches_sound {p : PProg} {l : PLine} (hl : l ∈ p)
    (env : List Addr32) :
    ∀ a ∈ PLine.touches env l, a ∈ PProg.reads p ∨ a ∈ env := by
  intro a ha
  obtain ⟨x, hx, hres⟩ := List.mem_filterMap.mp ha
  exact PProg.resolve_sound hl hx hres

/-! ## Hash-determined dataflow — the history is a pure recursion

DESIGN.md §2.1's load-bearing observation, made a definition and then a
theorem. The answer to a `put` is the content address of the node it
admits — Level 0, no premise on `H` — and a `load` answers its own
source. So *given `H`*, a table's whole answer environment is a function
of the table: no word, no store, no running. This is what the estate has
instead of the free applicative's "no dependence on earlier results": the
table DOES depend on earlier results, and is statically analysable anyway
because addressing is functional. -/

/-- The address a line ANSWERS, given `H` and the history: a put answers
the content address of the node it admits; a load answers its source. -/
def PLine.answer (H : Bytes → Addr32) (env : List Addr32) : PLine → Option Addr32
  | .put v t payload refs =>
      (resolveRefs env refs).map fun rs => H (encodeNode ⟨v, t, payload, rs⟩)
  | .load src => src.resolve env

/-- HASH-DETERMINED DATAFLOW: the answer history a table determines from
`H` alone. A pure recursion on the table — R14a-P1 all the way down. It
stops at the first line whose operands dangle, and at NOTHING else: being
store-free it keeps computing past a refusal a store would have raised,
which is the one place it over-approximates the run. -/
def PProg.answersFrom (H : Bytes → Addr32) (env : List Addr32) :
    PProg → List Addr32
  | [] => []
  | l :: rest =>
    match PLine.answer H env l with
    | some a => a :: PProg.answersFrom H (env ++ [a]) rest
    | none => []

section Envelope

variable (H : Bytes → Addr32)

/-- Every accepting put answers the CONTENT ADDRESS of the node it
admits — fresh and duplicate alike (`put_fresh_spec`, `put_duplicate_spec`
both give `addr H`). This is why the answer history is a function of `H`
and the table, and of nothing the store contributes. -/
theorem putWord_answer {n : Node} {w w' : Word} {a : Addr32}
    (h : putWord H n w = .ok (a, w')) : a = H (encodeNode n) := by
  unfold putWord referenceHandler at h
  by_cases hn : n.WF
  · simp only [dif_pos hn] at h
    cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, hn⟩ with
    | error e => rw [hp] at h; simp at h
    | ok o =>
      cases o with
      | fresh b σ' =>
        rw [hp] at h
        obtain ⟨hb, _⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨_, _, hba, _⟩ := put_fresh_spec hp
        rw [← hb, hba]
        rfl
      | duplicate b =>
        rw [hp] at h
        obtain ⟨hb, _⟩ := Prod.mk.inj (Except.ok.inj h)
        obtain ⟨_, hba, _⟩ := put_duplicate_spec hp
        rw [← hb, hba]
        rfl
      | conflict b m => rw [hp] at h; simp at h
  · simp only [dif_neg hn] at h; simp at h

/-- A put either APPENDS exactly its own binding or leaves the word
untouched — the duplicate outcome. The word only ever grows, and only by
nodes a put line named. -/
theorem putWord_word {n : Node} {w w' : Word} {a : Addr32}
    (h : putWord H n w = .ok (a, w')) :
    w' = w ∨ w' = w ++ [Binding.mk a n] := by
  unfold putWord referenceHandler at h
  by_cases hn : n.WF
  · simp only [dif_pos hn] at h
    cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, hn⟩ with
    | error e => rw [hp] at h; simp at h
    | ok o =>
      cases o with
      | fresh b σ' =>
        rw [hp] at h
        obtain ⟨hb, hw⟩ := Prod.mk.inj (Except.ok.inj h)
        subst hb; exact Or.inr hw.symm
      | duplicate b =>
        rw [hp] at h
        exact Or.inl (Prod.mk.inj (Except.ok.inj h)).2.symm
      | conflict b m => rw [hp] at h; simp at h
  · simp only [dif_neg hn] at h; simp at h

/-- **HASH-DETERMINED OPERATION** (HD-1) — the boundary, named. The
property `PLine.answer` has been computing all along, stated so it can
be a decided line rather than a habit of the proofs.

An operation is *hash-determined* when a total function from its
arguments to its answer exists that no handler may contradict. Here the
arguments are the line and the answer history it is reached in, the
answer is the address the line contributes to that history, and
`PLine.answer H` is the function. The quantifier over `w` is the whole
content: at EVERY word the direct interpreter answers what
`PLine.answer` computed, so the store may decide WHETHER the answer
arrives — a refusal — but never WHICH answer arrives.

**THE BOUNDARY RULING.** An operation INSIDE this line needs no trace
store. Its answer is recomputable from the operation itself, so
recording `(out, deps, recipe)` would only write down what a pure
function already returns, and the envelope, the sandwich and
`answersFrom` all survive untouched: a build step that DECLARES its
output address rides L-A exactly as `put` does, and the handler's job
is to check the declaration (`SPECS.md` ruling 19, first regime).

An operation OUTSIDE this line needs `(out, deps, recipe)` — under
`Hash v = k` that is three addresses and a list — and gets it from
`Persistable`/`PersistedCache` (`SPECS.md` decision 15), never from a
newly minted kind. Such an operation is summed into the signature and
interpreted away by an oracle in `Prog.handleLlm`'s exact shape
(ruling 19, second regime, and the ratified direction); the price is
the envelope for the summed program, which is correct and is said out
loud rather than hidden. `LlmSig.infer` (`Ops.lean`) is the estate's
live operation outside the boundary and `Prog.handleLlm`
(`Interp.lean`) is its discharge — the closing witness of this module
exhibits both. -/
def PLine.HashDetermined (l : PLine) : Prop :=
  ∀ (env : List Addr32) (w w' : Word) (b : Addr32),
    runPFrom H env [l] w = (.done b, w') → PLine.answer H env l = some b

/-- **HD-1, DISCHARGED: every operation of `CasSig` is
hash-determined.** A STATEMENT slice and not a proof slice — both
halves were landed before the property had a name, and are cited here
rather than re-argued. The put half is `putWord_answer`: hash-lattice
Level 0, no premise on `H`, fresh and duplicate alike. The load half is
`PIn.resolve`, where the equation is definitional because the entry a
load contributes to the history IS its resolved source address (the
node it reads is the store's contribution and is not an answer of the
dataflow). Where the definition is the composition the theorem may be
near-`rfl` and is still worth stating: this is the line every
downstream lane trips over, and it now has a name to cite. The
run-level consequence is `runPFrom_done_answers`. -/
theorem PLine.hashDetermined (l : PLine) : PLine.HashDetermined H l := by
  intro env w w' b h
  cases l with
  | put v t payload refs =>
    cases hr : resolveRefs env refs with
    | none => simp [runPFrom, hr] at h
    | some rs =>
      cases hp : putWord H ⟨v, t, payload, rs⟩ w with
      | error e => simp [runPFrom, hr, hp] at h
      | ok aw =>
        obtain ⟨c, w''⟩ := aw
        have hcb : c = b := by
          simp only [runPFrom, hr, hp, List.getLast?_concat, Prod.mk.injEq,
            Status.done.injEq] at h
          exact h.1
        subst hcb
        simp only [PLine.answer, hr, Option.map_some]
        exact congrArg some (putWord_answer H hp).symm
  | load src =>
    cases hs : src.resolve env with
    | none => simp [runPFrom, hs] at h
    | some c =>
      cases hf : Word.find w c with
      | none => simp [runPFrom, hs, hf] at h
      | some n =>
        have hcb : c = b := by
          simp only [runPFrom, hs, hf, List.getLast?_concat, Prod.mk.injEq,
            Status.done.injEq] at h
          exact h.1
        subst hcb
        exact hs

/-- HASH-DETERMINED DATAFLOW, AS A THEOREM (DESIGN.md §2.1): on a run that
reports `done`, the answer history the direct interpreter threaded is
exactly the one the table determines from `H` alone, and the designated
result is its last entry. The store contributed nothing to the dataflow;
it only decided whether the run got there.

The line count is the second conclusion, and it is where the gap is
located from the other side: on a `done` run the envelope is EXACT in
line count — every line executed, nothing skipped. -/
theorem runPFrom_done_answers :
    ∀ (env : List Addr32) (p : PProg) (w : Word) {a : Addr32} {w' : Word},
      runPFrom H env p w = (.done a, w') →
        (PProg.answersFrom H env p).length = p.length
          ∧ (env ++ PProg.answersFrom H env p).getLast? = some a := by
  intro env p
  induction p generalizing env with
  | nil =>
    intro w a w' h
    cases hg : env.getLast? with
    | none => simp [runPFrom, hg] at h
    | some b =>
      simp only [runPFrom, hg, Prod.mk.injEq, Status.done.injEq] at h
      obtain ⟨hb, _⟩ := h
      subst hb
      refine ⟨rfl, ?_⟩
      show (env ++ []).getLast? = some b
      simpa using hg
  | cons line rest ih =>
    intro w a w' h
    cases line with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none => simp [runPFrom, hr] at h
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e => simp [runPFrom, hr, hp] at h
        | ok aw =>
          obtain ⟨b, w''⟩ := aw
          simp only [runPFrom, hr, hp] at h
          have hb : b = H (encodeNode ⟨v, t, payload, rs⟩) := putWord_answer H hp
          obtain ⟨hlen, hlast⟩ := ih (env ++ [b]) w'' h
          refine ⟨?_, ?_⟩
          · show (PProg.answersFrom H env (PLine.put v t payload refs :: rest)).length = _
            rw [show PProg.answersFrom H env (PLine.put v t payload refs :: rest)
                = b :: PProg.answersFrom H (env ++ [b]) rest from by
              simp only [PProg.answersFrom, PLine.answer, hr, Option.map_some, ← hb]]
            simp [hlen]
          · rw [show PProg.answersFrom H env (PLine.put v t payload refs :: rest)
                = b :: PProg.answersFrom H (env ++ [b]) rest from by
              simp only [PProg.answersFrom, PLine.answer, hr, Option.map_some, ← hb]]
            simpa using hlast
    | load src =>
      cases hs : src.resolve env with
      | none => simp [runPFrom, hs] at h
      | some b =>
        cases hf : Word.find w b with
        | none => simp [runPFrom, hs, hf] at h
        | some n =>
          simp only [runPFrom, hs, hf] at h
          obtain ⟨hlen, hlast⟩ := ih (env ++ [b]) w h
          refine ⟨?_, ?_⟩
          · rw [show PProg.answersFrom H env (PLine.load src :: rest)
                = b :: PProg.answersFrom H (env ++ [b]) rest from by
              simp only [PProg.answersFrom, PLine.answer, hs]]
            simp [hlen]
          · rw [show PProg.answersFrom H env (PLine.load src :: rest)
                = b :: PProg.answersFrom H (env ++ [b]) rest from by
              simp only [PProg.answersFrom, PLine.answer, hs]]
            simpa using hlast

/-- THE DATAFLOW EDGE NAMES ITS SOURCE LINE: the history grows by exactly
one entry per line, in program order, so entry `j` IS line `j`'s answer
and an operand `ans j` at a later line resolves to it. The envelope's
edge `(i, j)` is this equation. -/
theorem PProg.answersFrom_cons_of {l : PLine} {env : List Addr32} {b : Addr32}
    (h : PLine.answer H env l = some b) (rest : PProg) :
    PProg.answersFrom H env (l :: rest)
      = b :: PProg.answersFrom H (env ++ [b]) rest := by
  simp only [PProg.answersFrom, h]

/-- SOUNDNESS, PUT HALF, WITH ORDER — the byte-observable corollary
(DESIGN.md §2.5): the run only APPENDS to the word, and the bindings it
appends carry, IN ORDER, a sublist of the shapes the envelope declared.
No run of a table from any word admits a node outside the table's
declared put set.

`Sublist` and not a prefix, for the two reasons triage located and named
above: a put that answers `duplicate` appends nothing (F2's
deduplication), and the lines after a refusal never execute. Both are
exhibited by the closing `example`s. -/
theorem runPFrom_puts_sound :
    ∀ (env : List Addr32) (p : PProg) (w : Word),
      ∃ d : Word, (runPFrom H env p w).2 = w ++ d
        ∧ List.Sublist (d.map fun b => PutShape.ofNode b.node) (PProg.puts p) := by
  intro env p
  induction p generalizing env with
  | nil =>
    intro w
    refine ⟨[], ?_, ?_⟩
    · cases hg : env.getLast? <;> simp [runPFrom, hg]
    · simp [PProg.puts]
  | cons line rest ih =>
    intro w
    cases line with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none => exact ⟨[], by simp [runPFrom, hr], by simp⟩
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e => exact ⟨[], by simp [runPFrom, hr, hp], by simp⟩
        | ok aw =>
          obtain ⟨b, w''⟩ := aw
          obtain ⟨d, hd, hsub⟩ := ih (env ++ [b]) w''
          have hputs : PProg.puts (PLine.put v t payload refs :: rest)
              = ⟨v, t, payload, refs.map Prod.fst⟩ :: PProg.puts rest := rfl
          rcases putWord_word H hp with hw | hw
          · refine ⟨d, ?_, ?_⟩
            · simp only [runPFrom, hr, hp]; rw [hd, hw]
            · rw [hputs]; exact List.Sublist.cons _ hsub
          · refine ⟨Binding.mk b ⟨v, t, payload, rs⟩ :: d, ?_, ?_⟩
            · simp only [runPFrom, hr, hp]; rw [hd, hw]; simp
            · rw [hputs]
              simp only [List.map_cons]
              have hshape : PutShape.ofNode ⟨v, t, payload, rs⟩
                  = ⟨v, t, payload, refs.map Prod.fst⟩ := by
                simp [PutShape.ofNode, resolveRefs_kinds hr]
              show List.Sublist ((PutShape.ofNode ⟨v, t, payload, rs⟩)
                :: (d.map fun b => PutShape.ofNode b.node)) _
              rw [hshape]
              exact List.Sublist.cons_cons _ hsub
    | load src =>
      cases hs : src.resolve env with
      | none => exact ⟨[], by simp [runPFrom, hs], by simp [PProg.puts]⟩
      | some b =>
        cases hf : Word.find w b with
        | none => exact ⟨[], by simp [runPFrom, hs, hf], by simp [PProg.puts]⟩
        | some n =>
          obtain ⟨d, hd, hsub⟩ := ih (env ++ [b]) w
          exact ⟨d, by simp only [runPFrom, hs, hf]; exact hd,
            by simpa [PProg.puts] using hsub⟩

/-- The same statement at `runP`: the word a table's run leaves extends
the word it started from by bindings whose shapes the envelope declared,
in order. -/
theorem runP_puts_sound (p : PProg) (w : Word) :
    ∃ d : Word, (runP H p w).2 = w ++ d
      ∧ List.Sublist (d.map fun b => PutShape.ofNode b.node) (PProg.puts p) :=
  runPFrom_puts_sound H [] p w

/-! ### The read half, at the observable

The address a refusal NAMES is the run's own report of an address it
consulted, so it is where `actual ⊆ possible` can be stated against the
word rather than against a trace. Both refusal clauses that name an
absent address are covered: a load's `noObject`, and a put reference's
`dangling`. -/

/-- Reads only grow with the table. -/
theorem PProg.reads_cons_of_mem {l : PLine} {rest : PProg} {a : Addr32}
    (h : a ∈ PProg.reads rest) : a ∈ PProg.reads (l :: rest) := by
  simp only [PProg.reads, List.mem_flatMap] at h ⊢
  obtain ⟨x, hx, hax⟩ := h
  exact ⟨x, List.mem_cons_of_mem l hx, hax⟩

/-- A put never refuses with a `failed` reason: its refusal clauses are
`notWellFormed`, admission's two, and `collision`. -/
theorem putWord_ne_failed {n : Node} {w : Word} {reason : String} :
    putWord H n w ≠ .error (.failed reason) := by
  intro h
  unfold putWord referenceHandler at h
  by_cases hn : n.WF
  · simp only [dif_pos hn] at h
    cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, hn⟩ with
    | error e =>
      rw [hp] at h
      have he : Refusal.ofAdmission e = Refusal.failed reason := by
        simpa using Except.error.inj h
      cases e <;> simp [Refusal.ofAdmission] at he
    | ok o =>
      cases o with
      | fresh b σ' => rw [hp] at h; simp at h
      | duplicate b => rw [hp] at h; simp at h
      | conflict b m =>
        rw [hp] at h
        exact Refusal.noConfusion (Except.error.inj h)
  · simp only [dif_neg hn] at h
    exact Refusal.noConfusion (Except.error.inj h)

/-- The address a refusal names as ABSENT, when it names one: a load that
found nothing, or a put whose reference dangled. The other clauses
(`notWellFormed`, `wrongKind`, `collision`, `failed`) report something
other than an address the run went looking for. -/
def Refusal.absentAddr : Refusal → Option Addr32
  | .noObject a => some a
  | .dangling a => some a
  | _ => none

/-- A put that refuses for an ABSENT address names one of its OWN
references — through `checkRefs`'s soundness, not by inspection. -/
theorem putWord_absent {n : Node} {w : Word} {r : Refusal} {a : Addr32}
    (h : putWord H n w = .error r) (ha : r.absentAddr = some a) :
    ∃ q ∈ n.refs, q.addr = a := by
  unfold putWord referenceHandler at h
  by_cases hn : n.WF
  · simp only [dif_pos hn] at h
    cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, hn⟩ with
    | error e =>
      rw [hp] at h
      have he : Refusal.ofAdmission e = r := Except.error.inj h
      cases e with
      | dangling b =>
        rw [← he] at ha
        have hb : b = a := by simpa [Refusal.absentAddr, Refusal.ofAdmission] using ha
        subst hb
        have hc : _root_.Cas.checkRefs (Word.toStore w) n.refs
            = Except.error (AdmissionError.dangling b) := put_error_iff.mp hp
        obtain ⟨t, ht, hta, _⟩ := checkRefs_error_condemns hc
        exact ⟨t, ht, hta⟩
      | wrongKind b exp act =>
        rw [← he] at ha; simp [Refusal.absentAddr, Refusal.ofAdmission] at ha
    | ok o =>
      cases o with
      | fresh b σ' => rw [hp] at h; simp at h
      | duplicate b => rw [hp] at h; simp at h
      | conflict b m =>
        rw [hp] at h
        have he : Refusal.collision b = r := Except.error.inj h
        rw [← he] at ha; simp [Refusal.absentAddr] at ha
  · simp only [dif_neg hn] at h
    have he : Refusal.notWellFormed = r := Except.error.inj h
    rw [← he] at ha; simp [Refusal.absentAddr] at ha

/-- SOUNDNESS AT THE OBSERVABLE, READ HALF: whenever a run refuses because
an address was absent — a load's `noObject` or a put reference's
`dangling` — the address it names is one the envelope accounts for: an
enveloped literal read, or an answer the table itself determined. This is
`actual ⊆ possible` at the reads, decided at the word, with the second
disjunct supplied by hash-determined dataflow rather than by running. -/
theorem runPFrom_absent_sound :
    ∀ (env : List Addr32) (p : PProg) (w : Word) {r : Refusal} {w' : Word}
      {a : Addr32},
      runPFrom H env p w = (.refused r, w') → r.absentAddr = some a →
        a ∈ PProg.reads p ∨ a ∈ env ++ PProg.answersFrom H env p := by
  intro env p
  induction p generalizing env with
  | nil =>
    intro w r w' a h ha
    cases hg : env.getLast? with
    | none =>
      simp only [runPFrom, hg, Prod.mk.injEq, Status.refused.injEq] at h
      rw [← h.1] at ha; simp [Refusal.absentAddr] at ha
    | some b => simp [runPFrom, hg] at h
  | cons line rest ih =>
    intro w r w' a h ha
    cases line with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none =>
        simp only [runPFrom, hr, Prod.mk.injEq, Status.refused.injEq] at h
        rw [← h.1] at ha; simp [Refusal.absentAddr] at ha
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e =>
          simp only [runPFrom, hr, hp, Prod.mk.injEq, Status.refused.injEq] at h
          have her : e = r := h.1
          subst her
          obtain ⟨t', ht', hta⟩ := putWord_absent H hp ha
          obtain ⟨x, hx, hres⟩ := resolveRefs_mem hr t' ht'
          rw [hta] at hres
          have hxop : x ∈ (PLine.put v t payload refs).operands := hx
          rcases PProg.resolve_sound (p := PLine.put v t payload refs :: rest)
              (l := PLine.put v t payload refs) List.mem_cons_self hxop hres with
            hmem | hmem
          · exact Or.inl hmem
          · exact Or.inr (by simp [hmem])
        | ok aw =>
          obtain ⟨b, w''⟩ := aw
          simp only [runPFrom, hr, hp] at h
          have hb : b = H (encodeNode ⟨v, t, payload, rs⟩) := putWord_answer H hp
          have hans : PLine.answer H env (PLine.put v t payload refs) = some b := by
            simp only [PLine.answer, hr, Option.map_some, ← hb]
          rw [PProg.answersFrom_cons_of H hans rest]
          rcases ih (env ++ [b]) w'' h ha with hmem | hmem
          · exact Or.inl (PProg.reads_cons_of_mem hmem)
          · right; simpa using hmem
    | load src =>
      cases hs : src.resolve env with
      | none =>
        simp only [runPFrom, hs, Prod.mk.injEq, Status.refused.injEq] at h
        rw [← h.1] at ha; simp [Refusal.absentAddr] at ha
      | some b =>
        cases hf : Word.find w b with
        | none =>
          simp only [runPFrom, hs, hf, Prod.mk.injEq, Status.refused.injEq] at h
          rw [← h.1] at ha
          have hba : b = a := by simpa [Refusal.absentAddr] using ha
          subst hba
          rcases PProg.resolve_sound (p := PLine.load src :: rest)
              (l := PLine.load src) List.mem_cons_self
              (x := src) (by simp [PLine.operands]) hs with hmem | hmem
          · exact Or.inl hmem
          · exact Or.inr (by simp [hmem])
        | some n =>
          simp only [runPFrom, hs, hf] at h
          have hans : PLine.answer H env (PLine.load src) = some b := hs
          rw [PProg.answersFrom_cons_of H hans rest]
          rcases ih (env ++ [b]) w h ha with hmem | hmem
          · exact Or.inl (PProg.reads_cons_of_mem hmem)
          · right; simpa using hmem

/-- The same statement at `runP`, where the history is the table's own. -/
theorem runP_absent_sound (p : PProg) (w : Word) {r : Refusal} {w' : Word}
    {a : Addr32} (h : runP H p w = (.refused r, w'))
    (ha : r.absentAddr = some a) :
    a ∈ PProg.reads p ∨ a ∈ PProg.answersFrom H [] p := by
  simpa using runPFrom_absent_sound H [] p w h ha

/-! ### FRAME-1 — the frame condition, for EVERY run

`runPFrom_absent_sound` states `actual ⊆ possible` at the observable: it
covers the addresses a REFUSAL names. `PProg.touches_sound` states it per
line, but against an arbitrary history, so on its own it says nothing
about the histories a run is actually in. `Fragments.lean`'s interop
claim 1 — "no run of the table from any word touches an address outside
`reads ∪ answers`" — is the conjunction, and it needs the missing middle:
*which* histories a run can reach a line in.

That middle is `runPFrom_append_done`: a run that reaches a line reaches
it at `env` extended by the history the table DETERMINED for the lines
before it — the store decided only whether the run got there.
`answersFrom_prefix` then says that determined history is a prefix of the
whole table's, including when `answersFrom` stops early, because it stops
only where an operand dangles and that is where the run refuses too. With
those two the claim holds for every run, refusing runs included, and the
overclaim the audit flagged is closed rather than softened. -/

/-- The determined history of a prefix is a PREFIX of the determined
history of the whole table — for every table and every extension. The
early stop is not an exception: `answersFrom` halts at the first line
whose operands dangle, and a longer table cannot un-dangle it. -/
theorem PProg.answersFrom_prefix (env : List Addr32) (p q : PProg) :
    (PProg.answersFrom H env p).IsPrefix (PProg.answersFrom H env (p ++ q)) := by
  induction p generalizing env with
  | nil => simp [PProg.answersFrom]
  | cons l rest ih =>
    cases ha : PLine.answer H env l with
    | none => simp [PProg.answersFrom, ha]
    | some a =>
      obtain ⟨t, ht⟩ := ih (env ++ [a])
      refine ⟨t, ?_⟩
      simp only [List.cons_append, PProg.answersFrom, ha]
      simpa using ht

/-- THE HISTORY AT A REACHED LINE, IDENTIFIED: when the run of a prefix
completes, the run of the whole table continues from exactly the history
that prefix DETERMINED — `env ++ answersFrom H env pre` — at whatever
word the prefix left. This is the carrier FRAME-1 was missing: it turns
"the run is somewhere in the table" into a named history, without a
reachability predicate and without a second spelling of the walk. -/
theorem runPFrom_append_done :
    ∀ (env : List Addr32) (pre post : PProg) (w : Word) {b : Addr32} {w' : Word},
      runPFrom H env pre w = (.done b, w') →
        runPFrom H env (pre ++ post) w
          = runPFrom H (env ++ PProg.answersFrom H env pre) post w' := by
  intro env pre
  induction pre generalizing env with
  | nil =>
    intro post w b w' h
    cases hg : env.getLast? with
    | none => simp [runPFrom, hg] at h
    | some c =>
      simp only [runPFrom, hg, Prod.mk.injEq, Status.done.injEq] at h
      obtain ⟨_, hw⟩ := h
      subst hw
      simp [PProg.answersFrom]
  | cons l rest ih =>
    intro post w b w' h
    cases l with
    | put v t payload refs =>
      cases hr : resolveRefs env refs with
      | none => simp [runPFrom, hr] at h
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e => simp [runPFrom, hr, hp] at h
        | ok aw =>
          obtain ⟨c, w''⟩ := aw
          simp only [runPFrom, hr, hp] at h
          have hc : c = H (encodeNode ⟨v, t, payload, rs⟩) := putWord_answer H hp
          have hans : PLine.answer H env (PLine.put v t payload refs) = some c := by
            simp only [PLine.answer, hr, Option.map_some, ← hc]
          rw [PProg.answersFrom_cons_of H hans rest]
          have hstep := ih (env ++ [c]) post w'' h
          simp only [List.cons_append, runPFrom, hr, hp]
          rw [hstep]
          simp
    | load src =>
      cases hs : src.resolve env with
      | none => simp [runPFrom, hs] at h
      | some c =>
        cases hf : Word.find w c with
        | none => simp [runPFrom, hs, hf] at h
        | some n =>
          simp only [runPFrom, hs, hf] at h
          have hans : PLine.answer H env (PLine.load src) = some c := hs
          rw [PProg.answersFrom_cons_of H hans rest]
          have hstep := ih (env ++ [c]) post w h
          simp only [List.cons_append, runPFrom, hs, hf]
          rw [hstep]
          simp

/-- **FRAME-1 — THE FRAME CONDITION.** At the history a run reaches a
line in — the one `runPFrom_append_done` names — every address that line
consults lies in the table's enveloped literal reads together with the
table's own determined answers. No `done` premise, so refusing runs are
covered: the bound is on the addresses CONSULTED, and a run that refuses
consulted a subset of what a run that continues would. -/
theorem runPFrom_frame_sound (env : List Addr32) (pre : PProg) (l : PLine)
    (post : PProg) :
    ∀ a ∈ PLine.touches (env ++ PProg.answersFrom H env pre) l,
      a ∈ PProg.reads (pre ++ l :: post)
        ∨ a ∈ env ++ PProg.answersFrom H env (pre ++ l :: post) := by
  intro a ha
  have hl : l ∈ pre ++ l :: post := by simp
  rcases PProg.touches_sound hl (env ++ PProg.answersFrom H env pre) a ha with h | h
  · exact Or.inl h
  · right
    rcases List.mem_append.mp h with h' | h'
    · exact List.mem_append_left _ h'
    · exact List.mem_append_right _
        ((PProg.answersFrom_prefix H env pre (l :: post)).subset h')

/-- **FRAME-1 AT THE TABLE — the interop claim, whole.** For a table
split at any line: if the run reaches that line, it reaches it at the
determined history, and every address the line consults is one the
envelope accounts for. This is the theorem `Fragments.lean`'s interop
claim 1 cites — the frame condition a scheduler computes read/write sets
from and a grant is checked against, decided before anything runs. -/
theorem runP_frame_sound (pre : PProg) (l : PLine) (post : PProg) (w : Word)
    {b : Addr32} {w' : Word} (hreach : runPFrom H [] pre w = (.done b, w')) :
    runP H (pre ++ l :: post) w
        = runPFrom H (PProg.answersFrom H [] pre) (l :: post) w'
      ∧ ∀ a ∈ PLine.touches (PProg.answersFrom H [] pre) l,
          a ∈ PProg.reads (pre ++ l :: post)
            ∨ a ∈ PProg.answersFrom H [] (pre ++ l :: post) := by
  refine ⟨?_, ?_⟩
  · simpa [runP] using runPFrom_append_done H [] pre (l :: post) w hreach
  · simpa using runPFrom_frame_sound H [] pre l post

/-! ### THE SANDWICH (b) — necessity, and where it stops

The lower bound, stated so it is not vacuous. A load line that executes
CONSULTS its operand: the run's continuation exists only because
`Word.find` answered at the resolved address, and removing that binding
changes the outcome to a refusal naming that exact address. There is no
model of the run in which the address goes untouched, so the envelope's
read entry for that line is not slack.

Necessity is stated per line rather than per table, and that is the
honest scope: for a line to be reached the run must not have refused
earlier, which is precisely the gap named below. `runP_head_load_necessary`
is the case where no reachability premise is needed. -/

/-- NECESSITY, absent half: a load line whose operand resolves to an
address the word does not hold refuses, naming that address. -/
theorem runPFrom_load_absent (env : List Addr32) (src : PIn) (rest : PProg)
    (w : Word) {a : Addr32} (hres : src.resolve env = some a)
    (hfind : Word.find w a = none) :
    runPFrom H env (.load src :: rest) w = (.refused (.noObject a), w) := by
  simp [runPFrom, hres, hfind]

/-- NECESSITY, present half: and when the word does hold it, the run
continues with that address in the history. Together with the previous
theorem: the outcome at a load line is a function of the word AT the
resolved address, and of nothing else. -/
theorem runPFrom_load_present (env : List Addr32) (src : PIn) (rest : PProg)
    (w : Word) {a : Addr32} {n : Node} (hres : src.resolve env = some a)
    (hfind : Word.find w a = some n) :
    runPFrom H env (.load src :: rest) w = runPFrom H (env ++ [a]) rest w := by
  simp [runPFrom, hres, hfind]

/-- NECESSITY at the table, where it holds with no reachability premise:
a table whose FIRST line loads a literal refuses at every word missing
that address — and the envelope names it. The lower bound is inhabited. -/
theorem runP_head_load_necessary (a : Addr32) (rest : PProg) (w : Word)
    (hfind : Word.find w a = none) :
    runP H (.load (.lit a) :: rest) w = (.refused (.noObject a), w)
      ∧ a ∈ PProg.reads (PLine.load (.lit a) :: rest) := by
  refine ⟨runPFrom_load_absent H [] (.lit a) rest w rfl hfind, ?_⟩
  simp [PProg.reads, PLine.operands]

/-! ### A refusal class the envelope decides without running

The dataflow component is not decoration: closedness of the DAG — every
edge naming a strictly earlier line — is decidable on the table alone and
rules out one whole refusal clause. This is the L-S product argument
(DESIGN.md §3.2, the LLM row) already available at L-A: admission of a
PROGRAM decided the way admission of a node is. -/

/-- An operand resolves whenever its index is inside the history. -/
theorem PIn.resolve_isSome_of {env : List Addr32} {x : PIn}
    (h : ∀ j, x = PIn.ans j → j < env.length) : (x.resolve env).isSome := by
  cases x with
  | lit a => simp [PIn.resolve]
  | ans j => simp [PIn.resolve, List.getElem?_eq_getElem (h j rfl)]

/-- Closedness at a table's head, split into the head line's obligation
and the tail's — the shape the run's own induction consumes. -/
theorem dataflowClosedFrom_cons {i : Nat} {l : PLine} {rest : PProg}
    (h : PProg.dataflowClosedFrom i (l :: rest) = true) :
    (∀ j, PIn.ans j ∈ l.operands → j < i)
      ∧ PProg.dataflowClosedFrom (i + 1) rest = true := by
  simp only [PProg.dataflowClosedFrom, PProg.dataflowFrom, List.all_append,
    Bool.and_eq_true] at h
  refine ⟨fun j hj => ?_, h.2⟩
  have hm : (i, j) ∈ l.operands.filterMap
      (fun x => match x with | .ans j => some (i, j) | .lit _ => none) :=
    List.mem_filterMap.mpr ⟨PIn.ans j, hj, rfl⟩
  simpa using List.all_eq_true.mp h.1 _ hm

/-- A CLOSED DATAFLOW CANNOT DANGLE, at any word and from any history of
matching length. The check is a `Bool` on the table; the conclusion is
about every run. -/
theorem runPFrom_no_dangling :
    ∀ (env : List Addr32) (p : PProg) (w : Word),
      PProg.dataflowClosedFrom env.length p = true →
        (runPFrom H env p w).1
          ≠ .refused (.failed "defun: dangling answer index") := by
  intro env p
  induction p generalizing env with
  | nil =>
    intro w _ hc
    cases hg : env.getLast? with
    | none => simp [runPFrom, hg] at hc
    | some b => simp [runPFrom, hg] at hc
  | cons line rest ih =>
    intro w hcl hc
    obtain ⟨hans, hrest⟩ := dataflowClosedFrom_cons hcl
    cases line with
    | put v t payload refs =>
      have hsome : (resolveRefs env refs).isSome :=
        resolveRefs_isSome fun x hx =>
          PIn.resolve_isSome_of fun j hj => hans j (hj ▸ hx)
      cases hr : resolveRefs env refs with
      | none => rw [hr] at hsome; simp at hsome
      | some rs =>
        cases hp : putWord H ⟨v, t, payload, rs⟩ w with
        | error e =>
          rw [show (runPFrom H env (PLine.put v t payload refs :: rest) w).1
              = Status.refused e from by simp [runPFrom, hr, hp]] at hc
          have he : e = Refusal.failed "defun: dangling answer index" := by
            simpa using hc
          exact putWord_ne_failed H (he ▸ hp)
        | ok aw =>
          obtain ⟨b, w''⟩ := aw
          rw [show (runPFrom H env (PLine.put v t payload refs :: rest) w).1
              = (runPFrom H (env ++ [b]) rest w'').1 from by
            simp [runPFrom, hr, hp]] at hc
          exact ih (env ++ [b]) w'' (by simpa using hrest) hc
    | load src =>
      have hsome : (src.resolve env).isSome :=
        PIn.resolve_isSome_of fun j hj => hans j (by simp [PLine.operands, hj])
      cases hs : src.resolve env with
      | none => rw [hs] at hsome; simp at hsome
      | some b =>
        cases hf : Word.find w b with
        | none => rw [runPFrom_load_absent H env src rest w hs hf] at hc; simp at hc
        | some n =>
          rw [runPFrom_load_present H env src rest w hs hf] at hc
          exact ih (env ++ [b]) w (by simpa using hrest) hc

/-- THE ENVELOPE DECIDES A REFUSAL CLASS: a table whose envelope reports a
closed dataflow never refuses for a dangling answer index, at any word.
Decided at stratum 1, before anything runs. -/
theorem runP_no_dangling (p : PProg) (w : Word)
    (h : (PProg.envelope p).dataflowClosed = true) :
    (runP H p w).1 ≠ .refused (.failed "defun: dangling answer index") :=
  runPFrom_no_dangling H [] p w h

/-! ### The envelope of a stored table — the leaves sync mechanically -/

/-- THE STORE CONTENT DETERMINES THE ENVELOPE: a table recovered from the
word it was laid down as has the same envelope, component for component.
Composed from `decodeProg_encodeProg`, so it is free — recovery is an
EQUALITY of tables, not a simulation. With `runP_decodeProg_encodeProg`
this closes the capability round trip on the analysis side: a stored
program's grant can be recomputed from the store alone. -/
theorem envelope_decodeProg_encodeProg (p : PProg)
    (hwf : ∀ l ∈ p, l.WF)
    (hsep : ∀ l ∈ p, ∀ l' ∈ p, lineAddr H l = lineAddr H l' → l = l')
    {q : PProg} (hq : decodeProg (encodeProg H p) = some q) :
    PProg.envelope q = PProg.envelope p := by
  rw [decodeProg_encodeProg H p hwf hsep] at hq
  exact congrArg PProg.envelope (Option.some.inj hq).symm

end Envelope

/-! ### THE GAP, LOCATED — the two witnesses

Where `possible` exceeds `actual`, exhibited rather than asserted, in the
style of `Address.lean`'s Level-2 witness and the `hsep` witness above.
Between them they are the WHOLE of L-A's over-approximation, and they
refute DESIGN.md §3.1's "exact: `over = under = actual`" for this rung. -/

/-- GAP 1 — THE REFUSAL SUFFIX. A table whose first line loads an address
no word holds refuses there; the envelope still declares the put on the
second line, which never executes and leaves no binding. The lines after
the first refusal are exactly what the envelope over-approximates. -/
example :
    ∃ (H : Bytes → Addr32) (a : Addr32) (p : PProg),
      runP H p [] = (.refused (.noObject a), [])
        ∧ (PProg.puts p).length = 1 := by
  refine ⟨fun _ => ⟨List.replicate 32 0, by simp⟩,
    ⟨List.replicate 32 0, by simp⟩,
    [.load (.lit ⟨List.replicate 32 0, by simp⟩), .put 0 0 [] []], rfl, rfl⟩

/-- GAP 2 — `put`'s DUPLICATE OUTCOME, the source DESIGN.md §2 does not
name. Two identical put lines declare two puts and admit ONE binding, on
a run that halts without refusing. The store has not lost anything; it
deduplicated, which is content addressing working as designed (F2). This
is why `runPFrom_puts_sound` concludes a sublist and not a prefix, and it
is a gap no amount of refusal analysis would close. -/
example :
    ∃ (H : Bytes → Addr32) (p : PProg),
      (runP H p []).1.isRunning = false
        ∧ (runP H p []).2.length = 1
        ∧ (PProg.puts p).length = 2 := by
  refine ⟨fun _ => ⟨List.replicate 32 0, by simp⟩,
    [.put 0 0 [] [], .put 0 0 [] []], ?_, ?_, rfl⟩
  · rfl
  · rfl

/-! ### THE BOUNDARY, EXHIBITED — the operation on the other side

HD-2. Everything above this line holds because `PLine.answer` exists.
This witness is the other side of `PLine.HashDetermined`, in the same
style: the estate's live NON-hash-determined operation, `LlmSig.infer`
(`Ops.lean`), inside the estate's live discharge for it,
`Prog.handleLlm` (`Interp.lean`). The witness decides.

Read it against `putWord_answer`. That theorem says a store operation's
answer moves with nothing — not the word, not the store, not a premise
on `H`. Here the program, the starting word and `H` all stand still and
the answer history moves anyway, because the answer is the oracle's and
the oracle is not a function of the operation. No `PLine.answer` can be
written for `infer`, at any effort, and that is not a gap in the
analysis: it is the definition of being outside the boundary.

So this witness is what makes the ruling in `PLine.HashDetermined`'s
docstring load-bearing rather than decorative. A build step whose output
address is DECLARED is a `put` — hash-determined, envelope intact, no
trace store. A build step whose output FLOATS is this witness — summed
in, oracled away in `handleLlm`'s shape, and owed `(out, deps, recipe)`
from `Persistable`. The two regimes are not a style choice; the line
between them is `PLine.HashDetermined`, and this program is on the far
side of it. -/

/-- THE COUNTER-WITNESS: one program over `AgentSig`, one starting word,
one address function, two oracles — two different answer histories. The
put line's payload is a function of the inference answer, so the address
it admits (the binding `putWord_word` appends, which IS the entry the
run writes into its history) moves with the oracle alone. A table over
`CasSig` cannot do this: `PLine.hashDetermined` forbids it. -/
example :
    ∃ (H : Bytes → Addr32) (p : Prog AgentSig Addr32) (o₁ o₂ : String → String),
      (runAgent H o₁ 2 p []).2.map Binding.address
        ≠ (runAgent H o₂ 2 p []).2.map Binding.address := by
  refine ⟨fun bs => ⟨List.replicate 32 (UInt8.ofNat bs.length), by simp⟩,
    (do
      let answer ← infer "how many?"
      liftCas (put ⟨0, 0, List.replicate answer.length 7, []⟩)),
    (fun _ => ""), (fun _ => "!"), by decide⟩

end Cas.Lang
