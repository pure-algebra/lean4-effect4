import Cas.Lang.Handler

/-!
# Authenticated computation — the prover and the verifier, as handlers

λ•'s three modes over one source program (Miller–Hicks–Katz–Shi, POPL
2014) become, here, three HANDLERS over one `Prog CasSig`. There is no
second term and no compilation pass, so λ•'s agreement relation — one
rule per language construct — has nothing to relate; what it would have
proved is instead the absence of a construction.

**The operation correspondence, and the correction it forces.** `put`
is λ•'s `auth`: both digest a canonical encoding, answer the digest,
and reveal NOTHING to a proof stream, because a verifier holding the
node can digest it itself. `load` is λ•'s `unauth`: both take a digest,
must be HANDED content by someone, and check that the content digests
to the demanded address. So the proof stream is the LOAD trace. It is
not the store word, which is the PUT trace; conflating the two is the
mistake this module exists to not make.

**The proof word.** The carrier is reused unchanged: a proof word is a
`Word` in its verifier-facing role, in which the `address` field is
UNTRUSTED DECORATION and the check is `addr H ⟨b.node, _⟩ = a`, never
`b.address = a`. `verifyHandler` never reads `b.address`, and
`verify_load_accept` states that as a theorem rather than a comment.

**Three handlers, three trust postures, one carrier.** `replayHandler`
(`Handler.lean`) is NEITHER of these: it answers a `put` by comparing
the whole node against the recorded binding, so it presupposes the
replayer already holds the content and can never be deceived. A
verifier holds a digest only and is handed content by an untrusted
party. `proveHandler` records; `verifyHandler` checks; `replayHandler`
compares.

**Level 0 throughout.** `verify_load_or_collision` — ADSG's Lemma 6 in
estate form — has NO premise on `H`. It PRODUCES a collision pair
rather than assuming none exists, so CAS-003's empty Level 2 is
untouched, and the statement is a direct application of
`addr_eq_or_collision` (`Cas/Core/Address.lean`).

**ADSF's correction, at one-operation granularity.** Brun–Traytel (ITP
2019) found that ADSG's published security theorem has the wrong shape:
the verifier cannot DETECT that a collision occurred and keeps
consuming the stream, so evaluation does not stop at the collision. At
this slice's granularity the correction is a placement rule, and the
statements below obey it: the fact that the verifier consumed exactly
one head and continues on the tail is stated OUTSIDE the
resident-or-collision disjunction, holding identically in both
branches. Nothing here says the verifier halts on the collision branch,
because it does not. The multi-step lift inherits that placement as
ADSF's `π₀′`.

**The whole run.** `whole_run_security` (W-SEC) and
`whole_run_correctness` (W-COR) close the pair over a whole program by
induction through `interpret`. Two things about their shape are
findings rather than transcription, and the triage note above the
W-SEC section states both: the consumed prefix agrees with the
prover's emitted word only on its NODES, because the `address` field
is decoration the verifier never reads; and the prover's run appears
as a HYPOTHESIS, because this estate's `put` is an admission judgment
and can refuse where λ•'s always-succeeding `auth` cannot.
-/

namespace Cas.Lang

section Authenticated

variable (H : Bytes → Addr32)

/-! ## The honest word

The premise that separates a STORE word from a CLAIMED one. -/

/-- An honest word: every binding is address-correct — its node is a
codec-image node bound at its OWN address. This is the invariant the
reference semantics maintains (`referenceHandler_honest`), and it is
exactly what the `address` field of a PROOF word does not carry. -/
def HonestWord (w : Word) : Prop :=
  ∀ b ∈ w, ∃ h : b.node.WF, addr H ⟨b.node, h⟩ = b.address

/-- The empty word is honest. -/
theorem honestWord_nil : HonestWord H [] := by
  intro b hb
  exact absurd hb (by simp)

/-- Appending an address-correct binding preserves honesty. -/
theorem honestWord_snoc {w : Word} {a : Addr32} {n : Node}
    (hw : HonestWord H w) (h : n.WF) (ha : addr H ⟨n, h⟩ = a) :
    HonestWord H (w ++ [Binding.mk a n]) := by
  intro b hb
  rcases List.mem_append.mp hb with hmem | hmem
  · exact hw b hmem
  · have hb' : b = Binding.mk a n := by simpa using hmem
    subst hb'
    exact ⟨h, ha⟩

/-- An honest word's resident at an address is that address's
pre-image: what `find` answers digests to the address asked for. -/
theorem honestWord_find {w : Word} {a : Addr32} {n : Node}
    (hw : HonestWord H w) (hf : Word.find w a = some n) :
    ∃ h : n.WF, addr H ⟨n, h⟩ = a := by
  obtain ⟨h, ha⟩ := hw _ (Word.find_mem hf)
  exact ⟨h, ha⟩

/-! ## Mode P — the prover -/

/-- The prover's target: the store word and the emitted proof word
threaded together, refusal terminal. -/
abbrev ProveM := StateT (Word × Word) (Except Refusal)

/-- THE PROVER (λ• mode P). The store clauses are the reference
semantics unchanged — the prover is an honest interpreter — with one
addition: every `load` EMITS the binding it answered onto the proof
word. `put` emits nothing, because a verifier holding the node computes
the address itself; that asymmetry is the whole content of the
correspondence, and it is why the proof word is the load trace. -/
def proveHandler : Handler CasSig ProveM where
  handle
    | .put n => fun s =>
      if h : n.WF then
        match _root_.Cas.put H (Word.toStore s.1) ⟨n, h⟩ with
        | .error e => .error (.ofAdmission e)
        | .ok (.fresh a _) => .ok (a, (s.1 ++ [Binding.mk a n], s.2))
        | .ok (.duplicate a) => .ok (a, (s.1, s.2))
        | .ok (.conflict a _) => .error (.collision a)
      else .error .notWellFormed
    | .load a => fun s =>
      match Word.find s.1 a with
      | some n => .ok (n, (s.1, s.2 ++ [Binding.mk a n]))
      | none => .error (.noObject a)
    | .fail reason => fun _ => .error (.failed reason)

/-- The prover's store discipline IS the reference semantics: the
answer and the successor store word agree with `referenceHandler` at
every operation. The proof word is a pure addition — the prover cannot
lie about the store by recording. -/
theorem proveHandler_store_agree (op : CasSig.Op) (w π : Word) :
    ((proveHandler H).handle op (w, π)).map (fun r => (r.1, r.2.1))
      = (referenceHandler H).handle op w := by
  cases op with
  | put n =>
    by_cases h : n.WF
    · cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, h⟩ with
      | error e =>
        simp [proveHandler, referenceHandler, dif_pos h, hp, Except.map]
      | ok o =>
        cases o <;>
          simp [proveHandler, referenceHandler, dif_pos h, hp, Except.map]
    · simp [proveHandler, referenceHandler, dif_neg h, Except.map]
  | load a =>
    cases hf : Word.find w a <;>
      simp [proveHandler, referenceHandler, hf, Except.map]
  | fail reason => simp [proveHandler, referenceHandler, Except.map]

/-! ## Mode V — the verifier -/

/-- The verifier's target: the CLAIMED proof word, consumed head-first,
and nothing else. No store — that is the point. -/
abbrev VerifyM := StateT Word (Except Refusal)

/-- THE VERIFIER (λ• mode V). It holds no store: a `put` is answered by
digesting the node it was handed, exactly as the prover would, because
the verifier constructed it. A `load` is the only stream-consuming
clause: pop the head of the claimed proof word, REQUIRE that its node
is a codec-image node whose address is the one demanded, and answer
that node. The head's own `address` field is never read.

The well-formedness gate is the codec's image condition, not an extra
assumption: `Node.WF` is decidable and, by image exactness
(`decode_exact`), is exactly membership in the encoder's image — the
verifier is checking that the bytes it was handed parse before it
believes their digest. -/
def verifyHandler : Handler CasSig VerifyM where
  handle
    | .put n => fun π =>
      if h : n.WF then .ok (addr H ⟨n, h⟩, π)
      else .error .notWellFormed
    | .load a => fun π =>
      match π with
      | [] => .error (.failed "verify: proof word exhausted")
      | b :: rest =>
        if h : b.node.WF then
          if addr H ⟨b.node, h⟩ = a then .ok (b.node, rest)
          else .error
            (.failed "verify: digest does not match the demanded address")
        else .error .notWellFormed
    | .fail reason => fun _ => .error (.failed reason)

/-- What an accepted `load` certifies, unpacked. Two facts, and the
second is the certificate: the verifier consumed EXACTLY ONE head off
the claimed proof word — whose `address` field is left existential,
because the verifier never reads it — and the answer is a codec-image
node whose address is the address demanded. Everything the verifier
knows after accepting is here; in particular it does not know the node
is the honest resident, which is what the next theorem is about. -/
theorem verify_load_accept {a : Addr32} {π rest : Word} {m : Node}
    (h : (verifyHandler H).handle (.load a) π = .ok (m, rest)) :
    (∃ dec : Addr32, π = Binding.mk dec m :: rest)
      ∧ ∃ hm : m.WF, addr H ⟨m, hm⟩ = a := by
  match π with
  | [] => simp [verifyHandler] at h
  | ⟨dec, node⟩ :: tail =>
    by_cases hwf : node.WF
    · by_cases hd : addr H ⟨node, hwf⟩ = a
      · have hval : (verifyHandler H).handle (.load a)
              (Binding.mk dec node :: tail) = .ok (node, tail) := by
          simp [verifyHandler, dif_pos hwf, if_pos hd]
        rw [hval] at h
        have h' := Except.ok.inj h
        have hfst : node = m := congrArg Prod.fst h'
        have hsnd : tail = rest := congrArg Prod.snd h'
        subst hfst
        subst hsnd
        exact ⟨⟨dec, rfl⟩, hwf, hd⟩
      · simp [verifyHandler, dif_pos hwf, if_neg hd] at h
    · simp [verifyHandler, dif_neg hwf] at h

/-- **ADSG Lemma 6, estate form** — the single-operation
ideal-or-collision disjunct, at hash-lattice **Level 0**: no premise on
`H` appears, and the right branch EXHIBITS a collision rather than
excluding one.

If the verifier accepts a `load` against address `a`, answering `m`
from a claimed proof word, and the honest word resides `n` at `a`, then
the verifier consumed exactly one head and continues on `rest` —
stated outside the disjunction, because it holds in BOTH branches
(ADSF's correction: the verifier cannot detect a collision and does not
halt on one) — and either `m` IS the honest resident, or `m` and `n`
are two distinct canonical byte strings that `H` maps to one address:
the witness, named where it lives.

The proof is `addr_eq_or_collision` applied once. That it is only that
is the finding: the verifier's acceptance condition and the honest
word's address-correctness are the SAME equation about `H`, read from
two sides.

What the multi-step lift owes, named here so it is not discovered late:
`hresident` is the ONLY hypothesis this statement cannot see for
itself, and it is not a hash property — it is the prover's own `load`
clause succeeding at the same address. A run in which the verifier
demands an address the honest word does not hold is an address the
PROVER would have refused, so the lift discharges `hresident` from the
prover run's success, never from an assumption about `H`. That is why
this slice stays at Level 0 and why the lift does too. -/
theorem verify_load_or_collision {w π rest : Word} {a : Addr32}
    {m n : Node}
    (hw : HonestWord H w)
    (hresident : Word.find w a = some n)
    (haccept : (verifyHandler H).handle (.load a) π = .ok (m, rest)) :
    (∃ dec : Addr32, π = Binding.mk dec m :: rest)
      ∧ (m = n ∨
          (encodeNode m ≠ encodeNode n ∧
            H (encodeNode m) = H (encodeNode n))) := by
  obtain ⟨hhead, hm, hma⟩ := verify_load_accept H haccept
  obtain ⟨hn, hna⟩ := honestWord_find H hw hresident
  refine ⟨hhead, ?_⟩
  have hdig : addr H (⟨m, hm⟩ : AdmittedNode)
      = addr H (⟨n, hn⟩ : AdmittedNode) := by
    rw [hma, hna]
  rcases addr_eq_or_collision H hdig with heq | ⟨hne, hcol⟩
  · exact Or.inl (congrArg Subtype.val heq)
  · exact Or.inr ⟨hne, hcol⟩

/-! ## The premise is discharged, not assumed -/

/-- The reference semantics maintains honesty: `put` binds a node at
its own address and `load` does not grow the word, so an honest word
stays honest under every accepted operation. `verify_load_or_collision`
therefore rests on a property the estate's own semantics establishes,
never on a claim about the store. -/
theorem referenceHandler_honest (op : CasSig.Op) {w w' : Word}
    {ans : CasSig.Ans op} (hw : HonestWord H w)
    (h : (referenceHandler H).handle op w = .ok (ans, w')) :
    HonestWord H w' := by
  cases op with
  | put n =>
    by_cases hwf : n.WF
    · cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, hwf⟩ with
      | error e => simp [referenceHandler, dif_pos hwf, hp] at h
      | ok o =>
        cases o with
        | fresh a σ' =>
          have hval : (referenceHandler H).handle (.put n) w
              = .ok (a, w ++ [Binding.mk a n]) := by
            simp [referenceHandler, dif_pos hwf, hp]
          rw [hval] at h
          have hsnd : w ++ [Binding.mk a n] = w' :=
            congrArg Prod.snd (Except.ok.inj h)
          subst hsnd
          obtain ⟨_, _, ha, _⟩ := put_fresh_spec hp
          exact honestWord_snoc H hw hwf ha.symm
        | duplicate a =>
          have hval : (referenceHandler H).handle (.put n) w = .ok (a, w) := by
            simp [referenceHandler, dif_pos hwf, hp]
          rw [hval] at h
          have hsnd : w = w' := congrArg Prod.snd (Except.ok.inj h)
          subst hsnd
          exact hw
        | conflict a occ => simp [referenceHandler, dif_pos hwf, hp] at h
    · simp [referenceHandler, dif_neg hwf] at h
  | load a =>
    cases hf : Word.find w a with
    | none => simp [referenceHandler, hf] at h
    | some m =>
      have hval : (referenceHandler H).handle (.load a) w = .ok (m, w) := by
        simp [referenceHandler, hf]
      rw [hval] at h
      have hsnd : w = w' := congrArg Prod.snd (Except.ok.inj h)
      subst hsnd
      exact hw
  | fail reason => simp [referenceHandler] at h

/-! ## The whole run — W-SEC

Slice 2: the one-operation disjunct lifted to a whole program, by
induction through `interpret`. Statement triage moved the designed
shape (`.staging/operational-structure/DESIGN.md` §1.6) twice, and
both moves are recorded here because both are findings about the
ESTATE's semantics rather than about λ•.

**Triage 1 — the consumed prefix is equal only up to decoration.** The
designed branch said `π_A = π ++ π′` with `π` the prover's emitted
proof word. That is false, and `verify_load_accept` already says why:
the verifier never reads a head's `address` field, so an adversary may
put anything there and still be accepted. What the verifier's
acceptance certifies is the head's NODE. The agreement is therefore
stated on `proofNodes` — the proof word with the untrusted decoration
erased — and that is exactly as strong as the truth.

**Triage 2 — the prover's run is a HYPOTHESIS, not a conclusion.**
ADSG's Security half puts the prover run's existence in the
conclusion, and it may: λ•'s `auth` always succeeds. The estate's
`put` is an admission JUDGMENT (`Cas.put` → `checkRefs`), and
`verifyHandler` performs no admission check at all — it holds no store
to check against. So a program that `put`s a node with a dangling
reference is ACCEPTED by the verifier and REFUSED by the prover, with
no collision anywhere: ADSG's conclusion-form is refuted for this
estate by a two-line witness. The advantage named at DESIGN §1.4 item
5 is what breaks the theorem's designed shape.

The repair is the one `verify_load_or_collision`'s docstring already
prescribes: the prover's run succeeding is the premise, and
`hresident` is read off it at each `load`. Nothing about `H` is
assumed — Level 0 is untouched, and the collision is exhibited.

**ADSF's placement, at run granularity.** The verifier consumes a
PREFIX of the claimed word — one head per `load`, nothing per `put` —
and it does so in both branches, because it cannot detect a collision
and does not halt on one. So `∃ π₀, π_A = π₀ ++ π′` is stated OUTSIDE
the disjunction (`verify_run_prefix` proves it with no honest word and
no prover in sight), and only the CONTENT agreement sits inside it.
That is ADSF's correction in this estate's spelling: the collision
branch constrains nothing about where in the claimed word the
collision fell, or about the tail the verifier went on consuming. -/

/-- The TRUSTED content of a proof word: its nodes, with the `address`
field erased. In the verifier's role that field is untrusted
decoration the verifier never reads (`verify_load_accept`), so this is
exactly the information on which a claimed word and the prover's
emitted word can be compared. -/
def proofNodes (π : Word) : List Node := π.map Binding.node

/-- The empty proof word carries no content. -/
@[simp] theorem proofNodes_nil : proofNodes [] = [] := rfl

/-- The content of a head is its node. -/
@[simp] theorem proofNodes_cons (b : Binding) (π : Word) :
    proofNodes (b :: π) = b.node :: proofNodes π := rfl

/-- Content is additive along the word — what makes the prover's
accumulator and the verifier's consumed prefix comparable piecewise. -/
@[simp] theorem proofNodes_append (π π' : Word) :
    proofNodes (π ++ π') = proofNodes π ++ proofNodes π' := by
  simp [proofNodes]

/-- Interpretation of a finished program: the answer, the state
untouched. -/
@[simp] theorem interpret_pure_state {σ : Type}
    (h : Handler CasSig (StateT σ (Except Refusal))) (a : A) (s : σ) :
    interpret h (Prog.pure a) s = .ok (a, s) := rfl

/-- Interpretation into a state-and-refusal target, one operation at a
time: the handler's clause decides the answer and the successor state,
or stops the run at its refusal. The generic form of `interpretRef_vis`
(`Handler.lean`); both authenticated handlers are instances, and every
induction below runs through it. -/
theorem interpret_vis_state {σ : Type}
    (h : Handler CasSig (StateT σ (Except Refusal)))
    (op : CasSig.Op) (k : CasSig.Ans op → Prog CasSig A) (s : σ) :
    interpret h (.vis op k) s
      = match h.handle op s with
        | .ok (ans, s') => interpret h (k ans) s'
        | .error r => .error r := by
  cases hh : h.handle op s with
  | ok as =>
    obtain ⟨ans, s'⟩ := as
    simp [interpret, bind, StateT.bind, Except.bind, hh]
  | error r =>
    simp [interpret, bind, StateT.bind, Except.bind, hh]

/-! ### The clauses, unpacked -/

/-- The verifier's `put` clause, positively: a well-formed node is
answered with its OWN address, and the claimed word is untouched. A
verifier holding the node needs no stream traffic — the asymmetry that
makes the proof word the LOAD trace. -/
theorem verify_put_clause {n : Node} (hn : n.WF) (π : Word) :
    (verifyHandler H).handle (.put n) π = .ok (addr H ⟨n, hn⟩, π) := by
  simp [verifyHandler, dif_pos hn]

/-- The verifier's `put`, read backwards from an acceptance. -/
theorem verify_put_answer {n : Node} {π π' : Word} {a : Addr32}
    (h : (verifyHandler H).handle (.put n) π = .ok (a, π')) :
    ∃ hn : n.WF, a = addr H ⟨n, hn⟩ ∧ π' = π := by
  by_cases hn : n.WF
  · rw [verify_put_clause H hn] at h
    exact ⟨hn, (congrArg Prod.fst (Except.ok.inj h)).symm,
      (congrArg Prod.snd (Except.ok.inj h)).symm⟩
  · simp [verifyHandler, dif_neg hn] at h

/-- The verifier consumes a PREFIX at every operation — one head at a
`load`, nothing at a `put`. No honest word and no prover appear: this
is the fact ADSF's correction requires to hold in both branches. -/
theorem verify_handle_prefix {op : CasSig.Op} {π π' : Word}
    {ans : CasSig.Ans op}
    (h : (verifyHandler H).handle op π = .ok (ans, π')) :
    ∃ π₀, π = π₀ ++ π' := by
  cases op with
  | put n =>
    obtain ⟨_, _, hπ⟩ := verify_put_answer H h
    exact ⟨[], by simp [hπ]⟩
  | load a =>
    obtain ⟨⟨dec, hdec⟩, _⟩ := verify_load_accept H h
    exact ⟨[Binding.mk dec ans], by simp [hdec]⟩
  | fail reason => simp [verifyHandler] at h

/-- The prover's `put`: the node's own address in both accepting
outcomes (`put_fresh_spec`, `put_duplicate_spec`), and NOTHING emitted
onto the proof word. The verifier answers the same address, so `put`
is the invariant-preserving step of the lift. -/
theorem prove_put_answer {n : Node} {w πacc w' πacc' : Word} {a : Addr32}
    (h : (proveHandler H).handle (.put n) (w, πacc) = .ok (a, (w', πacc'))) :
    ∃ hn : n.WF, a = addr H ⟨n, hn⟩ ∧ πacc' = πacc := by
  by_cases hn : n.WF
  · cases hp : _root_.Cas.put H (Word.toStore w) ⟨n, hn⟩ with
    | error e => simp [proveHandler, dif_pos hn, hp] at h
    | ok o =>
      cases o with
      | fresh b σ' =>
        have hval : (proveHandler H).handle (.put n) (w, πacc)
            = .ok (b, (w ++ [Binding.mk b n], πacc)) := by
          simp [proveHandler, dif_pos hn, hp]
        rw [hval] at h
        obtain ⟨_, _, hb, _⟩ := put_fresh_spec hp
        have h' := Except.ok.inj h
        have h1 : b = a := congrArg Prod.fst h'
        have h2 : πacc = πacc' := congrArg (fun r => r.2.2) h'
        exact ⟨hn, by rw [← h1]; exact hb, h2.symm⟩
      | duplicate b =>
        have hval : (proveHandler H).handle (.put n) (w, πacc)
            = .ok (b, (w, πacc)) := by
          simp [proveHandler, dif_pos hn, hp]
        rw [hval] at h
        obtain ⟨_, hb, _⟩ := put_duplicate_spec hp
        have h' := Except.ok.inj h
        have h1 : b = a := congrArg Prod.fst h'
        have h2 : πacc = πacc' := congrArg (fun r => r.2.2) h'
        exact ⟨hn, by rw [← h1]; exact hb, h2.symm⟩
      | conflict b occ => simp [proveHandler, dif_pos hn, hp] at h
  · simp [proveHandler, dif_neg hn] at h

/-- The prover's `load`: the honest resident, the store word untouched,
and the binding it answered appended to the proof word. This is where
`hresident` comes from — the prover's own clause, not a premise. -/
theorem prove_load_clause {a : Addr32} {w πacc w' πacc' : Word} {n : Node}
    (h : (proveHandler H).handle (.load a) (w, πacc) = .ok (n, (w', πacc'))) :
    Word.find w a = some n ∧ w' = w ∧ πacc' = πacc ++ [Binding.mk a n] := by
  cases hf : Word.find w a with
  | none => simp [proveHandler, hf] at h
  | some m =>
    have hval : (proveHandler H).handle (.load a) (w, πacc)
        = .ok (m, (w, πacc ++ [Binding.mk a m])) := by
      simp [proveHandler, hf]
    rw [hval] at h
    have h' := Except.ok.inj h
    have hmn : m = n := congrArg Prod.fst h'
    have hww : w = w' := congrArg (fun r => r.2.1) h'
    have hππ : πacc ++ [Binding.mk a m] = πacc' := congrArg (fun r => r.2.2) h'
    refine ⟨?_, hww.symm, ?_⟩
    · exact congrArg some hmn
    · rw [← hππ, hmn]

/-! ### HonestWord preservation — the load-bearing helper -/

/-- **HonestWord preservation, one operation.** The prover's store
clauses ARE the reference semantics (`proveHandler_store_agree`), so
the invariant the reference maintains (`referenceHandler_honest`) is
maintained by the prover for free: recording cannot corrupt the store
it records from. -/
theorem proveHandler_honest (op : CasSig.Op) {w πacc w' πacc' : Word}
    {ans : CasSig.Ans op} (hw : HonestWord H w)
    (h : (proveHandler H).handle op (w, πacc) = .ok (ans, (w', πacc'))) :
    HonestWord H w' := by
  have hmap := proveHandler_store_agree H op w πacc
  rw [h] at hmap
  simp only [Except.map] at hmap
  exact referenceHandler_honest H op hw hmap.symm

/-- **HonestWord preservation, whole run.** Honesty is an invariant of
the prover's interpretation of any program: every accepted operation
preserves it, so the final store word of a successful prover run over
an honest word is honest. This is what lets the lift below read
`hresident` off the prover at EVERY load rather than only the first. -/
theorem interpret_prove_honest (p : Prog CasSig A) :
    ∀ {w πacc w' πP : Word} {a : A}, HonestWord H w →
      interpret (proveHandler H) p (w, πacc) = .ok (a, (w', πP)) →
      HonestWord H w' := by
  induction p with
  | pure a₀ =>
    intro w πacc w' πP a hw h
    rw [interpret_pure_state] at h
    have hww : w = w' := congrArg (fun r => r.2.1) (Except.ok.inj h)
    rw [← hww]
    exact hw
  | vis op k ih =>
    intro w πacc w' πP a hw h
    rw [interpret_vis_state] at h
    cases hh : (proveHandler H).handle op (w, πacc) with
    | error r => simp only [hh] at h; simp at h
    | ok r =>
      obtain ⟨ans, w₁, πacc₁⟩ := r
      simp only [hh] at h
      exact ih ans (proveHandler_honest H op hw hh) h

/-! ### The verifier's prefix consumption — ADSF's placement -/

/-- The verifier consumes a PREFIX of the claimed word over a whole
run. Stated with no honest word, no prover, and no premise on `H`,
because ADSF's correction requires it to hold identically in both
branches of the security disjunction: the verifier cannot detect a
collision, so it goes on consuming past one. -/
theorem verify_run_prefix (p : Prog CasSig A) :
    ∀ {πA π' : Word} {a : A},
      interpret (verifyHandler H) p πA = .ok (a, π') → ∃ π₀, πA = π₀ ++ π' := by
  induction p with
  | pure a₀ =>
    intro πA π' a h
    rw [interpret_pure_state] at h
    have hπ : πA = π' := congrArg Prod.snd (Except.ok.inj h)
    exact ⟨[], by simp [hπ]⟩
  | vis op k ih =>
    intro πA π' a h
    rw [interpret_vis_state] at h
    cases hh : (verifyHandler H).handle op πA with
    | error r => simp only [hh] at h; simp at h
    | ok r =>
      obtain ⟨ans, πA₁⟩ := r
      simp only [hh] at h
      obtain ⟨π₀, h₀⟩ := verify_handle_prefix H hh
      obtain ⟨π₁, h₁⟩ := ih ans h
      exact ⟨π₀ ++ π₁, by rw [h₀, h₁]; simp⟩

/-! ### The single-operation lemma of the lift -/

/-- **One operation, both handlers, one honest word.** The prover's
successor word stays honest; the verifier consumed a prefix — stated
outside the disjunction, ADSF's placement; and either the two answers
agree and the consumed prefix's trusted content is exactly what the
prover emitted, or a collision is exhibited.

`put` is the invariant-preserving step: it consumes nothing and emits
nothing, so the prefix is empty on both sides and the answers agree by
`put`'s own characterization. `load` is the whole content, and it is
`verify_load_or_collision` applied once — with `hresident` discharged
from the PROVER's clause succeeding (`prove_load_clause`), never from
an assumption about `H`. -/
theorem handle_step_agree {op : CasSig.Op} {w πacc w₁ πacc₁ πA πA₁ : Word}
    {ansP ansV : CasSig.Ans op}
    (hw : HonestWord H w)
    (hP : (proveHandler H).handle op (w, πacc) = .ok (ansP, (w₁, πacc₁)))
    (hV : (verifyHandler H).handle op πA = .ok (ansV, πA₁)) :
    HonestWord H w₁ ∧
      ∃ π₀, πA = π₀ ++ πA₁ ∧
        ((ansV = ansP ∧
            proofNodes πacc₁ = proofNodes πacc ++ proofNodes π₀)
          ∨ ∃ bs bs' : Bytes, bs ≠ bs' ∧ H bs = H bs') := by
  refine ⟨proveHandler_honest H op hw hP, ?_⟩
  cases op with
  | put n =>
    obtain ⟨hnP, haP, haccP⟩ := prove_put_answer H hP
    obtain ⟨hnV, haV, hπV⟩ := verify_put_answer H hV
    exact ⟨[], by simp [hπV], Or.inl ⟨by rw [haV, haP], by simp [haccP]⟩⟩
  | load a =>
    obtain ⟨hres, _, hacc⟩ := prove_load_clause H hP
    obtain ⟨⟨dec, hdec⟩, hdisj⟩ := verify_load_or_collision H hw hres hV
    refine ⟨[Binding.mk dec ansV], by simp [hdec], ?_⟩
    rcases hdisj with heq | ⟨hne, hcol⟩
    · exact Or.inl ⟨heq, by simp [hacc, heq]⟩
    · exact Or.inr ⟨encodeNode ansV, encodeNode ansP, hne, hcol⟩
  | fail reason => exact ansP.elim

/-! ### W-SEC -/

/-- The lift's inductive form, with the prover's proof-word accumulator
generalized. The conclusion compares the whole emitted word against the
accumulator it started from, which is what makes the induction close at
each `load`. -/
theorem interpret_agree_or_collision (p : Prog CasSig A) :
    ∀ {w πacc w' πP πA π' : Word} {aP aV : A},
      HonestWord H w →
      interpret (proveHandler H) p (w, πacc) = .ok (aP, (w', πP)) →
      interpret (verifyHandler H) p πA = .ok (aV, π') →
      ∃ π₀, πA = π₀ ++ π' ∧
        ((aV = aP ∧ proofNodes πP = proofNodes πacc ++ proofNodes π₀)
          ∨ ∃ bs bs' : Bytes, bs ≠ bs' ∧ H bs = H bs') := by
  induction p with
  | pure a₀ =>
    intro w πacc w' πP πA π' aP aV _ hP hV
    rw [interpret_pure_state] at hP hV
    have hP' := Except.ok.inj hP
    have hV' := Except.ok.inj hV
    have haP : a₀ = aP := congrArg Prod.fst hP'
    have haV : a₀ = aV := congrArg Prod.fst hV'
    have hπP : πacc = πP := congrArg (fun r => r.2.2) hP'
    have hπV : πA = π' := congrArg Prod.snd hV'
    exact ⟨[], by simp [hπV],
      Or.inl ⟨by rw [← haV, ← haP], by simp [hπP]⟩⟩
  | vis op k ih =>
    intro w πacc w' πP πA π' aP aV hw hP hV
    rw [interpret_vis_state] at hP hV
    cases hPh : (proveHandler H).handle op (w, πacc) with
    | error r => simp only [hPh] at hP; simp at hP
    | ok rP =>
      obtain ⟨ansP, w₁, πacc₁⟩ := rP
      cases hVh : (verifyHandler H).handle op πA with
      | error r => simp only [hVh] at hV; simp at hV
      | ok rV =>
        obtain ⟨ansV, πA₁⟩ := rV
        simp only [hPh] at hP
        simp only [hVh] at hV
        obtain ⟨hw₁, π₀, hsplit, hcase⟩ := handle_step_agree H hw hPh hVh
        rcases hcase with ⟨hans, hcontent⟩ | hcol
        · subst hans
          obtain ⟨π₁, hsplit₁, hrest⟩ := ih ansV hw₁ hP hV
          refine ⟨π₀ ++ π₁, by rw [hsplit, hsplit₁]; simp, ?_⟩
          rcases hrest with ⟨heq, hc⟩ | hcol
          · exact Or.inl ⟨heq, by rw [hc, hcontent]; simp⟩
          · exact Or.inr hcol
        · obtain ⟨π₁, hsplit₁⟩ := verify_run_prefix H (k ansV) hV
          exact ⟨π₀ ++ π₁, by rw [hsplit, hsplit₁]; simp, Or.inr hcol⟩

/-- **W-SEC — the whole-run security theorem**, in ADSF's corrected
shape, at hash-lattice **Level 0**: no premise on `H` appears anywhere
in the statement or the proof, and the right branch EXHIBITS a
collision rather than excluding one.

Read it as the untrusted-producer guarantee. A program `p` is run by an
honest prover over an honest word `w`, emitting the proof word `πP`;
someone — a model, a mirror, a remote host — hands the estate an
ARBITRARY claimed proof word `πA`. If the verifier, which holds no
store at all, accepts `p` against `πA`, then:

- (outside the disjunction, holding in BOTH branches — ADSF's
  correction) the verifier consumed a PREFIX of `πA` and left the tail
  `π'` untouched: it cannot detect a collision, so it does not halt on
  one and the tail carries no claim; and
- (branch a) the verifier's answer is the TRUE answer `aP`, and the
  prefix it consumed is the prover's emitted proof word up to the
  `address` decoration the verifier never reads (`proofNodes`); **or**
- (branch b) two distinct byte strings with one `H`-image — the
  witness, named where it lives.

The prover's run appearing as a HYPOTHESIS rather than a conclusion is
this estate's correction to ADSG's shape, forced by admission being a
judgment; see the triage note above. `hresident` is discharged from
that hypothesis at every `load`, so CAS-003's empty Level 2 is
untouched. -/
theorem whole_run_security (p : Prog CasSig A)
    {w w' πP πA π' : Word} {aP aV : A}
    (hw : HonestWord H w)
    (hprove : interpret (proveHandler H) p (w, []) = .ok (aP, (w', πP)))
    (hverify : interpret (verifyHandler H) p πA = .ok (aV, π')) :
    ∃ π₀, πA = π₀ ++ π' ∧
      ((aV = aP ∧ proofNodes π₀ = proofNodes πP)
        ∨ ∃ bs bs' : Bytes, bs ≠ bs' ∧ H bs = H bs') := by
  obtain ⟨π₀, hsplit, hcase⟩ :=
    interpret_agree_or_collision H p hw hprove hverify
  refine ⟨π₀, hsplit, ?_⟩
  rcases hcase with ⟨heq, hc⟩ | hcol
  · exact Or.inl ⟨heq, by simpa using hc.symm⟩
  · exact Or.inr hcol

/-! ### W-COR — the correctness half

The easier direction, and what makes the pair meaningful: the proof
word the prover emits is exactly the word that makes the verifier
accept, with the same answer and nothing left over. -/

/-- The correctness half's inductive form, with the accumulator
generalized: what the prover appends to the accumulator is exactly what
the verifier consumes. -/
theorem interpret_prove_verify (p : Prog CasSig A) :
    ∀ {w πacc w' πP : Word} {a : A} (rest : Word),
      HonestWord H w →
      interpret (proveHandler H) p (w, πacc) = .ok (a, (w', πP)) →
      ∃ πe, πP = πacc ++ πe ∧
        interpret (verifyHandler H) p (πe ++ rest) = .ok (a, rest) := by
  induction p with
  | pure a₀ =>
    intro w πacc w' πP a rest _ h
    rw [interpret_pure_state] at h
    have h' := Except.ok.inj h
    have ha : a₀ = a := congrArg Prod.fst h'
    have hπ : πacc = πP := congrArg (fun r => r.2.2) h'
    exact ⟨[], by simp [hπ], by simp [ha]⟩
  | vis op k ih =>
    intro w πacc w' πP a rest hw h
    rw [interpret_vis_state] at h
    cases hh : (proveHandler H).handle op (w, πacc) with
    | error r => simp only [hh] at h; simp at h
    | ok r =>
      obtain ⟨ansP, w₁, πacc₁⟩ := r
      simp only [hh] at h
      have hw₁ := proveHandler_honest H op hw hh
      cases op with
      | put n =>
        obtain ⟨hn, ha, hacc⟩ := prove_put_answer H hh
        obtain ⟨πe, hπe, hv⟩ := ih ansP rest hw₁ h
        refine ⟨πe, by rw [hπe, hacc], ?_⟩
        have hval : (verifyHandler H).handle (.put n) (πe ++ rest)
            = .ok (ansP, πe ++ rest) := by
          rw [ha]; exact verify_put_clause H hn (πe ++ rest)
        rw [interpret_vis_state (verifyHandler H) (CasE.put n) k (πe ++ rest)]
        simp only [hval]
        exact hv
      | load b =>
        obtain ⟨hres, _, hacc⟩ := prove_load_clause H hh
        obtain ⟨hn, hna⟩ := honestWord_find H hw hres
        obtain ⟨πe, hπe, hv⟩ := ih ansP rest hw₁ h
        refine ⟨Binding.mk b ansP :: πe, by rw [hπe, hacc]; simp, ?_⟩
        have hval : (verifyHandler H).handle (.load b)
              ((Binding.mk b ansP :: πe) ++ rest)
            = .ok (ansP, πe ++ rest) := by
          simp [verifyHandler, dif_pos hn, hna]
        rw [interpret_vis_state (verifyHandler H) (CasE.load b) k
          ((Binding.mk b ansP :: πe) ++ rest)]
        simp only [hval]
        exact hv
      | fail reason => exact ansP.elim

/-- **W-COR — the correctness half.** The proof word the prover emits
over an honest word is precisely a word the verifier accepts, with the
SAME answer, consuming exactly it and leaving any suffix untouched.
Together with `whole_run_security` this is λ•'s Theorem 1 in estate
form: the pair is sound (the honest prover convinces the verifier) and
secure (nothing else does, absent a collision). -/
theorem whole_run_correctness (p : Prog CasSig A)
    {w w' πP : Word} {a : A} (rest : Word)
    (hw : HonestWord H w)
    (hprove : interpret (proveHandler H) p (w, []) = .ok (a, (w', πP))) :
    interpret (verifyHandler H) p (πP ++ rest) = .ok (a, rest) := by
  obtain ⟨πe, hπ, hv⟩ := interpret_prove_verify H p rest hw hprove
  rw [show πP = πe by simpa using hπ]
  exact hv

end Authenticated

end Cas.Lang
