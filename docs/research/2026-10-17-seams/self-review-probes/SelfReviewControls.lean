import Effect4

/-!
Finite controls for the adversarial self-review of `interfaces.md`, at the tree `774ddc3d7`.
Consumer: the review's findings SR-n in `../self-review.md`.
Fragment: one-row applications, two-child binds, one hole, root and below-root edits.
These controls prove no theorem; each `#guard` is a finite evaluation of today's code.
-/

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 2400000

namespace SelfReviewControls
open Effect4 Effect4.Program Effect4.Store

def n1 : NativeEff := .succeed (.lit (.nat 1))
def n2 : NativeEff := .succeed (.lit (.nat 2))
def n7 : NativeEff := .succeed (.lit (.nat 7))
def app : SigApp := { rows := [Row.hole "ask" .nat] }
def h0 : Row := Row.hole "h0" .nat
def initial : Sketch := ⟨.bind (.perform (.external 0) (.lit .unit)) (Sketch.hole app 0), [h0]⟩
def d0 : Doc := Doc.open app initial ⟨"demo", 0⟩

/-! ## Root edits under a kept type (SR on `feed_keepExact`, `kept_eq_certified`, loop 4) -/

def base : Sketch := ⟨.bind n1 n1, []⟩
def baseDoc : Doc := Doc.open {} base ⟨"anchor", 0⟩

-- The edit engine never splices at the root, even when the root type is kept.
#guard (baseDoc.session.feed (.fill [] (.bind n1 n2))).2 == .rechecked
-- Below the root, a kept edit splices.
#guard match (baseDoc.session.feed (.fill [1] n2)).2 with
  | .spliced _ => true
  | _ => false
-- Today's keep-exact commit accepts the root edit on this reference-free base.
#guard match baseDoc.target [] with
  | none => false
  | some t => (baseDoc.commit t (.fill (.bind n1 n2)) .keepExactType).isOk
-- The old certification refuses every root fill, on the same reference-free base.
#guard certifiedB base {} [] (.bind n1 n2) = false
-- The fill set refuses the root before it certifies.
#guard ((FillSet.ofDoc baseDoc).add [([], .bind n1 n2)]).2 == [.refused [] .root]

-- A sketch whose program is a hole: `Place.hole 0` resolves at the root (the probe's filter).
def rootHole : Sketch := ⟨Sketch.hole app 0, [h0]⟩
def occurrences (s : Sketch) (k : Nat) : List (List Nat) :=
  (Node.addresses (.eff s.program)).filter fun p =>
    decide ((Node.eff s.program).at_ p = some (.eff (Sketch.hole app k)))
#guard occurrences rootHole 0 = [[]]
-- Filling that root hole at its own type rechecks; it does not splice.
#guard ((SourceSession.open app rootHole).feed (.fill [] n7)).2 == .rechecked

/-! ## Loop 1, rows 2 and 3 -/

-- Row 3: `.var 0` at `[1]` splices, and the reply's shown addresses are these.
#guard (d0.session.feed (.fill [1] (.succeed (.var 0)))).2 == .spliced [[1]]
-- Row 2: the part verdict of `.var 1` at `[1]` is a located refusal at the part's root.
#guard match Table.typedAt d0.session.table [1] with
  | some (env, _) =>
    match Checker.check (initial.sigAt app [1]) env [] (.succeed (.var 1)) with
    | .error ⟨[], .term _⟩ => true
    | _ => false
  | none => false

/-! ## Loop 1, rows 5 to 7: the event spellings elaborate as written, `.control .flush` included -/

def filled : NativeEff := .bind (.perform (.external 0) (.lit .unit)) (.succeed (.var 0))
def started : Option Live :=
  match admitProgram filled (app.withHoles [h0]) with
  | .error _ => none
  | .ok admitted =>
    some ((Live.open ⟨app.withHoles [h0], filled, admitted, [("ask", 0), ("h0", 1)]⟩
      "0").feed Run.Event.start).1
#guard match started with
  | none => false
  | some l =>
    let before := (l.feed (.apply (.row "ask"))).1
    match (Run.live before.run).head? with
    | none => false
    | some seen =>
      let after := before.feedAll
        [.receive (.key seen.key) (.ofExit (.success (.nat 7))), .apply (.key seen.key),
         .control .flush]
      after.run.exit == some (.success (.nat 7))

/-! ## Revert of a nested batch (SR on revert's current-target rule) -/

-- Item 1 fills `[1]`; item 2 edits inside item 1's product at `[1,1]`.
def afterBatch : Option Sketch :=
  (initial.fillAt [1] (.bind n1 n2)).bind fun s => s.fillAt [1, 1] n7
-- After the batch, `[1]` no longer holds what item 1 produced: a forward per-address check refuses.
#guard (afterBatch.map fun s =>
  decide ((Node.eff s.program).at_ [1] = some (.eff (.bind n1 n2))))
    = some false
-- Undoing the items in reverse order meets each item's product.
#guard (afterBatch.map fun s =>
  decide ((Node.eff s.program).at_ [1, 1] = some (.eff n7))) = some true

/-! ## The memo's key equality loses the old cache's prefix-extension hit -/

def sigA : SigData := ⟨app, [], .root⟩
def sigB : SigData := ⟨app, [h0], .root⟩
def keyA : CheckCache.CheckKey := ⟨n7, sigA, []⟩
def keyB : CheckCache.CheckKey := ⟨n7, sigB, []⟩
-- One hole row allocated: the signature data differ, so an exact-key memo misses.
#guard sigA.extendsB sigB = true
#guard decide (keyA = keyB) = false
-- Today's cache answers the grown signature from the entry learned before the allocation.
#guard (CheckCache.lookup [CheckCache.Entry.compute keyA] keyB []).isSome

/-! ## The state carrier and the stored references -/

-- The interface's carrier shape: a witness in `Prop` and no retained list.
structure StateOf (Raw : Type) (empty : Raw) (replay : Raw → List Nat → Raw) where
  private mk ::
  raw : Raw
  reached : ∃ as : List Nat, replay empty as = raw

-- `State.transcript` cannot be read off the witness: it erases.
/-- error: Tactic `cases` failed -/
#guard_msgs(error, substring := true) in
def transcriptOf {Raw : Type} {e : Raw} {r : Raw → List Nat → Raw} (s : StateOf Raw e r) :
    List Nat :=
  match s.reached with
  | ⟨as, _⟩ => as

-- A raw `Digest` field (the probe's `SessionEntry.parent`, `after`, `Job.program`, `Tape.job`,
-- `Answered.query`) encodes bytes, so the store's edge traversal sees no reference.
#guard (Canonical.toVal zeroDigest).refs = []
#guard (Canonical.toVal (AnyRef.mk .program zeroDigest)).refs = [AnyRef.mk .program zeroDigest]

end SelfReviewControls

#eval IO.println "SelfReviewControls: all controls evaluated"
