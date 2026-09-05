import Effect4.Store.Digest

/-!
# Store.Pin

Owner: the pin entity, a span of pinned third-party source carried as store
content, and the one theorem that says what a matching digest means.

A pin is `(package, version, file, declaration, role, anchor, offsets, span
digest, literal text)`. The anchor is a literal substring that must occur on
exactly one line of the file; the span runs from that line plus `offsetStart`
to that line plus `offsetEnd`, inclusive. Line numbers are not fields: an edit
above the anchor moves them and must not move the address, so they are a
projection the pin generator prints beside the pin, never content.

The literal text is carried so that the `pinned` rung is a kernel computation
over the pin alone: `isWellFormed` checks that the text agrees with the offsets
and that its bytes hash to the recorded digest, with no file access. The bytes
are the lines joined by a newline with a trailing newline, exactly what
`sed -n 'a,bp' file` prints, so the digest here and the digest the census
generator computes in shell (`scripts/generate-effect-runtime-census.sh:355`)
are the same number. A line is taken as its UTF-8 bytes, a projection that
costs no axiom (`Store/Canonical.lean`, the string instance).

The pin is store content through its derived instance, `Store/PinDerived.lean`:
`Canonical Pin` written by `Effect4Gen` from this structure (constructor 0, the
fields in declaration order) and `Content Pin` at kind `source`
(`docs/research/2026-09-04-cas-trait-plan.md` §3). Nothing here projects to JSON
and nothing here names an address: the printer is derived from the shape, and
the address is the store's `address` over the node bytes. The span digest is a
`Digest` in the carrier — a foreign hash, checked by recomputation and never
resolved against the store (the facts note, Q4) — and frames as thirty-two bytes.

Hash level 0 (`docs/research/2026-09-05-workshop-char/02-pins/01-pin-entity.md`, section 4): the pin
theorem characterizes a collision and assumes nothing about `sha256`. The
level-1 statement takes injectivity as a named premise that is never
discharged in this tree. Level 2 is not stated.
-/

set_option autoImplicit false

namespace Effect4.Store

/-- Whether the pinned declaration is exported by its module. A label on the
pin, carried in the payload; not part of what the anchor is derived from. -/
inductive PinRole where
  | «public»
  | internal
deriving DecidableEq, Repr, Inhabited

/-- The manifest spelling of a role. -/
def PinRole.spelling : PinRole → String
  | .public => "public"
  | .internal => "internal"

/-- A pinned span of third-party source. Every field is a `String`, a `Nat`, a
`Digest` or a `List String`: first-order, DB-02 clean. -/
structure Pin where
  /-- The package, `"effect"`. -/
  package : String
  /-- The package version, `"4.0.0-rc.112"`. -/
  version : String
  /-- The file, root-relative, `"src/Queue.ts"`. Never the root it was read from,
  so the same span read from `node_modules` and from `vendor/` has one address. -/
  file : String
  /-- The declaration the anchor was derived from, `"releaseCapacity"`. -/
  declaration : String
  role : PinRole
  /-- A literal substring occurring on exactly one line of `file`. -/
  anchor : String
  /-- The span starts `offsetStart` lines after the anchor line. -/
  offsetStart : Nat
  /-- The span ends `offsetEnd` lines after the anchor line, inclusive. -/
  offsetEnd : Nat
  /-- SHA-256 of `spanBytes`, as bytes. -/
  spanDigest : Digest
  /-- The literal lines of the span, without their newlines. -/
  text : List String
deriving DecidableEq, Repr

namespace Pin

/-- The pinned bytes: each line's UTF-8 bytes followed by a newline. This is
what `sed -n 'a,bp'` prints, so `sha256 spanBytes` is the shell's span digest. -/
def spanBytes (p : Pin) : Bytes :=
  p.text.foldr (fun line acc => line.toUTF8.data.toList ++ (10 :: acc)) []

/-- The number of lines the offsets span. Meaningful only when
`offsetStart ≤ offsetEnd`, which `isWellFormed` checks first. -/
def lineCount (p : Pin) : Nat := p.offsetEnd + 1 - p.offsetStart

/-- Well-formedness, as a `Bool`: the offsets are ordered, the text has exactly
the lines the offsets span, and the text hashes to the recorded digest. Nothing
here reads the pinned file, so a `#guard` over a pin list is a kernel
computation over literal lines. -/
def isWellFormed (p : Pin) : Bool :=
  decide (p.offsetStart ≤ p.offsetEnd) &&
  decide (p.lineCount = p.text.length) &&
  decide (sha256 p.spanBytes = p.spanDigest)

/-- Well-formedness, as the `Prop` a theorem takes. -/
def WellFormed (p : Pin) : Prop := p.isWellFormed = true

instance (p : Pin) : Decidable p.WellFormed := by
  unfold WellFormed; infer_instance

/-- A well-formed pin's text hashes to its recorded digest. -/
theorem spanDigest_eq_of_wellFormed (p : Pin) (h : p.WellFormed) :
    sha256 p.spanBytes = p.spanDigest := by
  unfold WellFormed isWellFormed at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.2

/-- **The pin theorem, level 0.** Bytes read upstream that hash to the pin's
digest are the pinned bytes, or SHA-256 collided on them. No hypothesis on
`sha256`; the case split is on the decidable equality of byte lists. -/
theorem holds_or_collision (p : Pin) (upstream : Bytes) (hWF : p.WellFormed)
    (h : sha256 upstream = p.spanDigest) :
    upstream = p.spanBytes ∨
      (upstream ≠ p.spanBytes ∧ sha256 upstream = sha256 p.spanBytes) :=
  if hEq : upstream = p.spanBytes then Or.inl hEq
  else Or.inr ⟨hEq, h.trans (p.spanDigest_eq_of_wellFormed hWF).symm⟩

/-- **Level 1, with its premise named.** Under injectivity of `sha256`, a
matching digest is matching bytes. The premise is never an instance, never an
axiom, and never discharged in this tree. -/
theorem holds_of_injective (hInj : Function.Injective sha256) (p : Pin)
    (upstream : Bytes) (hWF : p.WellFormed) (h : sha256 upstream = p.spanDigest) :
    upstream = p.spanBytes :=
  hInj (h.trans (p.spanDigest_eq_of_wellFormed hWF).symm)

end Pin

/-! ## Receipts -/

#print axioms PinRole.spelling
#print axioms Pin.spanBytes
#print axioms Pin.isWellFormed
#print axioms Pin.spanDigest_eq_of_wellFormed
#print axioms Pin.holds_or_collision
#print axioms Pin.holds_of_injective

end Effect4.Store
