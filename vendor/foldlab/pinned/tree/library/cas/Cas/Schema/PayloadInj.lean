import Cas.Schema.SelfCodec
import Cas.Values.JsonParse

/-!
# Revision-1 payload injectivity — equal bytes, equal code

The schema plane's half of "bytes determine the canonical value". The
value plane owns the hard direction, `Json.RenderPlainInjective`;
everything here is the short derivation on top of it, plus the one thing
the value plane cannot know.

The hard direction is now PROVED (`Json.renderPlain_injective`,
`Cas.Values.JsonParse`, from the strict parser's adequacy), so every law
in this module is UNCONDITIONAL. It was stated conditionally through
Stage 3; the statements are unchanged, the hypothesis is gone.

## The chain

    a.payload = b.payload                       (hypothesis)
  → renderPlain a.envelope = renderPlain b.envelope   (payload_renderPlain)
  → a.envelope.numNorm = b.envelope.numNorm     (RenderPlainInjective,
                                                 envelope_canonical)
  → a.envelope = b.envelope                     (deNumNorm_envelope, WF)
  → a.repNorm = b.repNorm                       (envelope_inj)

## Where `WF` is load-bearing

The value plane's obligation can only conclude equality up to
`Value.numNorm`, the number collapse: `Json.Value.nat n` and
`Json.Value.int n` have one decimal spelling
(`Json.renderPlain_not_injective`). Recovering the spelling is a
SCHEMA-plane fact, and it is exactly where the well-formedness premise
does its work.

A revision-1 representation spells a number in three places, and the
key decides which constructor stands there:

- `"revision"` — the envelope's `Value.nat`;
- `"payload"` — `Value.nat` for row zero's kind tag (`Ast.ref`), and
  for the general declaration code (`Ast.decl`) whatever
  `DeclPayload` carries;
- `"value"` — `Value.int` for a number literal, and nothing else
  numeric (a property signature's name and the other literals are
  strings and booleans).

`deNumNorm` is that reading as a function: undo the collapse under the
key `"value"`, leave every other key alone. It inverts `numNorm` on the
representation image — but ONLY under `WF`. Without it,

    Ast.decl .date (.nat 5) []   and   Ast.decl .date (.int 5) []

are two codes with two representations and ONE payload byte string, so
`payload_inj` is FALSE without the premise. `WF` rules both out: the
registry's payload discipline (`DeclarationId.PayloadWF`) admits only
`.null` on every general row, so the general declaration code never
puts a number under `"payload"` at all. `deNumNorm_decl_payload` is
that step, and it is the only arm of the recovery that consumes a
hypothesis.

## All proved

- `deNumNorm_numNorm_representation`, `deNumNorm_numNorm_envelope`,
  `envelope_numNorm_inj` — kernel-checked here;
- `payload_inj_needs_wf` — the `WF` premise is necessary, exhibited by
  the two codes above;
- `payload_inj`, `payload_inj'`, `payloadBytes_inj` — the laws
  themselves, now unconditional. "The node at this address IS this
  code" is a fact, not a pin (survey blocker B7 closed, ruling 11
  closed).
-/

namespace Cas.Schema

open Cas.Json

/-! ## Undoing the number collapse on a revision-1 representation -/

/-- Restore the `Value.int` spelling a number literal is stored with.
Applied only under the key `"value"`, and only to a bare number: the
envelope's own `"value"` carries the representation document, which is
an object and passes through. -/
def reint : Json.Value → Json.Value
  | .nat n => .int (Int.ofNat n)
  | v => v

mutual

/-- The number collapse undone, keyed on the field name: `"value"` is
the one key a revision-1 representation spells a number under with
`Value.int`. Left inverse of `Json.Value.numNorm` on the representation
image of a WELL-FORMED code (`deNumNorm_numNorm_representation`). -/
def deNumNorm : Json.Value → Json.Value
  | .arr xs => .arr (deNumNormItems xs)
  | .obj fs => .obj (deNumNormFields fs)
  | v => v

def deNumNormItems : List Json.Value → List Json.Value
  | [] => []
  | x :: xs => deNumNorm x :: deNumNormItems xs

def deNumNormFields :
    List (String × Json.Value) → List (String × Json.Value)
  | [] => []
  | (k, v) :: fs =>
    (k, if k = "value" then reint (deNumNorm v) else deNumNorm v)
      :: deNumNormFields fs

end

/-- The general declaration code never carries a number: every general
registry row's payload discipline admits `.null` and nothing else, so
`WF` pins the payload before the collapse can reach it. THE arm where
the well-formedness premise is consumed. -/
theorem deNumNorm_decl_payload {g : DeclarationId.General} {p : DeclPayload}
    (h : g.PayloadWF p) : p = .null := by
  cases g <;> cases p <;> first | rfl | exact absurd h (by simp [
    DeclarationId.General.PayloadWF, DeclarationId.General.row,
    DeclarationId.PayloadWF])

/-- The recovery is exact on an enum member's value. A number member is
spelled under the key `"value"` — the same key a number literal uses —
so the same reading recovers it, and the string member carries no number
to recover. Stated OUTSIDE the mutual block below because an enum member
carries no code: the enum arm is not part of the recursion over `Ast`. -/
theorem deNumNorm_numNorm_enumValue (v : EnumValue) :
    deNumNorm (Json.Value.numNorm v.toJson) = v.toJson := by
  cases v with
  | str _ => rfl
  | int i =>
    by_cases h : 0 ≤ i.val
    · show (Json.Value.obj _) = _
      simp only [EnumValue.toJson, Json.Value.numNorm, numNormFields, deNumNorm,
        deNumNormFields, if_pos h, reint, ite_self, Json.Value.obj.injEq,
        List.cons.injEq, Prod.mk.injEq, if_true, and_true, true_and]
      exact congrArg Json.Value.int (Int.toNat_of_nonneg h)
    · show (Json.Value.obj _) = _
      simp only [EnumValue.toJson, Json.Value.numNorm, numNormFields, deNumNorm,
        deNumNormFields, if_neg h, reint, ite_self]

/-- The recovery is exact on a whole member list. -/
theorem deNumNorm_numNorm_enumMembers :
    ∀ (ms : List (String × EnumValue)),
      deNumNormItems (numNormItems (enumMembersToJson ms))
        = enumMembersToJson ms
  | [] => rfl
  | (n, v) :: ms => by
    show (_ :: _) = _
    simp only [enumMembersToJson, enumMemberToJson, numNormItems, deNumNormItems,
      Json.Value.numNorm, deNumNorm, deNumNorm_numNorm_enumValue v,
      deNumNorm_numNorm_enumMembers ms]

mutual

/-- The recovery is exact on the representation image of a well-formed
code: normalizing then de-normalizing is the identity. -/
theorem deNumNorm_numNorm_representation :
    ∀ (a : Ast), a.WF →
      deNumNorm (Json.Value.numNorm a.toRepresentationJson)
        = a.toRepresentationJson
  | .null, _ => rfl
  | .bool, _ => rfl
  | .str, _ => rfl
  | .int, _ => rfl
  | .lit .null, _ => rfl
  | .lit (.bool _), _ => rfl
  | .lit (.str _), _ => rfl
  | .ref _, _ => rfl
  | .lit (.int i), _ => by
    by_cases h : 0 ≤ i.val
    · show (Json.Value.obj _) = _
      simp only [Json.Value.numNorm, numNormFields, numNormItems, deNumNorm,
        deNumNormFields, deNumNormItems, if_pos h, reint, ite_self,
        Ast.toRepresentationJson, Json.Value.obj.injEq, List.cons.injEq,
        Prod.mk.injEq, if_true, and_true, true_and]
      exact congrArg Json.Value.int (Int.toNat_of_nonneg h)
    · show (Json.Value.obj _) = _
      simp only [Json.Value.numNorm, numNormFields, numNormItems, deNumNorm,
        deNumNormFields, deNumNormItems, if_neg h, reint, ite_self]
      rfl
  | .arr a, ha => by
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, numNormItems, deNumNorm,
      deNumNormFields, deNumNormItems, reint,
      deNumNorm_numNorm_representation a ha]
    rfl
  | .struct fs, ⟨_, hwf⟩ => by
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, deNumNorm,
      deNumNormFields, reint,
      deNumNorm_numNorm_fields fs hwf]
    rfl
  | .decl g p ps, ⟨hp, _, hps⟩ => by
    rw [deNumNorm_decl_payload hp]
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, deNumNorm,
      deNumNormFields, reint, deNumNorm_numNorm_params ps hps]
    rfl
  | .union ms _, ⟨_, hwf⟩ => by
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, deNumNorm,
      deNumNormFields, reint, deNumNorm_numNorm_members ms hwf]
    rfl
  | .enum ms, _ => by
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, deNumNorm,
      deNumNormFields, reint, deNumNorm_numNorm_enumMembers ms]
    rfl
  | .tuple e es r, ⟨he, hes, hr⟩ => by
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, numNormItems, deNumNorm,
      deNumNormFields, deNumNormItems, reint,
      deNumNorm_numNorm_element e he, deNumNorm_numNorm_elements es hes,
      deNumNorm_numNorm_rest r hr]
    rfl
  -- A reference's only payload is a STRING, which the number collapse
  -- never touches, so the recovery is the identity on the nose.
  | .reference _, _ => rfl
  | .susp a, ha => by
    show (Json.Value.obj _) = _
    simp only [Json.Value.numNorm, numNormFields, numNormItems, deNumNorm,
      deNumNormFields, deNumNormItems, reint,
      deNumNorm_numNorm_representation a ha]
    rfl

theorem deNumNorm_numNorm_element :
    ∀ (e : Bool × Ast), WFElement e →
      deNumNorm (Json.Value.numNorm (elementToRepresentationJson e))
        = elementToRepresentationJson e
  | (o, a), ha => by
    show (Json.Value.obj _) = _
    simp only [elementToRepresentationJson, Json.Value.numNorm, numNormFields,
      deNumNorm, deNumNormFields, reint, ite_self,
      deNumNorm_numNorm_representation a ha]
    rfl

theorem deNumNorm_numNorm_elements :
    ∀ (es : List (Bool × Ast)), WFElements es →
      deNumNormItems (numNormItems (elementsToRepresentationJson es))
        = elementsToRepresentationJson es
  | [], _ => rfl
  | e :: es, ⟨he, hes⟩ => by
    simp only [elementsToRepresentationJson, numNormItems, deNumNormItems,
      deNumNorm_numNorm_element e he, deNumNorm_numNorm_elements es hes]

theorem deNumNorm_numNorm_rest :
    ∀ (r : Option Ast), WFRest r →
      deNumNormItems (numNormItems (restToRepresentationJson r))
        = restToRepresentationJson r
  | none, _ => rfl
  | some a, ha => by
    simp only [restToRepresentationJson, numNormItems, deNumNormItems,
      deNumNorm_numNorm_representation a ha]

theorem deNumNorm_numNorm_fields :
    ∀ (fs : List (String × Bool × Ast)), WFFields fs →
      deNumNormItems (numNormItems (fieldsToRepresentationJson fs))
        = fieldsToRepresentationJson fs
  | [], _ => rfl
  | (n, o, a) :: fs, ⟨ha, hwf⟩ => by
    show (_ :: _) = _
    simp only [fieldsToRepresentationJson,
      Json.Value.numNorm, numNormFields, deNumNorm, deNumNormFields, reint,
      ite_self, deNumNorm_numNorm_representation a ha,
      deNumNorm_numNorm_fields fs hwf]
    rfl

theorem deNumNorm_numNorm_params :
    ∀ (ps : List Ast), WFParams ps →
      deNumNormItems (numNormItems (paramsToRepresentationJson ps))
        = paramsToRepresentationJson ps
  | [], _ => rfl
  | a :: as, ⟨ha, hwf⟩ => by
    simp only [paramsToRepresentationJson, numNormItems, deNumNormItems,
      deNumNorm_numNorm_representation a ha, deNumNorm_numNorm_params as hwf]

theorem deNumNorm_numNorm_members :
    ∀ (ms : List Ast), WFMembers ms →
      deNumNormItems (numNormItems (membersToRepresentationJson ms))
        = membersToRepresentationJson ms
  | [], _ => rfl
  | a :: as, ⟨ha, hwf⟩ => by
    simp only [membersToRepresentationJson, numNormItems, deNumNormItems,
      deNumNorm_numNorm_representation a ha, deNumNorm_numNorm_members as hwf]

end

/-- The recovery is exact on the whole envelope. The document's
`"references"` is the empty object and the envelope's `"revision"` is a
`Value.nat` under a key that is not `"value"`, so neither moves. -/
theorem deNumNorm_numNorm_envelope {a : Ast} (ha : a.WF) :
    deNumNorm (Json.Value.numNorm a.envelope) = a.envelope := by
  show (Json.Value.obj _) = _
  simp only [Ast.envelope, Ast.representationDocument, Json.Value.numNorm,
    numNormFields, deNumNorm, deNumNormFields, reint,
    deNumNorm_numNorm_representation a ha]
  rfl

/-- The `WF` premise of `payload_inj` is NOT decoration: without it the
statement is false. The two codes below are distinct — and distinct
after `repNorm`, which rewrites only type parameters on this arm — yet
they render to the same payload bytes, because the general declaration
code would otherwise be free to put a number under `"payload"` in
either spelling. The registry's payload discipline is what rules them
out. -/
theorem payload_inj_needs_wf :
    ∃ a b : Ast, a.payload = b.payload ∧ a.repNorm ≠ b.repNorm := by
  refine ⟨.decl .date (.nat 5) [], .decl .date (.int 5) [], ?_, ?_⟩
  · show Json.renderCompact _ = Json.renderCompact _
    rw [Json.renderCompact_eq_renderPlain _ (envelope_canonical _),
      Json.renderCompact_eq_renderPlain _ (envelope_canonical _),
      ← Json.renderPlain_numNorm
        (Ast.decl DeclarationId.General.date (DeclPayload.nat 5) []).envelope,
      ← Json.renderPlain_numNorm
        (Ast.decl DeclarationId.General.date (DeclPayload.int 5) []).envelope]
    exact congrArg Json.renderPlain rfl
  · intro h
    rw [Ast.repNorm_decl, Ast.repNorm_decl] at h
    injection h with _ hp _
    exact DeclPayload.noConfusion hp

/-! ## Injectivity of the envelope up to the number collapse -/

/-- The collapse identifies no two well-formed envelopes: equal
normalized envelopes are equal envelopes, hence equal normal codes. -/
theorem envelope_numNorm_inj {a b : Ast} (ha : a.WF) (hb : b.WF)
    (h : Json.Value.numNorm a.envelope = Json.Value.numNorm b.envelope) :
    a.repNorm = b.repNorm := by
  refine envelope_inj ?_
  have := congrArg deNumNorm h
  rwa [deNumNorm_numNorm_envelope ha, deNumNorm_numNorm_envelope hb] at this

/-! ## The payload law -/

/-- REVISION-1 PAYLOAD INJECTIVITY: for well-formed codes, equal
canonical payload bytes give equal normal codes. -/
theorem payload_inj {a b : Ast}
    (ha : a.WF) (hb : b.WF) (h : a.payload = b.payload) :
    a.repNorm = b.repNorm :=
  envelope_numNorm_inj ha hb
    (Json.renderPlain_injective _ _ (envelope_canonical a) (envelope_canonical b)
      (by rw [← payload_renderPlain a, ← payload_renderPlain b]; exact h))

/-- The `RepNormal` corollary: on the codes the decoder can produce,
equal payloads give equality on the nose — one payload, one code. -/
theorem payload_inj' {a b : Ast}
    (ha : a.WF) (hb : b.WF) (hna : a.RepNormal) (hnb : b.RepNormal)
    (h : a.payload = b.payload) : a = b := by
  have := payload_inj ha hb h
  rwa [hna, hnb] at this

/-- The same law at the bytes the schema node actually carries. -/
theorem payloadBytes_inj {a b : Ast}
    (ha : a.WF) (hb : b.WF) (h : a.payloadBytes = b.payloadBytes) :
    a.repNorm = b.repNorm :=
  payload_inj ha hb (String.toByteArray_inj.mp h)

/-- The door's own left inverse, at the bytes: a well-formed code's
canonical payload parses and ingests back to that code's revision-1
normal form. The read half of the loop, end to end. -/
theorem payload_parse {a : Ast} :
    Json.parse a.payload = some a.envelope.numNorm :=
  Json.parse_render (envelope_canonical a)

end Cas.Schema
