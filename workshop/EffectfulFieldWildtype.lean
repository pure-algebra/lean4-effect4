import Effect4.Algebra.Program
import Effect4.Schema.Annotations

/-!
# Effectful-field feasibility probe

This workshop file deliberately introduces no carrier.  An effectful optic is
the existing pure `Lens` composed with the existing semantic `Program`; the
field marker is an existing `AnnotationKey Json`.  Canonical generated content
must later lower the JSON payload to existing `ServiceKey` / `OperationId`
identities and a checked `RawFlow`, not retain the functions below.
-/

namespace Effect4.Workshop.EffectfulField

universe uOp uAns

/-- The persisted marker uses the already-owned annotation and JSON carriers. -/
def annotation : AnnotationKey Json where
  name := "effect4/field-effect"
  encode := id
  decode := some

theorem annotation_lawful : annotation.Lawful := by
  constructor
  · intro value
    rfl
  · intro raw value decoded
    exact (Option.some.inj decoded).symm

/-- Raw same-name multiplicity is observable before typed decoding. -/
def rawSpecs (annotations : Annotations) : List Json :=
  (Annotations.payloadsAt annotation.name).collect annotations

/-- Generation admits exactly one marker at a field site. -/
def ExactlyOne (annotations : Annotations) : Prop :=
  (rawSpecs annotations).length = 1

instance (annotations : Annotations) : Decidable (ExactlyOne annotations) :=
  inferInstanceAs (Decidable ((rawSpecs annotations).length = 1))

def readPayload : Json := .obj [("version", .str "1"), ("operation", .str "readEmail")]
def writePayload : Json := .obj [("version", .str "1"), ("operation", .str "writeEmail")]

example : ExactlyOne (annotation.singleton readPayload) := by decide

/-- Duplicate same-name entries stay visible and are refused, rather than
being collapsed by a map or hidden by successful typed decoding. -/
example : ¬ ExactlyOne
    (some [annotation.entry readPayload, annotation.entry writePayload]) := by
  decide

variable {Sig : Signature.{uOp, uAns}} {S A : Type uAns}

/-- Lift one existing total lens into the existing semantic program carrier. -/
def getM (optic : Lens S A) (read : A → Program Sig A) (source : S) :
    Program Sig A :=
  read (optic.get source)

/-- Effectfully choose a replacement, then rebuild through the existing lens. -/
def replaceM (optic : Lens S A) (write : A → Program Sig A)
    (value : A) (source : S) : Program Sig S := do
  let accepted ← write value
  pure (optic.replace accepted source)

/-- Sequential read/modify/write is ordinary `Program.bind`; no effectful
optic hierarchy or second program carrier is needed. -/
def modifyM (optic : Lens S A)
    (read : A → Program Sig A) (write : A → Program Sig A)
    (f : A → A) (source : S) : Program Sig S := do
  let current ← getM optic read source
  replaceM optic write (f current) source

/-- The effectful combinator conservatively extends the pure lens operation. -/
theorem replaceM_pure (optic : Lens S A) (value : A) (source : S) :
    replaceM (Sig := Sig) optic
        (fun candidate => Program.pure (signature := Sig) candidate)
        value source =
      Program.pure (signature := Sig) (optic.replace value source) :=
  rfl

/-- With pure read and write legs, sequential modification is the existing
pure `Lens.modify`. -/
theorem modifyM_pure (optic : Lens S A) (f : A → A) (source : S) :
    modifyM (Sig := Sig) optic
        (fun value => Program.pure (signature := Sig) value)
        (fun value => Program.pure (signature := Sig) value) f source =
      Program.pure (signature := Sig) (optic.modify f source) :=
  rfl

end Effect4.Workshop.EffectfulField
