import Test.Codegen.DataCodec
import Effect4.Laws.Program.Typed.AnswerSchema
import ProofGraph.Proof

/-! Independent pre-refactor boundary policies and prepared-codec controls.
Placement: OPERATIONAL-PLAN.md, concrete prepared JSON codec.
Concept: exact-codecs. Consumers: decode-encode, decode-iff, record-codec-layout; R2/R3.
The universal comparisons include refusals. Finite controls do not certify an outside host.
No performance claim follows from these checks. -/
set_option autoImplicit false
namespace MathTransferProbe.PreparedCodec
open Effect4 Effect4.Program Effect4.Machine

-- Frozen bodies from b459daec, independent of the new delegation.
def oldEncode (t : Ty) (v : Val) : Option Json :=
  let t := t.normalize
  if Val.hasTy v t then
    match Schema.Codec.encodeRaw (Schema.Codec.layout t) v with
    | none => none
    | some j => if Schema.Codec.decodeRaw (Schema.Codec.layout t) j = some v then some j else none
  else none

def oldDecode (t : Ty) (j : Json) : Option Val :=
  let t := t.normalize
  (Schema.Codec.decodeRaw (Schema.Codec.layout t) j).filter (fun v => Val.hasTy v t)

def oldIsValue (t : Ty) (v : Val) : Bool :=
  let t := t.normalize
  match Schema.Codec.encodeRaw (Schema.Codec.layout t) v with
  | none => false
  | some j => Val.hasTy v t && decide (Schema.Codec.decodeRaw (Schema.Codec.layout t) j = some v)

/-- Reader of the source-bound encoding connector at the independent old policy. -/
theorem encode_old {source : Ty} (prepared : Schema.Codec.Prepared source) (v : Val) :
    prepared.encode v = oldEncode source v := by
  rw [Schema.Codec.Prepared.encode_agrees]
  exact Schema.encode_policy source v

/-- Reader of the source-bound decoding connector at the independent old policy. -/
theorem decode_old {source : Ty} (prepared : Schema.Codec.Prepared source) (j : Json) :
    prepared.decode j = oldDecode source j := by
  rw [Schema.Codec.Prepared.decode_agrees]
  exact Schema.decode_policy source j

/-- Reader of the source-bound admission connector at the independent encode-first old policy. -/
theorem isValue_old {source : Ty} (prepared : Schema.Codec.Prepared source) (v : Val) :
    prepared.isValue v = oldIsValue source v := by
  rw [Schema.Codec.Prepared.isValue_agrees]
  exact Schema.Codec.isValue_policy source v

-- Dropping either boundary guard admits a wrong result.
#guard Schema.Codec.decodeRaw (Schema.Codec.layout (.lit "Ada")) (.str "Grace") = some (.str "Grace")
#guard (Schema.Codec.prepare (.lit "Ada")).decode (.str "Grace") = none
#guard Schema.Codec.encodeRaw (Schema.Codec.layout Effect4.Test.DataCodec.objectUnion)
  (Map.write [("x", .nat 7)]) = some (.obj [("x", Arch.Json.ofNat 7)])
#guard (Schema.Codec.prepare Effect4.Test.DataCodec.objectUnion).encode (Map.write [("x", .nat 7)]) = none

-- Source binding rules out a different normal form or a different interpreter's source.
#guard !decide ((Ty.lit "Ada").normalize = Ty.string.normalize)
#guard !decide ((Ty.tuple [.nat, .bool]).normalize = (Ty.tuple [.bool, .nat]).normalize)

-- One prepared interpreter supports repeated operations on a noncanonical source.
def spelling : Ty := .union .nat .never
#guard (Schema.Codec.prepare spelling).encode (.nat 7) = oldEncode spelling (.nat 7)
#guard (Schema.Codec.prepare spelling).decode (Arch.Json.ofNat 7) = oldDecode spelling (Arch.Json.ofNat 7)
#guard (Schema.Codec.prepare spelling).isValue (.nat 7) = oldIsValue spelling (.nat 7)

-- Audit every declaration introduced by this slice in both production modules and this file.
run_elab do
  let env ← Lean.getEnv
  let prefixes := [``Effect4.Schema.Codec.Prepared, "MathTransferProbe.PreparedCodec".toName]
  let exact := [``Effect4.Schema.Codec.prepare, ``Effect4.Schema.Codec.isValue,
    ``Effect4.Schema.encode, ``Effect4.Schema.decode, ``Effect4.Schema.Codec.isValue_policy,
    ``Effect4.Schema.encode_policy, ``Effect4.Schema.decode_policy,
    ``Effect4.Test.DataCodec.preparedPerson, ``Effect4.Schema.decode_of_encode,
    ``Effect4.Schema.encode_of_decode, ``Effect4.Schema.decode_iff,
    ``Effect4.Program.Typed.hasTy_of_decode]
  let modules := ["Effect4.Schema.Codec".toName, "Effect4.Laws.Schema.Codec".toName,
    "Test.Codegen.DataCodec".toName]
  let moduleNames := env.header.moduleNames
  let roots := env.constants.toList.filterMap fun (name, _) =>
    let owner := (env.getModuleIdxFor? name).bind fun index => moduleNames[index]?
    if prefixes.any (·.isPrefixOf name) || exact.contains name ||
        owner.any (modules.contains ·) then some name else none
  let (answers, _) := ProofGraph.reachedAxiomsMany env roots.toArray {}
  for (name, answer) in roots.toArray.zip answers do
    let some axioms := answer | throwError "axiom walk exhausted for {name}"
    for axiomName in axioms do
      unless [``propext, ``Quot.sound].contains axiomName do
        throwError "{name} reaches forbidden axiom {axiomName}"
    Lean.logInfo m!"{name} exact axioms: {axioms}"
  Lean.logInfo m!"prepared-codec exact axiom audit passed for {roots.length} declarations"

end MathTransferProbe.PreparedCodec
