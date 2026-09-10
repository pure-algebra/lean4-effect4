import Effect4.Laws.Program.TypeAlgebra
import Test.Data.DataContract

/-! DI-53: deep canonicalization, exact membership and deliberate admission deltas.
These finite controls supplement the universal laws; they do not prove host conformance. -/

open Effect4 Effect4.Machine Effect4.Program

namespace Test.Program.TypeAlgebraContract

private def raw : Ty := .union .bool (.union .never (.union .nat .bool))
private def canon : Ty := .union .nat .bool

#guard raw.normalize = canon
#guard (Ty.option raw).normalize = .option canon
#guard (Ty.list raw).normalize = .list canon
#guard (Ty.prod raw raw).normalize = .prod canon canon
#guard (Ty.except raw raw).normalize = .except canon canon
#guard (Ty.exitOf raw raw).normalize = .exitOf canon canon
#guard (Ty.causeOf raw).normalize = .causeOf canon
#guard (Ty.fiberOf raw raw).normalize = .fiberOf canon canon
#guard (Ty.union (.handle "é") (.handle "A")).normalize = .union (.handle "A") (.handle "é")
#guard (Ty.union (.handle "A") (.handle "é")).normalize = .union (.handle "A") (.handle "é")
#guard (Ty.union .never .never).normalize = .never
#guard (Ty.union (.option raw) (.option canon)).normalize = .option canon
#guard Ty.join raw raw = canon
#guard CTy.toRaw (CTy.join (CTy.ofRaw raw) (CTy.ofRaw raw)) = canon
#guard (Ty.union .nat .int).normalize != .nat
#guard (Ty.fiberOf .nat .nat).normalize != (Ty.fiberOf .bool .string).normalize

-- The old 13-guard snapshot falsifier is retained in research. These are the new outcomes.
#guard Val.hasTy (Val.fibers [⟨0⟩]) (.list (.union (.fiberOf .nat .nat) .never))
#guard Val.hasTy (Val.fibers [⟨0⟩]) (.list (.union (.fiberOf .nat .nat) .nat))
#guard Val.hasTy (Val.fibers [⟨0⟩]) (.list (.fiberOf .nat .nat))
#guard !Val.hasTy (Val.fibers [⟨0⟩]) (.list .nat)
#guard !Val.hasTy (Val.fibers [⟨0⟩]) (.list .never)
#guard !Val.hasTy (Val.fibers [⟨0⟩]) (.list .int)
#guard Val.hasTy (Val.fibers []) (.list .nat)
#guard Val.hasTy (Val.fibers []) (.list .never)
#guard Val.hasTy (Val.fibers []) (.list .int)
#guard Val.hasTy (Val.fibers []) (.list (.fiberOf .nat .nat))
#guard !Val.hasTy (Value.fiberSnapshot (.list [.nat 0])) (.list (.fiberOf .nat .nat))
#guard !Val.hasTy (Value.fiberSnapshot (.list [.nat 0])) (.list .never)

-- Cause and failed-exit membership follow the normalized error column, including allocations.
#guard Val.hasTy (Val.exitErr (Cause.fail (.text "lost")))
  (.causeOf (.union .string .never)) ["Resource"]
#guard Val.hasTy (Val.exitErr (Cause.fail (.text "lost")))
  (.exitOf raw (.union .string .never)) ["Resource"]
#guard !Val.hasTy (Val.exitErr (Cause.fail (.tag 4)))
  (.exitOf raw (.union .string .never)) ["Resource"]
#guard Val.hasTy (Value.external 0)
  (.union (.handle "Resource") .never) ["Resource"]
#guard !Val.hasTy (Value.external 0)
  (.union (.handle "Resource") .never) []

-- Normalization at both row comparisons preserves domain, shape and request refusals.
#guard (effTy nativeSignature [.union .nat .never] (.perform .refMake (.var 0))).isSome
#guard (effTy nativeSignature [.union NativeOp.deferredTy .never]
  (.callback .deferredAwait (.var 0))).isSome
#guard (effTy nativeSignature [.union .bool .never] (.perform .refMake (.var 0))).isNone
#guard (effTy nativeSignature [.union .nat .never] (.callback .deferredAwait (.var 0))).isNone
#guard (effTy nativeSignature [.nat] (.callback .refMake (.var 0))).isNone
#guard (effTy nativeSignature [.never] (.perform (.external 999) (.var 0))).isNone

#guard (effTy nativeSignature [.union Ty.scope .never]
  (.provideService nativeScopeKey (.var 0) (.service nativeScopeKey))).isSome

private def hiddenPair : Ty := .prod (.union .string .never) .string
#guard !supportedErrTy hiddenPair
#guard admittedErrTy hiddenPair
#guard (effTy nativeSignature [hiddenPair] (.fail (.var 0))).isSome
#guard (effTy nativeSignature [hiddenPair] (.yieldError (.var 0))).isSome
#guard (effTy nativeSignature [hiddenPair] (.failCause (.fail (.var 0)))).isSome
#guard (effTy nativeSignature [.prod (.union .string .bool) .string] (.fail (.var 0))).isNone

#check Ty.normalize_idem
#check hasTy_normalize
#check hasTy_fibers
#check hasTy_fibers_nil
#check Ty.join_self
#check Ty.join_never
#check Ty.join_comm
#check Ty.join_assoc
#check CTy.join_self
#check CTy.join_never

end Test.Program.TypeAlgebraContract
