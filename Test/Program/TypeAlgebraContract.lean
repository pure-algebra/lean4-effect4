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
#guard (Ty.prod raw raw).normalize =
  .union (.prod .nat .nat) (.union (.prod .nat .bool) (.union (.prod .bool .nat) (.prod .bool .bool)))
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

-- P2a: the exact 37-type universe of Seat A's retained p6.lean, normalized at entry.
private def scoutBase : List Ty :=
  [.never, .unit, .nat, .int, .string, .bool, .lit "A", .lit "B", .handle "H"]

private def scoutUniverse : List Ty :=
  scoutBase ++ scoutBase.map Ty.option ++ scoutBase.map Ty.list ++
    [.prod (.lit "A") .string, .prod .string .string,
      .union (.lit "A") (.lit "B"), .union (.lit "A") .string,
      .union .string (.lit "A"), .union .nat .string,
      .causeOf (.lit "A"), .causeOf .string,
      .exitOf .nat (.lit "A"), .exitOf .nat .string]

private def canonicalUniverse : List Ty := scoutUniverse.map Ty.normalize

#guard scoutUniverse.length == 37
#guard (canonicalUniverse.flatMap fun a => canonicalUniverse.filter fun b =>
  Ty.sub a b && Ty.sub b a && a != b).length == 0
#guard (canonicalUniverse.flatMap fun a => canonicalUniverse.filter fun b =>
  Ty.sub a b && Ty.join a b != b).length == 0
#guard Ty.join (.lit "A") .string = .string
#guard Ty.join (.prod (.lit "A") .string) (.prod .string .string) = .prod .string .string
#guard (Ty.prod (.union (.lit "A") (.lit "B")) .string).normalize =
  .union (.prod (.lit "A") .string) (.prod (.lit "B") .string)
#guard (Ty.prod .string (.union (.lit "A") (.lit "B"))).normalize =
  .union (.prod .string (.lit "A")) (.prod .string (.lit "B"))
#guard (Ty.list (.union .nat .string)).normalize = .list (.union .nat .string)
#guard (Ty.prod .never .string).normalize = .prod .never .string

-- Generic filtering preserves order and equivalent maximal occurrences.
#guard Effect4.Row.antichain (fun x y : Nat => decide (x ≤ y)) [] == []
#guard Effect4.Row.antichain (fun x y : Nat => decide (x ≤ y)) [3, 1, 3, 2] == [3, 3]
#guard Effect4.Row.antichain (fun x y : Nat => decide (x / 2 ≤ y / 2)) [0, 1, 2, 3] == [2, 3]
#guard Effect4.Row.antichain (fun x y : Nat => y % x == 0) [6, 1, 4, 2, 3] == [6, 4]
#guard Effect4.Row.antichain (fun _ _ : Nat => false) [2, 1, 2] == [2, 1, 2]
#guard Effect4.Row.antichain (fun x y : Nat => (x + 1) % 3 == y) [0, 1, 2] == []

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


/-! Public order, identity key and printed boundaries use the canonical type. -/
#guard CTy.ofRaw (.lit "A") ≤ CTy.ofRaw .string
#guard ¬ CTy.ofRaw .string ≤ CTy.ofRaw (.lit "A")
#guard CTy.ofRaw (.lit "A") < CTy.ofRaw .string
#guard CTy.key (CTy.ofRaw (.union (.lit "A") .string)) = CTy.key (CTy.ofRaw .string)
#guard Ty.key (.union (.lit "A") .string) != Ty.key .string
#guard Ty.render (.union (.lit "A") .string) = "string"
#guard Ty.render (.prod (.union (.lit "A") (.lit "B")) .string) =
  "readonly [\"A\", string] | readonly [\"B\", string]"
#guard Ty.render (.list (.union .nat .string)) = "ReadonlyArray<number | string>"

example : Std.IsPartialOrder CTy := inferInstance
example : Std.LawfulOrderSup CTy := inferInstance
example (a b : CTy) : a ≤ max a b := Ty.sub_join_left a b
example (a b c : CTy) (ha : a ≤ c) (hb : b ≤ c) : max a b ≤ c :=
  Ty.join_least a b c ha hb
example (a b : Ty) (h : Ty.sub a b = true) : Ty.sub a.normalize b.normalize = true :=
  Ty.sub_normalize_of_sub a b h
