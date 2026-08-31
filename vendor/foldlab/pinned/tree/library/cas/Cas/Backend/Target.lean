import Cas.Schema.Foreign

/-!
# The target semantics, L1 — the first five, by hand

The Effect surface forms the backend compiles into, as typed data over
the TypeScript type-expression fragment. Substance carries the full
type arguments; rendering elides trailing `never`s, which is the
pinned v4 idiom — every `example` below is `rfl`-pinned against a
verbatim type expression from the pinned effects sources, so this
module cannot drift from the target without going red.

These five are hand-written on purpose (EFFECTS-BACKEND R8): they are
the seed the mechanical surface ingestion is judged against. Every
further row of the target table arrives generated from the pinned
Effect surface through the extract→generate machinery, never by hand.
-/

namespace Cas.Backend

open Cas.Schema.Foreign.TypeScript

private def isNever : TypeExpr → Bool
  | .never => true
  | _ => false

/-- Keep arguments up to the last non-`never` — the v4 elision rule:
`Effect.Effect<A>` means `Effect.Effect<A, never, never>`. -/
private def elideTrailingNever (args : List TypeExpr) : List TypeExpr :=
  (args.reverse.dropWhile isNever).reverse

/-- `Effect.Effect<A, E, R>`. -/
structure EffectType where
  success : TypeExpr
  error : TypeExpr := .never
  services : TypeExpr := .never

def EffectType.lower (t : EffectType) : TypeExpr :=
  .apply ⟨["Effect", "Effect"], by simp⟩
    (t.success :: elideTrailingNever [t.error, t.services])

/-- `Layer.Layer<ROut, E, RIn>`. -/
structure LayerType where
  provides : TypeExpr
  error : TypeExpr := .never
  requires : TypeExpr := .never

def LayerType.lower (t : LayerType) : TypeExpr :=
  .apply ⟨["Layer", "Layer"], by simp⟩
    (t.provides :: elideTrailingNever [t.error, t.requires])

/-- `Schema.Codec<T, E, RD, RE>` (`Foreign.EffectSchemaRef` names codec
VALUES; this is the codec TYPE form). -/
structure CodecType where
  decoded : TypeExpr
  encoded : TypeExpr
  decodingServices : TypeExpr := .never
  encodingServices : TypeExpr := .never

def CodecType.lower (t : CodecType) : TypeExpr :=
  .apply ⟨["Schema", "Codec"], by simp⟩
    (t.decoded :: t.encoded ::
      elideTrailingNever [t.decodingServices, t.encodingServices])

/-- `Schema.Top` — the top of the codec lattice, the type generated
combinator positions carry. -/
def schemaTop : TypeExpr := .named ⟨["Schema", "Top"], by simp⟩

/-- `Option.Option<A>`. -/
def optionType (a : TypeExpr) : TypeExpr :=
  .apply ⟨["Option", "Option"], by simp⟩ [a]

/-- One operation of a service shape: named parameters answering an
Effect — the signature arrow (`Sig.Op`/`Sig.Ans` on the target side). -/
structure OperationSig where
  name : String
  params : List (String × TypeExpr)
  returns : EffectType

def OperationSig.lower (o : OperationSig) : TypeExpr :=
  .func o.params o.returns.lower

/-! ## The pins — verbatim type expressions from the pinned sources -/

private def ty (name : String) : TypeExpr := .named ⟨[name], by simp⟩

/-- `src/cas/Store.ts:60` — `load`'s type. -/
example :
    (OperationSig.lower
      { name := "load"
        params := [("id", ty "ContentId")]
        returns := { success := ty "CasNodeInput", error := ty "CasError" } }).render
    = "(id: ContentId) => Effect.Effect<CasNodeInput, CasError>" := rfl

/-- `src/cas/Store.ts:86` — the address digest's answer. -/
example :
    (EffectType.lower
      { success := ty "ContentId", error := ty "StoreFailure" }).render
    = "Effect.Effect<ContentId, StoreFailure>" := rfl

/-- Full-triple form: no elision when services are present. -/
example :
    (EffectType.lower
      { success := ty "ContentId", services := ty "CasStore" }).render
    = "Effect.Effect<ContentId, never, CasStore>" := rfl

/-- `src/cas/Backend.ts:137` — the memory backend's layer. -/
example :
    (LayerType.lower
      { provides := .union [ty "ByteReader", ty "ByteWriter", ty "RootStore"] }).render
    = "Layer.Layer<ByteReader | ByteWriter | RootStore>" := rfl

/-- `src/cas/Blob.ts:480` — a layer with requirements: the middle
`never` stays. -/
example :
    (LayerType.lower
      { provides := ty "Service", requires := ty "CasStore" }).render
    = "Layer.Layer<Service, never, CasStore>" := rfl

/-- `src/cas/CanonicalSchema.ts` — the AST codec's type. -/
example :
    (CodecType.lower { decoded := ty "Ast", encoded := ty "Ast" }).render
    = "Schema.Codec<Ast, Ast>" := rfl

/-- `Schema.Top` and `Option.Option` render as named. -/
example : schemaTop.render = "Schema.Top" := rfl
example : (optionType (ty "Ast")).render = "Option.Option<Ast>" := rfl

end Cas.Backend
