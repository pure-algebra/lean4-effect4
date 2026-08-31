import Cas.Schema.Codec.Laws

/-!
# Canonical schema codec

Public facade for the schema codec:

- `Codec.Scalars` owns canonical scalar representations;
- `Codec.References` owns the typed-reference sentinel;
- `Codec.Core` owns the mutually recursive encoder and decoder;
- `Codec.Laws` owns round-trip, image-exactness, and injectivity laws.

Compiler metaprogramming belongs at a separate deriving seam; importing
this runtime codec does not pull in `Lean.Elab.Deriving`.
-/

