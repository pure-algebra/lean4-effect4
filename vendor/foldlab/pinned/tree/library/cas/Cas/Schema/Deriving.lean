import Cas.Schema.Deriving.Handler

/-!
# Schema deriving

Opt-in compiler seam registering `deriving Described` for supported
native Lean structures. Runtime consumers can import
`Cas.Schema.Described` without importing Lean's elaborator.
-/
