import Cas.Digits
import Cas.Utf8
import Cas.Val
import Cas.Digest
import Cas.Kind
import Cas.Shape
import Cas.Canonical
import Cas.Templates
import Cas.Derived.Json
import Cas.Derived.Program
import Cas.Derived.Schema
import Cas.Genesis
import Cas.Program
import Cas.Node
import Cas.Store
import Cas.Word
import Cas.Traits
import Cas.Probe

/-!
# Cas

The CAS-trait spike (`docs/research/2026-09-04-cas-trait-plan.md` §8, step 1): the store
substrate rewritten in namespace `Effect4.Store` under `workshop/Cas`, importing nothing from
the old `src/Effect4/Store`. This root imports every module of the library; `lake build Cas`
is the gate.
-/
