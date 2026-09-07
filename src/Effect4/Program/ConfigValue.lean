import Effect4.Store.Image
import Effect4.Program.Config

/-!
# Program.ConfigValue — the configuration reader's values as a view of the shared carrier

Owner: the exact image, in `Effect4.Store.Val`, of `Config.Val` (`Program/Config.lean` §4), the
values a `Config` term resolves to. `Config.Val` is a literal sub-alphabet of the carrier —
`str`, `nat`, `bool`, `pair`, `none`, `some` — so the writer is the identity on the spelling
and the reader is the *admission*: it accepts exactly those six frames and refuses `unit`,
`bytes`, `list`, `ctor`, `ref` and `handle`. That refusal is the point (wave 2 §5, U0 item 2:
"Config must retain its accepted result shapes rather than silently accepting every
Store.Val"); U1 may replace the inductive with the carrier plus this admission, never with
the carrier alone.

`Resolution`, `Failure` and `Outcome` keep their records; only the value they carry shares
the encoding.
-/

set_option autoImplicit false

namespace Effect4.Program.Config

open Effect4.Store (Image)

namespace Val

/-- The identity on the spelling. -/
def toStore : Val → Store.Val
  | .str s => .str s
  | .nat n => .nat n
  | .bool b => .bool b
  | .pair a b => .pair (toStore a) (toStore b)
  | .none => .none
  | .some v => .some (toStore v)

/-- The admission: the six configuration frames, and nothing else. -/
def ofStore : Store.Val → Option Val
  | .str s => Option.some (.str s)
  | .nat n => Option.some (.nat n)
  | .bool b => Option.some (.bool b)
  | .pair a b =>
    match ofStore a, ofStore b with
    | Option.some x, Option.some y => Option.some (.pair x y)
    | _, _ => Option.none
  | .none => Option.some .none
  | .some v => (ofStore v).map .some
  | _ => Option.none

theorem ofStore_toStore : ∀ v : Val, ofStore (toStore v) = Option.some v
  | .str _ => rfl
  | .nat _ => rfl
  | .bool _ => rfl
  | .pair a b => by
    show (match ofStore (toStore a), ofStore (toStore b) with
      | Option.some x, Option.some y => Option.some (Val.pair x y)
      | _, _ => Option.none) = Option.some (.pair a b)
    rw [ofStore_toStore a, ofStore_toStore b]
  | .none => rfl
  | .some v => by
    show (ofStore (toStore v)).map Val.some = Option.some (.some v)
    rw [ofStore_toStore v, Option.map_some]

theorem ofStore_exact : ∀ (w : Store.Val) (v : Val), ofStore w = Option.some v → w = toStore v := by
  intro w
  induction w using Store.Val.ind with
  | unit => intro v h; exact nomatch h
  | bool b =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | nat n =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | str s =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | bytes bs => intro v h; exact nomatch h
  | list xs _ => intro v h; exact nomatch h
  | pair a b iha ihb =>
    intro v h
    simp only [ofStore] at h
    split at h
    · next x y hx hy =>
      injection h with h
      subst h
      show Store.Val.pair a b = Store.Val.pair (toStore x) (toStore y)
      rw [iha x hx, ihb y hy]
    · exact nomatch h
  | none =>
    intro v h
    simp only [ofStore] at h
    cases h
    rfl
  | some a ih =>
    intro v h
    simp only [ofStore] at h
    obtain ⟨x, hx, hj⟩ := Option.map_eq_some_iff.mp h
    subst hj
    show Store.Val.some a = Store.Val.some (toStore x)
    rw [ih x hx]
  | ctor i args _ => intro v h; exact nomatch h
  | ref k d => intro v h; exact nomatch h
  | handle k n => intro v h; exact nomatch h

/-- The configuration values as an exact image of the shared carrier. -/
def image : Image Val := ⟨toStore, ofStore, ofStore_toStore, fun h => ofStore_exact _ _ h⟩

/-- No configuration value carries a handle. -/
theorem toStore_handles : ∀ v : Val, (toStore v).handles = []
  | .str _ => rfl
  | .nat _ => rfl
  | .bool _ => rfl
  | .pair a b => by
    show (Store.Val.pair (toStore a) (toStore b)).handles = []
    rw [Store.Val.handles, toStore_handles a, toStore_handles b]
    rfl
  | .none => rfl
  | .some a => by
    show (Store.Val.some (toStore a)).handles = []
    rw [Store.Val.handles, toStore_handles a]

theorem image_handleFree : Image.HandleFree image := toStore_handles

end Val

/-! ## Receipts -/

#guard Val.toStore (.pair (.str "localhost") (.some (.nat 5432))) =
  .pair (.str "localhost") (.some (.nat 5432))
#guard Val.ofStore (.pair (.str "localhost") (.some (.nat 5432))) =
  Option.some (.pair (.str "localhost") (.some (.nat 5432)))
#guard Val.ofStore .unit = Option.none
#guard Val.ofStore (.list []) = Option.none
#guard Val.ofStore (.ctor 0 []) = Option.none
#guard Val.ofStore (.bytes []) = Option.none
#guard Val.ofStore (.handle 2 1) = Option.none
#guard Val.ofStore (.pair (.str "a") (.list [])) = Option.none
#guard Val.ofStore (.some (.ctor 0 [.nat 1])) = Option.none

#print axioms Val.image
#print axioms Val.image_handleFree

end Effect4.Program.Config
