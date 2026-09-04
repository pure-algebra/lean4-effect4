import Effect4.Codegen.Rule

/-!
# Codegen.Emit — the emitter, keyed by its rule

Design: `docs/research/2026-09-04-codegen-api-design.md` §3.3.

```lean
class Emit (r : Rule) where
  emit : r.Input → Except Refusal r.target.Syntax
```

One instance per rule, and the instance is the emitter. `emit r x` is the one call: it
answers the rule's artefact (syntax, never text) or the first refusal by name. The refusal
is either the carrier's own (an emitter never emits a carrier its `check` refuses, and it
answers that refusal unwrapped, so a caller reads `keyNotRequired "User" "email"` rather
than "emit failed") or one of the emitter group appended to `Surface/Refusal.lean`:
`refusedShape r.id shape site` for a shape in `r.refuses`, and the module-level clauses.

`Refusal.at` is how a sub-spelling's refusal (`Codegen.Spell` answers under the rule id
`"schema.constructor"` with no site) acquires the rule and the site of the emitter that
asked, so every refusal a caller sees names the rule it came from and the slot it was found
in.
-/

set_option autoImplicit false

namespace Effect4.Codegen

open Effect4 Effect4.Surface

/-- The emitter of a rule. -/
class Emit (r : Rule) where
  /-- The rule's artefact as syntax, or the first refusal by name. -/
  emit : r.Input → Except Refusal r.target.Syntax

/-- The one call: the artefact of a rule, or the first refusal by name. -/
def emit (r : Rule) [Emit r] (x : r.Input) : Except Refusal Artefact :=
  (Emit.emit x).map (Artefact.of r.target)

/-- `emit` answers in the rule's target. -/
theorem emit_target (r : Rule) [Emit r] (x : r.Input) (artefact : Artefact)
    (h : emit r x = .ok artefact) : artefact.target = r.target := by
  unfold emit at h
  revert h
  cases Emit.emit (r := r) x with
  | error refusal => intro h; simp only [Except.map] at h; exact absurd h (by simp)
  | ok content =>
    intro h
    simp only [Except.map] at h
    injection h with h
    rw [← h]
    exact Artefact.target_of r.target content

/-- Give a sub-spelling's refusal the rule and the site of the emitter that asked. Only
`refusedShape` is re-addressed; every other refusal is the carrier's own and is left as it
came. -/
def Refusal.at (rule site : String) : Refusal → Refusal
  | .refusedShape _ shape _ => .refusedShape rule shape site
  | other => other

/-- `Except.mapError`, spelled out because core's `Except` has no such combinator. -/
def mapRefusal {α : Type} (f : Refusal → Refusal) : Except Refusal α → Except Refusal α
  | .ok value => .ok value
  | .error refusal => .error (f refusal)

/-- An emitter's refusal, addressed. -/
def addressed {α : Type} (rule site : String) : Except Refusal α → Except Refusal α :=
  mapRefusal (Refusal.at rule site)

/-- Collect a list of answers, first refusal wins. -/
def collect {α : Type} : List (Except Refusal α) → Except Refusal (List α)
  | [] => .ok []
  | first :: rest =>
    match first, collect rest with
    | .ok head, .ok tail => .ok (head :: tail)
    | .error refusal, _ => .error refusal
    | _, .error refusal => .error refusal

/-- Map an emitting step over a list, first refusal wins. -/
def traverse {α β : Type} (f : α → Except Refusal β) (items : List α) : Except Refusal (List β) :=
  collect (items.map f)

/-- `collect` of successes is the list of their values. -/
theorem collect_ok {α : Type} :
    ∀ values : List α, collect (values.map (Except.ok : α → Except Refusal α)) = .ok values
  | [] => rfl
  | value :: rest => by simp [collect, collect_ok rest]

/-- The refusal an answer carries, when it is one. A battery pins an emitted module by its
refusal or by its rendered parts, never by `==` on syntax the target package gives no
equality for. -/
def refusal? {α : Type} : Except Refusal α → Option Refusal
  | .error refusal => some refusal
  | .ok _ => none

/-- The optional-slot lift: an absent slot is not a refusal. -/
def optional {α β : Type} (f : α → Except Refusal β) : Option α → Except Refusal (Option β)
  | none => .ok none
  | some value => (f value).map some

/-! ## Anti-vacuity -/

#guard (Refusal.at "surface.api.httpApi" "getUser.params"
    (.refusedShape "schema.constructor" "schema.suspend" "")) ==
  Refusal.refusedShape "surface.api.httpApi" "schema.suspend" "getUser.params"
#guard (Refusal.at "surface.api.httpApi" "getUser" (.keyEmpty "User")) == Refusal.keyEmpty "User"
#guard (collect [(.ok 1 : Except Refusal Nat), .ok 2]) == .ok [1, 2]
#guard (collect [(.ok 1 : Except Refusal Nat), .error (.keyEmpty "User"), .error (.keyEmpty "X")]) ==
  .error (.keyEmpty "User")
#guard (optional (fun (n : Nat) => (.ok (n + 1) : Except Refusal Nat)) none) == .ok none
#guard (optional (fun (n : Nat) => (.ok (n + 1) : Except Refusal Nat)) (some 1)) == .ok (some 2)

end Effect4.Codegen
