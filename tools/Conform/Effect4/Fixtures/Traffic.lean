import Conform.Lcnf.Cases

/-!
# Conform.Effect4.Fixtures.Traffic — the deliberately broken input

**What it is.** A four-constructor family and three functions over it, kept in the tree so that
every arm of `Conform.Lcnf.Cases`'s policy check can be *shown* to go red rather than asserted to.
The functions are what the checks are aimed at, not examples of good code:

* `Light.label` has a default arm absorbing `amber` and `off` — the shape of `Ty.render`'s
  `| .nat | .int => "number"`. The fixture policy `Fixtures/exhaustive-policy.json` declares it
  **exhaustive**, so the check must refuse it.
* `Light.isGo` has an arm for every constructor and no default. The fixture policy
  `Fixtures/stale-cover-policy.json` declares it `default` with a cover, so the check must refuse
  *that* — the other direction, a policy that has gone stale.
* `Light.brightness` has a default absorbing exactly `off`. It is the **green** control: the
  policy that names it correctly must pass, so a red run cannot be red for a trivial reason.

`#guard`s below are the unit controls for `Conform.Lcnf` helpers that no Effect4 declaration
exercises today (attribution: 0 of the 122 case sites in the Effect4 closure comes from a compiler
auxiliary, measured).

**This module is a fixture.** Nothing imports it but the audit's own red controls; it is under
`Conform.Effect4` because it names a configuration's subject, not a generic mechanism.
-/

namespace Conform.Effect4.Fixtures

/-- Four constructors, one of which every consumer forgets. -/
inductive Light
  | red
  | amber
  | green
  | off
deriving DecidableEq, Repr

namespace Light

/-- **Deliberately not exhaustive**: `amber` and `off` fall into the default. -/
def label : Light → String
  | .red => "stop"
  | .green => "go"
  | _ => "neither"

/-- Exhaustive, no default: the twin of `label`. -/
def isGo : Light → Bool
  | .red => false
  | .amber => false
  | .green => true
  | .off => false

/-- A default arm that absorbs exactly one constructor: the green control. -/
def brightness : Light → Nat
  | .red => 3
  | .amber => 2
  | .green => 3
  | _ => 0

end Light

/-! ## Unit controls for the attribution helper

`Conform.Lcnf.stripAux` is the pure half of `attributeOf`: it drops a private prefix and the
recognised auxiliary suffixes and says which it dropped. The Effect4 closure exercises none of
these (every one of its 122 case sites sits on a user declaration), so these guards are the only
witnesses that the table is right. -/

open Conform.Lcnf in
section
-- a plain user name is left alone
#guard stripAux `Effect4.Program.Ty.render == (`Effect4.Program.Ty.render, #[])
-- a matcher auxiliary belongs to the declaration it was generated for
#guard stripAux `Foo.bar.match_1 == (`Foo.bar, #["matcher"])
-- `_redArg` is the reduced-argument copy of its declaration
#guard stripAux `Foo.bar._redArg == (`Foo.bar, #["redArg"])
-- suffixes stack, outermost first
#guard stripAux `Foo.bar._redArg.match_2 == (`Foo.bar, #["matcher", "redArg"])
-- a private name is un-mangled first
#guard stripAux (Lean.mkPrivateNameCore `Some.Module `Foo.bar) == (`Foo.bar, #["private"])
-- an unrecognised internal component is NOT guessed at: nothing is stripped
#guard stripAux `Foo.bar._wat == (`Foo.bar._wat, #[])
end

/-! ## Unit control for the short-name helper

`FamilyTable.shortCtor` takes a constructor's last component. It uses `Name.mkSimple`, which is
the identity on that component; `String.toName`, which the first cut of this seat used, runs the
*parser* over it. The two agree on every constructor of this tree — these guards are the witness,
and the last one is the input on which they would not. -/

open Conform.Lcnf in
section
#guard FamilyTable.shortCtor `Effect4.Program.Ty.exitOf == `exitOf
#guard FamilyTable.shortCtor `Effect4.Program.Eff.acquireRelease
          == "acquireRelease".toName
#guard FamilyTable.shortCtor (Lean.Name.mkStr (Lean.Name.mkSimple "F") "a.b") == Lean.Name.mkSimple "a.b"
#guard (Lean.Name.mkSimple "a.b" != "a.b".toName)
end

end Conform.Effect4.Fixtures
