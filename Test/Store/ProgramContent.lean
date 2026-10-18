import Effect4.Store.Domain.Genesis
import Effect4.Store.Domain.Derived.Program

/-!
# Test.Store.ProgramContent — a program in the store, at kind `program`

`Content (Eff NativeOp)` is generated beside the program's `Canonical` instance
(`src/Effect4/Store/Domain/Derived/Program.lean`, the manifest's `--kind` request at kind
`program`). So the store's address lattice and its round trip, proved once over `Content`
(`src/Effect4/Store/Domain/Node.lean`, `src/Effect4/Store/Domain/Store.lean`), reach a whole
program. That is the proposed claim `program-digest-exact` (concept `exact-codecs`; seat ORG's
rank 5, `docs/research/2026-10-08-seat-ORG-theory-map.md` §7).

- **The kind**: a program's node files under `program` (a finite evaluation of the instance).
- **Two readers**: the address lattice's level 0 (`address_eq_or_collision`) and the round trip
  (`get_put`), applied at programs. Neither typechecks without the instance.
- **The control behind a piece's key**: one program, and the same program one slot deeper
  (`Eff.weaken 0`), have two addresses, since a variable is a level and its bytes move. So a stored
  subtree's key must fix its environment, which is the MCP note's ruling 3
  (`docs/research/2026-10-09-mcp-code-mode-design.md` §10.2), still open.

Placement. The readers instantiate laws at the program carrier; the battery states nothing of a
subtree's key, of sharing between programs, or of hash injectivity.
`address_inj_resident` (`src/Effect4/Store/Domain/Store.lean`) applies only to residents at their own addresses in one store.
-/

set_option autoImplicit false

namespace Test.Store.ProgramContent

open Effect4 Effect4.Store Effect4.Program

/-- Seat ORG's probe program: `bind (succeed 1) (succeed (var 0))`, its variable at level 0. -/
def atRoot : Eff NativeOp := .bind (.succeed (.lit (.nat 1))) (.succeed (.var 0))

-- A program's node files under kind `program`, the store's kind byte 5.
#guard Content.kind (Eff NativeOp) = .program
#guard (nodeOf atRoot).kind.byte = 5

-- The same program one slot deeper: its variable's level moves from 0 to 1, and so does its key.
#guard Eff.weaken 0 atRoot = .bind (.succeed (.lit (.nat 1))) (.succeed (.var 1))
#guard (address atRoot).digest ≠ (address (Eff.weaken 0 atRoot)).digest

/-- The reader of the address lattice at programs: equal addresses of two well-formed programs
are equal programs, or an exhibited collision. -/
example {p q : Eff NativeOp} (hp : (Canonical.toVal p).WF) (hq : (Canonical.toVal q).WF)
    (h : address p = address q) :
    p = q ∨ ((nodeOf p).encode ≠ (nodeOf q).encode ∧
      sha256 (nodeOf p).encode = sha256 (nodeOf q).encode) :=
  address_eq_or_collision hp hq h

/-- The reader of the round trip at programs: a program put without a conflict reads back. -/
example {p : Eff NativeOp} {s s' : Store} {o : Outcome} {r : Ref (Eff NativeOp)}
    (h : s.put p = .ok (o, r, s')) (hc : ∀ m, o ≠ .conflict m) : s'.get r = some p :=
  get_put h hc

end Test.Store.ProgramContent
