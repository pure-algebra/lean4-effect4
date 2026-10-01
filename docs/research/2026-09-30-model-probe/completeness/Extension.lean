import Effect4.Api

/-!
# Completeness seat: what "Σ ⊆ Σ'" has to mean for rows (R2)

Finite checks only (`#guard`): evidence word **tested**. No theorem, so no axiom line.
Read against HEAD `7cae243a`.

R2 says "for Σ ⊆ Σ' (one more row …) every theorem about Σ-programs holds for them in Σ'"
and calls rows "additive by construction". The tree has no signature-extension relation and no
lemma transporting a program's typing or certificate from one table to a larger one (grep for
`effTy_congr`, `Signature.Extends` and the like finds nothing). These checks show what the
relation must be:

1. **Append keeps the meaning of existing programs** (on this program): the type and the run
   are unchanged when a fresh row is appended.
2. **Insertion does not**: the same bytes name rows by position (`NativeOp.external i`), so a
   row inserted in front re-points every call and the program no longer checks. "Σ ⊆ Σ'" must
   be the append-only, names-fresh order DI-47 rules for the world description.
3. **Append of a clashing name makes Σ' unlawful** (`LawfulTable`), so the extension relation
   must also carry the lawfulness R1 leaves undefined.
4. A certificate is indexed by its table (`Api.Typed table`), so it is re-issued, never
   transported, at the larger table.

The red control is `ExtensionRed.lean`: guard 2 flipped (insertion expected harmless). It must
fail with exactly one guard error.
-/

set_option autoImplicit false

namespace Probe.Completeness.Extension

open Effect4 Effect4.Machine Effect4.Program

/-- An asynchronous host row answered by the host. -/
def row (name spelling : String) (request answer : Ty) : Row :=
  { name, spelling, kind := .async, registration := .external, request, answer,
    error := .never, cite := "docs/research/2026-09-30-model-probe/completeness/Extension.lean" }

/-- Acquire a host resource, read it, close it (the shape of the tree's own resource fixture,
`Test/Program/HostSpecContract.lean`, `resourceTable`). -/
def table : RowTable :=
  [ row "acquire" "Host.acquire" .unit (.handle "Probe.Res")
  , row "close" "Host.close" (.handle "Probe.Res") .unit
  , row "read" "Host.read" (.handle "Probe.Res") .nat ]

/-- A fresh row with a fresh name. -/
def extra : Row := row "ping" "Host.ping" .unit .string

/-- A row whose name clashes with an existing one. -/
def clash : Row := row "read" "Host.read" (.handle "Probe.Res") .nat

def program : NativeEff :=
  .scoped (.bind (.acquireRelease (.perform (.external 0) (.lit .unit))
      (.perform (.external 1) (.var 0)))
    (.perform (.external 2) (.var 0)))

def answers : List (Completion Val Err Defect FiberId Ann) :=
  [.ofExit (.success (.nat 0)), .ofExit (.success (.nat 7)), .ofExit (.success .unit)]

#guard (Api.typeOf program table).isSome
#guard LawfulTable table

-- 1. Append: the type and the run's exit are unchanged.
#guard Api.typeOf program (table ++ [extra]) = Api.typeOf program table
#guard (Api.run program 1000 answers (table ++ [extra])).exit =
  (Api.run program 1000 answers table).exit
#guard (Api.run program 1000 answers table).exit = some (.success (.nat 7))
#guard LawfulTable (table ++ [extra])

-- 2. Insertion in front: every call is re-pointed and the program no longer checks.
#guard Api.typeOf program (extra :: table) ≠ Api.typeOf program table
#guard (Api.typeOf program (extra :: table)).isNone

-- 3. Appending a clashing name: the larger table is not lawful.
#guard !(LawfulTable (table ++ [clash]))

-- 4. A certificate is indexed by its table: both exist, as different types.
#guard (Api.check program table).toOption.isSome
#guard (Api.check program (table ++ [extra])).toOption.isSome

end Probe.Completeness.Extension
