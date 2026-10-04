module

/-!
# The type language's declaration

`Ty` is the type language of the programs this tree prints: the wire types a service row spells
plus what an `Effect<A, E, R>` needs and a row never spells: `never`, the `Exit`, `Cause` and
`Fiber` handles, and unions of error types; and, appended once by the data wave (decisions row 162),
records with optional fields, string-keyed maps, tuples of any arity, nominal references, and the
leaves `null`, `undefined`, `number` and `bytes`.

The declaration sits alone in this module because three of its heads hold a list of children
(`record`, `tuple`, `app`): the family is nested, so Lean derives no `induction`, no `DecidableEq`
and only a `partial` `Repr`. The eliminator, the equality and the printer are generated from this
declaration (`Effect4.Program.TyEq`, the fold generator's `elim` kind), and `Effect4.Program.Ty`
holds the functions.

## The carrier rule for a new constructor

A `Ty` constructor is first-order, non-dependent and proof-free, and every field is a `Shape`:
a `Nat`, a `Bool`, a `String`, a `Unit`, an `Option`/`List`/`Prod` of one, a canonical row, or a
nominal carrier the description already knows, at its own parameters
(`Conform.Source.readShape`, `tools/Conform/Source/Description.lean`, which refuses a
function-typed, dependent or free-variable field by name). A field outside that grammar has no
image in the engine's structure mirror, so the OCaml estate cannot be cut from the declaration
and the constructor cannot land. A constructor is **appended**, never inserted, because the
mirror pins declaration order (`scripts/lib/program_structure.py`) and the wire tags are
positional (`tools/Effect4Gen/wire-tags.json`).
-/

@[expose] public section

namespace Effect4.Program

inductive Ty
  | never
  | unit
  | nat
  | int
  | string
  | bool
  | handle (target : String)
  | option (inner : Ty)
  | list (inner : Ty)
  | prod (left right : Ty)
  | except (error value : Ty)
  /-- `Exit.Exit<A, E>`: what `Effect.exit` and `Fiber.await` answer. -/
  | exitOf (value error : Ty)
  /-- `Cause.Cause<E>`: what a `catchCause` handler receives. -/
  | causeOf (error : Ty)
  /-- `Fiber.Fiber<A, E>`: what a fork answers. -/
  | fiberOf (value error : Ty)
  | union (left right : Ty)
  | lit (value : String)
  /-- `Ref.Ref<A>` (decisions row 42): a cell handle, coarse in `hasTy` as every handle is;
  what the cell holds is typed by the world's heap column. -/
  | refOf (value : Ty)
  /-- `Deferred.Deferred<A, E>` (decisions row 42): a promise handle; what it completes with is
  typed by the world's promise table. -/
  | deferredOf (value error : Ty)
  /-- A row template's parameter (`Ref.get<A>`), never a program's type: the checker
  instantiates every variable of a row from the request or the operation's type arguments
  (decisions row 42). -/
  | var (index : Nat)
  /-- TypeScript's `unknown` (decisions row 46): the top of `sub`, inhabited by every value;
  what rc.112 gives a release's exit parameter (`Exit<unknown, unknown>`, `Effect.ts:12930`)
  and the children snapshot's fiber columns. -/
  | unknown
  /-- A record (decisions rows 119, 157, 165; wire tag 20): each field a name, an optional-key
  flag (rc.112 `optionalKey`: the key absent, or present with a value of the type) and a type.
  Canonical when strictly ascending by the name's UTF-8 bytes (`Ty.canon`), so names are
  distinct. Printed `{ readonly a: A; readonly b?: B }`; its value carries its canonical names
  (`ctor 0 [list names, list values]`, row 165 (a)). -/
  | record (fields : List (String × Bool × Ty))
  /-- A string-keyed map (decisions row 125; wire tag 21): `Readonly<Record<string, V>>`, the key
  type exact, the value covariant; its value is a list of key-value pairs, keys strictly ascending
  by their UTF-8 bytes. -/
  | map (key value : Ty)
  /-- A tuple of any arity (decisions row 159; wire tag 22): `readonly [A, B, C]`, positional, no
  names and no sort; arity two is `prod` (normalized to it). -/
  | tuple (items : List Ty)
  /-- A nominal reference (decisions row 158; wire tag 23): `Name<Args>`, each argument at the
  named declaration's variance (`Ty.argVariance`); `app t []` and `handle t` are one canonical
  form (normalized to `handle t`). Membership is opaque by name, as a handle's is. -/
  | app (name : String) (args : List Ty)
  /-- `null` (decisions row 160; wire tag 24). -/
  | null
  /-- `undefined` (decisions row 160; wire tag 25), below `unit` (`void`). -/
  | undefined
  /-- A binary64 number (decisions row 121; wire tag 26), above `int` and so above `nat`: its
  members are the integers' images and the binary64 frame of the doubles that are not integers. -/
  | number
  /-- `Uint8Array` (decisions row 161 (a); wire tag 27), over the existing `Val.bytes` frame. -/
  | bytes

end Effect4.Program
