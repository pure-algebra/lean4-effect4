# 2026-10-16 `Modeled` and the universe of `Ty`: the deriver's obligations, and the abstraction under Eff

Status: a design note with landed evidence, not authority.
Base: `a8a8c2657` on `refactor/phase1-phase3`.
Role: the owner's question of 2026-10-16: what the mathematics says the deriver owes, and whether
`Modeled` is the abstraction that Eff is built on.

## The one thing to know first

`Ty` is a universe of codes, and `Model.Carrier` decodes a code to a Lean type. `Model.image` is a
generic function over the codes. `Modeled α` says that `α` is in the universe. A derived instance
now carries the generic image staged at its code: the fold unfolded into its combinators. That
staged image is the fold's image by definition, so the deriver owes no new law. The LCNF route
lowers it to native OCaml types and codecs.

## 1. Question

1. What does a derived `Modeled` instance owe, so that its codec runs without the fold and keeps
   the fold's laws?
2. Is `Modeled` the abstraction under Eff, and what would it take to make it the one?

## 2. What was read or run

| Item | Evidence | Result |
| --- | --- | --- |
| The derived codec through LCNF, before the change | tested (`docs/research/2026-10-15-modeled-lowering/README.md`) | the fold runs at run time; 109 declarations; refused |
| The staged image, written by hand for `Todo` and `Status` | proved by `rfl`, tested in OCaml | the whole `Image` equals `Modeled.image`; 48 declarations; compiles; round-trips |
| The staged image, written by the deriver | built: `Test.Schema.Modeled` | each derived instance's `modeled_staged_eq` closes |
| A record with an integer, a list, an option, a nested sum and a nested record, lowered | tested in OCaml (scratch probe, §4) | 64 declarations; round trip, the `negInt` frame, a refusal, five integers |
| `Store.Image`, `Columns`, `Image.union`, `Image.ofVal_eq_of_toVal_eq` | reading | the combinators carry their own laws; an exact image's reader is fixed by its writer |
| The step language (`src/Effect4/Step.lean`) and `field_ref%` | reading | a typed term language over the universe, evaluated into `CarrierAt` |

## 3. The mathematics

### 3.1 The universe

`Ty` is the syntax of codes, and the checked domain (`Model.refusal t = none`) is the set of codes
with a decoding. The decoding is a fold: `Model.Carrier t` is the carrier type, and `Model.image t`
is its exact embedding into `Val`. This is a universe in the sense of Martin-Löf, with `Ty` as the
codes and `Carrier` as the decoding. Every judgment of the tree is a fold over the same codes:
membership, inhabitance, normalization, the Schema bridge and the printers. A new judgment is a
new algebra, and a new code is a new constructor with an arm in each algebra.

`Modeled α` gives a code and an equivalence between `α` and the code's carrier. It is what
GHC's `Generic` gives (a representation and two maps), with the representation computed from a
first-class code. So one instance gives `α` every generic function over the universe.

### 3.2 Exact embeddings are determined by their writers

An exact embedding has a writer and a reader with retraction and exactness (`Store.Image`). The
reader is the partial inverse of the writer. So two exact embeddings with one writer have one
reader (`Image.ofVal_eq_of_toVal_eq`, `src/Effect4/Store/Carrier/Image.lean`). The literature's
term for this pair is a lawful prism. A reader therefore never needs its own agreement proof.

### 3.3 Staging the generic function

The fold reads its code at run time. At a known code it unfolds, by definition, into the
combinators. They are `Image.record` over `Columns.cons`, `Image.union`, `Image.lit`, `Image.list`,
`Image.option`, `Image.tuple2` and the scalar images. That term is the generic function partially
evaluated at the code. This is staged generic programming: the interpretation of the code is
removed and its result is kept.

### 3.4 What a derived instance owes

| Obligation | What discharges it | Per type? |
| --- | --- | --- |
| The code is in the checked domain | `modeled_checked`: the names' order by `decide`, each field's `checked` | yes, written by the deriver |
| The carrier equivalence | `modeled_to_of`, `modeled_of_to` | yes, written by the deriver |
| Retraction and exactness of the codec | the combinators' own laws | no |
| The staged image is the fold's image | `modeled_staged_eq`: each field's `staged_eq`, then `rfl` for a record; `rfl` for a union | yes, one line |
| The reader agrees with the fold's reader | `Image.ofVal_eq_of_toVal_eq` | no |
| Every encoded value is a member of its type | `Modeled.member`, through `staged_eq` and `Model.member` | no |

A union proves its staged image by `rfl` alone. Its carrier is a subtype whose predicate names the
members' images. So Lean's elaboration accepts the staged term only where they are the fold's by
definition. A
record's proof rewrites each field's staged image first, so a field instance may be opaque.

## 4. What landed

| File | Change |
| --- | --- |
| `src/Effect4/Schema/Modeled.lean` | `Modeled` gains `staged` (default `Model.image ty`) and `staged_eq` (default `rfl`); `Modeled.image` reads `staged`; the scalar, `List`, `Option` and pair instances give theirs |
| `src/Effect4/Schema/Modeled/Derive.lean` | the deriver writes `modeledStaged` and `modeled_staged_eq` for a structure and for an inductive |
| `src/Effect4/Laws/Schema/Modeled.lean` | `Modeled.member` reads the fold through `staged_eq` |
| `src/OCaml5/Lcnf/Builtins.lean` | `Int`'s four rows inside the profile bound: `Int.ofNat`, `Int.negSucc`, `Int.decLt`, `Int.natAbs` |
| `src/OCaml5/Lcnf/Translate.lean` | a constructor with a row takes the row's form: `Int` is `int`, which has no constructor |
| `src/OCaml5/Tools/LcnfGen.lean`, `src/OCaml5/Lcnf/Gen.lean` | the committed recipe places the manifests, so a probe's recipe writes beside its output |

The lowered record of §2 declares `type item = { … }`, `type status = Status_pending |
Status_closed of string` and `type 'a image = { to_val : 'a -> val_; of_val : val_ -> 'a option }`.
The image is a first-class OCaml value: the typed description that Jane Street's `Typerep` gives
by hand.

## 5. `Modeled` as the abstraction under Eff

### 5.1 What already reads the universe

| Layer | What it reads | Through `Modeled` today |
| --- | --- | --- |
| The program's types | `EffTy`'s columns are codes | no: a column is written as a `Ty` |
| Values on the machine | `Val`, membership by fold | the image's writer |
| Pure steps | `Step Γ t`, evaluated into `CarrierAt` | `field_ref%` over a derived record |
| Store cells | PubSub and PartitionedSemaphore cells | yes: derived records |
| Host calls | rows: request, answer and error codes | no |
| Hosts | `Run.Reactor` over `Val` | no: P1 types it |
| Faces | the TypeScript printer, the Schema bridge, the OCaml route | the OCaml route, since §4 |

### 5.2 What would make it the one

1. **Nominal instances.** `deriving Modeled` adds a declaration to the application's table
   (`TyDecls`), and the instance's code is the name. The carrier fold reads a name from the table,
   as `declAlg` reads it from an oracle. This is recursive types' wiring slice, seen from the Lean
   side: every face then prints `Todo` by name.
2. **The checked domain grows to the platform's shapes**: bytes, numbers, optional fields, maps
   and tuples. Each is an arm of the carrier fold with its combinator, and the staging and the
   proofs follow unchanged.
3. **Typed operations and services.** An operation with `Modeled` request, answer and error types
   is a row. A structure of operations is a row service. Its host is a structure of Lean functions,
   whose reactor decodes each request by the request's image and encodes each answer. This is P1,
   generalized from the to-do.
4. **Recursion and parameters.** A recursive inductive takes a declared name and a staged image by
   structural recursion (`Image.fix`). Parameters follow by regular recursion (decisions row 401).
5. **Programs as data.** `Eff` itself is a recursive inductive. With 1 and 4 it has an instance.
   A program is then a typed value of the universe, and an agent can send one through a row.

### 5.3 Literature, by name

- Per Martin-Löf, universes à la Tarski: codes and their decoding.
- Altenkirch and McBride, "Generic programming within dependently typed programming" (2003).
- Chapman, Dagand, McBride and Morris, "The gentle art of levitation" (2010): a universe that
  describes its own codes, as item 5 proposes.
- Magalhães, Dijkstra, Jeuring and Löh, "A generic deriving mechanism for Haskell" (2010).
- Yallop, "Staged generic programming" (2017): §3.3's staging.
- Rendel and Ostermann, "Invertible syntax descriptions" (2010), and profunctor optics: §3.2's
  exact embeddings.
- Jane Street's `Typerep`, and Effect's `Schema`: the same idea in OCaml and in TypeScript.

None of these was read in this session. Each is named for its idea.

## 6. Proposals

1. Make `Modeled` the application's entry for types: nominal instances over the declaration
   table. Land it as one slice with recursive types' wiring.
2. Widen the checked domain by the platform's shapes, in the order of their first consumers.
   Bytes and numbers serve P2's byte streams; optional fields and maps serve HTTP.
3. Write P1's typed host as the first typed service: operations with `Modeled` types, rows derived,
   the reactor generic.

## 7. What this does not establish

- The OCaml probes are finite runs on two declarations and one record.
- No lowered `Modeled` codec runs in a committed lane yet.
- §5.2 is a proposal. No part of items 1 to 5 is built.
- The literature is named, not read here.
