# Seat P (type-language probe, 2026-10-01): records and the type algebra, on a production-shaped copy

Base `bff50631` on `probe/P`, worktree `/Users/pooks/Dev/lean4-effect4-probe-P`; Lean 4.33.1.
Evidence words: **proved** (a kernel theorem compiled here, `#print axioms` at or below
`[propext, Quot.sound]`), **tested** (a `#guard`, a `#guard_msgs` fixture or a command run here),
**reading** (code or notes read, not run), **assumed** (not checked). A theorem about the copy is
about the copy, not the tree; the row-128 theorems (question 5) are about today's tree functions,
with the repaired functions defined beside them.

## The one thing

**Every law the wave needs holds on one production-shaped copy with T's whole constructor set and
the named record value (row 165 (a)), and the two row-128 exactness theorems hold by construction
on today's `Ty`, without the re-encoding guard** (proved). The design facts the briefs must carry:

1. **The cross-head rules are one table** (`leafEdges`, a list: `lit < string`, `nat < int <
   number`, `undefined < unit`), closed reflexively and transitively, consulted by `sub` before its
   rows. `sub_trans_core` and `sub_antisymm_normal` survive with no edge named; antisymmetry (and
   transitivity, at the literal's payload head) reads the table's acyclicity, `leafLe_antisymm`;
   `nat ⊑ number` follows from the two edges (`sub_nat_number`); membership needs one inclusion per
   edge (`hasTy_leafEdge`, `fits_leafEdge`), and **an edge forces the images to nest**: Lean's
   generated `Int` image breaks `nat ⊑ int` (`generated_int_image_breaks_tower`), so row 121's
   signed frame must hold the negative integers only and the binary64 frame only the doubles that
   are not integers (amendment proposed below).
2. **Under the named value the discriminant-first key order is not needed**: tags are read by
   name, tagged records are disjoint at the plain UTF-8 byte order (`tagged_disjoint`), and the
   positional ambiguity stays as a red control (`bytes_order_ambiguous`). Width is refused by the
   name list (`record_width_refused`); an optional key is absent from both lists and the read is a
   merge (`namedHasTy`); the named clause costs +164 lines over the positional one on the copy's
   judgments (measured) and makes the boundary projection type-blind (`lookupName`).
3. **Route (b) of W1 is proved, not owed**: the plain repaired decoder is exact modulo `N_J`
   (`decodeC_iff`, every arm including causes, through `decodeRawC_normJ`: the decoder reads `N_J`'s
   quotient), and the plain repaired schema reader is exact modulo `N_S` (`ofSchemaC_exact`, by
   `fun_induction`, no hand induction over the nested `Representation`).

## How the probes are built

Ten layers, each a standalone Lean file under `P/probes/`, compiled in order by `P/probes/run.sh`
(`lake env lean --root=P/probes -DwarningAsError=true -o <scratchpad>/olean/<L>.olean <L>.lean`,
`LEAN_NUM_THREADS=1`, one compiler at a time; the `.olean` files live in the session scratchpad,
never in the tree). Logs: `P/probes/logs/<L>.log`, each ending `exit=0`; the last full run (all ten
in order) is the one the logs hold. No theorem prints an axiom above `[propext, Quot.sound]` (the
summary command in the receipt). No `sorry`, `native_decide`, `partial`, `unsafe`, `axiom`; no
`simp_all`, `first`, `try` in a proof (the `grep` in the receipt); hand `simp` is `simp only`.

| Layer | What | Lines |
| --- | --- | --- |
| `P1FieldOrder.lean` | question 1: `canonBy`, its laws, the refusal, the `String.lt` red control | 770 |
| `P2Ty.lean` | `Ty` with T's set appended (28 constructors), the leaf table, `sub`, `normalize`, `Normal` | 1314 |
| `P3View.lean` | `TyView` with list heads, the table's laws, the order laws | 894 |
| `P4Algebra.lean` | `sub_trans_core`, `sub_antisymm_normal`, `sub_normalize_of_sub`, `sub_nat_number` | 809 |
| `P4Check.lean` | `Val.hasTy` (named records, T's arms), `hasTy_sub`, `hasTy_normalize`, TY-10 | 1091 |
| `P5Fits.lean` | `Fits` (I2's form), its five laws, `fits_normalize`, the boundary projection | 2070 |
| `P6Inhabited.lean` | question 6: `inhabited` and `inhabited_iff_fits` | 551 |
| `P7Tagged.lean` | question 4(c): the tag decision's record arm and its laws | 382 |
| `P8Codec.lean` | question 5: the JSON pair, `N_J`, exactness | 1144 |
| `P8Schema.lean` | question 5: the schema pair, `N_S`, exactness | 536 |

(`wc -l P/probes/P*.lean`.) The positional record clause the copy carried first is kept in the
branch's history: questions 2–3 at `1b069d15`, question 6 at `8fa1247f`, question 4(c) at
`056ca30b`; this note cites them where the two clauses are compared.

## Question 1. The key order and `canon`

**Answer (proved).** `canonBy key fs` (`P1FieldOrder.lean:129`) is an insertion sort by
`Ty.ltKey` on `key` of each field's name, payload-polymorphic (`β` any type), the first
occurrence of a repeated name kept (`insertBy`, `:120`). Every law is proved once for any key, so
it holds for both instances: `bytesKey` (`:36`), the name's UTF-8 bytes, which is `Ty.key (.lit s)`
minus the constructor code (`key_lit`, `:39`, `rfl`), injective through `Ty.key_injective` (`:41`);
and `tagFirstKey` (`:47`, `_tag` first), which the named clause no longer needs (question 4(c)).
The copy's main line uses `fieldKey := bytesKey` (`P2Ty.lean:358`) and the notation
`canonF := Field.canonBy fieldKey` (`:364`).

| Law | Theorem (`P1FieldOrder.lean`) | Axioms |
| --- | --- | --- |
| sorted | `canonBy_ascending` `:201` | `[propext, Quot.sound]` |
| no repeated name survives | `canonBy_names_nodup` `:219` | same |
| idempotent | `canonBy_idem` `:297` (via `canonBy_of_ascending` `:292`) | same |
| permutation-invariant on distinct names | `canonBy_perm` `:513` | same |
| the order reads names only | `canonBy_map` `:255` | none |
| nothing new | `mem_canonBy` `:316` | `[propext]` |
| the first occurrence is kept | `firstOf_canonBy` `:496` | `[propext, Quot.sound]` |
| on distinct names nothing is dropped | `mem_canonBy_iff` `:502` | same |
| the name set is kept | `mem_names_canonBy` `:522` | same |
| empty iff empty | `canonBy_eq_nil_iff` `:554` | none |
| size bound | `sizeOf_canonBy_le` `:597` | `[propext, Quot.sound]` |
| keyed ascending lists are extensional | `ascending_ext` `:365` | same |

**Refusal at formation (proved, tested).** `firstRepeated` (`:609`) with
`firstRepeated_eq_none_iff` (`:646`): `= none ↔ (fs.map Prod.fst).Nodup`, the located-refusal
shape; the type-level scan `Ty.findRepeatedField : Path → Ty → Option (Path × String)`
(`P2Ty.lean:1213`) returns the record's path and the name through every head, tuple and reference
items included (`#guard`s `P2Ty.lean:1264-1267`). The refusal is `repeatedField (at : Path)
(name : String)`. Why it is needed for the law (proved): `dup_order_matters` (`:673`) —
permutation invariance holds exactly on distinct names. `hasTy_normalize` does not need it (it
holds on raw types with repeats); `raw_fold_disagrees` (question 6) shows the canonical read is
what keeps the fold and membership agreeing there.

**Red control (tested, pinned).** `fieldBefore a b := decide (a < b)` on `String` (`:677`): a
`#guard_msgs` fixture pins its axioms at `[propext, Classical.choice, Quot.sound]` (Codex's
`Ordering.lean`, reproduced); `canonBy` and `bytesKey` depend on no axiom.

**What `Effect4.Row` supplies (proved, reading).** `Row` is a deduplicated ascending set over a
linear order on the element; a keyed list (two fields of one name, different payloads) is not one,
so `Row` cannot be instantiated at `String × β` and has no payload map, first-occurrence rule or
refusal. It supplies the canonical **name set**: `canon_names_row` (`:724`) proves
`(canon fs).map (Ty.lit ∘ fst) = (Row.normalize (fs.map (Ty.lit ∘ fst))).elems` through
`lit_lt_iff` (`:707`). The keyed laws are parallel copies of `Row`'s (`mem_insertBy` ≈
`mem_insertElems`, `insertBy_ascending` ≈ `ascending_insertElems`, `ascending_ext` ≈
`ascending_list_ext`); new are `canonBy_map`, `firstOf_canonBy`, the refusal. Proposal (not
needed for the wave): a keyed row `KeyedRow (key : α → κ)` of which `Row α` is `key := id`.

## Question 2. Membership in canonical order, the named value

**The record arm (proved, `P4Check.lean`, `P5Fits.lean`).** A record value is
`ctor 0 [list names, list values]` (`recordParts?`, `P4Check.lean:78`), names as `Val.str`, both in
canonical order, the absent optional fields absent from both lists. The arm builds one checker per
**written** field with the field-list companion (`checkers`, `:225`; `fitters`, `P5Fits.lean:221`),
sorts the checkers with `canonF`, and reads the value by a merge:

```lean
def namedHasTy : List (String × Bool × (Val → Bool)) → List Val → List Val → Bool
  | [], [], [] => true
  | (_, o, _) :: cs, [], [] => o && namedHasTy cs [] []
  | (n, o, c) :: cs, .str m :: ns, x :: xs =>
    if m = n then c x && namedHasTy cs ns xs
    else o && namedHasTy cs (.str m :: ns) (x :: xs)
  | _, _, _ => false
```

(`P4Check.lean:85`; `NamedFit`, `P5Fits.lean:122`, is its proposition.) A name equal to the next
canonical field's is read at that field's type; a field the value does not name must be optional;
any other name (one the type lacks, a repeat, one out of order) fails. The recursion never sorts
types, so `Val.hasTy` and `Fits` stay structural (the companion pattern of `Val.keys`).

- `hasTy_record` (`P4Check.lean:263`), `fits_record` (`P5Fits.lean:252`): with
  `recordParts? v = some (ns, xs)`, `hasTy v (.record fs) al = namedHasTy ((canonF fs).map (fun q
  => (q.1, checkerOf al q.2))) ns xs` and `Fits w v (.record fs) ↔ NamedFit ((canonF fs).map (fun q
  => (q.1, fitterOf w q.2))) ns xs`; a value without parts is no record's member
  (`hasTy_record_none`, `fits_record_inv`). All `[propext]` or `[propext, Quot.sound]`.
- One arm per appended constructor in each law (proved): `fits_hasTy` (`P5Fits.lean:390`),
  `fits_live` (`:746`), `fits_map` (`:1042`), `fits_sub` (`:1232`), `hasTy_sub`
  (`P4Check.lean:467`). Liveness reads the names (strings carry no keys) and the values.
- `hasTy_normalize` (`P4Check.lean:758`), **no premise**, records as factors: the record case
  (`hasTy_normalize_record`, `:709`) is `normalize_record` (`P4Algebra.lean:502`, normalizing a
  record maps its canonical list, names and flags kept) plus the induction hypothesis under
  `funext`; it is the positional proof with `namedHasTy` for `fieldsHasTy` (17 lines against 19,
  measured). `fits_normalize` (`P5Fits.lean:1563`), row 137's law, likewise; then `fits_subN`
  (`:1682`) and the joins (`:1686`, `:1689`), as I2 states them.
- **Records are factors, not distributed (tested)**, `#guard`s `P4Check.lean:1024-1025`.
- **`record_sub_not_complete` (proved, `P4Check.lean:980`)**, named: `record {a: nat | string}`
  and `record {a: nat} | record {a: string}` have the same members at every allocation table, the
  union is below the record, the record is not below the union.
- **Red control (proved)**: the written-order read is not normalization-invariant
  (`written_order_not_invariant`, `P5Fits.lean:2033`).
- Tested controls (`P4Check.lean:1030-1065`): the canonical names in order fit, the written order
  does not; an optional key absent, present, and present at `none`; an extra, a repeated or a
  missing name refused; row 165's case (`{a: nat, b: string}` and `{b: nat, c: string}`): the one
  value fits one branch only.

**T's arms (proved, with stand-in images).** `tuple`: a list read item by item (`itemsHasTy`);
arity two is `prod`'s value, so `tuple [a, b]` normalizes to `prod a b` and keeps membership
(`hasTy_tuple_pair`, `:282`; `fits_tuple_pair`). `app n _`: opaque, the handle arm at target `n`
(`handleHasTy`, `:120`, production's `.handle` arm extracted; I2's `HandleArm`, `P5Fits.lean:113`),
arguments unread, so invariance makes it monotone and `app n []` is `handle n`. `null`:
`Val.none`; `undefined`: `Val.unit` (one image with `void`); `int`: `nat n` for `n ≥ 0`,
`ctor 1 [nat k]` for `-(k+1)`; `number`: an integer's image or `ctor 2 [bytes b]`, eight bytes;
`bytes`: `Val.bytes`. These images are **assumed** stand-ins chosen so every edge of the leaf
table is an inclusion; the encodings are rows 121, 157, 160, 161's (constraint in the rows below).

## Question 3. Subtyping

**`sub`'s record arm (proved, `P2Ty.lean:737`).** Equal canonical heads (names with their
optional flags), then each field type below its partner, reached through `List.attach`:

```lean
  | .record fs, .record gs =>
    decide (heads (canonF fs) = heads (canonF gs)) &&
      ((canonF fs).attach.zip (canonF gs).attach).all fun pq =>
        have := sizeOf_field_lt (mem_canonBy pq.1.2)
        have := sizeOf_field_lt (mem_canonBy pq.2.2)
        sub pq.1.1.2.2 pq.2.1.2.2
```

TY-10's acceptance item holds: a permuted record is raw-below its normal form both ways
(`#guard`s `P2Ty.lean:1246-1249`); a dropped or added field is refused; a flag must match
(`:1251-1255`); the map is exact in the key and covariant in the value (`:1260-1262`); tuples are
pointwise at exact arity, references invariant at equal name and arity (`:1270-1277`).

**The cross-head rules, one table (the coordinator's precision; proved).** Production's one
non-congruence rule (`litRule`, `.lit _, .string`) and T's three become one relation on *leaf
heads*, read from data:

```lean
inductive LeafHead where | lit | string | nat | int | number | undefined | unit
def leafEdges : List (LeafHead × LeafHead) :=
  [(.lit, .string), (.nat, .int), (.int, .number), (.undefined, .unit)]
def leafReach (edges : List (LeafHead × LeafHead)) : Nat → LeafHead → LeafHead → Bool
  | 0, x, y => decide (x = y)
  | n + 1, x, y => decide (x = y) || edges.any fun e => decide (e.1 = x) && leafReach edges n e.2 y
def leafLe (x y : LeafHead) : Bool := leafReach leafEdges leafEdges.length x y
def leafRule (a b : Ty) : Bool :=
  match leafHead a, leafHead b with
  | some x, some y => !decide (x = y) && leafLe x y
  | _, _ => false
def sub (a b : Ty) : Bool :=
  if a = b then true
  else if leafRule a b then true       -- the table, before every row
  else match a, b with
  | .never, _ => true
  ...                                  -- production's rows; the `.lit _, .string` arm is gone
```

(`P2Ty.lean:666-722`, `:737`.) The laws, all over the finite head domain by `decide`, so they are
regenerated with the table and name no edge (`P3View.lean:666-826`): `leafLe_iff_path` (`:722`,
the closure is the reflexive-transitive closure of the table, against an inductive `LeafPath`);
`leafLe_trans` (`:695`); **`leafLe_antisymm` (`:706`), the acyclicity lemma**, with
`leafEdges_acyclic` (`:731`) its path form; `leafRule_trans` (`:775`: the composite of two rules
relates different heads because the table is acyclic; at a payload head on a cycle,
`lit "a" < y < lit "b"`, it would not); `leafRule_asymm` (`:787`); `leafRule_sameHead` (`:810`);
`leafRule_args`, `leafRule_ne_unknown`, `leafRule_normalize`. The view's order laws take the
table's rule where production takes `litRule`: `sub_eq_args` (`:472`, hypothesis
`hleaf : leafRule a b = false`) and the different-head theorem `sub_eq_false_of_not_sameHead`
(`:401`), whose conclusion is false exactly where the table relates the heads. Red control
(tested, `P2Ty.lean:1285`): a cyclic table (`int < nat` added) relates `nat` and `int` both ways.

- **`sub_trans_core` survives** (`P4Algebra.lean:44`): the two leaf branches read
  `sub_of_leafRule`, `leafRule_trans`, `leafRule_args` where production destructures its one
  literal rule; no edge named; 74 lines against production's 75.
- **`sub_antisymm_normal` survives** (`:286`): one rewrite through `Normal.canonHead` before
  `argsBelow_antisymm`, the leaf branches through `leafRule_asymm` (the acyclicity), the
  production `decreasing_by`'s `try (apply hsize <;> assumption)` replaced by two `have`s.
- **`nat ⊑ number` from the two edges** (`sub_nat_number`, `:130`): `sub_trans` over
  `sub_of_leafEdge` at `(nat, int)` and `(int, number)`; the table has no `(nat, number)` entry
  (`#guard`, `P2Ty.lean:1279`).
- **Membership, one obligation per edge** (`hasTy_leafEdge`, `P4Check.lean:356`;
  `fits_leafEdge`, `P5Fits.lean:1198`): a head's members are its representative's (`leafRep`,
  `lit ↦ string`); the closure is carried along a path (`hasTy_leafPath`); no edge enters `lit`
  (`leafEdges_target_ne_lit`, by `decide`). **Red control (proved)**:
  `generated_int_image_breaks_tower` (`P4Check.lean:1017`): under Lean's generated `Int` image
  (`ctor 0 [nat n]`) a natural's value is no integer's, so the edge `nat ⊑ int` would break
  `hasTy_sub`.
- Production cost of the table (measured, `logs/measure.log`): `litRule` (3 lines) becomes
  `leafEdges` (5); `litRule` and its three lemmas (20 lines) become the table's 20 laws (119
  lines), all generated; `sub` loses one arm and gains one line; every proof that unfolds `sub`
  passes the table's line with one more rewrite (`ite_leafRule_false`, `P2Ty.lean:1151`); the
  congruence arms keep their `fun_cases` numbers (`case7`–`case15`), the exceptional ones shift
  (`case2` is the table).

**The view for a head of variable arity (proved, `P3View.lean`).** `sub_eq_args` keeps its
statement (but for the leaf hypothesis's name). A record's `args` are its canonical field types at
`co` (`:49`); a tuple's its items at `co`; a reference's its arguments at `inv`; a map is a
fixed-arity head `[(inv, key), (co, value)]`. `sameHead` (`:80`) compares the canonical heads, the
arity, the reference's name. **One law changes its statement:** `eq_of_sameHead` is false at raw
records written out of order (`eq_of_sameHead_raw_false`, `:224`, red control); its conclusion
becomes `canonHead a = canonHead b` (`:185`), `canonHead` (`:111`) ordering a record's fields and
the identity elsewhere; `argsBelow_antisymm` (`:626`) inherits it; `eq_of_sameHead_nil` keeps its
statement (`:652`). The variance table's row for a list position is one variance applied to every
element (`record: co*`, `tuple: co*`, `app: inv*`), and the generator needs the head's normaliser
(`canonF`) to emit `args`, `sameHead`, `canonHead`.

**The eight proofs that follow a function's own principle** (synthesis §3.3), measured
(`P/probes/measure.py`, `logs/measure.log`): `fits_sub` 103 → 157 lines (`P5Fits.lean:1232`);
`sub_eq_false_of_not_sameHead` 13 → 21 (`P3View.lean:401`); `sub_eq_argsBelow_of_sameHead` 36 → 44
(`:424`); `sameHead_trans` 3 → 3 (`:136`); `sub_normalize_of_sub` 146 → 202 (`P4Algebra.lean:592`;
the nine congruence cases read `sub_args_*` because the unfolded `sub` now carries the table's
line); `cata_admits_sub` 62 lines, its copy-side analogue `hasTy_sub` 143 (`P4Check.lean:467`,
proved directly, not through `AdmitsSub`; production's change is one `AdmitsSub` field per
appended constructor and the literal field becoming the table's, reading); `cata_admits_extend`
(one `AdmitsExtend` field and one case per appended constructor, reading, not copied);
`infer_widens` (follows `infer`'s pairs; arms for record, tuple, reference and map or a refusal,
reading, not copied).

**Width (proved).** Refused inside a program; **under the named value the refusal is the
name-list inequality**: `record_width_refused` (`P4Check.lean:867`): a value is a member of two
all-required record types only when their canonical name lists are equal; `namedHasTy_names`
(`:840`): at an all-required type the accepted names are exactly the canonical names. Projected at
the boundary: `widthSub` (`P5Fits.lean:1749`, TypeScript's readonly rule) and `project`
(`:1768`), named: each declared field the value names is kept (projected), a declared optional
field the value lacks stays absent, the value's other names are dropped, the results placed by
`canonF`:

```lean
def project (v : Val) : Ty → Val
  | .record gs =>
    match recordParts? v with
    | some (ns, xs) =>
      .ctor 0 [.list ((canonF (projectNamed ns xs gs)).filterMap fun e => e.2.map fun _ => .str e.1),
        .list ((canonF (projectNamed ns xs gs)).filterMap fun e => e.2)]
    | none => v
  | _ => v
-- projectNamed ns xs ((n, _, t) :: rest) = (n, (lookupName n ns xs).map (project · t)) :: …
theorem fits_project (w : World) : ∀ (b a : Ty) (v : Val), widthSub a b = true → Fits w v a →
    Fits w (project v b) b
```

(`fits_project`, `:1932`, proved.) The projection reads the value by name (`lookupName`, `:1742`)
and the source type only through the relation: type-blind on the value, as row 165 argues for the
evaluator and the readers. Red control (proved): `named_width_refused` (`:2002`): the relation
holds, the value fits the wider record, is no member of the narrower one, and its projection is.
Under the positional clause the same four facts were unsoundness (`positional_width_unsound`,
`1b069d15`); under the named one they are a refusal. Bound: the projection recurses through
record fields only; under `list`, `option` and the other heads the relation is `sub`.

## Question 4. The other variable-arity forms

**(a) Optional keys (proved).** The field list carries the flag from the first commit:
`record (fields : List (String × Bool × Ty))` (`P2Ty.lean:71`). Under the named value, **the absent
field is absent from both lists**, and the canonical read becomes a merge instead of a zip: one
pass over the canonical checkers, deterministic because the names are strictly ascending
(`namedHasTy_absent`, `P4Check.lean:906`; `namedFit_skip`, `P5Fits.lean:1874`, the step that needs
the remaining names distinct, which canonical order gives). The value of a type with a given set
of present fields is unique (the canonical names in order), so exactness is kept; `hasTy_normalize`'s
record case is unchanged; `sub` stays a fold with no new case (the flag is part of the head). No
`Val` constructor is needed and no slot wrapper: the positional clause needed `none`/`some x` in
the slot because it could not omit a position (`1b069d15`). **A finding**: under the named value,
required-below-optional is membership-sound (`record_required_below_optional`, `:927`; the general
fact is `namedHasTy_mono`'s flag implication, `:387`), which TypeScript also allows; the copy keeps
flags exact in `sub` because admitting it turns the record head from an equality into an order,
which `sub_eq_args`'s `sameHead && argsBelow` shape does not have (a decision, below). The
absent-versus-`undefined` policy: `optionalKey` (absent or a value) is the clause above;
`optional` (`optionalKey(UndefinedOr(S))`) is the same clause at a field type `union t undefined`,
so it needs nothing new in the judgment (assumed: the codec's three-state slot is row 157/160's).

**(b) Keyed maps (proved).** `map (key value : Ty)`; a value is `list [pair k₁ v₁, …]`, keys
strictly ascending in the admitted key order (`keyLt`, `P4Check.lean:100`: strings by UTF-8 bytes,
naturals numerically), every key and value fitting; admitted key types `string` and `nat`
(`mapKeyOk`, `P2Ty.lean:1236`), a literal key being a record's property (rc.112's
`SchemaAST.record`, reading); `sub` exact in the key, covariant in the value; inhabited by the empty
map. Every law has a map case (questions 2, 3, 6).

**(c) Tagged unions of records (proved, `P7Tagged.lean`).** No constructor: a `union` of records
each with a required `_tag` at a literal. The tag decision's record arm reads the tag **by name**
(`nameTag?`, `:119`; `tagHit`, `:125`; `tagPayload?`, `:193`); `fits_tagged_name` (`:48`): a tagged
record's value names its tag; `tagged_disjoint` (`:89`) at the plain byte order;
`tagHit_of_isTagged` (`:131`), `diffTag_sound` (`:160`), `payload_hasTy` (`:201`, a record's
payload is the whole record). The positional clause needed the discriminant-first key
(`tag_head`, `056ca30b`) because `"X" < "_tag"` moved the tag's slot; that red control is kept with
the positional reader defined locally (`bytes_order_ambiguous`, `:351`) beside its named
counterpart (`named_tag_disjoint`, `:358`). **The exception to non-distribution**: a required field
whose type is a union, first in canonical order, splits membership-exactly (`fits_field_split`,
`:290`, at any name, `_tag` included); the tag decision refuses such a column (`taggedColumn`), so
a `_tag` union is refused at the decision or split by a normalization that would keep
`hasTy_normalize` (an option, not landed). The general position (a union field in the middle) is
the same merge argument (assumed, not proved).

**T's other forms on the same copy.** `tuple` (proved: every law above has its case;
`tuple [a, b]` normalizes to `prod a b`, `Normal`'s tuple clause requiring arity ≠ 2).
`app` (proved with invariant arguments: `app n []` normalizes to `handle n`, membership opaque by
name; **obstacle for declared variances**: the variance of an argument depends on the reference's
*name*, so `TyView.args (.app n ts)` and `sub`'s app arm must read a per-name table
`variancesOf : String → List Variance`, generated from rc.112's declarations beside
`variances.json`; every law goes through `argsBelow`, generic in the variance list, so the
obstacle is the table's home, not a proof; assumed, not re-proved here). `null`, `undefined`,
`number`, `bytes`, `int` inhabited: leaves (proved; images assumed, above).

## Question 5. Exactness today (row 128; the data wave's commit 1)

Both theorems hold **by construction** on today's `Ty` (no guard, no re-encoding): the repairs are
in the readers, and the theorems are inductions over the readers' own principles.

**The JSON pair (proved, `P8Codec.lean`).**

- `N_J` (`normJ`, `:47`): every object's entries sorted by key bytes, stable (`sortE`, `:42`),
  recursively; arrays element-wise. `sortE_perm` (`:90`): the sort is a permutation.
- The repair, one arm of `decodeRaw` (`decodeRawC`, `:408`): `match (decodeRaw a j).filter (hasTy ·
  a) with | some v => some v | none => (decodeRaw b j).filter (fun v => hasTy v b && !hasTy v a)`,
  the second branch only for a value the encoder sends there (seat S's arm, the same text).
- **The decoder reads `N_J`'s quotient** (`decodeRawC_normJ`, `:487`, every arm including the
  cause, reason, defect and error decoders): `fields?` and `payload?` commute with `N_J`
  (`fields?_normJ`, `:155`, through the sort's permutation and the singleton-filter lemma).
- **Exactness** (`decodeRawC_exact`, `:851`): `decodeRawC t j = some v → ∃ j', encodeRaw t v =
  some j' ∧ normJ j' = normJ j`, every arm; at the checked pair, with `encodeC`/`decodeC` the
  production `encode`/`decode` reading back through `decodeRawC`:

```lean
theorem encodeC_of_decodeC {t : Ty} {j : Json} {v : Val} (h : decodeC t j = some v) :
    ∃ j', encodeC t v = some j' ∧ normJ j' = normJ j
theorem decodeC_of_encodeC {t : Ty} {v : Val} {j : Json} (h : encodeC t v = some j) :
    decodeC t j = some v
theorem decodeC_iff {t : Ty} {j : Json} {v : Val} :
    decodeC t j = some v ↔ ∃ j', encodeC t v = some j' ∧ normJ j' = normJ j
```

  (`:1053`, `:1071`, `:1088`; all `[propext, Quot.sound]`.) The decoder is the inverse of the
  encoder modulo `N_J`, both ways.
- **Red control (proved)**, `codec_not_exact` (`:1108`): today's `decode` at
  `union (except nat nat) (exitOf nat nat)` reads `{"_tag":"Success","value":1}` and
  `{"_tag":"Failure","failure":1}` as one value, which `encode` writes as the second; the first is
  not the image modulo `N_J`. `repaired_refuses` (`:1116`): the repaired decoder refuses it.
- Not proved: that the repaired and today's encoders have the same domain (they agree on the
  control; the repaired decoder can answer differently from today's only on JSON today's reads at
  a non-canonical branch).

**The schema pair (proved, `P8Schema.lean`).**

- `N_S` (`normS`, `:76`) is a **fold**, `cata_representation normSAlg` (`:49`), rebuilding every
  node with `normAnn` of its annotations (`:40`): the entries that do not change decoding dropped,
  an empty bag `none`. The annotation policy is a parameter: the proofs read only
  `normAnn none = none` and the reader's guard. The copy's policy is the synthesis's (NS1:
  `parseOptions` and `identifier` change decoding, `decodingKey`, `:37`, assumed complete); seat S's
  allowlist (eight documentation keys erased, every other key refused) instantiates the same
  `normAnn` and the same proofs.
- The repairs (`ofSchemaC`, `:89`): **whole checks** (`checks = [isIntCheck, nonNegativeCheck]`,
  `[isIntCheck]`); the **type-parameter** declaration refused by id; a **decoding annotation**
  refused at every node it reads, by a guard first in each arm; and one the synthesis did not list:
  **the defect slot's annotations** (today's `isDefect` ignores them, so a decoding annotation there
  was read as absent; `isDefectC`, `:81`).
- **Exactness** (`ofSchemaC_exact`, `:411`, by `fun_induction ofSchemaC`, 39 cases from the
  reader's own principle; the refusing ones close by `nomatch`) and the retraction:

```lean
theorem ofSchemaC_exact (r : Representation) : ∀ t, ofSchemaC r = some t → normS r = schema t
theorem ofSchemaC_exact' {r : Representation} {t : Ty} (h : ofSchemaC r = some t) :
    normS r = normS (schema t)
theorem normS_schema (t : Ty) : normS (schema t) = schema t
theorem ofSchemaC_schema (t : Ty) (h : t.closed = true) (hr : reservedFree t = true) :
    ofSchemaC (schema t) = some t
```

  (`:411`, `:522`, `:270`, `:337`.) The retraction gains one premise: no handle target is
  `effect/schema/TypeParameter` (`reservedFree`, `:328`), which formation should refuse (S's
  `schemaWf` carries it).
- **Red controls (proved)**: `ofSchema_reads_check_ids` (`:170`, "number ≥ 5" read as `nat`);
  `ofSchema_reads_typeParameter` (`:176`, `schema (var 0)` read as a handle, and `var 0`, `var 1`
  sharing one schema); `ofSchema_drops_parseOptions` (`:186`). `ofSchemaC_refuses` (`:193`) refuses
  all three and reads a `title` annotation through.

**Against seat S** (reading `S/note.md` §1.1, §1.4): S proved route (a), the guarded readers
(`ofSchemaExact`, `decodeExact`, one re-encoding per read), and tested route (b) on 23 inputs,
recording it as owed. The two proofs here are route (b) at today's forms; the canonical-branch arm
and the `N_J` sort are the same; S's `N_S` erases every bag and flattens an `anyOf` spine (for its
n-ary reader), this one erases the non-decoding entries and reads binary unions (today's reader);
both statements are at the bridge level.

## Question 6. Inhabitance at the new forms (proved, `P6Inhabited.lean`)

`inhabited` (`:35`) is a fold with the record arm on the canonical fields (one Boolean per written
field through `inhabitedFields`, sorted by `canonF`: a field is optional or its type inhabited),
`map` always, `tuple` when every item is, `app` always (a handle at any target), `int`, `number`,
`null`, `undefined`, `bytes` true. `inhabited_iff_fits` (`:461`): `inhabited t = true ↔ ∃ w v,
Fits w v t` at every type of the copy, sound by `namedFit_inhabited` (`:92`), complete by one world
threaded through the fields with fresh keys (`namedFit_fresh`, `:309`: an optional field is left
out of both lists, a required one gets a witness in the grown world; `itemsFit_fresh`, `:347`).
`inhabited_normalize` (`:470`). Controls: `record [(a, never)]` is empty in every world and the
column check refuses it (`neverField_empty`, `admitColumn_neverField`); `record []` is inhabited by
`ctor 0 [list [], list []]` (`emptyRecord_fits`); an optional field at `never` does not empty the
record (`optionalNever_fits`); `raw_fold_disagrees` (`:511`): a fold over the written fields
disagrees with membership at a raw repeated name, the canonical one agrees (Codex's
`RawDuplicates`, named).

## The named clause against the positional one: cost (measured)

`P/probes/measure.py named` (output in `logs/measure.log`, totals by `sum.py` in `logs/sum.log`):
the 23 judgment-side declarations that differ cost **358 lines positional, 522 named (+164)**. The
read itself is three lines longer; most of the difference is the merge's lemmas (lookup by name
+17, a required field present +26, an assembled value fits +21, the absent-field skip +9) and the
named monotonicity (+14, which also carries the flag implication). Lines saved: the optional slot's
wrapper (−1), the growth law (−3), `hasTy_normalize_record` and `fits_normalize_record` (−2 each),
the discriminant-first slot (−13: no longer needed). What the extra lines buy (proved): an untyped
lookup that the projection, the tag test and (row 165) the evaluator share; width refused by the
names; tagged records disjoint at the plain order; required-below-optional sound.

## Production obligations (measured on the copy)

`python3 P/probes/measure.py prod` (`logs/measure.log`); a line count is the declaration without its
docstring; "gen." is a generated declaration (its generator changes, not a hand edit).

| production declaration | today (`bff50631`) | lines | on the copy | lines | change | what changes |
| --- | --- | --- | --- | --- | --- | --- |
| `Ty` | `Ty.lean:37` | 39 | `P2Ty.lean:48` | 40 | +1 | eight constructors appended |
| `Ty.key` | `Ty.lean:146` | 21 | `P2Ty.lean:143` | 29 | +8 | arms; companions over the lists |
| `Ty.renderRaw` | `Ty.lean:95` | 23 | `P2Ty.lean:610` | 32 | +9 | arms |
| `Ty.members` | `Ty.lean:120` | 21 | `P2Ty.lean:457` | 29 | +8 | arms |
| `Ty.closed` | `Ty.lean:200` | 6 | `P2Ty.lean:548` | 9 | +3 | arms |
| `Ty.isMember` | `Ty.lean:403` | 6 | `P2Ty.lean:503` | 7 | +1 | arms |
| `Ty.sub` | `Ty.lean:437` | 20 | `P2Ty.lean:737` | 38 | +18 | the table's line; four congruence arms; `.lit _, .string` removed |
| `Ty.instantiate` | `Ty.lean:474` | 21 | `P2Ty.lean:570` | 29 | +8 | arms |
| `Ty.normalize` | `Ty.lean:607` | 22 | `P2Ty.lean:830` | 32 | +10 | record via `canonF`; pair tuple; `app t []` |
| `Ty.Normal` | `Ty.lean:631` | 25 | `P2Ty.lean:904` | 34 | +9 | clauses |
| `normal_normalize` | `Ty.lean:677` | 38 | `P2Ty.lean:967` | 86 | +48 | cases |
| `sub_union_right` | `Ty.lean:816` | 9 | `P2Ty.lean:1167` | 11 | +2 | the table's line |
| `sub_lit_string` | `Ty.lean:831` | 5 | `P2Ty.lean:1185` | 3 | −2 | one line: `sub_of_leafRule rfl` |
| `sub_unknown` | `Ty.lean:767` | 4 | `P2Ty.lean:1190` | 13 | +9 | the table's line |
| `TyView.args` (gen.) | `TyView.lean:34` | 21 | `P3View.lean:49` | 29 | +8 | list heads |
| `TyView.sameHead` (gen.) | `TyView.lean:57` | 22 | `P3View.lean:80` | 29 | +7 | canonical heads, arity, name |
| `litRule` → the table (gen.) | `TyView.lean:82` | 3 | `P2Ty.lean:693` | 5 | +2 | data, in the core |
| `sameHead_trans` (gen.) | `TyView.lean:158` | 3 | `P3View.lean:136` | 3 | 0 | none |
| `eq_of_sameHead` (gen.) | `TyView.lean:174` | 3 | `P3View.lean:185` | 36 | +33 | conclusion `canonHead a = canonHead b`; production's is one `aesop` |
| `sub_eq_false_of_not_sameHead` (gen.) | `TyView.lean:275` | 13 | `P3View.lean:401` | 21 | +8 | `hleaf`; case list |
| `sub_eq_argsBelow_of_sameHead` (gen.) | `TyView.lean:291` | 36 | `P3View.lean:424` | 44 | +8 | cases |
| `sub_eq_args` (gen.) | `TyView.lean:333` | 8 | `P3View.lean:472` | 8 | 0 | hypothesis name |
| `argsBelow_antisymm` (gen.) | `TyView.lean:493` | 7 | `P3View.lean:626` | 7 | 0 | conclusion through `canonHead` |
| `sub_trans_core` | `TypeAlgebra.lean:40` | 75 | `P4Algebra.lean:44` | 74 | −1 | the table's lemmas |
| `sub_antisymm_normal` | `TypeAlgebra.lean:618` | 86 | `P4Algebra.lean:286` | 87 | +1 | `Normal.canonHead`; no `try` |
| `sub_normalize_of_sub` | `TypeAlgebra.lean:883` | 146 | `P4Algebra.lean:592` | 202 | +56 | four cases; `sub_args_*` |
| `normal_args` | `TypeAlgebra.lean:600` | 17 | `P4Algebra.lean:242` | 32 | +15 | list heads |
| `normal_members` | `TypeAlgebra.lean:546` | 7 | `P4Algebra.lean:197` | 14 | +7 | rewritten without `try` |
| `sub_member_right_iff` | `TypeAlgebra.lean:508` | 16 | `P4Algebra.lean:156` | 17 | +1 | rewritten without `simp_all` |
| `hasTy_normalize` and its named cases | 10 decl., `TypeAlgebra.lean` | 94 | 5 decl., `P4Check.lean` | 109 | +15 | record, tuple, app cases |
| `Val.hasTy` | `Typed.lean:34` | 68 | `P4Check.lean:148` | 76 | +8 | the named record arm; T's arms |
| `cata_admits_sub` | `Admits.lean:36` | 62 | (`hasTy_sub`, `P4Check.lean:467`) | 143 | n/a | `AdmitsSub` fields; the copy proves `hasTy_sub` directly |
| `Fits` | `Membership.lean:87` | 62 | `P5Fits.lean:145` | 75 | +13 | arms (I2's form) |
| `fits_hasTy` | `Membership.lean:269` | 151 | `P5Fits.lean:390` | 188 | +37 | one arm each |
| `fits_live` | `Membership.lean:520` | 127 | `P5Fits.lean:746` | 178 | +51 | one arm each |
| `fits_map` | `Membership.lean:729` | 98 | `P5Fits.lean:1042` | 134 | +36 | one arm each |
| `fits_sub` | `Membership.lean:837` | 103 | `P5Fits.lean:1232` | 157 | +54 | the table; four cases |
| `isTagged`, `payloadOf` | `Ty.lean:774`, `:798` | 3, 3 | `P7Tagged.lean:109`, `:172` | 4, 4 | +1, +1 | the record arm |
| `decodeRaw` | `Codec.lean:181` | 33 | `P8Codec.lean:408` | 34 | +1 | the canonical branch |
| `ofSchema` | `Bridge.lean:79` | 57 | `P8Schema.lean:89` | 72 | +15 | whole checks; `TypeParameter`; guards |
| `ofSchema_schema` | `Bridge.lean:140` | 62 | `P8Schema.lean:337` | 69 | +7 | `reservedFree` premise |
| the leaf rule's laws (gen.) | 4 decl., `TyView.lean` | 20 | 20 decl., `P3View.lean` | 119 | +99 | the table's closure, acyclicity, inversions |

Totals of the per-declaration rows (`logs/sum.log`): 1564 lines today, 2193 on the copy (+629).
New declarations with no production counterpart (not in the totals): the keyed canonical order
(question 1, `P1FieldOrder.lean`), the named read and its lemmas, the projection, `N_J`/`N_S` and
the exactness proofs. Counts are of the copy, not of a patch.

## Proposed statements (exact Lean text, on the copy)

- **`canon`**: `canonBy (key : String → List Nat) (fs : List (String × β)) := fs.foldl (fun acc p
  => insertBy key p acc) []`, with `canonF := canonBy bytesKey` (`P1FieldOrder.lean:129`).
- **`Fits`'s record arm** (`P5Fits.lean:145`): `| .record fs => match recordParts? v with
  | some (ns, xs) => NamedFit (canonF (fitters w fs)) ns xs | none => False`.
- **`Val.hasTy`'s record arm** (`P4Check.lean:148`): `| .record fs => match recordParts? v with
  | some (ns, xs) => namedHasTy (canonF (checkers fs allocated)) ns xs | none => false`.
- **`sub`'s record arm and the table**: as quoted in question 3.
- **`hasTy_normalize`'s record case**: `theorem hasTy_normalize_record (fs) (v) (al) (ih : ∀ p ∈ fs,
  ∀ v, hasTy v (normalize p.2.2) al = hasTy v p.2.2 al) : hasTy v (normalize (.record fs)) al =
  hasTy v (.record fs) al` (`P4Check.lean:709`).
- **The exact-subtyping law, named** (`fits_sub`'s record case, `P5Fits.lean:1232`, through
  `namedFit_mono`): the names of `canonF fs` equal those of `canonF gs`, flags equal, values
  pointwise below; and width refused: `theorem record_width_refused (v) (fs gs) (al) (hf : ∀ p ∈ fs,
  p.2.1 = false) (hg : ∀ p ∈ gs, p.2.1 = false) (hvf : hasTy v (.record fs) al = true) (hvg : hasTy
  v (.record gs) al = true) : (canonF fs).map Prod.fst = (canonF gs).map Prod.fst`.
- **`record_sub_not_complete`** (`P4Check.lean:980`): `(∀ v al, hasTy v recordOfUnion al = hasTy v
  unionOfRecords al) ∧ sub unionOfRecords recordOfUnion = true ∧ sub recordOfUnion unionOfRecords =
  false`.
- **The boundary projection**: `project`, `fits_project`, as quoted in question 3.
- **Row 128**: `decodeC_iff` and `ofSchemaC_exact'` with their retractions, as quoted in question 5.

## Decisions rows to amend (proposed; the coordinator writes the register)

- **Row 119** (records): add "a record's field list carries the optional flag (row 157); the
  canonical read of the named value (row 165) is a merge over the canonical fields, an absent
  optional field absent from both lists (seat P: `namedHasTy`, proved); width is refused by the
  name list (`record_width_refused`) and projected at the boundary by name (`fits_project`); the
  discriminant-first key order is not needed (`tagged_disjoint` at the byte order); the three proved
  facts and exact subtyping unchanged".
- **Row 125** (maps): add "value `list [pair k v, …]`, keys strictly ascending in `keyLt`
  (strings by UTF-8 bytes, naturals numerically), key types `string`, `nat`; `sub` exact in the key,
  covariant in the value; every law re-proved on seat P's copy".
- **Row 128** (exactness): add "proved by construction at today's forms (seat P): the JSON pair
  with the canonical-branch arm is exact modulo `N_J` both ways (`decodeC_iff`); the schema reader
  with whole checks, the `TypeParameter` refusal and a decoding-annotation guard at every node it
  reads, the defect slot included, is exact modulo `N_S`, a fold (`ofSchemaC_exact'`); route (a)'s
  guard is not needed".
- **Row 121** (`int`, numbers): add a constraint, "the order's edges `nat ⊑ int ⊑ number` are
  membership inclusions only if the images nest: the signed frame holds the negative integers only
  (a non-negative integer is its `nat` image) and the binary64 frame holds only doubles that are not
  integers in the integer image (seat P: `hasTy_leafEdge`; red control
  `generated_int_image_breaks_tower`); one value, one image, so the codec stays exact".
- **Row 157** (optional keys): add "under row 165 (a) the absent field is absent from both lists;
  no slot wrapper and no new `Val` frame; required-below-optional is membership-sound (proved) and
  left out of `sub` by default (new row below)".
- **Row 158** (`app`): add "declared variances need a per-name table `variancesOf` read by `sub`'s
  arm and `TyView.args`; the laws are generic in the variance list (assumed); invariant until the
  table exists".
- **New row (the leaf-order table)**: "The order's cross-head rules are one table of declared edges
  on leaf heads (`leafEdges : List (LeafHead × LeafHead)`), closed reflexively and transitively and
  consulted by `sub` before its rows; its laws are decided over the finite head domain and
  regenerated with it; an edge costs one membership inclusion (`hasTy_leafEdge`) and requires the
  table to stay acyclic (`leafLe_antisymm`)". Recommended.
- **New row (required-below-optional)**: (a) keep flags exact in `sub` (today's copy); (b) admit
  `{a: T} ⊑ {a?: T}`, sound under the named value, with the record head an order (names equal,
  flags `≤`) and `sub_eq_args` restated with a head order. Recommended (a) for the wave, (b) when
  row 68's lane meets the pair.
- **New row (the annotation policy of `N_S`)**: one policy shared by `N_S` and the reader's guard,
  seat S's allowlist (eight documentation keys erased, every other key refused) or the synthesis's
  denylist (`parseOptions`, `identifier` refused); the exactness proof is the same for either.
  Recommended: S's allowlist.

## Brief text

**For W1 (the data wave's commit 1; synthesis §7's commit 2), P's half:**

> Route (b) is proved on seat P's copy, at today's forms: take it, not the guard.
> 1. `Schema/Codec.lean`: `decodeRaw`'s union arm reads its second branch only for a value that is
>    not a member of the first (`P8Codec.lean:408`). `N_J` is `normJ` (`:47`): a stable sort of
>    every object's entries by key bytes, recursively.
> 2. `Laws/Schema/Codec.lean`: `decodeRaw_normJ` (`decodeRawC_normJ`, `:487`; its lemmas
>    `fields?_normJ`, `payload?_normJ` and the four sub-decoders' versions), `decodeRaw_exact`
>    (`:851`; `nat?_exact`, `fields?_two`, `payload?_exact`, `normJ_tagged_of_payload`, the
>    sub-decoders' exactness), then `encode_of_decode` and `decode_iff` (`:1053`, `:1088`) beside
>    `decode_of_encode`; the red control `codec_not_exact` (`:1108`) as a fixture.
> 3. `Schema/Bridge.lean`: `ofSchema` with whole checks, the `TypeParameter` refusal, the
>    annotation guard first in each arm and `isDefect` reading the defect slot's annotations
>    (`P8Schema.lean:89`); `N_S` the fold `normS` (`:76`) with the policy row's `normAnn`;
>    `ofSchema_exact` by `fun_induction ofSchema` (`:411`; 39 cases), `normS_schema`, the
>    retraction with `reservedFree` (or `schemaWf`). Red controls `:170`, `:176`, `:186`.
> 4. Every proof in `P8Codec.lean` and `P8Schema.lean` is `[propext, Quot.sound]`, uses no `try`,
>    `first` or `simp_all`, and states its `simp` as `simp only`; copy them, renaming `C`.

**For W2 (commit 2), the leaf-order table:**

> The table is `leafEdges` (`P2Ty.lean:693`) over `LeafHead` (`:666`), with `leafHead` (`:680`),
> `leafReach`/`leafLe` (`:700`, `:706`) and `leafRule` (`:710`), in the core because `sub` consults
> it (`:739`); the generator reads `Ty.leafEdges` from the environment and emits its laws
> (`P3View.lean:666-826`), each by `decide` over `LeafHead.all`, plus `leafHead_facts` per head;
> `litRule` and its three lemmas are deleted. `sub_eq_args` and the different-head theorem take
> `hleaf : leafRule a b = false` (`P3View.lean:401`, `:472`). Controls: the accepted cross-head case
> `sub .nat .number` with its rejected converse (`P2Ty.lean:1281-1283`) and the cyclic table
> (`:1285`). Membership's obligation is one lemma per edge (`hasTy_leafEdge`, W4's).

**For W4 (commit 4, the `Ty` append), P's half:**

> The laws, with their text on seat P's copy (`P/probes/P2Ty.lean` to `P7Tagged.lean`): `sub` with
> the table and the four congruence arms; `normalize` (record via `canonF`, `tuple [a, b]` to
> `prod`, `app t []` to `handle t`); `Normal` (record ascending, tuple arity ≠ 2, app args ≠ []);
> `sub_trans_core`, `sub_antisymm_normal` (through `Normal.canonHead`), `sub_normalize_of_sub`;
> `Val.hasTy` and `Fits` with the named record arm (`namedHasTy`/`NamedFit`), the map, tuple, app
> and leaf arms; `hasTy_sub`/`fits_sub` (the table's case by `hasTy_leafRule`), `hasTy_normalize`
> and `fits_normalize` with their record, tuple and app cases, `fits_hasTy`, `fits_live`,
> `fits_map`; `inhabited` and `inhabited_iff_fits`; the tag decision by name; `record_sub_not_complete`.
> The leaf images must nest (row 121's amendment). Red controls kept as fixtures:
> `eq_of_sameHead_raw_false`, `written_order_not_invariant`, `named_width_refused`,
> `bytes_order_ambiguous`, `raw_fold_disagrees`, `neverField_empty`,
> `generated_int_image_breaks_tower`, the cyclic table. Eight production proofs touched by the
> append use `try` or `simp_all` and are rewritten on the copy without them (the rule for a touched
> proof): `key_injective` (`P2Ty.lean:254`), `members_atom` (`:525`), `factors_isFactor`
> (`:790`), `factors_singleton` (`:804`), `sub_member_right_iff` (`P4Algebra.lean:156`),
> `normal_members` (`:197`), the `decreasing_by` of `sub_antisymm_normal` (`:286`), and
> `hasTy_members` (`P4Check.lean:627`).

## Receipt

**First, the one thing:** the laws hold on one copy with T's set, the named value and the leaf
table; the leaf images must nest (row 121); row 128's route (b) is proved at today's forms.

- **Base** `bff50631`; **head** the commit that adds this note (`git log -1` on `probe/P`); commits
  `ddccf289` (question 1), `1b069d15` (questions 2–3, positional), `8fa1247f` (question 6,
  positional), `056ca30b` (question 4(c), positional), `5ebb62cc` (T's set, the leaf table, the
  named value), `eb4c0e53` (question 5), then this note with the measuring scripts and logs.
- **Changed paths**: `docs/research/2026-10-01-type-language-probe/P/` only (`note.md`;
  `probes/P1FieldOrder.lean` … `P8Schema.lean`, `run.sh`, `measure.py`, `sum.py`; `probes/logs/`).
  No tracked file outside it; nothing pushed.
- **Commands and results**: `P/probes/run.sh` (all ten layers in order, each `exit=0`; logs in
  `P/probes/logs/`); `grep 'depends on axioms' P/probes/logs/*.log | grep -v '\[propext, Quot.sound\]$\|\[propext\]$\|\[Quot.sound\]$'`
  gives no line (196 axiom lines in all, none above the ceiling); `grep -nE
  'sorry|native_decide|simp_all|first \||\btry\b|\bpartial\b|\bunsafe\b|^axiom' P/probes/P*.lean`
  gives nine docstring lines only (each naming a production proof rewritten without `try` or
  `simp_all`); `python3 P/probes/measure.py all > P/probes/logs/measure.log`;
  `python3 P/probes/sum.py > P/probes/logs/sum.log`.
- **Axioms**: every theorem `[propext, Quot.sound]` or less; the one `Classical.choice` is the
  pinned red control `fieldBefore` (`P1FieldOrder.lean:677`, inside `#guard_msgs`).
- **Bounded or assumed**: T's leaf images (assumed stand-ins); declared variances for `app`
  (obstacle stated, not re-proved); a union field in the middle of a record (the split proved first
  in canonical order only); the projection recurses through record fields only; `decodingKey`'s set
  (the synthesis's, assumed complete); the repaired and today's encoders' domains (not proved
  equal); the production line counts are of the copy (`measure.py`), not of a patch; I2's
  `Membership.lean` read from a copy of `seat/I2`'s text, not this base.
- **Host-only**: none (no `bun`, `tsgo`, `node` or `dune` run by this seat).
- **Refused permissions**: none.
- **Proposed decisions rows and brief text**: the two sections above.
