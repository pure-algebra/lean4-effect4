import Effect4.Program.Config

/-!
# Config contract — the provider algebra and the reader, frozen

Plan: `docs/research/2026-09-04-production-standards-spike.md` §4 (the algebra) and §10 (the
six register rows and their pairs). The module under contract is
`src/Effect4/Program/Config.lean` (spiked as `docs/research/2026-09-05-workshop-config/Config.lean`).

Every obligation below is ascribed at its exact proposition and supplied by name with `@`, so
a declaration that keeps the frozen name but weakens the statement fails here
(`Test/Program/ProvisionContract.lean` is the model). The executable receipts are the six
register rows restated as `#guard`s beside their positive controls; a row whose witnesses do
not walk a `String` is *also* a theorem by `decide`, and a row that reaches the source through
`fromEnvRecord` or `configCase` stays a `#guard` on purpose — `String.toNat?`, `toUpper` and
`splitOn` reach `Classical.choice` on this toolchain, which is the whole reason `Scalars` is a
parameter (`src/Effect4/Program/Config.lean` §4). Never `native_decide`, never `sorry`.

The counterexample witnesses are restated here rather than imported: every one of them is
`private` in the module.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-CONF-CE-001` — `mapInput` is pre-composition on `load`. Refuted: the transform already on
  the provider runs first, so the two readings look up different paths.
* `E4-CONF-CE-002` — the flat env spelling resolves. Refuted: this model keeps the trie and
  drops rc.112's flat alias; the segmented spelling is the positive control.
* `E4-CONF-CE-003` — a `${}` reference cycle has a normal form. Refuted: refused at every fuel,
  where rc.112 diverges; an acyclic chain still expands.
* `E4-CONF-CE-004` — `orElse` is commutative. Refuted: two sources disagreeing at one path;
  associativity, idempotence and both units stand.
* `E4-CONF-CE-005` — a partially supplied group takes its default. Refuted: it is a failure
  carrying the group's evidence; forgetting both members takes the default.
* `E4-CONF-CE-006` — a later `nested` is the inner prefix, and is cased. Refuted: it is the
  outer prefix and it reaches the source uncased.
-/

set_option autoImplicit false

namespace Test.Program.ConfigContract

open Effect4
open Effect4.Program.Config

/-! ## C1 — the provider algebra

`Provider`, `load`, `mapInput`, `nested`, `orElse`: `src/Effect4/Program/Config.lean` §1. -/

section C1

#check (@Effect4.Program.Config.load_source :
  ∀ {Name : Type} (get : Lookup Name) (t : Path Name → Path Name) (p : Path Name),
    (Provider.source get t).load p = get (t p))

#check (@Effect4.Program.Config.load_make :
  ∀ {Name : Type} (get : Lookup Name) (p : Path Name), (Provider.make get).load p = get p)

#check (@Effect4.Program.Config.load_orElse :
  ∀ {Name : Type} (a b : Provider Name) (p : Path Name),
    (Provider.orElse a b).load p =
      match a.load p with
      | .ok (some n) => .ok (some n)
      | .ok none => b.load p
      | .error e => .error e)

#check (@Effect4.Program.Config.orElse_assoc :
  ∀ {Name : Type} (a b c : Provider Name),
    (Provider.orElse (Provider.orElse a b) c).load
      = (Provider.orElse a (Provider.orElse b c)).load)

#check (@Effect4.Program.Config.orElse_empty_left :
  ∀ {Name : Type} (p : Provider Name), (Provider.orElse Provider.empty p).load = p.load)

#check (@Effect4.Program.Config.orElse_empty_right :
  ∀ {Name : Type} (p : Provider Name), (Provider.orElse p Provider.empty).load = p.load)

#check (@Effect4.Program.Config.orElse_idem :
  ∀ {Name : Type} (p : Provider Name), (Provider.orElse p p).load = p.load)

#check (@Effect4.Program.Config.mapInput_mapInput :
  ∀ {Name : Type} (f g : Path Name → Path Name) (p : Provider Name),
    (p.mapInput g).mapInput f = p.mapInput (fun q => f (g q)))

#check (@Effect4.Program.Config.mapInput_id :
  ∀ {Name : Type} (p : Provider Name), p.mapInput id = p)

#check (@Effect4.Program.Config.mapInput_orElse :
  ∀ {Name : Type} (f : Path Name → Path Name) (a b : Provider Name),
    (Provider.orElse a b).mapInput f = Provider.orElse (a.mapInput f) (b.mapInput f))

#check (@Effect4.Program.Config.nested_nested :
  ∀ {Name : Type} (p : Provider Name) (q r : Path Name),
    (p.nested q).nested r = p.nested (r ++ q))

#check (@Effect4.Program.Config.load_mapInput_fresh :
  ∀ {Name : Type} (get : Lookup Name) (f : Path Name → Path Name) (p : Path Name),
    ((Provider.make get).mapInput f).load p = get (f p))

#check (@Effect4.Program.Config.load_nested_fresh :
  ∀ {Name : Type} (get : Lookup Name) (q p : Path Name),
    ((Provider.make get).nested q).load p = get (q ++ p))

#check (@Effect4.Program.Config.load_mapInput_orElse :
  ∀ {Name : Type} (f : Path Name → Path Name) (a b : Provider Name) (p : Path Name),
    ((Provider.orElse a b).mapInput f).load p
      = (Provider.orElse (a.mapInput f) (b.mapInput f)).load p)

end C1

/-! ## C2 — the reader

`eval`, its combinators, and the transfer law between the two `nested`s:
`src/Effect4/Program/Config.lean` §4. -/

section C2

#check (@Effect4.Program.Config.eval_withDefault_absent :
  ∀ {Name : Type} (S : Scalars) (c : ConfigTerm Name) (d : Val) (P : Provider Name)
    (q : Path Name) (e : ConfigError Name),
    eval S c P q = .ok (.absent e) → eval S (.withDefault c d) P q = .ok (.resolved d false))

#check (@Effect4.Program.Config.eval_withDefault_resolved :
  ∀ {Name : Type} (S : Scalars) (c : ConfigTerm Name) (d v : Val) (P : Provider Name)
    (q : Path Name) (hi : Bool),
    eval S c P q = .ok (.resolved v hi) → eval S (.withDefault c d) P q = .ok (.resolved v hi))

#check (@Effect4.Program.Config.eval_orElse_absent :
  ∀ {Name : Type} (S : Scalars) (c d : ConfigTerm Name) (P : Provider Name) (q : Path Name)
    (e : ConfigError Name),
    eval S c P q = .ok (.absent e) → eval S (.orElse c d) P q = eval S d P q)

#check (@Effect4.Program.Config.eval_orElse_failure :
  ∀ {Name : Type} (S : Scalars) (c d : ConfigTerm Name) (P : Provider Name) (q : Path Name)
    (f : Failure Name),
    eval S c P q = .error f → eval S (.orElse c d) P q = recover f (eval S d P q))

#check (@Effect4.Program.Config.recover_no_input :
  ∀ {Name : Type} (f : Failure Name) (y : Outcome Name), f.hasInput = false → recover f y = y)

#check (@Effect4.Program.Config.eval_option_absent :
  ∀ {Name : Type} (S : Scalars) (c : ConfigTerm Name) (P : Provider Name) (q : Path Name)
    (e : ConfigError Name),
    eval S c P q = .ok (.absent e) → eval S (.option c) P q = .ok (.resolved Val.none false))

#check (@Effect4.Program.Config.eval_nested :
  ∀ {Name : Type} (S : Scalars) (n : Name) (c : ConfigTerm Name) (P : Provider Name)
    (q : Path Name),
    eval S (.nested n c) P q = eval S c P (q ++ [Seg.key n]))

#check (@Effect4.Program.Config.eval_nested_transfer :
  ∀ {Name : Type} (S : Scalars) (get : Lookup Name) (q : Path Name)
    (c : ConfigTerm Name) (r : Path Name),
    reroot q (eval S c ((Provider.make get).nested q) r) = eval S c (Provider.make get) (q ++ r))

#check (@Effect4.Program.Config.eval_nested_eq_provider_nested :
  ∀ {Name : Type} (S : Scalars) (get : Lookup Name) (n : Name) (c : ConfigTerm Name),
    eval S (.nested n c) (Provider.make get) []
      = reroot [Seg.key n] (eval S c ((Provider.make get).nested [Seg.key n]) []))

end C2

/-! ## C3 — substitution

`Tmpl` and `expand`: `src/Effect4/Program/Config.lean` §5. -/

section C3

#check (@Effect4.Program.Config.expand_lit :
  ∀ {Name : Type} [DecidableEq Name] (fuel : Nat) (env : List (Name × Tmpl Name)) (s : String),
    expand fuel env (.lit s) = .ok s)

#check (@Effect4.Program.Config.expand_ref_self_refused :
  ∀ {Name : Type} [DecidableEq Name] (a : Name) (fuel : Nat),
    expand fuel [(a, Tmpl.ref a none)] (Tmpl.ref a none) = .error (.cycle a))

#check (@Effect4.Program.Config.expand_fuel_mono :
  ∀ {Name : Type} [DecidableEq Name] (n m : Nat) (env : List (Name × Tmpl Name))
    (t : Tmpl Name) (r : String),
    n ≤ m → expand n env t = .ok r → expand m env t = .ok r)

end C3

/-! ## C4 — the requirement row

`reads`, `provided`, `readsRow`, `providedRow`, `residual`:
`src/Effect4/Program/Config.lean` §6. -/

section C4

#check (@Effect4.Program.Config.absent_names_missing :
  ∀ {Name : Type} [DecidableEq Name] (S : Scalars) (render : Seg Name → String)
    (entries : List (Path Name × String)) (c : ConfigTerm Name) (q : Path Name)
    (e : ConfigError Name),
    eval S c (fromRecord render entries) q = .ok (.absent e) →
      ∃ p, p ∈ reads q c ∧ p ∉ provided entries)

#check (@Effect4.Program.Config.residual_empty_of_subset :
  ∀ {Name : Type} [DecidableEq Name] (table : List (Path Name)) (q : Path Name)
    (c : ConfigTerm Name) (entries : List (Path Name × String)),
    Row.Subset (readsRow table q c) (providedRow table entries) →
      residual table q c entries = Row.empty)

end C4

/-! ## The register rows

Each row is the module's pair of `#guard`s restated, a positive control beside it, and — where
the witnesses do not walk a `String` — the same pair as theorems by `decide`. -/

section Register

/-! ### `E4-CONF-CE-001` — `mapInput` is not pre-composition on `load`

The claim refuted: `(P.mapInput f).load = P.load ∘ f`, i.e. that a provider is a function of
the requested path. `makeSource(get, flow(transform, f))` (`ConfigProvider.ts:373`) runs the
transform already on the provider *first* and `f` second, so the source below — which answers
at `["b", "a"]` and nowhere else — is found by rc.112's reading and missed by the naive one.
The law that stands is `load_mapInput_fresh`: pre-composition is the special case of a *fresh*
source, whose transform is `id`. -/

private def ce001Get : Lookup String := fun p =>
  if p = [Seg.key "b", Seg.key "a"] then .ok (some (.value "hit")) else .ok none

private def ce001P : Provider String := .source ce001Get (fun p => Seg.key "a" :: p)

private def ce001F : Path String → Path String := fun p => Seg.key "b" :: p

-- E4-CONF-CE-001: rc.112 reads `get (f (t []))` = `get ["b", "a"]`.
#guard answerEq ((ce001P.mapInput ce001F).load []) (.ok (some (.value "hit")))
-- E4-CONF-CE-001: the pre-composition reading would read `get (t (f []))` = `get ["a", "b"]`.
#guard answerEq (ce001P.load (ce001F [])) (.ok none)

/-- `E4-CONF-CE-001`: the transform on the provider runs first. -/
theorem ce001_mapInput_is_post_composition :
    answerEq ((ce001P.mapInput ce001F).load []) (.ok (some (.value "hit"))) = true := by decide

/-- `E4-CONF-CE-001`: the pre-composition reading finds nothing at the same place. -/
theorem ce001_precomposition_reading_misses :
    answerEq (ce001P.load (ce001F [])) (.ok none) = true := by decide

/-- `E4-CONF-CE-001`, the positive control: on a fresh source the two readings agree, which is
`load_mapInput_fresh` at this witness. -/
theorem ce001_fresh_is_precomposition :
    answerEq (((Provider.make ce001Get).mapInput ce001F).load [Seg.key "a"])
      (.ok (some (.value "hit"))) = true := by decide

/-! ### `E4-CONF-CE-002` — the flat env spelling is the quotient this model takes

The claim refuted: an env-backed provider answers wherever rc.112 answers. rc.112 joins the
requested path with `_` before reading the record (`ConfigProvider.ts:1227`) *and* splits every
env name into the trie (`:1206-1207`), so `DATABASE_HOST` is found at both spellings; this
model keeps the tree and drops the flat alias. The law that stands is that every `ConfigTerm`
reaches a leaf through `prefix ++ [key name]` (`eval`, `reads`), so nothing in §4 can observe
the difference — the segmented spelling below is the positive control. -/

private def envDb : List (String × String) :=
  [("DATABASE_HOST", "localhost"), ("DATABASE_PORT", "5432"), ("A", ""),
   ("ITEMS_0", "a"), ("ITEMS_1", "b")]

-- E4-CONF-CE-002: rc.112 finds the value here as well; this model does not.
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE_HOST"]) (.ok none)
-- E4-CONF-CE-002, the positive control: the segmented spelling, which both agree on.
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE", Seg.key "HOST"])
  (.ok (some (.value "localhost")))
-- The trie the flat alias would have to duplicate: a record, an array, an empty value.
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE"])
  (.ok (some (.record ["HOST", "PORT"] none)))
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "ITEMS"]) (.ok (some (.array 2 none)))
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "A"]) (.ok none)

/-! ### `E4-CONF-CE-003` — a `${}` reference cycle has no normal form

The claim refuted: `interpolate` is a total rewriting to a string. rc.112 rewrites the
right-most `${VAR}` group and calls itself on the result (`ConfigProvider.ts:1396-1399`), which
on `A=${A}` and on the two-key cycle `A=${B}, B=${A}` exceeds a call depth of 2000 and throws.
The law that stands is `expand_ref_self_refused` — the self-reference is refused at *every*
fuel, so no amount of fuel turns the refusal into an answer — together with
`expand_fuel_mono`: more fuel never loses an answer, so the refusal is not impatience. -/

private def dotenv : List (String × Tmpl String) :=
  [("HOST", .lit "db"), ("PORT", .lit "5432"), ("B", .lit "x"), ("A", .ref "B" none),
   ("EMPTY", .lit "")]

private def expandIs (r : Except (Refusal String) String) (s : String) : Bool :=
  match r with
  | .ok t => t == s
  | .error _ => false

private def isRefused (r : Except (Refusal String) String) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

-- E4-CONF-CE-003: rc.112 diverges here; the model refuses.
#guard isRefused (expand 8 [("A", Tmpl.ref "A" none)] (Tmpl.ref "A" none))
-- E4-CONF-CE-003: and on the two-key cycle.
#guard isRefused (expand 8 [("A", Tmpl.ref "B" none), ("B", Tmpl.ref "A" none)]
  (Tmpl.ref "A" none))
-- E4-CONF-CE-003, the positive control: an acyclic chain still expands.
#guard expandIs (expand 8 dotenv (Tmpl.ref "A" none)) "x"

/-- `E4-CONF-CE-003`: the self-reference is refused. -/
theorem ce003_self_cycle_refused :
    isRefused (expand 8 [("A", Tmpl.ref "A" none)] (Tmpl.ref "A" none)) = true := by decide

/-- `E4-CONF-CE-003`: so is the two-key cycle. -/
theorem ce003_two_key_cycle_refused :
    isRefused (expand 8 [("A", Tmpl.ref "B" none), ("B", Tmpl.ref "A" none)]
      (Tmpl.ref "A" none)) = true := by decide

/-- `E4-CONF-CE-003`, the positive control: an acyclic chain has a normal form. -/
theorem ce003_acyclic_chain_expands :
    expandIs (expand 8 dotenv (Tmpl.ref "A" none)) "x" = true := by decide

/-! ### `E4-CONF-CE-004` — `orElse` is not commutative

The claim refuted: `orElse` is a commutative monoid on `load`, so the order of a provider stack
does not matter. `makeOrElse` returns the first *found* node (`ConfigProvider.ts:379-383`), and
the two sources below disagree at one path. The laws that stand are every other monoid law:
`orElse_assoc`, `orElse_idem`, `orElse_empty_left`, `orElse_empty_right` — witnessed below on
the same two operands. -/

private def ce004A : Provider String :=
  Provider.make (fun p => if p = [Seg.key "K"] then .ok (some (.value "a")) else .ok none)

private def ce004B : Provider String :=
  Provider.make (fun p => if p = [Seg.key "K"] then .ok (some (.value "b")) else .ok none)

-- E4-CONF-CE-004
#guard answerEq ((Provider.orElse ce004A ce004B).load [Seg.key "K"]) (.ok (some (.value "a")))
-- E4-CONF-CE-004
#guard answerEq ((Provider.orElse ce004B ce004A).load [Seg.key "K"]) (.ok (some (.value "b")))

/-- `E4-CONF-CE-004`: the left operand wins. -/
theorem ce004_left_wins :
    answerEq ((Provider.orElse ce004A ce004B).load [Seg.key "K"])
      (.ok (some (.value "a"))) = true := by decide

/-- `E4-CONF-CE-004`: swapping the operands changes the answer. -/
theorem ce004_swap_changes_the_answer :
    answerEq ((Provider.orElse ce004B ce004A).load [Seg.key "K"])
      (.ok (some (.value "b"))) = true := by decide

/-- `E4-CONF-CE-004`, the positive control: idempotence, `orElse_idem` at this witness. -/
theorem ce004_idempotent :
    answerEq ((Provider.orElse ce004A ce004A).load [Seg.key "K"])
      (ce004A.load [Seg.key "K"]) = true := by decide

/-- `E4-CONF-CE-004`, the positive control: `empty` is a unit on both sides,
`orElse_empty_left` and `orElse_empty_right` at this witness. -/
theorem ce004_empty_is_a_unit :
    answerEq ((Provider.orElse Provider.empty ce004B).load [Seg.key "K"])
        (.ok (some (.value "b"))) = true
      ∧ answerEq ((Provider.orElse ce004B Provider.empty).load [Seg.key "K"])
        (.ok (some (.value "b"))) = true := by decide

/-- `E4-CONF-CE-004`, the positive control: associativity, `orElse_assoc` at this witness. -/
theorem ce004_associative :
    answerEq ((Provider.orElse (Provider.orElse ce004A ce004B) ce004A).load [Seg.key "K"])
      ((Provider.orElse ce004A (Provider.orElse ce004B ce004A)).load [Seg.key "K"]) = true := by
  decide

/-! ### `E4-CONF-CE-005` — a partially supplied group is not defaulted

The claim refuted: `withDefault` over a group fires whenever the group did not produce a value,
so forgetting one member of a pair silently takes the default. `withDefault` replaces an
*absence* and not a failure (`Config.ts:847-852`), and a group one of whose members read input
while another is missing is a failure, not an absence (`Config.ts:674-675`, `:589-593`). The
law that stands is `eval_withDefault_absent` beside `eval_withDefault_resolved`: the default
fires exactly on `absent`, and forgetting *both* members is an absence — the positive control
below. -/

private def ce005Term : ConfigTerm String :=
  .withDefault (.zip (.string "host") (.string "port")) (.str "fallback")

-- E4-CONF-CE-005: one member supplied, one missing — a failure carrying the group's evidence.
#guard outcomeEq (eval stdScalars ce005Term (fromEnvRecord [("host", "db")]) [])
  (.error ⟨.missing [Seg.key "port"], true⟩)
-- E4-CONF-CE-005, the positive control: nothing supplied — the default, with no evidence.
#guard outcomeEq (eval stdScalars ce005Term (fromEnvRecord []) [])
  (.ok (.resolved (.str "fallback") false))
-- And the group resolves when both members are supplied.
#guard outcomeEq (eval stdScalars ce005Term (fromEnvRecord [("host", "db"), ("port", "p")]) [])
  (.ok (.resolved (.pair (.str "db") (.str "p")) true))
-- A found container with no co-located scalar is absent, not invalid (`Config.ts:1041`,
-- `:1211-1213`) — which is why `withDefault` fires on it.
#guard outcomeEq (eval stdScalars (.string "DATABASE") (fromEnvRecord envDb) [])
  (.ok (.absent (.missing [Seg.key "DATABASE"])))
#guard outcomeEq
  (eval stdScalars (.withDefault (.string "DATABASE") (.str "d")) (fromEnvRecord envDb) [])
  (.ok (.resolved (.str "d") false))

/-! ### `E4-CONF-CE-006` — a later `nested` is the outer prefix, and it is not cased

The claim refuted: `nested` names a path in the provider's own coordinates, so the order of
`nested` and `constantCase` does not matter. `nested` is `mapInput` with a prepended prefix
(`ConfigProvider.ts:883-886`), and `mapInput` post-composes (`:373`), so a `nested` applied
after `constantCase` prepends its prefix *outside* the casing and reaches the source uncased
(`:767-772`). Swapping the two combinators changes which env var is read. The law that stands
is `nested_nested`: `(p.nested q).nested r = p.nested (r ++ q)` — the later prefix is the outer
one, witnessed below on a source that walks no `String`. -/

private def ce006Env : List (String × String) :=
  [("app_HOST", "localhost"), ("APP_HOST", "prod")]

private def ce006Late : Provider String :=
  ((fromEnvRecord ce006Env).constantCase).nested [Seg.key "app"]

private def ce006Early : Provider String :=
  ((fromEnvRecord ce006Env).nested [Seg.key "APP"]).constantCase

-- E4-CONF-CE-006: the later `nested` is outer and uncased, so this reads `app_HOST`.
#guard answerEq (ce006Late.load [Seg.key "host"]) (.ok (some (.value "localhost")))
-- E4-CONF-CE-006: the earlier `nested` is inside the casing, so this reads `APP_HOST`.
#guard answerEq (ce006Early.load [Seg.key "host"]) (.ok (some (.value "prod")))

private def ce006Get : Lookup String := fun p =>
  if p = [Seg.key "a", Seg.key "b"] then .ok (some (.value "hit")) else .ok none

/-- `E4-CONF-CE-006`, the law that stands: the later `nested` is the outer prefix, so nesting
under `b` and then under `a` reads `["a", "b"]`. This is `nested_nested` at a witness. -/
theorem ce006_later_nested_is_outer :
    answerEq ((((Provider.make ce006Get).nested [Seg.key "b"]).nested [Seg.key "a"]).load [])
      (.ok (some (.value "hit"))) = true := by decide

/-- `E4-CONF-CE-006`: the reading in which the later `nested` were the inner prefix looks up
`["b", "a"]` and finds nothing. -/
theorem ce006_inner_prefix_reading_misses :
    answerEq ((((Provider.make ce006Get).nested [Seg.key "a"]).nested [Seg.key "b"]).load [])
      (.ok none) = true := by decide

end Register

/-! ## The residual receipt

The module's docs-style example: `DATABASE_HOST`, `DATABASE_PORT` and `OTEL_SERVICE_NAME`, the
last one defaulted. The evaluation succeeds either way — that is the point: only the residual
row says that the third path was never supplied, and it is `Row.empty` exactly when it was
(`residual_empty_of_subset`, frozen in C4). -/

section Residual

private def demoTable : List (Path String) :=
  [[Seg.key "DATABASE", Seg.key "HOST"],
   [Seg.key "DATABASE", Seg.key "PORT"],
   [Seg.key "OTEL", Seg.key "SERVICE", Seg.key "NAME"]]

private def demoTerm : ConfigTerm String :=
  .zip (.nested "DATABASE" (.zip (.string "HOST") (.nat "PORT")))
       (.withDefault (.nested "OTEL" (.nested "SERVICE" (.string "NAME"))) (.str "effect4"))

private def demoTwo : List (String × String) :=
  [("DATABASE_HOST", "localhost"), ("DATABASE_PORT", "5432")]

private def demoThree : List (String × String) :=
  ("OTEL_SERVICE_NAME", "checkout") :: demoTwo

private def entriesOf (env : List (String × String)) : List (Path String × String) :=
  env.map (fun kv => (splitUnderscore kv.1, kv.2))

-- The three paths the term may read are exactly the table.
#guard reads [] demoTerm == demoTable

#guard readsRow demoTable [] demoTerm == Row.normalize [keyOf 0, keyOf 1, keyOf 2]
-- Two provided: the residual is the third path's key.
#guard providedRow demoTable (entriesOf demoTwo) == Row.normalize [keyOf 0, keyOf 1]
#guard residual demoTable [] demoTerm (entriesOf demoTwo) == Row.normalize [keyOf 2]
-- All three provided: the residual is empty.
#guard providedRow demoTable (entriesOf demoThree) == Row.normalize [keyOf 0, keyOf 1, keyOf 2]
#guard residual demoTable [] demoTerm (entriesOf demoThree) == Row.empty

-- Both runs succeed, which is why the row is the only witness of what was missing.
#guard outcomeEq (eval stdScalars demoTerm (fromEnvRecord demoThree) [])
  (.ok (.resolved (.pair (.pair (.str "localhost") (.nat 5432)) (.str "checkout")) true))
#guard outcomeEq (eval stdScalars demoTerm (fromEnvRecord demoTwo) [])
  (.ok (.resolved (.pair (.pair (.str "localhost") (.nat 5432)) (.str "effect4")) true))

#check @Effect4.Program.Config.residual_empty_of_subset

end Residual

end Test.Program.ConfigContract
