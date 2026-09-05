import Effect4.Data.Row
import Effect4.Machine.Key

/-!
# Program.Config — configuration as a provider algebra, a reader, and a requirement row

Design: `docs/research/2026-09-04-production-standards-spike.md` §4 (the algebra) and §10 (the
lane's findings against the source); spiked as `workshop/Config/Config.lean`. The batteries
are `Test/Program/ConfigContract.lean` (the frozen statements and the six register rows
`E4-CONF-CE-001..006`) and `Test/Program/ConfigAxiomReport.lean`.

The rc.112 model of `ConfigProvider` (`vendor/effect-4.0.0-rc.112/src/ConfigProvider.ts`) and
`Config` (`.../Config.ts`), first-order and total. A provider is a *path transformer over a
source*, not a closure over a store: `makeSource(get, transform)` (`ConfigProvider.ts:367-375`)
keeps the two apart so that `mapInput` can post-compose the transform (`:373`) and `orElse`
can distribute it to both operands (`:384`). That is the whole reason the ordering laws of
§1 are true and the "obvious" ones (§2) are false.

Everything with a theorem attached is parametric in the name type `{Name : Type}`, and every
walk over a `String` is a supplied hook rather than an unfolded definition. `String.decEq`,
`BEq String` and `List.contains` are at the library's axiom ceiling on this toolchain, but
every function that *iterates* a `String` — `String.toNat?`, `toUpper`, `splitOn`, `toList`,
`length` — reaches `Classical.choice`, because the iteration is well-founded recursion over
`String.Pos`. So the scalar codecs live in `Scalars` (§4), which `eval` takes as a parameter
the way `Effect4/Program/Provision.lean` takes `LeafSem`: `stdScalars` is the rc.112
instantiation, it appears in the `#guard`s, and it appears in no theorem.

Three places where the model deliberately parts company with rc.112, each pinned below:

* **`SourceError` carries a path.** rc.112's carries `message` and an optional `cause`
  (`ConfigProvider.ts:207-210`) and no path; the path is added here so a source failure can
  be told apart from a `missing` at the same place. Nothing else depends on it.
* **A found container with no scalar value is `absent`, not a failure.** `hasProviderInput`
  is `getScalar(node) !== undefined` for every scalar schema (`Config.ts:1041`), and a decode
  failure with no input evidence becomes `Effect.succeed(absent(error))` (`Config.ts:1211-1213`).
  So `Config.string` over a `Record` node without a co-located value is *absent* — which is
  what makes `withDefault` fire on it. `primOf` reproduces exactly that.
* **The two `nested`s do not transfer on the nose.** `Config.nested` extends the *evaluator's*
  path prefix (`Config.ts:2050-2051`) and `ConfigProvider.nested` extends the *provider's*
  transform (`ConfigProvider.ts:883-886`). They agree on values and on input evidence, and
  they disagree on the path a `missing`/`invalid` error reports, because that path is the
  Config-level one (`Config.ts:1209`) and it knows nothing of the provider's prefix.
  `eval_nested_transfer` is therefore stated modulo `reroot`, and that is the true law.

| | |
| --- | --- |
| Carrier | `Provider Name` (a source with a path transform, closed under `orElse`); `ConfigTerm Name` |
| Operations | `load`, `mapInput`, `nested`, `orElse`; `eval`; `expand`; `reads`/`provided`/`residual` |
| Laws | `orElse` is an idempotent monoid on `load`; `mapInput` is a contravariant action; `eval` transfers across the two `nested`s modulo `reroot`; absence names an unprovided path |
| Structure | one constructor per rc.112 export the corpus uses; no closures except the source's own `get` and the scalar codecs |
| Payoff | the requirement row of a configuration: `residual` is empty exactly when every path the term may read is supplied, and `absent_names_missing` says a run that came back absent names one that was not |
| Anti-vacuity | six counterexample rows, `E4-CONF-CE-001..006`, each a pair of `#guard`s that would both have to change to fake the law |
-/

set_option autoImplicit false

namespace Effect4.Program.Config

open Effect4

/-! ## §1 Paths, nodes, providers

`Path` is rc.112's `Path` (`ConfigProvider.ts:212-230`): string segments name object keys,
numeric segments index arrays. `Node` is `ConfigProvider.ts:55-72`; its `keys` is a
`ReadonlySet<string>` there and a `List String` here, so this model orders what rc.112 does
not — no law below reads that order. -/

/-- One addressed step: an object key or an array index (`ConfigProvider.ts:212-215`). -/
inductive Seg (Name : Type) where
  /-- A named object key. -/
  | key (name : Name)
  /-- A numeric array index. -/
  | index (n : Nat)
deriving DecidableEq, Repr

/-- An ordered sequence of segments addressing a node (`ConfigProvider.ts:227`). -/
abbrev Path (Name : Type) := List (Seg Name)

/-- What a lookup finds: a scalar leaf, or a container that may carry a co-located scalar
(`ConfigProvider.ts:55-72`). `value : undefined` inside a found container means "this node
exists and has no scalar of its own", which is *not* the same as "no node here" (`:44-46`). -/
inductive Node where
  /-- A terminal string value (`ConfigProvider.ts:56-60`). -/
  | value (v : String)
  /-- An object; rc.112's `keys` is unordered (`ConfigProvider.ts:61-66`). -/
  | record (keys : List String) (value : Option String)
  /-- An array-like container of known length (`ConfigProvider.ts:67-72`). -/
  | array (length : Nat) (value : Option String)
deriving DecidableEq, Repr

/-- The co-located scalar of a node, i.e. rc.112's `getScalar` (`Config.ts:1041`). -/
def nodeValue : Node → Option String
  | .value v => some v
  | .record _ v => v
  | .array _ v => v

/-- A source that could not be read (`ConfigProvider.ts:207-210`). rc.112 carries `message`
and an optional `cause`; the path is this model's addition. -/
structure SourceError (Name : Type) where
  /-- Where the read was attempted. -/
  path : Path Name
  /-- What went wrong. -/
  message : String
deriving DecidableEq, Repr

/-- What a lookup answers: absence is `ok none`, failure is `error` (`ConfigProvider.ts:286`). -/
abbrev Answer (Name : Type) := Except (SourceError Name) (Option Node)

/-- The raw lookup a source is built from (`ConfigProvider.ts:368`). -/
abbrev Lookup (Name : Type) := Path Name → Answer Name

/-- Boolean equality on answers, so the `#guard`s below are closed `Bool` tests without
depending on whether core derives `DecidableEq` for `Except`. -/
def answerEq {Name : Type} [DecidableEq Name] : Answer Name → Answer Name → Bool
  | .ok a, .ok b => decide (a = b)
  | .error a, .error b => decide (a = b)
  | _, _ => false

/-- A provider is a source paired with its accumulated path transform, closed under `orElse`.
rc.112 keeps the pair apart for exactly one reason: `mapInput` must post-compose the transform
(`ConfigProvider.ts:373`) and `orElse` must push it into both operands (`:384`). -/
inductive Provider (Name : Type) where
  /-- `makeSource(get, transform)` (`ConfigProvider.ts:367-375`). -/
  | source (get : Lookup Name) (transform : Path Name → Path Name)
  /-- `makeOrElse(first, second)` (`ConfigProvider.ts:377-386`). -/
  | orElse (first second : Provider Name)

namespace Provider

/-- `make(get)` is a source with the identity transform (`ConfigProvider.ts:355`, `:389-402`). -/
def make {Name : Type} (get : Lookup Name) : Provider Name := .source get id

/-- The provider that finds nothing anywhere: the unit of `orElse`. -/
def empty {Name : Type} : Provider Name := .source (fun _ => .ok none) id

/-- `load` (`ConfigProvider.ts:286`, `:372`, `:379-383`): the transform runs, then the source;
`orElse` consults its fallback on absence only, and a `SourceError` propagates (`:498-499`). -/
def load {Name : Type} : Provider Name → Path Name → Answer Name
  | .source get t, p => get (t p)
  | .orElse a b, p =>
      match load a p with
      | .ok (some n) => .ok (some n)
      | .ok none => load b p
      | .error e => .error e

/-- `mapInput` (`ConfigProvider.ts:373`, `:384`, `:709-713`): `f` runs *after* the transform
already on the provider, and a composite distributes it to both operands. -/
def mapInput {Name : Type} (f : Path Name → Path Name) : Provider Name → Provider Name
  | .source get t => .source get (fun p => f (t p))
  | .orElse a b => .orElse (mapInput f a) (mapInput f b)

/-- `nested(prefix)` (`ConfigProvider.ts:883-886`): `mapInput` with a prepended prefix. -/
def nested {Name : Type} (pre : Path Name) (p : Provider Name) : Provider Name :=
  p.mapInput (fun q => pre ++ q)

end Provider

/-! ### The laws of §1 -/

section ProviderLaws

variable {Name : Type}

/-- A source loads by transforming and then reading. -/
theorem load_source (get : Lookup Name) (t : Path Name → Path Name) (p : Path Name) :
    (Provider.source get t).load p = get (t p) := rfl


/-- A fresh source loads at the requested path. -/
theorem load_make (get : Lookup Name) (p : Path Name) :
    (Provider.make get).load p = get p := rfl


/-- `orElse` consults its fallback exactly on absence (`ConfigProvider.ts:379-383`). -/
theorem load_orElse (a b : Provider Name) (p : Path Name) :
    (Provider.orElse a b).load p =
      match a.load p with
      | .ok (some n) => .ok (some n)
      | .ok none => b.load p
      | .error e => .error e := rfl


/-- `orElse` is associative on `load`. -/
theorem orElse_assoc (a b c : Provider Name) :
    (Provider.orElse (Provider.orElse a b) c).load
      = (Provider.orElse a (Provider.orElse b c)).load := by
  funext p
  simp only [Provider.load]
  cases ha : a.load p with
  | error e => rfl
  | ok na =>
    cases na with
    | some n => rfl
    | none =>
      cases hb : b.load p with
      | error e => rfl
      | ok nb => cases nb <;> rfl


/-- `empty` is a left unit for `orElse`. -/
theorem orElse_empty_left (p : Provider Name) :
    (Provider.orElse Provider.empty p).load = p.load := by
  funext q
  simp only [Provider.load, Provider.empty]


/-- `empty` is a right unit for `orElse`. -/
theorem orElse_empty_right (p : Provider Name) :
    (Provider.orElse p Provider.empty).load = p.load := by
  funext q
  simp only [Provider.load, Provider.empty]
  cases h : p.load q with
  | error e => rfl
  | ok n => cases n <;> rfl


/-- `orElse` is idempotent on `load`. -/
theorem orElse_idem (p : Provider Name) :
    (Provider.orElse p p).load = p.load := by
  funext q
  simp only [Provider.load]
  cases h : p.load q with
  | error e => rfl
  | ok n => cases n <;> rfl


/-- Transforms compose in application order: the later one runs outermost
(`ConfigProvider.ts:628-631`). -/
theorem mapInput_mapInput (f g : Path Name → Path Name) (p : Provider Name) :
    (p.mapInput g).mapInput f = p.mapInput (fun q => f (g q)) := by
  induction p with
  | source get t => rfl
  | orElse a b iha ihb => simp only [Provider.mapInput, iha, ihb]


/-- Transforming by the identity changes nothing. -/
theorem mapInput_id (p : Provider Name) : p.mapInput id = p := by
  induction p with
  | source get t => rfl
  | orElse a b iha ihb => simp only [Provider.mapInput, iha, ihb]


/-- A composite distributes a transform to both operands (`ConfigProvider.ts:384`). -/
theorem mapInput_orElse (f : Path Name → Path Name) (a b : Provider Name) :
    (Provider.orElse a b).mapInput f = Provider.orElse (a.mapInput f) (b.mapInput f) := rfl


/-- A later `nested` is the *outer* prefix (`ConfigProvider.ts:767-772`). -/
theorem nested_nested (p : Provider Name) (q r : Path Name) :
    (p.nested q).nested r = p.nested (r ++ q) := by
  simp only [Provider.nested, mapInput_mapInput, List.append_assoc]


/-- On a fresh source, `mapInput` is pre-composition — the special case that makes the
general rule look like something it is not (compare `E4-CONF-CE-001`). -/
theorem load_mapInput_fresh (get : Lookup Name) (f : Path Name → Path Name) (p : Path Name) :
    ((Provider.make get).mapInput f).load p = get (f p) := rfl


/-- On a fresh source, `nested` prepends its prefix to the requested path. -/
theorem load_nested_fresh (get : Lookup Name) (q p : Path Name) :
    ((Provider.make get).nested q).load p = get (q ++ p) := rfl


/-- Transforming a composite is transforming both operands. -/
theorem load_mapInput_orElse (f : Path Name → Path Name) (a b : Provider Name) (p : Path Name) :
    ((Provider.orElse a b).mapInput f).load p
      = (Provider.orElse (a.mapInput f) (b.mapInput f)).load p := rfl


end ProviderLaws

/-! ## §2 The counterexamples

Each row below is a pair of `#guard`s: one pinning what rc.112 does, one pinning the
plausible reading it refutes. -/

/-! ### `configCase` (`String.ts:1760-1761`)

`normalizeCase(self, CONFIG_SPLIT_REGEXP, [STRIP_REGEXP], "_", toUpperCase)`
(`String.ts:1628-1654`): insert a break at each `CONFIG_SPLIT_REGEXP` boundary
(`String.ts:1661` — `([a-z0-9])([A-Z])` and `([A-Z])([A-Z][a-z])`, so digit boundaries are
*not* split and `v2` survives, `String.ts:1753-1754`), collapse every run of non-word
characters (`String.ts:1664`), then upper-case each token and join with `_`. Both split
regexps consume their match, but neither can suppress a boundary the other would find, so
the character-pair test below is the same function. -/

private def isWordChar (c : Char) : Bool := c.isAlpha || c.isDigit

/-- The two `CONFIG_SPLIT_REGEXP` boundaries as a test on a character pair with one
character of lookahead (`String.ts:1661`). -/
private def splitsHere (prev cur : Char) (next : Option Char) : Bool :=
  ((prev.isLower || prev.isDigit) && cur.isUpper)
    || (prev.isUpper && cur.isUpper && (match next with | some n => n.isLower | none => false))

private def configTokens : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => if cur.isEmpty then acc.reverse else (cur.reverse :: acc).reverse
  | c :: rest, cur, acc =>
      if !isWordChar c then
        configTokens rest [] (if cur.isEmpty then acc else cur.reverse :: acc)
      else
        match cur with
        | [] => configTokens rest [c] acc
        | p :: _ =>
            if splitsHere p c rest.head? then configTokens rest [c] (cur.reverse :: acc)
            else configTokens rest (c :: cur) acc

/-- `Str.configCase` (`String.ts:1760-1761`), the casing `ConfigProvider.constantCase` uses. -/
def configCase (s : String) : String :=
  String.intercalate "_" ((configTokens s.toList [] []).map (fun t => (String.ofList t).toUpper))

#guard configCase "databaseHost" == "DATABASE_HOST"
#guard configCase "host" == "HOST"
#guard configCase "v2" == "V2"
-- `String.ts:1754` states this one outright.
#guard configCase "api-v2 xml" == "API_V2_XML"
#guard configCase "APIKey" == "API_KEY"

/-- Casing a path segment leaves numeric indices alone (`ConfigProvider.ts:749`). -/
def segCase : Seg String → Seg String
  | .key n => .key (configCase n)
  | .index i => .index i

/-- `constantCase` (`ConfigProvider.ts:748-750`): `mapInput` of `configCase` over segments. -/
def Provider.constantCase (p : Provider String) : Provider String :=
  p.mapInput (fun path => path.map segCase)

/-! ### `E4-CONF-CE-001` — `mapInput` is not pre-composition on `load`

`makeSource(get, flow(transform, f))` (`ConfigProvider.ts:373`) runs the *existing* transform
first and `f` second, so `(P.mapInput f).load p` is `get (f (t p))`, not `P.load (f p)`. The
source below answers at one path only; the two readings disagree there. -/

private def ce001Get : Lookup String := fun p =>
  if p = [Seg.key "b", Seg.key "a"] then .ok (some (.value "hit")) else .ok none

private def ce001P : Provider String := .source ce001Get (fun p => Seg.key "a" :: p)

private def ce001F : Path String → Path String := fun p => Seg.key "b" :: p

-- E4-CONF-CE-001: rc.112 reads `get (f (t []))` = `get ["b", "a"]`.
#guard answerEq ((ce001P.mapInput ce001F).load []) (.ok (some (.value "hit")))
-- E4-CONF-CE-001: the pre-composition reading would read `get (t (f []))` = `get ["a", "b"]`.
#guard answerEq (ce001P.load (ce001F [])) (.ok none)

/-! ### `E4-CONF-CE-004` — `orElse` is not commutative

`makeOrElse` returns the first *found* node (`ConfigProvider.ts:379-383`); the operands
below disagree at one path, so the two orders answer differently. `orElse` is associative,
idempotent and unital (§1) — every monoid law except this one. -/

private def ce004A : Provider String :=
  Provider.make (fun p => if p = [Seg.key "K"] then .ok (some (.value "a")) else .ok none)

private def ce004B : Provider String :=
  Provider.make (fun p => if p = [Seg.key "K"] then .ok (some (.value "b")) else .ok none)

-- E4-CONF-CE-004
#guard answerEq ((Provider.orElse ce004A ce004B).load [Seg.key "K"]) (.ok (some (.value "a")))
-- E4-CONF-CE-004
#guard answerEq ((Provider.orElse ce004B ce004A).load [Seg.key "K"]) (.ok (some (.value "b")))

/-! ## §3 Sources: an env record and a JSON-ish tree -/

/-- rc.112 counts the literal empty string as a missing value unless `preserveEmptyStrings`
(`ConfigProvider.ts:1089-1091`, `:1084-1087`). This model never preserves them. -/
def presentValue (v : String) : Option String :=
  if v = "" then none else some v

/-- The first entry at exactly `p` whose value is present. A JS record cannot repeat a key,
so this and "the first entry at `p`, then test its value" agree on every record rc.112 can
build; this spelling is the one that makes `absent_names_missing` true of a `List`. -/
def leafAt {Name : Type} [DecidableEq Name] :
    List (Path Name × String) → Path Name → Option String
  | [], _ => none
  | (q, v) :: rest, p =>
      if q = p then
        match presentValue v with
        | some w => some w
        | none => leafAt rest p
      else leafAt rest p

/-- The paths an entry list actually supplies a value for. -/
def provided {Name : Type} : List (Path Name × String) → List (Path Name)
  | [] => []
  | (q, v) :: rest =>
      match presentValue v with
      | some _ => q :: provided rest
      | none => provided rest

private def distinct {α : Type} [DecidableEq α] : List α → List α
  | [] => []
  | a :: as =>
      let r := distinct as
      if r.contains a then r else a :: r

/-- The segment by which `q` extends `p`, when it does — the trie step of
`trieNodeAt`/`buildEnvTrie` (`ConfigProvider.ts:1200-1217`, `:1246-1256`). -/
def nextSeg {Name : Type} [DecidableEq Name] : Path Name → Path Name → Option (Seg Name)
  | [], [] => none
  | [], s :: _ => some s
  | _ :: _, [] => none
  | a :: p, b :: q => if a = b then nextSeg p q else none

/-- The distinct immediate children of `p` (`ConfigProvider.ts:1230-1231`). -/
def childrenAt {Name : Type} [DecidableEq Name]
    (entries : List (Path Name × String)) (p : Path Name) : List (Seg Name) :=
  distinct (entries.filterMap (fun e => nextSeg p e.1))

/-- All children numeric, and their indices — rc.112's `NUMERIC_INDEX` test (`:1219`, `:1237`). -/
def indicesOf {Name : Type} : List (Seg Name) → Option (List Nat)
  | [] => some []
  | .index n :: rest => (indicesOf rest).map (fun ns => n :: ns)
  | .key _ :: _ => none

/-- `nodeAtEnv` (`ConfigProvider.ts:1221-1244`): no children is a leaf, all-numeric children
is an `Array` of length `max + 1`, otherwise a `Record`; either container carries the
co-located leaf value. `render` spells a child segment in the key set — a hook, because
`ConfigProvider.ts:1227` spells a numeric child with `String(seg)` and rendering a `Nat`
walks a `String`. -/
def nodeAt {Name : Type} [DecidableEq Name] (render : Seg Name → String)
    (entries : List (Path Name × String)) (p : Path Name) : Option Node :=
  match childrenAt entries p with
  | [] => (leafAt entries p).map Node.value
  | c :: cs =>
      match indicesOf (c :: cs) with
      | some ns => some (.array (ns.foldl Nat.max 0 + 1) (leafAt entries p))
      | none => some (.record ((c :: cs).map render) (leafAt entries p))

/-- A provider backed by an explicit list of `(path, value)` entries. -/
def fromRecord {Name : Type} [DecidableEq Name] (render : Seg Name → String)
    (entries : List (Path Name × String)) : Provider Name :=
  Provider.make (fun p => .ok (nodeAt render entries p))

/-- How a child segment is spelled in a `Record` node's key set: `path.map(String)`
(`ConfigProvider.ts:1227`). -/
def segName : Seg String → String
  | .key n => n
  | .index i => toString i

/-- A segment of an env var name: a canonically spelled number is an index (`:1219`). -/
def segOfString (s : String) : Seg String :=
  match s.toNat? with
  | some n => if s = toString n then .index n else .key s
  | none => .key s

/-- Split an env var name on `_`, keeping empty segments (`ConfigProvider.ts:1206-1207`). -/
def splitUnderscore (s : String) : Path String :=
  (s.splitOn "_").map segOfString

/-- `fromEnvRecord` (`ConfigProvider.ts:1121-1128`). -/
def fromEnvRecord (env : List (String × String)) : Provider String :=
  fromRecord segName (env.map (fun kv => (splitUnderscore kv.1, kv.2)))

private def envDb : List (String × String) :=
  [("DATABASE_HOST", "localhost"), ("DATABASE_PORT", "5432"), ("A", ""),
   ("ITEMS_0", "a"), ("ITEMS_1", "b")]

#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE", Seg.key "HOST"])
  (.ok (some (.value "localhost")))
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE"])
  (.ok (some (.record ["HOST", "PORT"] none)))
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "ITEMS"]) (.ok (some (.array 2 none)))
-- An empty string is a missing value (`ConfigProvider.ts:1089-1091`).
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "A"]) (.ok none)

/-! ### `E4-CONF-CE-002` — the flat spelling is the quotient this model takes

rc.112 joins the requested path with `_` before reading the record (`ConfigProvider.ts:1227`)
*and* splits every env name into the trie (`:1206-1207`), so `DATABASE_HOST` is found at both
`["DATABASE", "HOST"]` and the single-segment `["DATABASE_HOST"]`. This model resolves only
segmented paths: it keeps the tree and drops the flat alias. Every `Config` term reaches a
leaf through `prefix ++ [key name]`, so nothing in §4 can observe the difference — but a
provider written against the flat spelling would. -/

-- E4-CONF-CE-002: rc.112 finds the value here as well; this model does not.
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE_HOST"]) (.ok none)
-- E4-CONF-CE-002: the segmented spelling, which both agree on.
#guard answerEq ((fromEnvRecord envDb).load [Seg.key "DATABASE", Seg.key "HOST"])
  (.ok (some (.value "localhost")))

/-! ### `E4-CONF-CE-006` — a later `nested` is the outer prefix, and it is not cased

`nested` after `constantCase` prepends its prefix *after* the casing transform has already
been composed, so the prefix reaches the source uncased (`ConfigProvider.ts:767-772`,
`:883-886`). Swapping the two combinators changes which env var is read. -/

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

/-! ### `fromUnknown` over a JSON-ish tree -/

/-- The fragment of `unknown` that `describeUnknown` distinguishes (`ConfigProvider.ts:1070-1082`). -/
inductive Tree where
  /-- A string leaf. -/
  | str (s : String)
  /-- A numeric leaf; rendered with `String(u)` (`ConfigProvider.ts:1074`). -/
  | nat (n : Nat)
  /-- A boolean leaf, rendered the same way. -/
  | bool (b : Bool)
  /-- An array (`ConfigProvider.ts:1076`). -/
  | arr (items : List Tree)
  /-- An object (`ConfigProvider.ts:1077-1079`). -/
  | obj (fields : List (String × Tree))

/-- The first binding of a field name. -/
def lookupField (k : String) : List (String × Tree) → Option Tree
  | [] => none
  | (n, t) :: rest => if n = k then some t else lookupField k rest

/-- One descent step (`ConfigProvider.ts:1050-1064`): arrays take indices, objects take keys,
and anything else cannot be descended. -/
def Tree.child : Tree → Seg String → Option Tree
  | .obj fields, .key k => lookupField k fields
  | .arr items, .index i => items[i]?
  | _, _ => none

/-- `nodeAtJson`'s walk (`ConfigProvider.ts:1044-1065`). -/
def Tree.descend : Tree → Path String → Option Tree
  | t, [] => some t
  | t, s :: rest =>
      match t.child s with
      | some c => Tree.descend c rest
      | none => none

/-- `describeUnknown` (`ConfigProvider.ts:1070-1082`). -/
def Tree.describe : Tree → Option Node
  | .str s => (presentValue s).map Node.value
  | .nat n => some (.value (toString n))
  | .bool b => some (.value (if b then "true" else "false"))
  | .arr items => some (.array items.length none)
  | .obj fields => some (.record (fields.map Prod.fst) none)

/-- `fromUnknown` (`ConfigProvider.ts:1037-1042`): never fails, absence is `ok none`. -/
def fromTree (root : Tree) : Provider String :=
  Provider.make (fun p => .ok ((root.descend p).bind Tree.describe))

private def demoTree : Tree :=
  .obj [("db", .obj [("host", .str "localhost"), ("port", .nat 5432)]),
        ("tags", .arr [.str "a", .str "b"]),
        ("blank", .str "")]

#guard answerEq ((fromTree demoTree).load [Seg.key "db", Seg.key "port"])
  (.ok (some (.value "5432")))
#guard answerEq ((fromTree demoTree).load [Seg.key "tags"]) (.ok (some (.array 2 none)))
#guard answerEq ((fromTree demoTree).load [Seg.key "blank"]) (.ok none)
#guard answerEq ((fromTree demoTree).load [Seg.key "db"])
  (.ok (some (.record ["host", "port"] none)))

/-! ## §4 The `Config` reader

`Evaluator<T> = (provider, pathPrefix) => Effect<Resolution<T>, EvaluationFailure>`
(`Config.ts:136-139`). Composition needs to tell an *absent* recipe from a hard failure
before the public error channel is finalised, and `hasInput` records provider evidence
separately from the value (`Config.ts:113-134`). -/

/-- The values a term can resolve to. -/
inductive Val where
  /-- A string. -/
  | str (s : String)
  /-- A number. -/
  | nat (n : Nat)
  /-- A boolean. -/
  | bool (b : Bool)
  /-- `Config.all` on a pair. -/
  | pair (a b : Val)
  /-- `Option.none` (`Config.ts:887-888`). -/
  | none
  /-- `Option.some` (`Config.ts:887-888`). -/
  | some (v : Val)
deriving DecidableEq, Repr

/-- Why a term could not produce a value. -/
inductive ConfigError (Name : Type) where
  /-- Nothing was supplied at this path. -/
  | missing (path : Path Name)
  /-- Something was supplied and did not decode (`Config.ts:1208-1210`). -/
  | invalid (path : Path Name) (message : String)
  /-- The source itself failed (`Config.ts:205-206`). -/
  | source (e : SourceError Name)
deriving DecidableEq, Repr

/-- `Resolution<T> = Resolved<T> | Absent` (`Config.ts:118-129`). -/
inductive Resolution (Name : Type) where
  /-- A value, and whether provider input was read for it (`Config.ts:118-122`). -/
  | resolved (value : Val) (hasInput : Bool)
  /-- No relevant input was present (`Config.ts:124-127`). -/
  | absent (error : ConfigError Name)
deriving DecidableEq, Repr

/-- `EvaluationFailure` (`Config.ts:131-134`): a hard failure carries the same evidence, so
recovery cannot erase it. -/
structure Failure (Name : Type) where
  /-- What failed. -/
  error : ConfigError Name
  /-- Whether provider input was read anywhere in the group. -/
  hasInput : Bool
deriving DecidableEq, Repr

/-- What one evaluation answers (`Config.ts:136-139`). -/
abbrev Outcome (Name : Type) := Except (Failure Name) (Resolution Name)

/-- Boolean equality on outcomes, for the `#guard`s. -/
def outcomeEq {Name : Type} [DecidableEq Name] : Outcome Name → Outcome Name → Bool
  | .ok a, .ok b => decide (a = b)
  | .error a, .error b => decide (a = b)
  | _, _ => false

/-- Which primitive schema is being read. -/
inductive Prim where
  /-- `Config.string`. -/
  | str
  /-- `Config.number` at `Int`. -/
  | nat
  /-- `Config.boolean`. -/
  | bool
deriving DecidableEq, Repr

/-- The scalar codecs, supplied rather than unfolded: reading a `Nat` out of a `String` walks
the string, and every such walk reaches `Classical.choice` on this toolchain. This is the
trusted-boundary position `LeafSem` occupies in `Effect4/Program/Provision.lean`. -/
structure Scalars where
  /-- `Config.number` at `Int` (`Config.ts:1192-1220`). -/
  natOf : String → Option Nat
  /-- `Config.boolean` (`Config.ts:1224-1227`). -/
  boolOf : String → Option Bool

/-- `TrueValues` (`Config.ts:1224`). -/
def trueValues : List String := ["true", "yes", "on", "1", "y"]

/-- `FalseValues` (`Config.ts:1227`). Case-sensitive (`Config.ts:1239-1240`). -/
def falseValues : List String := ["false", "no", "off", "0", "n"]

/-- The boolean schema as a partial function on the supplied scalar. -/
def boolOfString (v : String) : Option Bool :=
  if trueValues.contains v then some true
  else if falseValues.contains v then some false
  else none

/-- The rc.112 scalar codecs. -/
def stdScalars : Scalars where
  natOf := String.toNat?
  boolOf := boolOfString

#guard stdScalars.boolOf "yes" == some true
#guard stdScalars.boolOf "off" == some false
#guard stdScalars.boolOf "maybe" == none
#guard stdScalars.natOf "5432" == some 5432
#guard stdScalars.natOf "x" == none

/-- Decoding a scalar that was actually supplied: `hasInput` is true because
`getScalar(node) !== undefined` (`Config.ts:1041`), so a decode failure here is a hard failure
(`Config.ts:1211-1212`), never an absence. -/
def decodeVal {Name : Type} (S : Scalars) (k : Prim) (path : Path Name) (v : String) :
    Outcome Name :=
  match k with
  | .str => .ok (.resolved (.str v) true)
  | .nat =>
      match S.natOf v with
      | some n => .ok (.resolved (.nat n) true)
      | none => .error ⟨.invalid path "expected a number", true⟩
  | .bool =>
      match S.boolOf v with
      | some b => .ok (.resolved (.bool b) true)
      | none => .error ⟨.invalid path "expected a boolean", true⟩

/-- Reading one primitive out of one lookup answer.

The absent case covers both "no node here" and "a container with no co-located scalar":
`hasProviderInput` for a scalar schema is `getScalar(node) !== undefined` (`Config.ts:1041`),
and a decode failure with no input evidence is `Effect.succeed(absent(error))`
(`Config.ts:1211-1213`). A `SourceError` is wrapped and carries no input evidence
(`Config.ts:205-206`). -/
def primOf {Name : Type} (S : Scalars) (k : Prim) (path : Path Name) (a : Answer Name) :
    Outcome Name :=
  match a with
  | .error e => .error ⟨.source e, false⟩
  | .ok node =>
      match node.bind nodeValue with
      | none => .ok (.absent (.missing path))
      | some v => decodeVal S k path v

/-- Reading one primitive at `prefix ++ [key name]`. -/
def evalPrim {Name : Type} (S : Scalars) (k : Prim) (n : Name) (P : Provider Name)
    (q : Path Name) : Outcome Name :=
  primOf S k (q ++ [Seg.key n]) (P.load (q ++ [Seg.key n]))

/-- `withDefault` (`Config.ts:847-852`): it maps the success channel only, and only the
`Absent` case, with `hasInput := false` on the substituted value. -/
def defaultStep {Name : Type} (d : Val) : Outcome Name → Outcome Name
  | .ok (.absent _) => .ok (.resolved d false)
  | .ok (.resolved v h) => .ok (.resolved v h)
  | .error f => .error f

/-- `option` is `map(Option.some)` then `withDefault(Option.none())` (`Config.ts:887-888`). -/
def optionStep {Name : Type} : Outcome Name → Outcome Name
  | .ok (.resolved v h) => .ok (.resolved (Val.some v) h)
  | .ok (.absent _) => .ok (.resolved Val.none false)
  | .error f => .error f

/-- `preserveInputEvidence` (`Config.ts:211-224`): when the recovered-from failure read
input, the recovery inherits it — a resolved value becomes `hasInput := true` and an absence
becomes a hard failure. When it did not, the fallback passes through untouched. -/
def recover {Name : Type} (f : Failure Name) : Outcome Name → Outcome Name
  | .ok (.resolved v h) => .ok (.resolved v (h || f.hasInput))
  | .ok (.absent e) => if f.hasInput then .error ⟨e, true⟩ else .ok (.absent e)
  | .error g => .error ⟨g.error, g.hasInput || f.hasInput⟩

/-- `orElse` (`Config.ts:562-574`): absence falls through with no evidence carried, a failure
falls through with its evidence preserved. -/
def orElseStep {Name : Type} : Outcome Name → Outcome Name → Outcome Name
  | .ok (.resolved v h), _ => .ok (.resolved v h)
  | .ok (.absent _), y => y
  | .error f, y => recover f y

/-- `Config.all` on a pair, i.e. `resolveArray` at length two (`Config.ts:640-678`): the
first failure wins and carries the group's accumulated evidence; otherwise the first absence
wins, and it is an absence only when *nothing* in the group read input — once a sibling read
input, a missing member makes the group incomplete and parsing fails (`Config.ts:589-593`). -/
def zipRes {Name : Type} : Outcome Name → Outcome Name → Outcome Name
  | .ok (.resolved va ha), .ok (.resolved vb hb) => .ok (.resolved (.pair va vb) (ha || hb))
  | .ok (.resolved _ ha), .ok (.absent e) => if ha then .error ⟨e, true⟩ else .ok (.absent e)
  | .ok (.absent e), .ok (.resolved _ hb) => if hb then .error ⟨e, true⟩ else .ok (.absent e)
  | .ok (.absent e), .ok (.absent _) => .ok (.absent e)
  | .error f, .ok (.resolved _ hb) => .error ⟨f.error, f.hasInput || hb⟩
  | .error f, .ok (.absent _) => .error ⟨f.error, f.hasInput⟩
  | .ok (.resolved _ ha), .error g => .error ⟨g.error, ha || g.hasInput⟩
  | .ok (.absent _), .error g => .error ⟨g.error, g.hasInput⟩
  | .error f, .error g => .error ⟨f.error, f.hasInput || g.hasInput⟩

/-- The `Config` language: one constructor per rc.112 export the corpus uses. -/
inductive ConfigTerm (Name : Type) where
  /-- `Config.string(name)`. -/
  | string (name : Name)
  /-- `Config.number(name)` at `Int`. -/
  | nat (name : Name)
  /-- `Config.boolean(name)`. -/
  | bool (name : Name)
  /-- `Config.succeed(v)`: a value with no provider evidence. -/
  | succeed (v : Val)
  /-- A term that always fails. -/
  | fail (message : String)
  /-- `Config.withDefault` (`Config.ts:744`). -/
  | withDefault (c : ConfigTerm Name) (d : Val)
  /-- `Config.orElse` (`Config.ts:444`). -/
  | orElse (c d : ConfigTerm Name)
  /-- `Config.option` (`Config.ts:887`). -/
  | option (c : ConfigTerm Name)
  /-- `Config.nested` (`Config.ts:1943`). -/
  | nested (name : Name) (c : ConfigTerm Name)
  /-- `Config.all` on a pair. -/
  | zip (a b : ConfigTerm Name)
deriving DecidableEq, Repr

/-- The evaluator (`Config.ts:136-139`). `orElse` and `zip` evaluate both operands here where
rc.112 is lazy in the second; the model is total and the provider is pure, so nothing but
work is observable in the difference. -/
def eval {Name : Type} (S : Scalars) :
    ConfigTerm Name → Provider Name → Path Name → Outcome Name
  | .string n, P, q => evalPrim S .str n P q
  | .nat n, P, q => evalPrim S .nat n P q
  | .bool n, P, q => evalPrim S .bool n P q
  | .succeed v, _, _ => .ok (.resolved v false)
  | .fail m, _, q => .error ⟨.invalid q m, false⟩
  | .withDefault c d, P, q => defaultStep d (eval S c P q)
  | .orElse c d, P, q => orElseStep (eval S c P q) (eval S d P q)
  | .option c, P, q => optionStep (eval S c P q)
  | .nested n c, P, q => eval S c P (q ++ [Seg.key n])
  | .zip a b, P, q => zipRes (eval S a P q) (eval S b P q)

/-! ### The laws of §4 -/

section EvalLaws

variable {Name : Type} (S : Scalars)

/-- `withDefault` fills absence, with no input evidence (`Config.ts:850`). -/
theorem eval_withDefault_absent (c : ConfigTerm Name) (d : Val) (P : Provider Name)
    (q : Path Name) (e : ConfigError Name) (h : eval S c P q = .ok (.absent e)) :
    eval S (.withDefault c d) P q = .ok (.resolved d false) := by
  simp only [eval, h, defaultStep]


/-- `withDefault` never replaces a value that resolved (`Config.ts:850`). -/
theorem eval_withDefault_resolved (c : ConfigTerm Name) (d v : Val) (P : Provider Name)
    (q : Path Name) (hi : Bool) (h : eval S c P q = .ok (.resolved v hi)) :
    eval S (.withDefault c d) P q = .ok (.resolved v hi) := by
  simp only [eval, h, defaultStep]


/-- `orElse` on absence is the fallback, evaluated with no evidence carried
(`Config.ts:570-572`). -/
theorem eval_orElse_absent (c d : ConfigTerm Name) (P : Provider Name) (q : Path Name)
    (e : ConfigError Name) (h : eval S c P q = .ok (.absent e)) :
    eval S (.orElse c d) P q = eval S d P q := by
  simp only [eval, h, orElseStep]


/-- `orElse` on a failure is the fallback with the failure's evidence preserved
(`Config.ts:564-568`, `:211-224`). -/
theorem eval_orElse_failure (c d : ConfigTerm Name) (P : Provider Name) (q : Path Name)
    (f : Failure Name) (h : eval S c P q = .error f) :
    eval S (.orElse c d) P q = recover f (eval S d P q) := by
  simp only [eval, h, orElseStep]


/-- A recovery that read no input is the fallback untouched (`Config.ts:215`). -/
theorem recover_no_input (f : Failure Name) (y : Outcome Name) (h : f.hasInput = false) :
    recover f y = y := by
  cases y with
  | error g => simp [recover, h]
  | ok r =>
    cases r with
    | resolved v hi => simp [recover, h]
    | absent e => simp [recover, h]


/-- `option` turns absence into `none`, with no input evidence (`Config.ts:887-888`). -/
theorem eval_option_absent (c : ConfigTerm Name) (P : Provider Name) (q : Path Name)
    (e : ConfigError Name) (h : eval S c P q = .ok (.absent e)) :
    eval S (.option c) P q = .ok (.resolved Val.none false) := by
  simp only [eval, h, optionStep]


/-- `Config.nested` extends the evaluator's prefix (`Config.ts:2050-2051`). -/
theorem eval_nested (n : Name) (c : ConfigTerm Name) (P : Provider Name) (q : Path Name) :
    eval S (.nested n c) P q = eval S c P (q ++ [Seg.key n]) := rfl


end EvalLaws

/-! ### The transfer law between the two `nested`s

`Config.nested` extends the evaluator's path prefix (`Config.ts:2050-2051`);
`ConfigProvider.nested` extends the provider's transform (`ConfigProvider.ts:883-886`). They
read the same source at the same place, and they *do not* produce equal outcomes: a
`missing` or `invalid` error records the Config-level path (`Config.ts:1209`), which knows
nothing of the provider's prefix. The honest law is equality after re-rooting the
Config-level paths — and a `SourceError` is not re-rooted, because that path is the
provider's own report of where *it* looked. -/

/-- Re-root a Config-level error path under a prefix; a source error is left alone. -/
def rerootError {Name : Type} (pre : Path Name) : ConfigError Name → ConfigError Name
  | .missing p => .missing (pre ++ p)
  | .invalid p m => .invalid (pre ++ p) m
  | .source e => .source e

/-- Re-root a resolution: values and their evidence are untouched. -/
def rerootRes {Name : Type} (pre : Path Name) : Resolution Name → Resolution Name
  | .resolved v h => .resolved v h
  | .absent e => .absent (rerootError pre e)

/-- Re-root an outcome. -/
def reroot {Name : Type} (pre : Path Name) : Outcome Name → Outcome Name
  | .ok r => .ok (rerootRes pre r)
  | .error f => .error ⟨rerootError pre f.error, f.hasInput⟩

section Transfer

variable {Name : Type}

private theorem reroot_decodeVal (S : Scalars) (pre path : Path Name) (k : Prim) (v : String) :
    reroot pre (decodeVal S k path v) = decodeVal S k (pre ++ path) v := by
  cases k with
  | str => rfl
  | nat => cases h : S.natOf v <;> simp [decodeVal, h, reroot, rerootRes, rerootError]
  | bool => cases h : S.boolOf v <;> simp [decodeVal, h, reroot, rerootRes, rerootError]

private theorem reroot_primOf (S : Scalars) (pre path : Path Name) (k : Prim)
    (a : Answer Name) : reroot pre (primOf S k path a) = primOf S k (pre ++ path) a := by
  cases a with
  | error e => rfl
  | ok node =>
    simp only [primOf]
    cases h : node.bind nodeValue with
    | none => rfl
    | some v => exact reroot_decodeVal S pre path k v

private theorem reroot_evalPrim (S : Scalars) (get : Lookup Name) (k : Prim) (n : Name)
    (q r : Path Name) :
    reroot q (evalPrim S k n ((Provider.make get).nested q) r)
      = evalPrim S k n (Provider.make get) (q ++ r) := by
  simp only [evalPrim, load_nested_fresh, load_make, List.append_assoc]
  exact reroot_primOf S q (r ++ [Seg.key n]) k (get (q ++ (r ++ [Seg.key n])))

private theorem reroot_defaultStep (pre : Path Name) (d : Val) (x : Outcome Name) :
    reroot pre (defaultStep d x) = defaultStep d (reroot pre x) := by
  cases x with
  | error f => rfl
  | ok r => cases r <;> rfl

private theorem reroot_optionStep (pre : Path Name) (x : Outcome Name) :
    reroot pre (optionStep x) = optionStep (reroot pre x) := by
  cases x with
  | error f => rfl
  | ok r => cases r <;> rfl

private theorem reroot_recover (pre : Path Name) (f : Failure Name) (y : Outcome Name) :
    reroot pre (recover f y)
      = recover ⟨rerootError pre f.error, f.hasInput⟩ (reroot pre y) := by
  cases y with
  | error g => rfl
  | ok r =>
    cases r with
    | resolved v h => rfl
    | absent e => cases hf : f.hasInput <;> simp [recover, reroot, rerootRes, rerootError, hf]

private theorem reroot_orElseStep (pre : Path Name) (x y : Outcome Name) :
    reroot pre (orElseStep x y) = orElseStep (reroot pre x) (reroot pre y) := by
  cases x with
  | error f =>
    simp only [orElseStep, reroot]
    exact reroot_recover pre f y
  | ok r => cases r <;> rfl

private theorem reroot_zipRes (pre : Path Name) (x y : Outcome Name) :
    reroot pre (zipRes x y) = zipRes (reroot pre x) (reroot pre y) := by
  cases x with
  | error f =>
    cases y with
    | error g => rfl
    | ok s => cases s <;> rfl
  | ok r =>
    cases r with
    | resolved v h =>
      cases y with
      | error g => rfl
      | ok s =>
        cases s with
        | resolved w k => rfl
        | absent e => cases h <;> rfl
    | absent e =>
      cases y with
      | error g => rfl
      | ok s =>
        cases s with
        | resolved w k => cases k <;> rfl
        | absent e2 => rfl

/-- **The transfer law.** Reading through a provider nested at `q` and reading at the prefix
`q` are the same evaluation, up to the prefix the Config layer puts on the paths it reports.
Every load a term performs goes through `prefix ++ [key name]`, so the whole proof is
`List.append_assoc` plus the fact that every combinator inspects only the shape of its
operands' outcomes. -/
theorem eval_nested_transfer (S : Scalars) (get : Lookup Name) (q : Path Name) :
    ∀ (c : ConfigTerm Name) (r : Path Name),
      reroot q (eval S c ((Provider.make get).nested q) r)
        = eval S c (Provider.make get) (q ++ r) := by
  intro c
  induction c with
  | string n => intro r; exact reroot_evalPrim S get .str n q r
  | nat n => intro r; exact reroot_evalPrim S get .nat n q r
  | bool n => intro r; exact reroot_evalPrim S get .bool n q r
  | succeed v => intro r; rfl
  | fail m => intro r; rfl
  | withDefault c d ih => intro r; simp only [eval, reroot_defaultStep, ih]
  | orElse c d ihc ihd => intro r; simp only [eval, reroot_orElseStep, ihc, ihd]
  | option c ih => intro r; simp only [eval, reroot_optionStep, ih]
  | nested n c ih =>
    intro r
    simp only [eval]
    rw [ih (r ++ [Seg.key n]), List.append_assoc]
  | zip a b iha ihb => intro r; simp only [eval, reroot_zipRes, iha, ihb]


/-- The corollary the two `nested`s are usually confused by: nesting the *term* under `n` and
nesting the *provider* under `n` agree, once the provider-side answer is re-rooted. -/
theorem eval_nested_eq_provider_nested (S : Scalars) (get : Lookup Name) (n : Name)
    (c : ConfigTerm Name) :
    eval S (.nested n c) (Provider.make get) []
      = reroot [Seg.key n] (eval S c ((Provider.make get).nested [Seg.key n]) []) := by
  rw [eval_nested_transfer S get [Seg.key n] c []]
  rfl


end Transfer

/-! ### `E4-CONF-CE-005` — a partially supplied group is not defaulted

`withDefault` replaces an *absence*; it does not replace a failure (`Config.ts:847-852`), and
a group one of whose members read input while another is missing is a failure, not an
absence (`Config.ts:674-675`, `:589-593`). So supplying `host` and forgetting `port` does not
silently take the default: it fails, with `hasInput = true`. Forgetting both takes the
default. -/

private def ce005Term : ConfigTerm String :=
  .withDefault (.zip (.string "host") (.string "port")) (.str "fallback")

-- E4-CONF-CE-005: one member supplied, one missing — a failure carrying the group's evidence.
#guard outcomeEq (eval stdScalars ce005Term (fromEnvRecord [("host", "db")]) [])
  (.error ⟨.missing [Seg.key "port"], true⟩)
-- E4-CONF-CE-005: nothing supplied — the default, with no evidence.
#guard outcomeEq (eval stdScalars ce005Term (fromEnvRecord []) [])
  (.ok (.resolved (.str "fallback") false))

-- The primitive readings, pinned: a supplied scalar, a missing one, a bad number, a bad flag.
#guard outcomeEq (eval stdScalars (.string "host") (fromEnvRecord [("host", "db")]) [])
  (.ok (.resolved (.str "db") true))
#guard outcomeEq (eval stdScalars (.nat "port") (fromEnvRecord [("port", "5432")]) [])
  (.ok (.resolved (.nat 5432) true))
#guard outcomeEq (eval stdScalars (.nat "port") (fromEnvRecord [("port", "x")]) [])
  (.error ⟨.invalid [Seg.key "port"] "expected a number", true⟩)
#guard outcomeEq (eval stdScalars (.bool "debug") (fromEnvRecord [("debug", "yes")]) [])
  (.ok (.resolved (.bool true) true))
#guard outcomeEq (eval stdScalars (.bool "debug") (fromEnvRecord [("debug", "maybe")]) [])
  (.error ⟨.invalid [Seg.key "debug"] "expected a boolean", true⟩)
-- A found container with no co-located scalar is absent, not invalid (`Config.ts:1041`,
-- `:1211-1213`) — which is why `withDefault` fires on it.
#guard outcomeEq (eval stdScalars (.string "DATABASE") (fromEnvRecord envDb) [])
  (.ok (.absent (.missing [Seg.key "DATABASE"])))
#guard outcomeEq
  (eval stdScalars (.withDefault (.string "DATABASE") (.str "d")) (fromEnvRecord envDb) [])
  (.ok (.resolved (.str "d") false))

/-! ## §5 String substitution (`ConfigProvider.ts:1364-1408`)

rc.112's `interpolate` rewrites the right-most `${VAR}` group and calls itself on the result
(`:1396-1399`). On `A=${A}`, and on the two-key cycle `A=${B}, B=${A}`, that recursion does
not terminate — transcribed and run in node on 2026-09-04, it exceeds a call depth of 2000
and throws. A total model cannot reproduce divergence, so it refuses by fuel:
`E4-CONF-CE-003` below. Values are modelled as templates rather than strings, which is the
same choice: rc.112 re-scans the substituted text, so the grammar is the object and the
string is its normal form when one exists. -/

/-- A dotenv value: literal text, a `${name}` or `${name:-default}` reference
(`ConfigProvider.ts:1387`), and concatenation. -/
inductive Tmpl (Name : Type) where
  /-- Literal text. -/
  | lit (s : String)
  /-- `${name}` or `${name:-default}`. -/
  | ref (name : Name) (default : Option String)
  /-- Concatenation. -/
  | cat (a b : Tmpl Name)
deriving DecidableEq, Repr

/-- Why an expansion was refused. -/
inductive Refusal (Name : Type) where
  /-- The reference cycle rc.112 diverges on. -/
  | cycle (name : Name)
deriving DecidableEq, Repr

/-- The first binding of a name in the parsed file. -/
def lookupTmpl {Name : Type} [DecidableEq Name] (n : Name) :
    List (Name × Tmpl Name) → Option (Tmpl Name)
  | [] => none
  | (m, t) :: rest => if m = n then some t else lookupTmpl n rest

private def catOk {Name : Type} :
    Except (Refusal Name) String → Except (Refusal Name) String → Except (Refusal Name) String
  | .ok a, .ok b => .ok (a ++ b)
  | .error e, _ => .error e
  | _, .error e => .error e

private theorem catOk_ok {Name : Type} {x y : Except (Refusal Name) String} {r : String}
    (h : catOk x y = .ok r) : ∃ sa sb, x = .ok sa ∧ y = .ok sb ∧ r = sa ++ sb := by
  cases x with
  | error e => simp [catOk] at h
  | ok sa =>
    cases y with
    | error e => simp [catOk] at h
    | ok sb => exact ⟨sa, sb, rfl, rfl, by simpa [catOk] using h.symm⟩

/-- What a resolved reference does with the text it expanded to: the empty string counts as
missing and falls back to the `:-` default (`ConfigProvider.ts:1392-1394`). -/
private def refFinish {Name : Type} (d : Option String) :
    Except (Refusal Name) String → Except (Refusal Name) String
  | .error e => .error e
  | .ok s => .ok (if s = "" then d.getD "" else s)

/-- One expansion pass, with the recursive step supplied. A missing name, and a name that
expands to the empty string, both fall back to the `:-` default or to `""`
(`ConfigProvider.ts:1392-1394`). -/
def expandAt {Name : Type} [DecidableEq Name] (env : List (Name × Tmpl Name))
    (step : Name → Tmpl Name → Except (Refusal Name) String) :
    Tmpl Name → Except (Refusal Name) String
  | .lit s => .ok s
  | .cat a b => catOk (expandAt env step a) (expandAt env step b)
  | .ref n d =>
      match lookupTmpl n env with
      | none => .ok (d.getD "")
      | some t => refFinish d (step n t)

/-- Expansion with a fuel bound. rc.112 recurses without one and diverges on a cycle
(`ConfigProvider.ts:1396-1399`); this refuses instead. -/
def expand {Name : Type} [DecidableEq Name] :
    Nat → List (Name × Tmpl Name) → Tmpl Name → Except (Refusal Name) String
  | 0, env, t => expandAt env (fun n _ => .error (.cycle n)) t
  | fuel + 1, env, t => expandAt env (fun _ u => expand fuel env u) t

section Expand

variable {Name : Type} [DecidableEq Name]

/-- Literal text expands to itself at every fuel. -/
theorem expand_lit (fuel : Nat) (env : List (Name × Tmpl Name)) (s : String) :
    expand fuel env (.lit s) = .ok s := by
  cases fuel <;> rfl


/-- `E4-CONF-CE-003` as a theorem: the self-reference rc.112 diverges on is refused at every
fuel, so no amount of fuel turns the refusal into an answer. -/
theorem expand_ref_self_refused (a : Name) (fuel : Nat) :
    expand fuel [(a, Tmpl.ref a none)] (Tmpl.ref a none) = .error (.cycle a) := by
  induction fuel with
  | zero => simp [expand, expandAt, lookupTmpl, refFinish]
  | succ n ih => simp [expand, expandAt, lookupTmpl, refFinish, ih]


private theorem expandAt_mono (env : List (Name × Tmpl Name))
    (s1 s2 : Name → Tmpl Name → Except (Refusal Name) String)
    (hs : ∀ n t r, s1 n t = .ok r → s2 n t = .ok r) :
    ∀ (t : Tmpl Name) (r : String), expandAt env s1 t = .ok r → expandAt env s2 t = .ok r := by
  intro t
  induction t with
  | lit s => intro r h; exact h
  | ref n d =>
    intro r h
    simp only [expandAt] at h ⊢
    cases hl : lookupTmpl n env with
    | none =>
      rw [hl] at h
      exact h
    | some u =>
      rw [hl] at h
      show refFinish d (s2 n u) = .ok r
      replace h : refFinish d (s1 n u) = .ok r := h
      cases h1 : s1 n u with
      | error e => rw [h1] at h; simp [refFinish] at h
      | ok w =>
        rw [hs n u w h1]
        rw [h1] at h
        exact h
  | cat a b iha ihb =>
    intro r h
    simp only [expandAt] at h ⊢
    obtain ⟨sa, sb, ha, hb, rfl⟩ := catOk_ok h
    rw [iha sa ha, ihb sb hb]
    rfl

/-- More fuel never loses an answer. -/
theorem expand_fuel_mono :
    ∀ (n m : Nat) (env : List (Name × Tmpl Name)) (t : Tmpl Name) (r : String),
      n ≤ m → expand n env t = .ok r → expand m env t = .ok r := by
  intro n
  induction n with
  | zero =>
    intro m env t r _ h
    cases m with
    | zero => exact h
    | succ m =>
      refine expandAt_mono env (fun n _ => .error (.cycle n)) _ ?_ t r h
      intro k u w hw
      simp at hw
  | succ n ih =>
    intro m env t r hnm h
    cases m with
    | zero => exact absurd hnm (Nat.not_succ_le_zero n)
    | succ m =>
      refine expandAt_mono env (fun _ u => expand n env u) _ ?_ t r h
      intro k u w hw
      exact ih m env u w (Nat.le_of_succ_le_succ hnm) hw


end Expand

private def expandIs (r : Except (Refusal String) String) (s : String) : Bool :=
  match r with
  | .ok t => t == s
  | .error _ => false

private def isRefused (r : Except (Refusal String) String) : Bool :=
  match r with
  | .ok _ => false
  | .error _ => true

private def dotenv : List (String × Tmpl String) :=
  [("HOST", .lit "db"), ("PORT", .lit "5432"), ("B", .lit "x"), ("A", .ref "B" none),
   ("EMPTY", .lit "")]

#guard expandIs (expand 8 dotenv
  (.cat (.ref "HOST" none) (.cat (.lit ":") (.ref "PORT" none)))) "db:5432"
#guard expandIs (expand 8 dotenv (.ref "MISSING" (some "fallback"))) "fallback"
#guard expandIs (expand 8 dotenv (.ref "A" none)) "x"
-- A name that expands to the empty string is treated as missing (`:1392-1394`).
#guard expandIs (expand 8 dotenv (.ref "EMPTY" (some "fallback"))) "fallback"
-- E4-CONF-CE-003: rc.112 diverges here; the model refuses.
#guard isRefused (expand 8 [("A", .ref "A" none)] (.ref "A" none))
-- E4-CONF-CE-003: and on the two-key cycle.
#guard isRefused (expand 8 [("A", .ref "B" none), ("B", .ref "A" none)] (.ref "A" none))

/-! ## §6 The configuration requirement row

What a term may read is a finite set of paths; what a source supplies is another. The
residual is `Row.diff` of the two through an index table, and it is empty exactly when the
term is fully provided — the same shape as `Layer`'s `Exclude<RIn, ROut>`
(`Effect4/Program/Provision.lean`), and the table is the interpretation.

The row element is `ServiceKey`, not `Nat`. `Row α` needs `Std.IsLinearOrder α` and
`Std.LawfulOrderLT α`, and *core's* instances for `Nat` reach `Classical.choice`: measured
on 2026-09-04, `Row.diff_eq_empty_iff_subset` is `[propext, Quot.sound]` generically and
`[propext, Classical.choice, Quot.sound]` the moment it is instantiated at `Nat`, while
`Row.normalize` and `Row.diff` themselves stay clean. `ServiceKey`'s order is hand-proved
from `Nat.lt_trichotomy` and friends at the library's ceiling
(`Effect4/Machine/Key.lean:270-290`), which is what a row over it costs — nothing. This is
the same reason `Requirement := Row ServiceKey` in `Effect4/Machine/Context.lean`. -/

/-- The paths a term may load from the prefix `q`. -/
def reads {Name : Type} (q : Path Name) : ConfigTerm Name → List (Path Name)
  | .string n => [q ++ [Seg.key n]]
  | .nat n => [q ++ [Seg.key n]]
  | .bool n => [q ++ [Seg.key n]]
  | .succeed _ => []
  | .fail _ => []
  | .withDefault c _ => reads q c
  | .orElse c d => reads q c ++ reads q d
  | .option c => reads q c
  | .nested n c => reads (q ++ [Seg.key n]) c
  | .zip a b => reads q a ++ reads q b

private theorem decodeVal_not_absent {Name : Type} (S : Scalars) (k : Prim) (path : Path Name)
    (v : String) (e : ConfigError Name) : decodeVal S k path v ≠ .ok (.absent e) := by
  intro h
  cases k with
  | str => simp [decodeVal] at h
  | nat =>
    simp only [decodeVal] at h
    split at h <;> simp at h
  | bool =>
    simp only [decodeVal] at h
    split at h <;> simp at h

private theorem recover_absent {Name : Type} {f : Failure Name} {x : Outcome Name}
    {e : ConfigError Name} (h : recover f x = .ok (.absent e)) : x = .ok (.absent e) := by
  cases x with
  | error g => simp [recover] at h
  | ok r =>
    cases r with
    | resolved v hi => simp [recover] at h
    | absent e' =>
      simp only [recover] at h
      split at h
      · simp at h
      · exact h

private theorem zipRes_absent {Name : Type} {x y : Outcome Name} {e : ConfigError Name}
    (h : zipRes x y = .ok (.absent e)) : x = .ok (.absent e) ∨ y = .ok (.absent e) := by
  cases x with
  | error f =>
    cases y with
    | error g => simp [zipRes] at h
    | ok s => cases s <;> simp [zipRes] at h
  | ok r =>
    cases r with
    | resolved v hi =>
      cases y with
      | error g => simp [zipRes] at h
      | ok s =>
        cases s with
        | resolved w k => simp [zipRes] at h
        | absent e' =>
          simp only [zipRes] at h
          split at h
          · simp at h
          · exact Or.inr h
    | absent e' =>
      cases y with
      | error g => simp [zipRes] at h
      | ok s =>
        cases s with
        | resolved w k =>
          simp only [zipRes] at h
          split at h
          · simp at h
          · exact Or.inl h
        | absent e2 =>
          simp only [zipRes] at h
          exact Or.inl h

section Missing

variable {Name : Type} [DecidableEq Name]

private theorem leafAt_none_not_provided (p : Path Name) :
    ∀ entries : List (Path Name × String),
      leafAt entries p = none → p ∉ provided entries := by
  intro entries
  induction entries with
  | nil => intro _; simp [provided]
  | cons x rest ih =>
    obtain ⟨q, v⟩ := x
    intro h
    simp only [leafAt] at h
    split at h
    · rename_i hq
      cases hv : presentValue v with
      | some w => rw [hv] at h; simp at h
      | none =>
        rw [hv] at h
        simp only [provided, hv]
        exact ih h
    · rename_i hq
      cases hv : presentValue v with
      | some w =>
        simp only [provided, hv]
        intro hmem
        rcases List.mem_cons.mp hmem with heq | hmem
        · exact hq heq.symm
        · exact ih h hmem
      | none =>
        simp only [provided, hv]
        exact ih h

private theorem leaf_none_of_scalar_none (render : Seg Name → String)
    (entries : List (Path Name × String)) (p : Path Name)
    (h : (nodeAt render entries p).bind nodeValue = none) : leafAt entries p = none := by
  cases hl : leafAt entries p with
  | none => rfl
  | some v =>
    exfalso
    unfold nodeAt at h
    rw [hl] at h
    split at h
    · simp [nodeValue] at h
    · split at h <;> simp [nodeValue] at h

private theorem evalPrim_absent (S : Scalars) (render : Seg Name → String)
    (entries : List (Path Name × String)) (k : Prim) (n : Name) (q : Path Name)
    (e : ConfigError Name)
    (h : evalPrim S k n (fromRecord render entries) q = .ok (.absent e)) :
    (q ++ [Seg.key n]) ∉ provided entries := by
  simp only [evalPrim, fromRecord, load_make, primOf] at h
  revert h
  cases hs : (nodeAt render entries (q ++ [Seg.key n])).bind nodeValue with
  | none =>
    intro _
    exact leafAt_none_not_provided _ entries (leaf_none_of_scalar_none render entries _ hs)
  | some v =>
    intro h
    exact absurd h (decodeVal_not_absent S k _ v e)

/-- **Absence names an unprovided path.** If a term evaluates to `absent` over an entry list,
then one of the paths it may read is not among the paths that list supplies. This is what
makes the residual row below mean something: an absent run is not a mystery, it is a name. -/
theorem absent_names_missing (S : Scalars) (render : Seg Name → String)
    (entries : List (Path Name × String)) :
    ∀ (c : ConfigTerm Name) (q : Path Name) (e : ConfigError Name),
      eval S c (fromRecord render entries) q = .ok (.absent e) →
      ∃ p, p ∈ reads q c ∧ p ∉ provided entries := by
  intro c
  induction c with
  | string n =>
    intro q e h
    exact ⟨q ++ [Seg.key n], by simp [reads], evalPrim_absent S render entries .str n q e h⟩
  | nat n =>
    intro q e h
    exact ⟨q ++ [Seg.key n], by simp [reads], evalPrim_absent S render entries .nat n q e h⟩
  | bool n =>
    intro q e h
    exact ⟨q ++ [Seg.key n], by simp [reads], evalPrim_absent S render entries .bool n q e h⟩
  | succeed v => intro q e h; simp [eval] at h
  | fail m => intro q e h; simp [eval] at h
  | withDefault c d ih =>
    intro q e h
    simp only [eval] at h
    exfalso
    revert h
    cases hc : eval S c (fromRecord render entries) q with
    | error f => simp [defaultStep]
    | ok r => cases r <;> simp [defaultStep]
  | orElse c d ihc ihd =>
    intro q e h
    simp only [eval] at h
    revert h
    cases hc : eval S c (fromRecord render entries) q with
    | error f =>
      intro h
      simp only [orElseStep] at h
      obtain ⟨p, hp, hnp⟩ := ihd q e (recover_absent h)
      exact ⟨p, by simp [reads, hp], hnp⟩
    | ok r =>
      cases r with
      | resolved v hi => intro h; simp [orElseStep] at h
      | absent e' =>
        intro h
        simp only [orElseStep] at h
        obtain ⟨p, hp, hnp⟩ := ihd q e h
        exact ⟨p, by simp [reads, hp], hnp⟩
  | option c ih =>
    intro q e h
    simp only [eval] at h
    exfalso
    revert h
    cases hc : eval S c (fromRecord render entries) q with
    | error f => simp [optionStep]
    | ok r => cases r <;> simp [optionStep]
  | nested n c ih => intro q e h; exact ih (q ++ [Seg.key n]) e h
  | zip a b iha ihb =>
    intro q e h
    simp only [eval] at h
    rcases zipRes_absent h with ha | hb
    · obtain ⟨p, hp, hnp⟩ := iha q e ha
      exact ⟨p, by simp [reads, hp], hnp⟩
    · obtain ⟨p, hp, hnp⟩ := ihb q e hb
      exact ⟨p, by simp [reads, hp], hnp⟩


end Missing

/-! ### The row -/

/-- The position of a path in the index table, counting from `i`. -/
def indexOfFrom {Name : Type} [DecidableEq Name] (p : Path Name) :
    Nat → List (Path Name) → Option Nat
  | _, [] => none
  | i, x :: rest => if x = p then some i else indexOfFrom p (i + 1) rest

/-- Interpret a path as a row element. -/
def indexOf {Name : Type} [DecidableEq Name] (table : List (Path Name)) (p : Path Name) :
    Option Nat :=
  indexOfFrom p 0 table

/-- The row element a table position denotes: the diagonal key `⟨⟨i⟩, ⟨i⟩⟩`, injective
because both fields are `i`. -/
def keyOf (i : Nat) : ServiceKey := ⟨⟨i⟩, ⟨i⟩⟩

/-- The row of table positions a term may read. -/
def readsRow {Name : Type} [DecidableEq Name] (table : List (Path Name)) (q : Path Name)
    (c : ConfigTerm Name) : Row ServiceKey :=
  Row.normalize ((reads q c).filterMap (fun p => (indexOf table p).map keyOf))

/-- The row of table positions an entry list supplies. -/
def providedRow {Name : Type} [DecidableEq Name] (table : List (Path Name))
    (entries : List (Path Name × String)) : Row ServiceKey :=
  Row.normalize ((provided entries).filterMap (fun p => (indexOf table p).map keyOf))

/-- What is still owed: the configuration's requirement row, in the very carrier
`Effect4/Machine/Context.lean` calls `Requirement`. -/
def residual {Name : Type} [DecidableEq Name] (table : List (Path Name)) (q : Path Name)
    (c : ConfigTerm Name) (entries : List (Path Name × String)) : Row ServiceKey :=
  Row.diff (readsRow table q c) (providedRow table entries)

/-- Nothing is owed exactly when everything read is supplied — `Row.diff_eq_empty_iff_subset`
at this instance, the same test `Layer`'s closed-ness is. -/
theorem residual_empty_of_subset {Name : Type} [DecidableEq Name] (table : List (Path Name))
    (q : Path Name) (c : ConfigTerm Name) (entries : List (Path Name × String))
    (h : Row.Subset (readsRow table q c) (providedRow table entries)) :
    residual table q c entries = Row.empty :=
  (Row.diff_eq_empty_iff_subset _ _).mpr h

-- The receipt for the carrier choice above, measured on 2026-09-04 by instantiating this
-- same theorem at `Nat` and printing its axioms:
--   Row.diff_eq_empty_iff_subset (generic)          [propext, Quot.sound]
--   Row.normalize, Row.diff (generic)               [propext, Quot.sound]
--   Row.diff_eq_empty_iff_subset at `Nat`           [propext, Classical.choice, Quot.sound]
-- Core's `Nat` order instances are the whole difference, so no theorem here mentions
-- `Row Nat`. `Effect4/Machine/Key.lean` is what a clean row over positions costs.

/-! ### Anti-vacuity: the docs-style example

`DATABASE_HOST`, `DATABASE_PORT` and `OTEL_SERVICE_NAME`, the last one defaulted. The
evaluation succeeds either way — that is the point: only the residual row tells you that the
third was never supplied. -/

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

#guard reads [] demoTerm == demoTable

#guard readsRow demoTable [] demoTerm == Row.normalize [keyOf 0, keyOf 1, keyOf 2]
#guard providedRow demoTable (entriesOf demoTwo) == Row.normalize [keyOf 0, keyOf 1]
#guard residual demoTable [] demoTerm (entriesOf demoTwo) == Row.normalize [keyOf 2]
#guard residual demoTable [] demoTerm (entriesOf demoThree) == Row.empty

#guard outcomeEq (eval stdScalars demoTerm (fromEnvRecord demoThree) [])
  (.ok (.resolved (.pair (.pair (.str "localhost") (.nat 5432)) (.str "checkout")) true))
#guard outcomeEq (eval stdScalars demoTerm (fromEnvRecord demoTwo) [])
  (.ok (.resolved (.pair (.pair (.str "localhost") (.nat 5432)) (.str "effect4")) true))

end Effect4.Program.Config
