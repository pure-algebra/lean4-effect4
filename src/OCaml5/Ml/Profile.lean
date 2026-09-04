import OCaml5.Ml.Render

/-!
# OCaml5.Ml.Profile

**Everything written in OCaml must be directly representable in the Lean model.** This module is
where that rule is data rather than a habit: an admitted *construct* set and an admitted
*library* surface, both first-order, and `OCaml5.Ml.Check.profile` rejects a module that steps
outside either.

The rule bites in two directions and the two are different failures:

* a **construct** outside the set is a form the Lean model has no clause for — `Obj.magic`'s
  effect on a value, a first-class module, a `class`. The renderer cannot even spell most of
  them, which is why `Ml.Syntax`'s fragment is small; the ones it can spell and the model cannot
  interpret are listed here;
* a **library value** outside the surface is a name whose *meaning* is unmodelled. `Base.Map.find`
  is perfectly representable — a partial function on an ordered key — and `Marshal.from_string`
  is not, at any price.

## What a row asserts

A `LibVal` carries three things beyond its name: its **signature** as `Ml.Ty`, so the checker and
a reader see the same type; the **laws** it is relied on for, as **stable names** into the `laws`
catalogue below; and, on its module, the **carrier** — the Lean file whose semantics stands for
it, or `none`.

The law names are the interface to seat W4, which is proving them under `src/OCaml5/Lib/`.
A name here is a claim that something in the generated code depends on that behaviour, and
`Check.lawReport` says, per generated module, which laws it has come to depend on. A `Law.site`
of `none` means nobody has proved it yet; the name is stable across that transition, so a module
that depends on `Deque.fifo` keeps depending on `Deque.fifo` whether or not it is a theorem.

`carrier := none` is a **refusal row**: the value is admitted into generated OCaml because the
port needs it, and nothing in the Lean model says what it means. Today most of the library
surface is refusal rows, and `Profile.refusals` counts them so the number is visible rather than
implied. A row moves off that list by someone writing the carrier, not by editing this file.

## What this is not

It is not a model of Base, Eio or Picos. Each module lists the values the estate's generated
code actually uses or is expected to use, with the signature it uses them at. An unlisted value
of a listed module is reported (`profile-value`), so the surface grows by a deliberate edit here
and never by accident.
-/

namespace OCaml5.Ml

/-! ## Construct tags

One tag per syntactic form, so an admitted set is a list of strings and a diagnostic can name
what it rejected. The tags are the constructor names of `Ml.Syntax`, prefixed by their type. -/

/-- Every tag `Ml.Syntax` can produce. A `Profile` with `constructs := allConstructs` admits the
whole surface; a narrower profile lists a subset. -/
def allConstructs : List String :=
  -- types
  ["ty.var", "ty.con", "ty.arrow", "ty.tuple", "ty.larrow", "ty.polyVariant", "ty.anon",
   "ty.asVar",
  -- patterns
   "pat.wild", "pat.var", "pat.int", "pat.str", "pat.ctor", "pat.record", "pat.tuple",
   "pat.cons", "pat.alias", "pat.orPat", "pat.char", "pat.float", "pat.listPat",
   "pat.recordOpen", "pat.constrained", "pat.exnPat", "pat.polyPat", "pat.lazyPat",
  -- expressions
   "expr.var", "expr.int", "expr.str", "expr.bool", "expr.unit", "expr.ctor", "expr.app",
   "expr.binop", "expr.fn", "expr.letIn", "expr.letRecIn", "expr.seq", "expr.ifThen",
   "expr.matchE", "expr.tryWith", "expr.record", "expr.recordWith", "expr.field",
   "expr.setField", "expr.tuple", "expr.listLit", "expr.mkRef", "expr.deref", "expr.assign",
   "expr.raiseE", "expr.perform", "expr.continueK", "expr.discontinueK", "expr.matchWith",
   "expr.tryWithEff", "expr.annot", "expr.hole", "expr.raw", "expr.char", "expr.float",
   "expr.intOf", "expr.lam", "expr.functionE", "expr.letPat", "expr.openIn", "expr.assertE",
   "expr.lazyE", "expr.arrayLit", "expr.arrayGet", "expr.arraySet", "expr.whileE", "expr.forE",
   "expr.polyCtor", "expr.ifThenOnly", "expr.handler", "expr.matchWithK",
   "expr.shallowContinue", "expr.shallowDiscontinue", "expr.reperform", "expr.appL",
  -- structure items
   "decl.types", "decl.exn", "decl.effects", "decl.letD", "decl.ext", "decl.openM",
   "decl.comment", "decl.rawD", "decl.typeExt", "decl.includeD", "decl.moduleD",
   "decl.moduleAliasD", "decl.moduleTypeD", "decl.attrD", "decl.floatingAttrD", "decl.letPatD",
   "decl.blank"]

private def tyTag : Ty → String
  | .var _ => "ty.var" | .con _ _ => "ty.con" | .arrow _ _ => "ty.arrow"
  | .tuple _ => "ty.tuple" | .larrow _ _ _ => "ty.larrow"
  | .polyVariant _ _ => "ty.polyVariant" | .anon => "ty.anon" | .asVar _ _ => "ty.asVar"

private def patTag : Pat → String
  | .wild => "pat.wild" | .var _ => "pat.var" | .int _ => "pat.int" | .str _ => "pat.str"
  | .ctor _ _ => "pat.ctor" | .record _ => "pat.record" | .tuple _ => "pat.tuple"
  | .cons _ _ => "pat.cons" | .alias _ _ => "pat.alias" | .orPat _ _ => "pat.orPat"
  | .char _ => "pat.char" | .float _ => "pat.float" | .listPat _ => "pat.listPat"
  | .recordOpen _ => "pat.recordOpen" | .constrained _ _ => "pat.constrained"
  | .exnPat _ => "pat.exnPat" | .polyPat _ _ => "pat.polyPat" | .lazyPat _ => "pat.lazyPat"

private def exprTag : Expr → String
  | .var _ => "expr.var" | .int _ => "expr.int" | .str _ => "expr.str" | .bool _ => "expr.bool"
  | .unit => "expr.unit" | .ctor _ _ => "expr.ctor" | .app _ _ => "expr.app"
  | .binop _ _ _ => "expr.binop" | .fn _ _ => "expr.fn" | .letIn _ _ _ => "expr.letIn"
  | .letRecIn _ _ => "expr.letRecIn" | .seq _ _ => "expr.seq" | .ifThen _ _ _ => "expr.ifThen"
  | .matchE _ _ => "expr.matchE" | .tryWith _ _ => "expr.tryWith" | .record _ => "expr.record"
  | .recordWith _ _ => "expr.recordWith" | .field _ _ => "expr.field"
  | .setField _ _ _ => "expr.setField" | .tuple _ => "expr.tuple" | .listLit _ => "expr.listLit"
  | .mkRef _ => "expr.mkRef" | .deref _ => "expr.deref" | .assign _ _ => "expr.assign"
  | .raiseE _ => "expr.raiseE" | .perform _ => "expr.perform"
  | .continueK _ _ => "expr.continueK" | .discontinueK _ _ => "expr.discontinueK"
  | .matchWith _ _ _ _ _ _ _ => "expr.matchWith" | .tryWithEff _ _ _ _ => "expr.tryWithEff"
  | .annot _ _ => "expr.annot" | .hole _ _ => "expr.hole" | .raw _ => "expr.raw"
  | .char _ => "expr.char" | .float _ => "expr.float" | .intOf _ => "expr.intOf"
  | .lam _ _ => "expr.lam" | .functionE _ => "expr.functionE" | .letPat _ _ _ => "expr.letPat"
  | .openIn _ _ => "expr.openIn" | .assertE _ => "expr.assertE" | .lazyE _ => "expr.lazyE"
  | .arrayLit _ => "expr.arrayLit" | .arrayGet _ _ => "expr.arrayGet"
  | .arraySet _ _ _ => "expr.arraySet" | .whileE _ _ => "expr.whileE"
  | .forE _ _ _ _ _ => "expr.forE" | .polyCtor _ _ => "expr.polyCtor"
  | .ifThenOnly _ _ => "expr.ifThenOnly" | .handler _ _ _ _ _ => "expr.handler"
  | .matchWithK _ _ _ _ => "expr.matchWithK" | .shallowContinue _ _ _ => "expr.shallowContinue"
  | .shallowDiscontinue _ _ _ => "expr.shallowDiscontinue" | .reperform _ _ _ => "expr.reperform"
  | .appL _ _ => "expr.appL"

private def declTag : Decl → String
  | .types _ => "decl.types" | .exn _ _ => "decl.exn" | .effects _ => "decl.effects"
  | .letD _ _ => "decl.letD" | .ext _ _ _ _ => "decl.ext" | .openM _ => "decl.openM"
  | .comment _ => "decl.comment" | .rawD _ => "decl.rawD" | .typeExt _ _ _ _ => "decl.typeExt"
  | .includeD _ => "decl.includeD" | .moduleD _ _ _ _ => "decl.moduleD"
  | .moduleAliasD _ _ => "decl.moduleAliasD" | .moduleTypeD _ _ => "decl.moduleTypeD"
  | .attrD _ _ => "decl.attrD" | .floatingAttrD _ => "decl.floatingAttrD"
  | .letPatD _ _ => "decl.letPatD" | .blank => "decl.blank"

/-! ## The law catalogue

One entry per behaviour the estate relies on, with a **stable name**. Seat W4 is proving these
under `src/OCaml5/Lib/`; `site` is where, and `none` means not yet. The name never changes,
so a generated module's dependency list is stable across that transition. -/

/-- One behavioural law of an admitted library value. -/
structure Law where
  /-- The stable name: `Deque.fifo`, `Map.find_set_same`, `Ivar.one_shot`. -/
  name : String
  /-- What it says, in one sentence. -/
  statement : String
  /-- `src/OCaml5/Lib/<file>.lean`, and the theorem, once W4 has it. -/
  site : Option String := none
deriving Repr, Inhabited, DecidableEq

/-- Every law any admitted value names. A name used in a `LibVal` and absent here is a bug and
is `#guard`ed against below. -/
def laws : List Law :=
  -- The `Map.*` names are seat W4's own, from `src/OCaml5/Lib/Map.lean`'s "Named
  -- properties (theorem names are stable; cite these)". They are cited, not invented here.
  [{ name := "Map.find_empty", statement := "find empty k = None",
     site := some "src/OCaml5/Lib/Map.lean (Map.find_empty)" },
   { name := "Map.find_set_same", statement := "find (set m ~key ~data) key = Some data",
     site := some "src/OCaml5/Lib/Map.lean (Map.find_set_same)" },
   { name := "Map.find_set_other",
     statement := "key ≠ key' → find (set m ~key ~data) key' = find m key'",
     site := some "src/OCaml5/Lib/Map.lean (Map.find_set_other)" },
   { name := "Map.set_set_same",
     statement := "set (set m ~key ~data) ~key ~data' = set m ~key ~data'",
     site := some "src/OCaml5/Lib/Map.lean (Map.set_set_same)" },
   { name := "Map.set_comm", statement := "set at two distinct keys commutes",
     site := some "src/OCaml5/Lib/Map.lean (Map.set_comm)" },
   { name := "Map.find_remove_same", statement := "find (remove m k) k = None",
     site := some "src/OCaml5/Lib/Map.lean (Map.find_remove_same)" },
   { name := "Map.find_remove_other",
     statement := "k' ≠ k → find (remove m k) k' = find m k'",
     site := some "src/OCaml5/Lib/Map.lean (Map.find_remove_other)" },
   { name := "Map.ext_find",
     statement := "two maps that answer find alike are equal: the canonical form",
     site := some "src/OCaml5/Lib/Map.lean (Map.ext_find)" },
   { name := "Map.mem_find", statement := "mem m k = (find m k ≠ None)" },
   { name := "Map.toAlist_sorted",
     statement := "to_alist is strictly ascending by key: the canonical order a diff uses",
     site := some "src/OCaml5/Lib/Map.lean (Map.toAlist_sorted)" },
   { name := "Map.find_toAlist",
     statement := "to_alist carries the same bindings as find",
     site := some "src/OCaml5/Lib/Map.lean (Map.find_toAlist)" },
   { name := "Map.ofAlist_toAlist", statement := "of_alist ∘ to_alist = id",
     site := some "src/OCaml5/Lib/Map.lean (Map.ofAlist_toAlist)" },
   { name := "Map.fold_visits_keys_in_order",
     statement := "fold accumulating the keys reproduces keys: each key once, in key order",
     site := some "src/OCaml5/Lib/Map.lean (Map.fold_visits_keys_in_order)" },
   { name := "Map.fold_length", statement := "fold performs exactly length steps",
     site := some "src/OCaml5/Lib/Map.lean (Map.fold_length)" },
   { name := "Set.mem_add", statement := "mem (add s x) x" },
   { name := "Set.mem_remove", statement := "¬ mem (remove s x) x" },
   { name := "Set.to_list_sorted", statement := "to_list is sorted by the comparator" },
   { name := "Deque.fifo",
     statement := "dequeue_front after n enqueue_backs returns them in enqueue order" },
   { name := "Option.value_some", statement := "value (Some x) ~default = x" },
   { name := "Option.value_none", statement := "value None ~default:d = d" },
   { name := "Option.map_none", statement := "map None ~f = None" },
   { name := "Option.map_some", statement := "map (Some x) ~f = Some (f x)" },
   { name := "Result.bind_fail", statement := "bind (fail e) ~f = fail e" },
   { name := "List.rev_rev", statement := "rev (rev xs) = xs" },
   { name := "List.map_length", statement := "length (map xs ~f) = length xs" },
   { name := "List.append_assoc", statement := "append is associative" },
   { name := "List.append_nil", statement := "append [] xs = xs" },
   { name := "Int.wraps_63",
     statement := "OCaml's int is 63-bit and wraps; the model's Nat does not, so every "
       ++ "generated arithmetic is claimed only inside that bound" },
   { name := "Sexp.of_to_string",
     statement := "of_string ∘ to_string = id on the sexps the derivers produce" },
   { name := "Deriving.sexp_roundtrip",
     statement := "t_of_sexp ∘ sexp_of_t = id on values the generator builds" },
   { name := "Deriving.compare_total",
     statement := "compare_t is a total order: antisymmetric, transitive, total" },
   { name := "Deriving.compare_equal", statement := "compare_t x y = 0 ↔ equal_t x y" },
   { name := "Deriving.equal_structural",
     statement := "equal_t is an equivalence relation and is structural" },
   { name := "Deriving.hash_congruence", statement := "equal_t x y → hash_t x = hash_t y" },
   { name := "Fields.fold_once_in_order",
     statement := "Fields.fold visits every field exactly once, in declaration order: the walk "
       ++ "a field-by-field simulation relation is stated over" },
   { name := "Variants.to_rank_declaration_order",
     statement := "Variants.to_rank is the declaration order of the constructors: the order a "
       ++ "constructor-by-constructor diff uses" },
   { name := "Effect.perform_transfers",
     statement := "perform e in a fiber with a handler for e transfers to that handler's effc",
     site := some "src/OCaml5/Effect.lean (Machine.step, the perform clause)" },
   { name := "Effect.unhandled_raises",
     statement := "perform e with no handler raises Effect.Unhandled e",
     site := some "src/OCaml5/Effect.lean (ExnId.unhandled)" },
   { name := "Deep.match_with_pure",
     statement := "match_with f x h = h.retc (f x) when f performs nothing",
     site := some "src/OCaml5/Effect.lean (Stdlib.deepMatchWith)" },
   { name := "Deep.continuation_one_shot",
     statement := "resuming a continuation twice raises Effect.Continuation_already_resumed",
     site := some "src/OCaml5/Effect.lean (ExnId.continuationAlreadyResumed)" },
   { name := "Deep.try_with_is_match_with",
     statement := "try_with is match_with with the identity retc and a re-raising exnc "
       ++ "(effect.ml:84-91)",
     site := some "src/OCaml5/Effect.lean (Stdlib.deepTryWith)" },
   { name := "Deep.continue_resumes",
     statement := "continue k v resumes the fiber at its perform with v",
     site := some "src/OCaml5/Effect.lean (Stdlib.deepContinue)" },
   { name := "Deep.discontinue_raises",
     statement := "discontinue k e resumes the fiber by raising e at its perform",
     site := some "src/OCaml5/Effect.lean (Stdlib.deepDiscontinue)" },
   { name := "Shallow.continue_with_no_reinstall",
     statement := "continue_with k v h resumes with v under h, and h is not reinstalled",
     site := some "src/OCaml5/Effect.lean (Stdlib.shallowContinueWith)" },
   { name := "Switch.run_waits",
     statement := "run f returns only after every fiber forked on the switch has finished" },
   { name := "Switch.fail_cancels", statement := "a failing fiber cancels the switch" },
   { name := "Switch.finalizers_reverse",
     statement := "on_release finalizers run in reverse install order" },
   { name := "Promise.write_once", statement := "resolving a promise twice is an error" },
   { name := "Promise.await_stable",
     statement := "await blocks until resolve, then returns that value forever" },
   { name := "Fiber.fork_attaches", statement := "the child is attached to the given switch" },
   { name := "Fiber.first_cancels_loser",
     statement := "first f g cancels the loser once one finishes" },
   { name := "Computation.at_most_one_outcome",
     statement := "at most one of try_return and try_cancel takes effect" },
   { name := "Trigger.await_once", statement := "await returns at most once per trigger" },
   { name := "Trigger.signal_idempotent", statement := "signalling a signalled trigger is a no-op" },
   { name := "Ivar.one_shot", statement := "write-once: the second try_fill is refused" }]

/-- The stable names, for a membership test. -/
def lawNames : List String := laws.map (·.name)

/-- One law by name. -/
def lawOf (n : String) : Option Law := laws.find? (fun l => l.name == n)

/-- The laws nobody has proved yet. -/
def unprovenLaws : List String := (laws.filter (fun l => l.site.isNone)).map (·.name)

/-! ## The admitted library surface -/

/-- One admitted value of a library module. -/
structure LibVal where
  /-- The name inside its module: `find`, not `Base.Map.find`. -/
  name : String
  /-- Its signature, as `Ml.Ty`, at the instantiation the estate uses it at. `Ty.anon` is a
  signature nobody has written down yet, which is a smaller admission than a wrong one. -/
  ty : Ty
  /-- Stable law names into `laws`. -/
  lawNames : List String := []
deriving Repr, Inhabited

/-- One admitted library module. -/
structure LibModule where
  /-- The qualified path a generated module writes: `Base.Map`, `Effect.Deep`. -/
  path : String
  /-- What it is here for, in one line. -/
  doc : String
  /-- The type names it exports, unqualified, so `Base.Map.t` is admitted as a type path. -/
  types : List String := []
  values : List LibVal := []
  /-- The Lean file that carries the meaning of this module, or `none`. `none` is a **refusal
  row**: the module is admitted into generated OCaml and the Lean model says nothing about what
  it means. -/
  carrier : Option String := none
deriving Repr, Inhabited

/-- Whether this module's meaning exists in the Lean model. -/
def LibModule.modelled (m : LibModule) : Bool := m.carrier.isSome

/-- Every law name this module's values depend on. -/
def LibModule.lawNames (m : LibModule) : List String :=
  (m.values.flatMap (·.lawNames)).eraseDups

/-- An admitted-construct-and-library profile. -/
structure Profile where
  name : String
  /-- The syntactic forms a module may use. -/
  constructs : List String
  /-- The library modules a module may name. -/
  modules : List LibModule
  /-- Modules refused outright, with the reason. Their *presence* is the failure: nothing the
  Lean semantics says about a value survives an `Obj.magic`. -/
  banned : List (String × String) := []
deriving Repr, Inhabited

namespace Profile

/-- The modules with no Lean carrier: admitted into generated OCaml, unmodelled in Lean. -/
def refusals (p : Profile) : List String :=
  (p.modules.filter (fun m => !m.modelled)).map (·.path)

/-- The modules with a Lean carrier, and which file it is. -/
def modelled (p : Profile) : List (String × String) :=
  p.modules.filterMap fun m => m.carrier.map fun c => (m.path, c)

/-- The admitted module paths. -/
def paths (p : Profile) : List String := p.modules.map (·.path)

/-- The module of that path, if admitted. -/
def moduleOf (p : Profile) (path : String) : Option LibModule :=
  p.modules.find? (fun m => m.path == path)

/-- How many values the whole surface admits. -/
def valueCount (p : Profile) : Nat :=
  p.modules.foldl (init := 0) fun acc m => acc + m.values.length

/-- Every law name the whole surface names. -/
def lawNames (p : Profile) : List String := (p.modules.flatMap (·.lawNames)).eraseDups

end Profile

/-! ## The estate's profile

One entry per module the generated OCaml is allowed to name. The signatures are the ones the
estate uses, at `Base`'s spelling; `'k`, `'v`, `'a`, `'b`, `'cmp` are the modules' own
parameters. `Ty.anon` is a signature nobody has written down yet — a smaller admission than a
wrong one, and `Profile.unsignedValues` counts them. -/

private def tA : Ty := .var "a"
private def tB : Ty := .var "b"
private def tK : Ty := .var "k"
private def tV : Ty := .var "v"
private def arr (x y : Ty) : Ty := .arrow x y
private def mapT : Ty := .con "Base.Map.t" [tK, tV, .var "cmp"]
private def setT : Ty := .con "Base.Set.t" [tA, .var "cmp"]
private def dequeT : Ty := .con "Base.Deque.t" [tA]

/-- `Base.Map`: the dispatcher's priority buckets are one. -/
def libMap : LibModule where
  path := "Base.Map"
  doc := "an ordered finite map with an explicit comparator"
  types := ["t"]
  values :=
    [{ name := "empty", ty := mapT, lawNames := ["Map.find_empty"] },
     { name := "find", ty := arr mapT (arr tK (Ty.option tV)),
       lawNames := ["Map.find_set_same", "Map.find_set_other", "Map.find_remove_same",
                    "Map.find_remove_other", "Map.ext_find"] },
     { name := "set", ty := .larrow (.lbl "key") tK (.larrow (.lbl "data") tV (arr mapT mapT)),
       lawNames := ["Map.find_set_same", "Map.set_set_same", "Map.set_comm"] },
     { name := "remove", ty := arr mapT (arr tK mapT),
       lawNames := ["Map.find_remove_same", "Map.find_remove_other"] },
     { name := "mem", ty := arr mapT (arr tK Ty.bool), lawNames := ["Map.mem_find"] },
     { name := "length", ty := arr mapT Ty.int },
     { name := "to_alist", ty := arr mapT (Ty.list (.tuple [tK, tV])),
       lawNames := ["Map.toAlist_sorted", "Map.find_toAlist", "Map.ofAlist_toAlist"] },
     { name := "fold", ty := .anon,
       lawNames := ["Map.fold_visits_keys_in_order", "Map.fold_length"] }]

/-- `Base.Set`. -/
def libSet : LibModule where
  path := "Base.Set"
  doc := "an ordered finite set with an explicit comparator"
  types := ["t"]
  values :=
    [{ name := "empty", ty := setT },
     { name := "add", ty := arr setT (arr tA setT), lawNames := ["Set.mem_add"] },
     { name := "remove", ty := arr setT (arr tA setT), lawNames := ["Set.mem_remove"] },
     { name := "mem", ty := arr setT (arr tA Ty.bool) },
     { name := "to_list", ty := arr setT (Ty.list tA), lawNames := ["Set.to_list_sorted"] }]

/-- `Base.Deque`: the dispatcher's per-priority FIFO. -/
def libDeque : LibModule where
  path := "Base.Deque"
  doc := "a double-ended queue"
  types := ["t"]
  values :=
    [{ name := "create", ty := arr Ty.unit dequeT },
     { name := "enqueue_back", ty := arr dequeT (arr tA Ty.unit), lawNames := ["Deque.fifo"] },
     { name := "dequeue_front", ty := arr dequeT (Ty.option tA), lawNames := ["Deque.fifo"] },
     { name := "is_empty", ty := arr dequeT Ty.bool },
     { name := "length", ty := arr dequeT Ty.int }]

/-- `Base.Option`. Its meaning is carried: `Value.none` and `Value.some`. -/
def libOption : LibModule where
  path := "Base.Option"
  doc := "the option type"
  types := ["t"]
  carrier := some "src/OCaml5/Value.lean (Value.none, Value.some)"
  values :=
    [{ name := "is_some", ty := arr (Ty.option tA) Ty.bool },
     { name := "value", ty := .arrow (Ty.option tA) (.larrow (.lbl "default") tA tA),
       lawNames := ["Option.value_some", "Option.value_none"] },
     { name := "map", ty := .anon, lawNames := ["Option.map_none", "Option.map_some"] },
     { name := "iter", ty := .anon }]

/-- `Base.Result`, which is the shape an `Exit` has. -/
def libResult : LibModule where
  path := "Base.Result"
  doc := "the success/failure sum an Exit is"
  types := ["t"]
  values :=
    [{ name := "return", ty := arr tA (.con "Base.Result.t" [tA, tB]) },
     { name := "fail", ty := arr tB (.con "Base.Result.t" [tA, tB]) },
     { name := "bind", ty := .anon, lawNames := ["Result.bind_fail"] }]

/-- `Base.List`. -/
def libList : LibModule where
  path := "Base.List"
  doc := "the list type"
  types := ["t"]
  values :=
    [{ name := "length", ty := arr (Ty.list tA) Ty.int },
     { name := "rev", ty := arr (Ty.list tA) (Ty.list tA), lawNames := ["List.rev_rev"] },
     { name := "map", ty := .anon, lawNames := ["List.map_length"] },
     { name := "filter", ty := .anon },
     { name := "fold", ty := .anon },
     { name := "iter", ty := .anon },
     { name := "mem", ty := .anon },
     { name := "append", ty := arr (Ty.list tA) (arr (Ty.list tA) (Ty.list tA)),
       lawNames := ["List.append_assoc", "List.append_nil"] }]

/-- `Base.String`. -/
def libString : LibModule where
  path := "Base.String"
  doc := "strings"
  types := ["t"]
  values :=
    [{ name := "length", ty := arr Ty.string Ty.int },
     { name := "concat", ty := .anon },
     { name := "equal", ty := arr Ty.string (arr Ty.string Ty.bool) },
     { name := "compare", ty := arr Ty.string (arr Ty.string Ty.int) }]

/-- `Base.Int`. Carried by `Value.int`, with the one law that matters: it is not `Nat`. -/
def libInt : LibModule where
  path := "Base.Int"
  doc := "63-bit integers"
  types := ["t"]
  carrier := some "src/OCaml5/Value.lean (Value.int)"
  values :=
    [{ name := "to_string", ty := arr Ty.int Ty.string },
     { name := "of_string", ty := arr Ty.string Ty.int },
     { name := "compare", ty := arr Ty.int (arr Ty.int Ty.int) },
     { name := "equal", ty := arr Ty.int (arr Ty.int Ty.bool) },
     { name := "max_value", ty := Ty.int, lawNames := ["Int.wraps_63"] }]

/-- `Sexplib0.Sexp`, the wire the derivers produce. -/
def libSexp : LibModule where
  path := "Sexplib0.Sexp"
  doc := "the s-expression the ppx_sexp_conv derivers produce"
  types := ["t"]
  values :=
    [{ name := "to_string", ty := arr (.con "Sexplib0.Sexp.t" []) Ty.string },
     { name := "to_string_hum", ty := arr (.con "Sexplib0.Sexp.t" []) Ty.string },
     { name := "of_string", ty := arr Ty.string (.con "Sexplib0.Sexp.t" []),
       lawNames := ["Sexp.of_to_string"] }]

/-- What each deriver of `janeDerivers` generates for a type `t`, and the laws it is relied on
for. This is not a library module: it is what `ppx_jane` writes into the unit that carries the
attribute. -/
def derivedFunctions : List (String × List String × List String) :=
  [("sexp", ["sexp_of_t", "t_of_sexp"], ["Deriving.sexp_roundtrip"]),
   ("compare", ["compare_t"], ["Deriving.compare_total", "Deriving.compare_equal"]),
   ("equal", ["equal_t"], ["Deriving.equal_structural"]),
   ("hash", ["hash_t", "hash_fold_t"], ["Deriving.hash_congruence"]),
   ("fields", ["Fields.names", "Fields.fold", "Fields.iter", "Fields.map"],
    ["Fields.fold_once_in_order"]),
   ("variants", ["Variants.to_rank", "Variants.descriptions", "Variants.fold"],
    ["Variants.to_rank_declaration_order"])]

/-- The unqualified names `[@@deriving …]` puts in scope for a type of this name. `Fields` and
`Variants` are submodules, so their members are qualified and are judged as module paths, not as
values; only the flat functions are listed. -/
def derivedNames (tyName : String) (ds : List String) : List String :=
  ds.flatMap fun d =>
    if d == "sexp" then ["sexp_of_" ++ tyName, tyName ++ "_of_sexp"]
    else if d == "sexp_of" then ["sexp_of_" ++ tyName]
    else if d == "of_sexp" then [tyName ++ "_of_sexp"]
    else if d == "compare" then ["compare_" ++ tyName]
    else if d == "equal" then ["equal_" ++ tyName]
    else if d == "hash" then ["hash_" ++ tyName, "hash_fold_" ++ tyName]
    else if d == "enumerate" then ["all_of_" ++ tyName]
    else []

/-- `Fields`, from `[@@deriving fields]`: the field-by-field walk the relation is stated over. -/
def libFields : LibModule where
  path := "Fields"
  doc := "generated by [@@deriving fields]"
  values :=
    [{ name := "names", ty := Ty.list Ty.string },
     { name := "fold", ty := .anon, lawNames := ["Fields.fold_once_in_order"] },
     { name := "iter", ty := .anon, lawNames := ["Fields.fold_once_in_order"] },
     { name := "map", ty := .anon }]

/-- `Variants`, from `[@@deriving variants]`: the constructor order a diff uses. -/
def libVariants : LibModule where
  path := "Variants"
  doc := "generated by [@@deriving variants]"
  values :=
    [{ name := "to_rank", ty := .anon, lawNames := ["Variants.to_rank_declaration_order"] },
     { name := "descriptions", ty := Ty.list (.tuple [Ty.string, Ty.int]) },
     { name := "fold", ty := .anon }]

/-- `Effect`, `stdlib/effect.ml`: the one surface whose every value has a Lean carrier. -/
def libEffect : LibModule where
  path := "Effect"
  doc := "OCaml 5's effect handlers"
  types := ["t"]
  carrier := some "src/OCaml5/Effect.lean (Term.perform, Machine.step)"
  values :=
    [{ name := "perform", ty := .arrow (Ty.effect tA) tA,
       lawNames := ["Effect.perform_transfers", "Effect.unhandled_raises"] }]

/-- `Effect.Deep` (`stdlib/effect.ml:60-98`). -/
def libEffectDeep : LibModule where
  path := "Effect.Deep"
  doc := "deep handlers: the continuation carries its own handler"
  types := ["continuation", "handler", "effect_handler"]
  carrier :=
    some "src/OCaml5/Effect.lean (Stdlib.deepMatchWith, deepContinue, deepDiscontinue)"
  values :=
    [{ name := "match_with", ty := .anon,
       lawNames := ["Deep.match_with_pure", "Deep.continuation_one_shot"] },
     { name := "try_with", ty := .anon, lawNames := ["Deep.try_with_is_match_with"] },
     { name := "continue", ty := .anon, lawNames := ["Deep.continue_resumes"] },
     { name := "discontinue", ty := .anon, lawNames := ["Deep.discontinue_raises"] },
     { name := "discontinue_with_backtrace", ty := .anon }]

/-- `Effect.Shallow` (`stdlib/effect.ml:110-160`). -/
def libEffectShallow : LibModule where
  path := "Effect.Shallow"
  doc := "shallow handlers: the resumer supplies the handler"
  types := ["continuation", "handler", "fiber"]
  carrier := some "src/OCaml5/Effect.lean (Stdlib.shallowFiber, shallowContinueWith)"
  values :=
    [{ name := "fiber", ty := .anon },
     { name := "continue_with", ty := .anon,
       lawNames := ["Shallow.continue_with_no_reinstall"] },
     { name := "discontinue_with", ty := .anon },
     { name := "discontinue_with_backtrace", ty := .anon }]

/-- `Eio.Switch`: a scope. -/
def libEioSwitch : LibModule where
  path := "Eio.Switch"
  doc := "a structured-concurrency scope"
  types := ["t"]
  values :=
    [{ name := "run", ty := .anon, lawNames := ["Switch.run_waits", "Switch.fail_cancels"] },
     { name := "fail", ty := .anon, lawNames := ["Switch.fail_cancels"] },
     { name := "on_release", ty := .anon, lawNames := ["Switch.finalizers_reverse"] }]

/-- `Eio.Promise`: a Deferred. -/
def libEioPromise : LibModule where
  path := "Eio.Promise"
  doc := "a write-once cell: a Deferred"
  types := ["t", "u"]
  values :=
    [{ name := "create", ty := .anon },
     { name := "resolve", ty := .anon, lawNames := ["Promise.write_once"] },
     { name := "await", ty := .anon, lawNames := ["Promise.await_stable"] },
     { name := "peek", ty := .anon }]

/-- `Eio.Fiber`: fork, first and any. -/
def libEioFiber : LibModule where
  path := "Eio.Fiber"
  doc := "the structured-concurrency combinators"
  values :=
    [{ name := "fork", ty := .anon, lawNames := ["Fiber.fork_attaches"] },
     { name := "fork_daemon", ty := .anon },
     { name := "both", ty := .anon },
     { name := "first", ty := .anon, lawNames := ["Fiber.first_cancels_loser"] },
     { name := "any", ty := .anon },
     { name := "yield", ty := .anon }]

/-- `Picos.Computation`. -/
def libPicosComputation : LibModule where
  path := "Picos.Computation"
  doc := "a cancellable, completable unit of work"
  types := ["t"]
  values :=
    [{ name := "create", ty := .anon },
     { name := "try_return", ty := .anon, lawNames := ["Computation.at_most_one_outcome"] },
     { name := "try_cancel", ty := .anon, lawNames := ["Computation.at_most_one_outcome"] },
     { name := "await", ty := .anon },
     { name := "is_running", ty := .anon }]

/-- `Picos.Trigger`. -/
def libPicosTrigger : LibModule where
  path := "Picos.Trigger"
  doc := "a one-shot wake-up a fiber parks on"
  types := ["t"]
  values :=
    [{ name := "create", ty := .anon },
     { name := "await", ty := .anon, lawNames := ["Trigger.await_once"] },
     { name := "signal", ty := .anon, lawNames := ["Trigger.signal_idempotent"] },
     { name := "on_signal", ty := .anon }]

/-- `Picos_std_sync.Ivar`. -/
def libPicosIvar : LibModule where
  path := "Picos_std_sync.Ivar"
  doc := "a write-once cell"
  types := ["t"]
  values :=
    [{ name := "create", ty := .anon },
     { name := "try_fill", ty := .anon, lawNames := ["Ivar.one_shot"] },
     { name := "read", ty := .anon },
     { name := "peek_opt", ty := .anon }]

/-- Every admitted library module, in the order the seat report tabulates them. -/
def admittedModules : List LibModule :=
  [libMap, libSet, libDeque, libOption, libResult, libList, libString, libInt, libSexp,
   libFields, libVariants, libEffect, libEffectDeep, libEffectShallow,
   libEioSwitch, libEioPromise, libEioFiber,
   libPicosComputation, libPicosTrigger, libPicosIvar]

/-- The modules refused outright. Each is a hole no signature can close: nothing the Lean
semantics says about a value survives these. -/
def bannedModules : List (String × String) :=
  [("Obj", "erases the type the model is stated over"),
   ("Marshal", "reconstructs a value the model never built"),
   ("Domain", "parallelism: the Lean machine is one scheduler, `Effect.lean`'s `Machine`"),
   ("Thread", "as `Domain`"),
   ("Mutex", "as `Domain`"),
   ("Unix", "the world outside the model"),
   ("Sys", "the world outside the model"),
   ("Random", "unmodelled nondeterminism: a generated program must be a function of its tape"),
   ("Gc", "observes an allocation the model does not have"),
   ("Weak", "observes a collection the model does not have"),
   ("Printexc", "reads a backtrace the model does not carry"),
   ("Lazy", "`Lazy.force` is a mutation the model does not sequence")]

/-- The estate's profile: the whole syntactic surface, and the library above. -/
def estateProfile : Profile where
  name := "effect4"
  constructs := allConstructs
  modules := admittedModules
  banned := bannedModules

/-- A profile for a self-contained generated carrier module: every construct, and no library
beyond what `[@@deriving …]` puts in scope. -/
def carrierProfile : Profile where
  name := "carriers-only"
  constructs := allConstructs
  modules := [libFields, libVariants]
  banned := bannedModules

/-! ## Collecting what a module uses

One traversal, one accumulator. `*Paths` are the **qualified** names a module writes — an
unqualified name is the module's own and is `OCaml5.Ml.Check`'s business, not the profile's —
and `forms` is every construct tag. -/

/-- What a module uses: the qualified names, and the syntactic forms. -/
structure Usage where
  valuePaths : List String := []
  typePaths : List String := []
  ctorPaths : List String := []
  modulePaths : List String := []
  forms : List String := []
deriving Repr, Inhabited

namespace Usage
def empty : Usage := {}
def add (x y : Usage) : Usage :=
  { valuePaths := x.valuePaths ++ y.valuePaths, typePaths := x.typePaths ++ y.typePaths,
    ctorPaths := x.ctorPaths ++ y.ctorPaths, modulePaths := x.modulePaths ++ y.modulePaths,
    forms := x.forms ++ y.forms }
/-- Every qualified name, of every kind. -/
def allPaths (u : Usage) : List String :=
  (u.valuePaths ++ u.typePaths ++ u.ctorPaths ++ u.modulePaths).eraseDups
end Usage

instance : Append Usage := ⟨Usage.add⟩

/-- `A.B.c` split into its module prefix and its last segment; `none` when unqualified. -/
def splitPath (s : String) : Option (String × String) :=
  match (s.splitOn ".").reverse with
  | [] => none
  | [_] => none
  | last :: mods => some (String.intercalate "." mods.reverse, last)

private def qual (n : String) : List String :=
  if (n.splitOn ".").length > 1 then [n] else []

mutual
private def useTy : Ty → Usage
  | .var _ => { forms := ["ty.var"] }
  | .con n args => { typePaths := qual n, forms := ["ty.con"] } ++ useTys args
  | .arrow x y => { forms := ["ty.arrow"] } ++ useTy x ++ useTy y
  | .larrow _ x y => { forms := ["ty.larrow"] } ++ useTy x ++ useTy y
  | .tuple ps => { forms := ["ty.tuple"] } ++ useTys ps
  | .polyVariant _ rows => { forms := ["ty.polyVariant"] } ++ useRows rows
  | .anon => { forms := ["ty.anon"] }
  | .asVar t _ => { forms := ["ty.asVar"] } ++ useTy t
private def useTys : List Ty → Usage
  | [] => .empty
  | t :: rest => useTy t ++ useTys rest
private def useRows : List (String × List Ty) → Usage
  | [] => .empty
  | (_, ts) :: rest => useTys ts ++ useRows rest
end

mutual
private def usePat (p : Pat) : Usage :=
  { forms := [patTag p] } ++
    (match p with
     | .ctor n args => { ctorPaths := qual n } ++ usePats args
     | .record fs => usePatFields fs
     | .recordOpen fs => usePatFields fs
     | .tuple ps => usePats ps
     | .listPat ps => usePats ps
     | .cons x y => usePat x ++ usePat y
     | .alias q _ => usePat q
     | .orPat x y => usePat x ++ usePat y
     | .constrained q t => usePat q ++ useTy t
     | .exnPat q => usePat q
     | .polyPat _ (some q) => usePat q
     | .lazyPat q => usePat q
     | _ => .empty)
private def usePats : List Pat → Usage
  | [] => .empty
  | p :: rest => usePat p ++ usePats rest
private def usePatFields : List (String × Pat) → Usage
  | [] => .empty
  | (_, p) :: rest => usePat p ++ usePatFields rest
end

mutual
private def useExpr (e : Expr) : Usage :=
  { forms := [exprTag e] } ++
    (match e with
     | .var n => { valuePaths := qual n }
     | .ctor n args => { ctorPaths := qual n } ++ useExprs args
     | .polyCtor _ a => useExprOpt a
     | .app f args => useExpr f ++ useExprs args
     | .appL f args => useExpr f ++ useLabelled args
     | .binop _ x y => useExpr x ++ useExpr y
     | .fn _ b => useExpr b
     | .lam ps b => useParams ps ++ useExpr b
     | .functionE arms => useArms arms
     | .letIn _ v b => useExpr v ++ useExpr b
     | .letPat p v b => usePat p ++ useExpr v ++ useExpr b
     | .letRecIn bs b => useLocalBinds bs ++ useExpr b
     | .openIn path b => { modulePaths := [path] } ++ useExpr b
     | .seq x y => useExpr x ++ useExpr y
     | .ifThen c t f => useExpr c ++ useExpr t ++ useExpr f
     | .ifThenOnly c t => useExpr c ++ useExpr t
     | .whileE c b => useExpr c ++ useExpr b
     | .forE _ lo hi _ b => useExpr lo ++ useExpr hi ++ useExpr b
     | .matchE s arms => useExpr s ++ useArms arms
     | .tryWith b arms => useExpr b ++ useArms arms
     | .record fs => useFields fs
     | .recordWith b fs => useExpr b ++ useFields fs
     | .field x _ => useExpr x
     | .setField x _ v => useExpr x ++ useExpr v
     | .tuple ps => useExprs ps
     | .listLit xs => useExprs xs
     | .arrayLit xs => useExprs xs
     | .arrayGet x i => useExpr x ++ useExpr i
     | .arraySet x i v => useExpr x ++ useExpr i ++ useExpr v
     | .mkRef x => useExpr x
     | .deref x => useExpr x
     | .assign r v => useExpr r ++ useExpr v
     | .raiseE x => useExpr x
     | .assertE x => useExpr x
     | .lazyE x => useExpr x
     | .perform x => useExpr x
     | .continueK k v => useExpr k ++ useExpr v
     | .discontinueK k x => useExpr k ++ useExpr x
     | .shallowContinue k v h => useExpr k ++ useExpr v ++ useExpr h
     | .shallowDiscontinue k x h => useExpr k ++ useExpr x ++ useExpr h
     | .reperform x k l => useExpr x ++ useExpr k ++ useExpr l
     | .matchWith c a ty _ r ex ef =>
         useExpr c ++ useExpr a ++ useTy ty ++ useExpr r ++ useArms ex ++ useEffc ef
     | .tryWithEff c a ty ef => useExpr c ++ useExpr a ++ useTy ty ++ useEffc ef
     | .matchWithK _ c a h => useExpr c ++ useExpr a ++ useExpr h
     | .handler _ ty retc ex ef =>
         useTy ty ++ (match retc with | none => .empty | some (_, r) => useExpr r)
           ++ useArms ex ++ useEffc ef
     | .annot x ty => useExpr x ++ useTy ty
     | .hole _ fill => useExpr fill
     | _ => .empty)
private def useExprs : List Expr → Usage
  | [] => .empty
  | e :: rest => useExpr e ++ useExprs rest
private def useExprOpt : Option Expr → Usage
  | none => .empty
  | some e => useExpr e
private def useLabelled : List (ArgLabel × Expr) → Usage
  | [] => .empty
  | (_, e) :: rest => useExpr e ++ useLabelled rest
private def useFields : List (String × Expr) → Usage
  | [] => .empty
  | (_, e) :: rest => useExpr e ++ useFields rest
private def useLocalBinds : List (String × List String × Expr) → Usage
  | [] => .empty
  | (_, _, e) :: rest => useExpr e ++ useLocalBinds rest
private def useArms : List Arm → Usage
  | [] => .empty
  | .mk p g b :: rest =>
      usePat p ++ (match g with | none => .empty | some ge => useExpr ge) ++ useExpr b
        ++ useArms rest
private def useEffc : List Effc → Usage
  | [] => .empty
  | .mk n args _ b :: rest =>
      { ctorPaths := qual n } ++ usePats args ++ useExpr b ++ useEffc rest
private def useParams : List Param → Usage
  | [] => .empty
  | .mk _ p t d :: rest =>
      usePat p ++ (match t with | none => .empty | some ty => useTy ty)
        ++ (match d with | none => .empty | some e => useExpr e) ++ useParams rest
end

private def useField (f : Field) : Usage := useTy f.ty
private def useCtorDecl (c : Ctor) : Usage :=
  useTys c.args ++ (match c.result with | none => .empty | some t => useTy t)
    ++ (match c.inlineRecord with
        | none => .empty
        | some fs => fs.foldl (fun acc f => acc ++ useField f) Usage.empty)

private def useTyBody : TyBody → Usage
  | .record fs => fs.foldl (fun acc f => acc ++ useField f) Usage.empty
  | .variant cs => cs.foldl (fun acc c => acc ++ useCtorDecl c) Usage.empty
  | .alias t => useTy t
  | .abstract => .empty
  | .extensible => .empty

private def useTypeDecl (d : TypeDecl) : Usage := useTyBody d.body

private def useBind (b : Bind) : Usage :=
  b.params.foldl (fun acc p => acc ++ (match p.2 with | none => .empty | some t => useTy t))
      Usage.empty
    ++ useParams b.lparams
    ++ (match b.result with | none => .empty | some t => useTy t)
    ++ useExpr b.body

mutual
private def useModTy : ModTy → Usage
  | .path n => { modulePaths := [n] }
  | .sig items => useSigItems items
  | .functor _ argTy res => useModTy argTy ++ useModTy res
  | .withType base _ _ t => useModTy base ++ useTy t
private def useSigItems : List SigItem → Usage
  | [] => .empty
  | it :: rest => useSigItem it ++ useSigItems rest
private def useSigItem : SigItem → Usage
  | .val _ t => useTy t
  | .types g => g.foldl (fun acc d => acc ++ useTypeDecl d) Usage.empty
  | .exn _ args => useTys args
  | .ext _ t _ _ => useTy t
  | .modS _ mt => useModTy mt
  | .modTypeS _ mt => useModTy mt
  | .includeS mt => useModTy mt
  | .openS n => { modulePaths := [n] }
  | .commentS _ => .empty
  | .rawS _ => .empty
end

mutual
private def useDecl (d : Decl) : Usage :=
  { forms := [declTag d] } ++
    (match d with
     | .types g => g.foldl (fun acc t => acc ++ useTypeDecl t) Usage.empty
     | .exn _ args => useTys args
     | .effects cs =>
         cs.foldl (fun acc c => acc ++ useTys c.2.1 ++ useTy c.2.2) Usage.empty
     | .letD _ binds => binds.foldl (fun acc b => acc ++ useBind b) Usage.empty
     | .ext _ t _ _ => useTy t
     | .openM n => { modulePaths := [n] }
     | .typeExt path _ cs _ =>
         { typePaths := qual path }
           ++ cs.foldl (fun acc c => acc ++ useCtorDecl c) Usage.empty
     | .includeD mt => useModTy mt
     | .moduleD _ params ascribe body =>
         params.foldl (fun acc p => acc ++ useModTy p.2) Usage.empty
           ++ (match ascribe with | none => .empty | some mt => useModTy mt)
           ++ useDecls body
     | .moduleAliasD _ target => { modulePaths := [target] }
     | .moduleTypeD _ mt => useModTy mt
     | .attrD _ inner => useDecl inner
     | .letPatD p v => usePat p ++ useExpr v
     | _ => .empty)
private def useDecls : List Decl → Usage
  | [] => .empty
  | d :: rest => useDecl d ++ useDecls rest
end

/-- Everything one module uses: its qualified names, and its construct tags. -/
def usageOf (m : Module) : Usage :=
  let u := useDecls m.items
  { u with valuePaths := u.valuePaths.eraseDups, typePaths := u.typePaths.eraseDups,
           ctorPaths := u.ctorPaths.eraseDups, modulePaths := u.modulePaths.eraseDups,
           forms := u.forms.eraseDups }

/-! ## Checks -/

-- Every law a profile names is in the catalogue, and the catalogue has no duplicates.
#guard estateProfile.lawNames.all (fun n => lawNames.contains n)
#guard lawNames.eraseDups.length == lawNames.length
#guard (derivedFunctions.flatMap (·.2.2)).all (fun n => lawNames.contains n)

-- The shape of the surface, so a change to it is a visible change to these numbers.
#guard estateProfile.modules.length == 20
#guard estateProfile.valueCount == 88
#guard estateProfile.banned.length == 12
#guard estateProfile.lawNames.length == 50

-- Four modules of twenty have a Lean carrier; the other sixteen are refusal rows.
#guard estateProfile.modelled.length == 5
#guard estateProfile.refusals.length == 15
#guard estateProfile.modelled.map (·.1) ==
  ["Base.Option", "Base.Int", "Effect", "Effect.Deep", "Effect.Shallow"]

-- Every law of the three `Effect` modules has a site in `src/OCaml5/Effect.lean`, and no
-- other law has one. Being *modelled* and having a *proved law* are two different things:
-- `Base.Option` has a carrier (`Value.none`/`Value.some`) and none of its laws is a theorem yet.
#guard [libEffect, libEffectDeep, libEffectShallow].all
  (fun m => m.lawNames.all (fun n => match lawOf n with
                                     | some l => l.site.isSome
                                     | none => false))
-- 34 of the 55 laws are nobody's theorem yet. The 21 that are: the eight effect-handler laws
-- (`src/OCaml5/Effect.lean`) and W4's thirteen `Map.*` (`src/OCaml5/Lib/Map.lean`),
-- whose names are cited from that file and not invented here.
#guard unprovenLaws.length == 34
#guard laws.length == 55
#guard (laws.filter (fun l => l.site.isSome)).length == 21

-- The construct tags cover the surface exactly: every tag a form can produce is admitted.
#guard allConstructs.eraseDups.length == allConstructs.length
#guard estateProfile.constructs == allConstructs

-- `splitPath` is the module/last split the checker keys on.
#guard splitPath "Base.Map.find" == some ("Base.Map", "find")
#guard splitPath "f" == none
#guard splitPath "Effect.Deep.continue" == some ("Effect.Deep", "continue")

end OCaml5.Ml
