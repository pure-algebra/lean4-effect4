import ProbeQW.Ty
import Effect4.Store.Carrier.Val

/-!
# ProbeQ5.Lower — the roots seat Q lowers through the tree's LCNF route (question 5)

Three roots, each a copy of what the data wave adds to a lowered closure:

* `canonFields`: the type-level canonical sort of a record's fields (insertion by `ltKey` on the
  UTF-8 bytes of the name, `ProbeQW.Ty.canon`), at the field triple `(name, type, optional)`;
* `canonRecord`/`canonRecordVal`: the value-level sort of R's row 165 (a record value is
  `ctor 0 [list names, list values]`; the canonical form sorts the names with the values in
  step), over `Effect4.Store.Val`;
* `ProbeQW.Ty.sub` itself (lowered by naming it as a root below): the wave's subtyping with the
  record, map, tuple and app arms and the declared leaf edges, since today's `Ty.sub` is in the
  closures of `ocaml/gen/api_gen.ml` and `ocaml/engine/api_engine.ml`.
-/

set_option autoImplicit false

namespace ProbeQ5
open Effect4.Store

/-- The record's fields in canonical order (the type level). -/
def canonFields (fs : List (String × ProbeQW.Ty × Bool)) : List (String × ProbeQW.Ty × Bool) :=
  ProbeQW.Ty.canon fs

/-- The names sorted with the values in step (the value level, R's row 165). -/
def canonRecord (names : List String) (values : List Val) : List String × List Val :=
  (ProbeQW.Ty.canon (names.zip values)).unzip

/-- A record value's frame read back, sorted, and rebuilt; `none` off the frame. -/
def canonRecordVal : Val → Option Val
  | .ctor 0 [.list ns, .list vs] => do
    let names ← ns.mapM fun
      | .str s => some s
      | _ => none
    if names.length = vs.length then
      let (n', v') := canonRecord names vs
      some (.ctor 0 [.list (n'.map Val.str), .list v'])
    else none
  | _ => none

#guard canonFields [("b", .nat, false), ("a", .string, true)] =
  [("a", .string, true), ("b", .nat, false)]
#guard canonRecord ["é", "z", "a"] [.nat 1, .nat 2, .nat 3] =
  (["a", "z", "é"], [.nat 3, .nat 2, .nat 1])

end ProbeQ5
