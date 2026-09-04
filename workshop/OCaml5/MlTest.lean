import OCaml5.Render

/-!
# OCaml5.MlTest — the battery for the `OCaml5.Ml` API

Status: seat W3, 2026-09-04. Report: `docs/research/2026-09-04-seat-w3-ml-api.md`.

Four checks, in the order the seat brief asks for them.

**(a) Every syntax form renders text `ocamlc` accepts.** `fixture` below is one `Ml.Module` that
uses every constructor of `Ml.Syntax` — every type form, every pattern, every expression, every
structure item, signatures, functors, attributes — and `tools/ml-check.sh` renders it with
`main`, compiles it with `ocamlc`, `ocamlopt` and `js_of_ocaml`, runs it, and diffs its output
against `expectedRows` pinned here. Rendering is checked in Lean; being OCaml is checked by
OCaml.

Two forms are deliberately absent from the fixture and are checked elsewhere:

* `Expr.reperform`. The raw `%reperform` primitive is typed over `last_fiber`, which
  `stdlib/effect.ml` does not export, so no ordinary compilation unit can name it. The
  declaration that *can* is `OCaml5.Render.fixedPrelude`, and `tools/fuzz.sh witnesses` compiles
  and runs it on all three hosts. What `MlTest` checks about `reperform` is the tail-position
  rule, which is a `Check` property and is checked below.
* `Ty.asVar`, the `(t as 'a)` constraint. It is legal only where the equation is not cyclic, and
  every use a generator would have is inside a `constraint` clause the surface does not spell.
  It renders (`Ml/Render.lean`'s `#guard`s) and is not compiled.

**(b) The five avatar carriers still render byte-identical.** That is
`tools/fuzz.sh avatar`, unchanged, which cuts each carrier out of
`workshop/OCaml5/avatar/deep_fibers.ml` and out of the generated module and runs `diff`. It is
not repeated here: a copy of the file inside Lean would be the thing the check exists to avoid.

**(c) The checker rejects ten deliberately bad modules and accepts the good ones.**
`badModules` below, one per diagnostic code, each `#guard`ed to produce exactly its code; and
`fixture` is `#guard`ed well-formed.

**(d) The identifier mangling round-trips.** `unmangleField ∘ mangleField = id` on the estate's
own field names and on an adversarial row.
-/

namespace OCaml5.MlTest

open OCaml5.Ml

/-! ## (a) The fixture: every syntax form, in one compilation unit -/

private def tyA : Ty := .var "a"

/-! ### Types and modules -/

/-- `type color = Red | Green | Blue of int`. -/
def colorDecl : Decl :=
  .types [{ name := "color",
            body := .variant [{ name := "Red" }, { name := "Green" },
                              { name := "Blue", args := [Ty.int] }] }]

/-- A record with a `mutable` field. -/
def pointDecl : Decl :=
  .types [{ name := "point",
            body := .record [{ name := "px", ty := Ty.int },
                             { name := "py", ty := Ty.int, isMutable := true }] }]

/-- Two parameters, and a recursive parameterised variant, as one `and`-group. -/
def treeDecls : Decl :=
  .types
    [{ name := "both", params := ["a", "b"],
       body := .record [{ name := "left", ty := .var "a" }, { name := "right", ty := .var "b" }] },
     { name := "tree", params := ["a"],
       body := .variant [{ name := "Leaf" },
                         { name := "Node",
                           args := [.con "tree" [tyA], tyA, .con "tree" [tyA]] }] }]

/-- A **phantom parameter**: nothing determines `'a`, and only the `+` makes OCaml accept it
(§11.6, "type-param"). -/
def phantomDecl : Decl :=
  .types [{ name := "phantom", tparams := [{ name := "a", variance := .covariant }],
            body := .record [{ name := "ph", ty := Ty.int }] }]

/-- An abbreviation, an abstract type, and an extensible one. -/
def miscTypeDecls : List Decl :=
  [.types [{ name := "ident", body := .alias Ty.int, attrs := ["warning \"-34\""] }],
   .types [{ name := "opaque", body := .abstract }],
   .types [{ name := "shape", body := .extensible }]]

/-- `type shape += Sq of int | Tri of int * int` — an extension of an extensible variant. -/
def shapeExtDecl : Decl :=
  .typeExt "shape" []
    [{ name := "Sq", args := [Ty.int] }, { name := "Tri", args := [Ty.int, Ty.int] }]

/-- A GADT: the constructors carry their own return type. -/
def gadtDecl : Decl :=
  .types [{ name := "gadt", params := ["a"],
            body := .variant
              [{ name := "GInt", args := [Ty.int], result := some (.con "gadt" [Ty.int]) },
               { name := "GBool", args := [Ty.bool],
                 result := some (.con "gadt" [Ty.bool]) }] }]

/-- An inline record argument, `| Rc of { … }`. -/
def inlineRecordDecl : Decl :=
  .types [{ name := "boxed",
            body := .variant
              [{ name := "Rc",
                 inlineRecord := some [{ name := "ra", ty := Ty.int },
                                       { name := "rb", ty := Ty.int, isMutable := true }] }] }]

/-- Two exceptions, one with a payload and one without. -/
def exnDecls : List Decl := [.exn "Boom" [Ty.int], .exn "Plain" []]

/-- The effect declaration: `type _ Effect.t += …`. -/
def effectDecl : Decl :=
  .effects [("Ask", [Ty.int], Ty.int), ("Beep", [], Ty.unit)]

/-- An `external` with a primitive name and an attribute. -/
def externalDecl : Decl := .ext "ident_ext" (.arrow tyA tyA) "%identity" []

/-- A module type with one item of every `SigItem` shape. -/
def sigDecl : Decl :=
  .moduleTypeD "S"
    (.sig [.commentS "one item of every signature shape",
           .types [{ name := "t", body := .abstract }],
           .val "f" (.arrow (.named "t") (.named "t")),
           .val "labelled_" (.larrow (.lbl "x") Ty.int (.larrow (.opt "y") Ty.int
             (.arrow Ty.unit Ty.int))),
           .exn "SigExn" [Ty.int],
           .ext "sig_id" (.arrow tyA tyA) "%identity" [],
           .openS "Stdlib",
           .rawS "(* a verbatim signature line *)"])

/-- `module type SI = S with type t = int`. -/
def withTypeDecl : Decl :=
  .moduleTypeD "SI" (.withType (.path "S") "t" [] Ty.int)

/-- `module type FS = functor (X : S) -> sig … end`. -/
def functorTypeDecl : Decl :=
  .moduleTypeD "FS"
    (.functor "X" (.path "S") (.sig [.val "g" (.arrow Ty.int Ty.int)]))

/-- A structure, a functor, a functor application, and an `include`. -/
def moduleDecls : List Decl :=
  [.moduleD "M" [] none
     [.types [{ name := "t", body := .alias Ty.int }],
      .letD false [{ name := "f", params := [("x", none)],
                     body := .binop "+" (.var "x") (.int 1) }],
      .exn "SigExn" [Ty.int],
      .ext "sig_id" (.arrow tyA tyA) "%identity" [],
      .letD false [{ name := "labelled_",
                     lparams := [Param.named "x", Param.optionalD "y" (.int 0), Param.unit],
                     body := .binop "+" (.var "x") (.var "y") }]],
   .moduleD "F" [("X", .path "S")] none
     [.letD false [{ name := "g", params := [("y", none)],
                     body := Expr.call "X.f" [Expr.call "X.f" [.var "y"]] }]],
   .moduleAliasD "MF" "F (M)",
   .moduleD "MI" [] none
     [.includeD (.path "M"),
      .letD false [{ name := "h", params := [("x", none)], body := Expr.call "f" [.var "x"] }]]]

/-! ### Values -/

/-- A `ref`, a dereference and an assignment. -/
def counterDecls : List Decl :=
  [.letD false [{ name := "counter", body := .mkRef (.int 0) }],
   .letD false
     [{ name := "bump", params := [("()", none)],
        body := .seq (.assign (.var "counter") (.binop "+" (.deref (.var "counter")) (.int 1)))
                     (.deref (.var "counter")) }]]

/-- `let rec … and …`, with `if`, and the operator table's `*`, `-`, `<=`, `mod`, `=`. -/
def recDecls : Decl :=
  .letD true
    [{ name := "fact", params := [("n", some Ty.int)], result := some Ty.int,
       body := .ifThen (.binop "<=" (.var "n") (.int 1)) (.int 1)
                 (.binop "*" (.var "n") (Expr.call "fact" [.binop "-" (.var "n") (.int 1)])) },
     { name := "is_even", params := [("n", some Ty.int)], result := some Ty.bool,
       body := .binop "=" (.binop "mod" (.var "n") (.int 2)) (.int 0) }]

/-- Labelled and optional parameters, with a default. -/
def labelledDecl : Decl :=
  .letD false
    [{ name := "labelled",
       lparams := [Param.named "a", Param.optionalD "b" (.int 2), Param.unit],
       result := some Ty.int,
       body := .binop "+" (.var "a") (.var "b") }]

/-- Every literal form, including the negative integer and the float, whose spelling is the
caller's (`Expr.float`'s docstring). -/
def literalsDecl : Decl :=
  .letD false
    [{ name := "literals", params := [("()", none)], result := some Ty.int,
       body :=
         .letIn "c" (.char 'x') <|
         .letIn "f" (.float "0x1.8p1") <|
         .letIn "s" (.str "a\tb\"q") <|
         .letIn "b" (.bool true) <|
         .seq (Expr.ignoreE (.var "c")) <|
         .seq (Expr.ignoreE (.var "f")) <|
         .seq (Expr.ignoreE (.var "s")) <|
         .seq (Expr.ignoreE (.var "b")) <|
         .intOf (-3) }]

/-- Arrays: a literal, a read and a write. -/
def arraysDecl : Decl :=
  .letD false
    [{ name := "arrays", params := [("()", none)], result := some Ty.int,
       body :=
         .letIn "a" (.arrayLit [.int 1, .int 2, .int 3])
           (.seq (.arraySet (.var "a") (.int 0) (.int 9))
             (.binop "+" (.arrayGet (.var "a") (.int 0)) (.arrayGet (.var "a") (.int 1)))) }]

/-- `for`, `while`, and `if … then` with no `else`. -/
def loopsDecl : Decl :=
  .letD false
    [{ name := "loops", params := [("()", none)], result := some Ty.int,
       body :=
         .letIn "s" (.mkRef (.int 0))
           (.seq (.forE "i" (.int 0) (.int 3) false
                    (.assign (.var "s") (.binop "+" (.deref (.var "s")) (.var "i"))))
             (.seq (.whileE (.bool false) .unit)
               (.seq (.ifThenOnly (.bool false) (Expr.call "print_newline" [.unit]))
                 (.deref (.var "s"))))) }]

/-- A `match` with a guard, an or-pattern and a wildcard. -/
def classifyDecl : Decl :=
  .letD false
    [{ name := "classify", params := [("v", some (.named "color"))], result := some Ty.int,
       body :=
         .matchE (.var "v")
           [.mk (.ctor "Blue" [.var "n"]) (some (.binop ">" (.var "n") (.int 0))) (.var "n"),
            .mk (.ctor "Blue" [.wild]) none (.int 0),
            .mk (.orPat (.ctor "Red" []) (.ctor "Green" [])) none (.intOf (-1))] }]

/-- A partial record pattern, a field read, a field write and a functional record update. -/
def pointDecls : List Decl :=
  [.letD false
     [{ name := "read_point", params := [("p", some (.named "point"))], result := some Ty.int,
        body := .matchE (.var "p") [.mk (.recordOpen [("px", .var "x")]) none (.var "x")] }],
   .letD false
     [{ name := "update_point", params := [("p", some (.named "point"))],
        result := some (.named "point"),
        body := .seq (.setField (.var "p") "py" (.binop "+" (.field (.var "p") "py") (.int 1)))
                  (.recordWith (.var "p") [("px", .binop "+" (.field (.var "p") "px") (.int 1))]) }],
   .letD false
     [{ name := "make_point", params := [("()", none)], result := some (.named "point"),
        body := .record [("px", .int 1), ("py", .int 2)] }]]

/-- `try … with`, `raise`, and a constructor with a payload. -/
def caughtDecl : Decl :=
  .letD false
    [{ name := "caught", params := [("()", none)], result := some Ty.int,
       body :=
         .tryWith (.raiseE (.ctor "Boom" [.int 3]))
           [.mk (.ctor "Boom" [.var "n"]) none (.var "n"),
            .mk (.ctor "Plain" []) none (.int 0),
            .mk .wild none (.int 0)] }]

/-- An `exception` pattern in a `match`: OCaml 5 lets a `match` catch as well as match. -/
def exnPatDecl : Decl :=
  .letD false
    [{ name := "exn_pat", params := [("()", none)], result := some Ty.int,
       body :=
         .matchE (.annot (.raiseE (.ctor "Boom" [.int 4])) Ty.int)
           [.mk (.exnPat (.ctor "Boom" [.var "n"])) none (.var "n"),
            .mk (.var "v") none (.var "v")] }]

/-- A polymorphic variant, in a type, an expression and a pattern. -/
def polyDecl : Decl :=
  .letD false
    [{ name := "poly",
       params := [("v", some (.polyVariant .exact [("A", []), ("B", [Ty.int])]))],
       result := some Ty.int,
       body := .matchE (.var "v")
         [.mk (.polyPat "A" none) none (.int 0),
          .mk (.polyPat "B" (some (.var "n"))) none (.var "n")] }]

/-- A list literal, `::`, an `as` pattern, a `function`, and a tuple. -/
def listyDecls : List Decl :=
  [.letD false
     [{ name := "sign", result := some (.arrow Ty.int Ty.int),
        body := .functionE
          [.mk (.int 0) none (.int 0),
           .mk (.var "n") none (.var "n")] }],
   .letD false
     [{ name := "listy", params := [("()", none)], result := some Ty.int,
        body :=
          .letIn "xs" (.listLit [.int 1, .int 2, .int 3])
            (.matchE (.var "xs")
              [.mk (.alias (.cons (.var "hd") .wild) "whole") none
                 (.binop "+" (.var "hd") (Expr.call "List.length" [.var "whole"])),
               .mk (.listPat []) none (.int 0)]) }],
   .letD false
     [{ name := "tupled", params := [("()", none)], result := some Ty.int,
        body :=
          .letPat (.tuple [.var "a", .var "b"]) (.tuple [.int 1, .int 2])
            (.letPat (.constrained (.var "z") Ty.int) (.int 5)
              (.binop "+" (.binop "+" (.var "a") (.var "b")) (.var "z"))) }]]

/-- `let open … in`, `assert`, `lazy` in both an expression and a pattern, and a `_` annotation. -/
def sundryDecls : List Decl :=
  [.letD false
     [{ name := "opened", params := [("()", none)], result := some Ty.int,
        body := .openIn "M" (Expr.call "f" [.int 1]) }],
   .letD false
     [{ name := "lazily", params := [("()", none)], result := some Ty.int,
        body := .letIn "v" (.lazyE (.binop "+" (.int 1) (.int 1)))
                  (.matchE (.var "v") [.mk (.lazyPat (.var "n")) none (.var "n")]) }],
   .letD false
     [{ name := "asserted", params := [("()", none)], result := some Ty.int,
        body := .seq (.assertE (.binop "=" (.int 1) (.int 1))) (.annot (.int 1) .anon) }],
   .letD false
     [{ name := "inlined", params := [("x", none)], body := .var "x", attrs := ["inline"] }],
   .letPatD (.tuple [.var "ga", .var "gb"]) (.tuple [.int 1, .int 2])]

/-! ### Effects: the two handler families -/

/-- `Effect.Deep.match_with` with an inline `retc`/`exnc`/`effc` record, one clause per effect
constructor and the `| _ -> None` default. -/
def handledDecl : Decl :=
  .letD false
    [{ name := "handled", params := [("()", none)], result := some Ty.int,
       body :=
         .matchWith
           (.fn ["()"]
             (.letIn "a" (.perform (.ctor "Ask" [.int 1]))
               (.seq (.perform (.ctor "Beep" [])) (.var "a"))))
           .unit Ty.int "v" (.var "v")
           [.mk (.ctor "Boom" [.var "n"]) none (.var "n")]
           [.mk "Ask" [.var "x"] "k" (.continueK (.var "k") (.binop "+" (.var "x") (.int 1))),
            .mk "Beep" [] "k" (.continueK (.var "k") .unit)] }]

/-- The same handler as a **value**: `Effect.Deep.handler` is a record type, so a handler can be
bound once and passed. `discontinueK` is here rather than in `handled`, so both resumption forms
are compiled. -/
def deepHandlerDecls : List Decl :=
  [.letD false
     [{ name := "deep_handler", result := some (Ty.deepHandler Ty.int Ty.int),
        body := .handler .deep Ty.int (some ("v", .var "v"))
          [.mk (.ctor "Boom" [.var "n"]) none (.var "n")]
          [.mk "Ask" [.var "x"] "k" (.continueK (.var "k") (.binop "+" (.var "x") (.int 10))),
           .mk "Beep" [] "k" (.discontinueK (.var "k") (.ctor "Boom" [.int 7]))] }],
   .letD false
     [{ name := "handled_by_value", params := [("()", none)], result := some Ty.int,
        body := .matchWithK .deep
          (.fn ["()"] (.perform (.ctor "Ask" [.int 5]))) .unit (.var "deep_handler") }],
   .letD false
     [{ name := "try_with_eff", params := [("()", none)], result := some Ty.int,
        body := .tryWithEff (.fn ["()"] (.perform (.ctor "Ask" [.int 2]))) .unit Ty.int
          [.mk "Ask" [.var "x"] "k" (.continueK (.var "k") (.binop "*" (.var "x") (.int 3)))] }]]

/-- `Effect.Shallow`: a handler with no `effc` clause, one with both `continue_with` and
`discontinue_with`, and the `fiber` that feeds them (`stdlib/effect.ml:110-160`). For a shallow
handler the answer type the clauses annotate is the **fiber's** result type. -/
def shallowDecls : List Decl :=
  [.letD false
     [{ name := "plain_shallow", result := some (Ty.shallowHandler Ty.int Ty.int),
        body := .handler .shallow Ty.int (some ("v", .var "v"))
          [.mk (.ctor "Boom" [.var "n"]) none (.var "n")] [] }],
   .letD false
     [{ name := "shallow_handler", result := some (Ty.shallowHandler Ty.int Ty.int),
        body := .handler .shallow Ty.int (some ("v", .var "v"))
          [.mk (.ctor "Boom" [.var "n"]) none (.var "n")]
          [.mk "Beep" [] "k" (.shallowContinue (.var "k") .unit (.var "plain_shallow")),
           .mk "Ask" [.wild] "k"
             (.shallowDiscontinue (.var "k") (.ctor "Boom" [.int 1]) (.var "plain_shallow"))] }],
   .letD false
     [{ name := "shallowed", params := [("()", none)], result := some Ty.int,
        body :=
          .letIn "fib"
            (Expr.call "Effect.Shallow.fiber"
              [.fn ["()"] (.seq (.perform (.ctor "Beep" [])) (.int 7))])
            (Expr.call "Effect.Shallow.continue_with"
              [.var "fib", .unit, .var "shallow_handler"]) }]]

/-! ### The driver -/

/-- Every row the fixture prints, in order. `tools/ml-check.sh` diffs the program's stdout
against this list, so a change in what the fixture *computes* is caught as well as a change in
what it renders. -/
def expectedRows : List String :=
  ["1", "6", "-3", "11", "6", "3", "1", "3", "4", "2", "4", "1", "3", "2", "1", "5", "8", "2",
   "6", "7", "3"]

private def say (e : Expr) : Expr :=
  Expr.call "print_endline" [Expr.call "string_of_int" [e]]

/-- `let () = …`: every value above is called, so the fixture is executed and not only
compiled. Each row is offset by a constant so that a wrong answer is a wrong row rather than a
coincidence. -/
def mainDecl : Decl :=
  .letD false
    [{ name := "()",
       body :=
         (([say (Expr.call "bump" [.unit]),
            say (Expr.call "fact" [.int 3]),
            say (Expr.call "literals" [.unit]),
            say (Expr.call "arrays" [.unit]),
            say (Expr.call "loops" [.unit]),
            say (.appL (.var "labelled") [(.lbl "a", .int 1), (.nolabel, .unit)]),
            say (Expr.call "classify" [.ctor "Blue" [.int 1]]),
            say (.binop "+" (Expr.call "read_point" [Expr.call "make_point" [.unit]]) (.int 2)),
            say (.binop "+" (Expr.call "caught" [.unit]) (.int 1)),
            say (.binop "-" (Expr.call "exn_pat" [.unit]) (.int 2)),
            say (Expr.call "poly" [.polyCtor "B" (some (.int 4))]),
            say (Expr.call "sign" [.int 1]),
            say (.binop "-" (Expr.call "listy" [.unit]) (.int 1)),
            say (.binop "-" (Expr.call "tupled" [.unit]) (.int 6)),
            say (.binop "-" (Expr.call "opened" [.unit]) (.int 1)),
            say (Expr.call "MI.h" [.int 4]),
            say (Expr.call "MF.g" [.int 6]),
            say (Expr.call "lazily" [.unit]),
            say (.binop "+" (Expr.call "handled" [.unit]) (.int 4)),
            say (.binop "-" (Expr.call "handled_by_value" [.unit]) (.int 8)),
            say (.binop "-" (Expr.call "shallowed" [.unit]) (.int 4))] : List Expr).foldr
           (fun a b => Expr.seq a b)
           (.seq (Expr.ignoreE (Expr.call "try_with_eff" [.unit]))
             (.seq (Expr.ignoreE (Expr.call "update_point" [Expr.call "make_point" [.unit]]))
               (Expr.ignoreE (.var "asserted"))))) }]

/-- The whole fixture, in declaration order. -/
def fixture : Module :=
  { name := "ml_fixture",
    header := some "Generated by OCaml5.MlTest. Every syntax form of OCaml5.Ml.Syntax.",
    items :=
      [.floatingAttrD "warning \"-a\"",
       .comment "Types.",
       colorDecl, pointDecl, treeDecls, phantomDecl] ++ miscTypeDecls ++
      [shapeExtDecl, gadtDecl, inlineRecordDecl] ++ exnDecls ++
      [effectDecl, externalDecl, .blank,
       .comment "Module types and modules.",
       sigDecl, withTypeDecl, functorTypeDecl] ++ moduleDecls ++
      [.blank, .comment "Values.",
       .rawD "let verbatim_line = 0"] ++ counterDecls ++
      [recDecls, labelledDecl, literalsDecl, arraysDecl, loopsDecl, classifyDecl] ++
      pointDecls ++ [caughtDecl, exnPatDecl, polyDecl] ++ listyDecls ++ sundryDecls ++
      [.blank, .comment "Effects.", handledDecl] ++ deepHandlerDecls ++ shallowDecls ++
      [.blank, mainDecl] }

/-! ## (c) The checker

`fixture` passes; ten deliberately bad modules do not, each for exactly one reason. -/

#guard Module.wf fixture
#guard checkModule fixture == []
#guard rawSites fixture == 1

private def wrap (items : List Decl) : Module := { name := "bad", items := items }

/-- A module whose only fault is the named one, and the code it must produce. Ten entries, one
per diagnostic the checker decides. -/
def badModules : List (String × String × Module) :=
  [("unbound value", "unbound-value",
    wrap [.letD false [{ name := "f", params := [("x", none)],
                         body := .binop "+" (.var "x") (.var "nope") }]]),

   ("unbound constructor", "unbound-ctor",
    wrap [.letD false [{ name := "f", params := [("()", none)],
                         body := .ctor "Nope" [.int 1] }]]),

   ("constructor arity, in an expression", "ctor-arity",
    wrap [.types [{ name := "t", body := .variant [{ name := "C", args := [Ty.int] }] }],
          .letD false [{ name := "f", params := [("()", none)],
                         body := .ctor "C" [.int 1, .int 2] }]]),

   ("constructor arity, in a pattern", "ctor-arity",
    wrap [.types [{ name := "t", body := .variant [{ name := "C", args := [Ty.int] }] }],
          .letD false [{ name := "f", params := [("v", none)],
                         body := .matchE (.var "v")
                           [.mk (.ctor "C" [.var "a", .var "b"]) none (.var "a")] }]]),

   ("a type parameter no constructor determines", "undetermined-param",
    wrap [.types [{ name := "t", params := ["a"],
                    body := .record [{ name := "x", ty := Ty.int }] }]]),

   ("the handler's answer type mentions the locally abstract `a`", "effc-abstract",
    wrap [.effects [("Ask", [Ty.int], Ty.int)],
          .letD false [{ name := "h", params := [("()", none)],
                         body := .tryWithEff (.fn ["()"] .unit) .unit (Ty.list (.var "a"))
                           [.mk "Ask" [.var "x"] "k" (.continueK (.var "k") (.var "x"))] }]]),

   ("an `effc` clause on a constructor that is not a declared effect", "effc-unknown",
    wrap [.effects [("Ask", [Ty.int], Ty.int)],
          .letD false [{ name := "h", params := [("()", none)],
                         body := .tryWithEff (.fn ["()"] .unit) .unit Ty.int
                           [.mk "Nope" [] "k" (.continueK (.var "k") .unit)] }]]),

   ("`reperform` outside tail position", "reperform-position",
    wrap [.letD false [{ name := "f", params := [("e", none), ("k", none), ("l", none)],
                         body := .binop "+" (.int 1)
                           (.reperform (.var "e") (.var "k") (.var "l")) }]]),

   ("a record declaration that names a label twice", "duplicate-field",
    wrap [.types [{ name := "t",
                    body := .record [{ name := "x", ty := Ty.int },
                                     { name := "x", ty := Ty.bool }] }]]),

   ("a `let rec … and …` that binds a name twice", "duplicate-binding",
    wrap [.letD true [{ name := "f", params := [("()", none)], body := .int 1 },
                      { name := "f", params := [("()", none)], body := .int 2 }]]),

   ("a value name outside the identifier profile", "bad-name",
    wrap [.letD false [{ name := "Capital", body := .int 1 }]]),

   ("one variant that declares a constructor twice", "duplicate-ctor",
    wrap [.types [{ name := "t", body := .variant [{ name := "C" }, { name := "C" }] }]])]

-- Every bad module produces its code, and nothing produces a code that is not its own.
#guard badModules.all fun entry =>
  let ds := checkModule entry.2.2
  !ds.isEmpty && ds.all (fun d => d.code == entry.2.1)

-- Twelve of them, over eleven distinct codes: `ctor-arity` is exercised twice, once in an
-- expression and once in a pattern.
#guard badModules.length == 12
#guard (badModules.map (·.2.1)).eraseDups.length == 11

-- The good ones are accepted: the fixture, and each bad module with its fault removed.
#guard Module.wf { name := "empty", items := [] }
#guard Module.wf (wrap [.types [{ name := "t", params := ["a"],
                                  body := .record [{ name := "x", ty := .var "a" }] }]])
#guard Module.wf (wrap [.types [{ name := "t",
                                  tparams := [{ name := "a", variance := .covariant }],
                                  body := .record [{ name := "x", ty := Ty.int }] }]])
-- `reperform` in tail position is accepted; the same expression as an operand is not.
#guard Module.wf (wrap [.letD false
  [{ name := "f", params := [("e", none), ("k", none), ("l", none)],
     body := .reperform (.var "e") (.var "k") (.var "l") }]])
#guard !(Module.wf (wrap [.letD false
  [{ name := "f", body := .reperform (.var "e") (.var "k") (.var "l") }]]))

/-! ### The deriving fixture

The plan's ruling is that every generated carrier carries
`[@@deriving sexp, compare, equal, hash, fields, variants]`, which plain `ocamlc` cannot compile:
the attribute needs `ppx_jane`. So the derivers are a **second fixture**, written to
`ml_deriving.ml` and compiled by `tools/ml-check.sh`'s ppx lane — which SKIPs until the `effect4`
opam switch exists. `Check` knows what the attribute puts in scope
(`Profile.derivedNames`), so `probe` below calls `compare_point` and `equal_color` with nothing
declaring them and the checker is satisfied. -/

def derivingFixture : Module :=
  { name := "ml_deriving",
    header := some "Generated by OCaml5.MlTest. Every carrier carries the ppx_jane derivers.",
    items :=
      [.floatingAttrD "warning \"-a\"",
       .types [{ name := "color",
                 body := .variant [{ name := "Red" }, { name := "Green" },
                                   { name := "Blue", args := [Ty.int] }],
                 derivers := janeVariantDerivers }],
       .types [{ name := "point",
                 body := .record [{ name := "px", ty := Ty.int },
                                  { name := "py", ty := Ty.int, isMutable := true }],
                 derivers := janeRecordDerivers }],
       .types [{ name := "tree", params := ["a"],
                 body := .variant [{ name := "Leaf" },
                                   { name := "Node", args := [.con "tree" [.var "a"],
                                                              .var "a",
                                                              .con "tree" [.var "a"]] }],
                 derivers := ["sexp", "compare", "equal"] }],
       .letD false
         [{ name := "probe", params := [("()", none)], result := some Ty.unit,
            body :=
              .letIn "a" (.record [("px", .int 1), ("py", .int 2)]) <|
              .letIn "b" (.recordWith (.var "a") [("px", .int 2)]) <|
              .seq (Expr.ignoreE (Expr.call "compare_point" [.var "a", .var "b"])) <|
              .seq (Expr.ignoreE (Expr.call "equal_color" [.ctor "Red" [], .ctor "Green" []])) <|
              .seq (Expr.ignoreE (Expr.call "sexp_of_color" [.ctor "Blue" [.int 1]])) <|
              .seq (Expr.ignoreE (Expr.call "hash_color" [.ctor "Red" []])) .unit }]] }

#guard Module.wf derivingFixture
#guard ((render derivingFixture).splitOn
  "[@@deriving sexp, compare, equal, hash, variants]").length == 2
#guard ((render derivingFixture).splitOn
  "[@@deriving sexp, compare, equal, hash, fields]").length == 2
-- `compare_point`, `equal_color`, `sexp_of_color` and `hash_color` are in scope because the
-- attribute puts them there, and the checker knows it.
#guard derivedNames "point" janeRecordDerivers ==
  ["sexp_of_point", "point_of_sexp", "compare_point", "equal_point", "hash_point",
   "hash_fold_point"]

/-! ## (e) The profile: what the Lean model can represent

`OCaml5.Ml.Profile` is the admitted construct set and the admitted library surface;
`Check.profile` decides membership and `Check.lawReport` says which named laws a module has come
to depend on. Six modules below: one inside the profile, four outside it for one reason each, and
one whose only point is the law list it produces. -/

/-- A generated carrier module: derivers, and nothing from any library. It is inside the
`carriers-only` profile, which is the profile a generated carrier file should pass. -/
def carrierModule : Module :=
  { name := "carriers",
    items :=
      [.types [{ name := "color",
                 body := .variant [{ name := "Red" }, { name := "Blue", args := [Ty.int] }],
                 derivers := janeVariantDerivers }],
       .types [{ name := "point",
                 body := .record [{ name := "px", ty := Ty.int },
                                  { name := "py", ty := Ty.int, isMutable := true }],
                 derivers := janeRecordDerivers }],
       .letD false
         [{ name := "rank", params := [("c", some (.named "color"))], result := some Ty.int,
            body := Expr.call "Variants.to_rank" [.var "c"] }]] }

#guard Check.inProfile carrierProfile carrierModule
#guard Check.inProfile estateProfile carrierModule
#guard Module.wf carrierModule

-- The laws that module has come to depend on: exactly `Variants.to_rank`'s.
#guard Check.lawsUsed estateProfile carrierModule == ["Variants.to_rank_declaration_order"]
#guard Check.lawReport estateProfile carrierModule ==
  ["Variants.to_rank_declaration_order  unproven — Variants.to_rank is the declaration order "
    ++ "of the constructors: the order a constructor-by-constructor diff uses"]

/-- A module using the dispatcher's queue and map: five laws, all of them W4's. -/
def queueModule : Module :=
  { name := "queue",
    items :=
      [.letD false
         [{ name := "step", params := [("d", none), ("m", none), ("k", none)],
            body :=
              .seq (Expr.call "Base.Deque.enqueue_back" [.var "d", .int 1])
                (.matchE (Expr.call "Base.Map.find" [.var "m", .var "k"])
                  [.mk (.ctor "None" []) none .unit,
                   .mk (.ctor "Some" [.var "v"]) none
                     (Expr.ignoreE (Expr.call "Base.Deque.dequeue_front" [.var "v"]))]) }]] }

#guard Check.inProfile estateProfile queueModule
#guard Check.lawsUsed estateProfile queueModule ==
  ["Deque.fifo", "Map.find_set_same", "Map.find_set_other", "Map.find_remove_same",
   "Map.find_remove_other", "Map.ext_find"]
-- …and five of those six are already theorems, in seat W4's `workshop/OCaml5/Lib/Map.lean`.
-- The one that is not is `Deque.fifo`, which is the law the scheduling order rests on.
#guard (Check.lawsUsed estateProfile queueModule).filter
  (fun n => match lawOf n with | some l => l.site.isNone | none => true) == ["Deque.fifo"]

/-- The four ways to leave the profile, one module each. -/
def outOfProfile : List (String × String × Module) :=
  [("a module the profile refuses outright", "profile-banned",
    { name := "bad", items :=
        [.letD false [{ name := "f", params := [("x", none)],
                        body := Expr.call "Obj.magic" [.var "x"] }]] }),

   ("a module the profile does not admit", "profile-module",
    { name := "bad", items :=
        [.letD false [{ name := "f", params := [("x", none)],
                        body := Expr.call "Zarith.Q.of_int" [.var "x"] }]] }),

   ("an admitted module, an unlisted value", "profile-value",
    { name := "bad", items :=
        [.letD false [{ name := "f", params := [("d", none)],
                        body := Expr.call "Base.Deque.peek_back_exn" [.var "d"] }]] }),

   ("a construct the profile does not admit", "profile-construct",
    { name := "bad", items := [.letD false [{ name := "f", params := [("()", none)],
                                              body := .lazyE (.int 1) }]] })]

-- Each leaves the profile for exactly its own reason. The construct case is checked against a
-- narrowed profile, since the estate's admits every construct.
#guard (outOfProfile.take 3).all fun entry =>
  let ds := Check.profile estateProfile entry.2.2
  !ds.isEmpty && ds.all (fun d => d.code == entry.2.1)

#guard
  let narrow : Profile := { estateProfile with
                            constructs := allConstructs.filter (· != "expr.lazyE") }
  let ds := Check.profile narrow (outOfProfile.getD 3 ("", "", { name := "x", items := [] })).2.2
  ds.length == 1 && (ds.getD 0 { code := "", site := "", detail := "" }).code
    == "profile-construct"

-- The fixture of (a) is not inside the estate profile, and should not be: it names `M`, `MI`,
-- `MF` and `List.length`, which are its own modules and OCaml's `Stdlib.List`, neither of which
-- a *library* profile admits. That is the profile working, and it is why `carrierModule` — a
-- generated carrier, which is what a profile is for — is the one that passes.
#guard !(Check.inProfile estateProfile fixture)

/-! ## (f) A description of an OCaml library type

`Reflect.ofTypeDecl` is the other direction: an OCaml declaration, as signature data, becomes the
`TypeDesc` a Lean carrier is stated against. Here it is on a slice of `Base.Deque`'s interface,
written as `Ml.Syntax` data. Once the `effect4` switch exists, `tools/ml-check.sh`'s ppxlib lane
is what turns a real `.mli` into this data. -/

def dequeSig : ModTy :=
  .sig [.types [{ name := "elt", params := ["a"], body := .alias (.var "a") }],
        .types [{ name := "snapshot", params := ["a"],
                  body := .record [{ name := "front", ty := Ty.list (.var "a") },
                                   { name := "back", ty := Ty.list (.var "a") }] }],
        .val "create" (.arrow Ty.unit (.con "t" [.var "a"])),
        .val "dequeue_front" (.arrow (.con "t" [.var "a"]) (Ty.option (.var "a")))]

#guard (ofModTy [] "base/deque.mli" dequeSig).length == 1
#guard (ofModTy [] "base/deque.mli" dequeSig).map TypeDesc.leanName == ["Snapshot"]
#guard (match (ofModTy [] "base/deque.mli" dequeSig).getD 0 (.struct default) with
        | .struct d => d.fields.map (·.leanName)
        | _ => []) == ["front", "back"]

/-! ## (d) The identifier mangling round-trips -/

#guard (Ml.Avatar.runFiber.fields.map (·.leanName)).all
  (fun n => unmangleField (mangleField n) == n)
#guard (Ml.Avatar.frameFiber.fields.map (·.leanName)).all
  (fun n => unmangleField (mangleField n) == n)
#guard (Ml.Avatar.inductives.flatMap (fun d => d.ctors.flatMap (fun c =>
          c.args.map (·.leanName)))).all
  (fun n => unmangleField (mangleField n) == n)
#guard ["exit", "type", "currentOpCount", "a_b", "aB", "x'", "ABC", "", "let", "a__b",
        "a.b", "ν", "f0", "_x", "with", "μ'", "A_B_c", "0", "__"].all
  (fun n => unmangleField (mangleField n) == n)

-- …and the mangling separates what a naive camel-to-snake would collapse.
#guard mangleField "aB" != mangleField "a_b"
#guard mangleField "exit" == "exit_"

/-! ## Emitting the fixture

`tools/ml-check.sh <dir>` runs this and then compiles what it writes. -/

/-- Write `ml_fixture.ml` and `ml_fixture.rows` into the directory named by the first
argument. -/
def emit (args : List String) : IO Unit := do
  let dir := args.getD 0 "."
  IO.FS.writeFile (dir ++ "/" ++ fixture.fileName) (render fixture)
  IO.FS.writeFile (dir ++ "/" ++ derivingFixture.fileName) (render derivingFixture)
  IO.FS.writeFile (dir ++ "/ml_fixture.rows")
    (String.join (expectedRows.map (· ++ "\n")))
  IO.println s!"ml_fixture {fixture.items.length} declarations, \
{(render fixture).length} bytes, {expectedRows.length} rows"
  IO.println s!"ml_deriving {derivingFixture.items.length} declarations"
  let diags := checkModule fixture ++ checkModule derivingFixture
  if diags.isEmpty then IO.println "check      OK"
  else do
    IO.println "check      FAILED"
    for d in diags do IO.println ("  " ++ d.toLine)
  let pdiags := Check.profile carrierProfile carrierModule
  if pdiags.isEmpty then
    IO.println s!"profile    OK (carriers-only; {estateProfile.valueCount} values admitted, \
{estateProfile.refusals.length} of {estateProfile.modules.length} modules unmodelled)"
  else do
    IO.println "profile    FAILED"
    for d in pdiags do IO.println ("  " ++ d.toLine)
  IO.println "laws       the generated carriers depend on:"
  for l in Check.lawReport estateProfile carrierModule do IO.println ("  " ++ l)

end OCaml5.MlTest

/-- `lake env lean --run workshop/OCaml5/MlTest.lean <dir>`, which is what
`tools/ml-check.sh` invokes. -/
def main (args : List String) : IO Unit := OCaml5.MlTest.emit args
