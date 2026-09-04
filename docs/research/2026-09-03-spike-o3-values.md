# Spike O3: the value profile of OCaml 5.1.1 and js_of_ocaml 5.7.1

Status: spike report, 2026-09-03. Base commit `b47c292` (`main`). Row O3 of
`docs/research/2026-09-03-ocaml5-deep-plan.md`, and ruling 6 of that plan ("values are
backend-relative"). Files owned and written by this spike:

| File | What | Lines |
| --- | --- | ---: |
| `workshop/OCaml5/Value.lean` | the profile: `Backend`, `Host`, `Ty`, `Val`, the operations, a `Backend`-indexed evaluator, and 51 `#guard`s | 1577 |
| `workshop/OCaml5/values/w_{int,boxed,float,string,block,closure,compare}.ml` | seven witness programs, 215 printed rows | 330 |
| `workshop/OCaml5/values/p_jsrepr.{ml,js}` | the js_of_ocaml-only representation probe, 34 rows | 101 |
| `workshop/OCaml5/values/run-values.sh` | the runner: four hosts, one TSV per host, the comparison report | 74 |
| `workshop/OCaml5/values/check-transcription.py` | checks that `Value.lean`'s transcribed rows are the observed ones | 56 |
| `workshop/OCaml5/values/out/*.tsv` | the executed observations, 33 files | — |

Nothing else was touched. No `sorry`, no `axiom`, no `partial`, no `unsafe`, no
`native_decide`, no `implemented_by`.

## Summary

1. **215 facts, 38 of which differ between the two backends.** Every fact is a row printed by
   an OCaml program compiled and run on four hosts; every row is transcribed into
   `Value.lean` and predicted there. `lake build OCaml5.Value` is green, and each of the 51
   `#guard`s passes.
2. **Exactly one fact differs between `ocamlopt` and `ocamlrun`** (`phys_tuple`), and
   **exactly one is changed by `--disable use-js-string`** (`string_phys_eq`). Both are `==`
   on immutable values, which OCaml leaves unspecified; the profile classifies them as
   `PhysEq.unspecified` and `Host.physEqStrings` rather than predicting a Boolean. Ruling 3 of
   the plan asks for a bytecode/native difference to be reported as a finding: this is the one,
   and it is a constant-sharing decision in `ocamlopt`, not a value-representation difference.
3. **js_of_ocaml 5.7.1 disagrees with itself about `int_of_float`.** Its constant folder
   *saturates* (`int_of_float 1e18` folds to `2147483647`), while the code it emits for the same
   expression at run time is `x | 0` (`generate.ml:326,947`), which gives `-1486618624`. Both
   are witnessed, as `int_of_float_big_fold` and `int_of_float_big_rt`. This is a defect, not a
   width difference, and it is the one row where "the js_of_ocaml semantics" is not a function
   of the source program alone.
4. **`Hashtbl.hash 0.0 = Hashtbl.hash 0` under js_of_ocaml and not natively.** An integral
   `float` is a JS number, indistinguishable from an `int`, so `0.0`, `-0.0` and `0` all hash to
   `129913994` there; natively `0.0` is a `Double_tag` block and hashes to `256347020`. A
   non-integral float (`1.5`) hashes the same on both hosts.
5. **The `use-js-string` flag is observationally inert at the OCaml level**, on everything but
   `==`. `String.length`, byte access, `sub`, `^`, `compare` and `=` all agree on the two
   js_of_ocaml builds. The flag is nonetheless carried in the profile as `Host.strings`,
   because the *representation* it selects is visible to the probe (`jsstring[3]:"abc"` versus
   `MlBytes{t=0,l=3,c="abc"}`), and because the one `==` row needs it.
6. **The NaN bit pattern is not the same.** `Int64.bits_of_float (0.0 /. 0.0)` is
   `7ff8000000000000` natively and `7ff0000000000001` under js_of_ocaml, because
   `ieee_754.js:33-42` hands back a fixed triple for every NaN rather than the host float's
   own pattern. Every other float in the corpus has identical bits on both hosts, and every
   *printed* float is the same string on both.
7. **`caml_call_gen` is the same law as `caml_apply`.** All nine partial- and
   over-application rows agree on the two backends, including the effect count: an effect
   between two arities happens once per real application and not per partial step.

## 1. Method

A fact is a `key<TAB>value` line printed by a witness program. `values/run-values.sh` compiles
each `w_*.ml` four ways and runs it:

```
ocamlopt -o w.native w.ml                                   # native, OCaml 5.1.1
ocamlc   -o w.byte   w.ml   &&  ocamlrun w.byte             # bytecode, OCaml 5.1.1
js_of_ocaml compile --target-env=nodejs w.byte -o w.js      # jsoo 5.7.1, use-js-string on
js_of_ocaml compile --target-env=nodejs --disable use-js-string w.byte -o w.nostr.js
```

with `node` v22.23.2. The four outputs are joined into `values/out/all.tsv`
(`witness, key, native, byte, jsoo, jsoo-nostr`) and the disagreeing rows into
`values/out/differ.tsv`.

`Value.lean` then states the profile as a `Backend`-indexed evaluator over a small expression
language (`Expr`, `EVal`, `eval`, `run`), and each fact becomes a `Fact` record carrying the
program and the two transcribed observations:

```lean
⟨"w_int", "lsl_1_62", "-4611686018427387904", "1073741824", .shiftE .shl (ei 1) 62⟩
```

`#guard (facts.filter (fun f => !f.holds)).map (·.key) = []` is the check: for each row,
`run .native prog` must equal the native column and `run .jsoo prog` the js_of_ocaml column.
The failing keys are *named* rather than counted, so a regression says which fact broke.

Three kinds of fact are not a single computed value, and get their own claims instead:

- **float printing** (15 rows) — `caml_format_float` is not reimplemented; the claim is
  *agreement*, `#guard floatPrintingAgrees`, plus the observation that the one exception
  (`float_of_int_max`) is entirely the int width, checked as
  `#guard … = [toString Backend.jsoo.maxInt]`.
- **`Hashtbl.hash`** (15 rows) — `caml_hash` is not reimplemented; the claims are *relations
  between rows*, nine of them, each a `#guard` (§4.4).
- **physical equality** (2 rows) — classified as `PhysEq.yes` / `.no` / `.unspecified`.

`values/check-transcription.py`, run as the last step of the runner, closes the loop the
`#guard`s leave open: the `#guard`s check that the profile *predicts* the transcribed rows, and
the checker checks that the transcribed rows are the *observed* ones, byte for byte, for all
215 plus the 34 probe rows.

### 1.1 The js_of_ocaml representation probe

`Obj.tag`/`Obj.size`/`Obj.is_int` answer in OCaml's own alphabet on both hosts (`obj.js`
translates), so they cannot see the JavaScript side. `values/p_jsrepr.js` overrides `caml_hash`
— the one runtime primitive that receives an arbitrary OCaml value and can be redefined from an
extra runtime file — so that `Hashtbl.hash (key, v)` prints a description of `v`'s JS
representation. Bytecode cannot link a fresh external (`ocamlc` refuses at link time with
"The external function … is not available"), which is why the hook has to be an existing
primitive and why the probe is js_of_ocaml-only; on the native side the corresponding facts are
the `mlvalues.h` header layout, already witnessed through `Obj` by `w_block.ml`.

`Host.jsRepr` in `Value.lean` is the profile's prediction of that printer, and
`#guard (jsFacts.filter (fun f => !f.holds)).map (·.key) = []` checks all 28 data rows against
both `use-js-string` settings. The six closure rows are predicted by `jsClosure`.

## 2. The census

| | Count |
| --- | ---: |
| Facts | 215 |
| …computed by the evaluator | 183 |
| …float printings (agreement claim) | 15 |
| …hashes (relation claims) | 15 |
| …physical equality (classification) | 2 |
| Facts where native ≠ js_of_ocaml | 38 |
| Facts where `ocamlopt` ≠ `ocamlrun` | 1 |
| Facts changed by `--disable use-js-string` | 1 |
| js_of_ocaml representation probe rows | 34 |
| `#guard`s in `Value.lean` | 51 |

## 3. The findings

Every row where the two backends disagree, grouped by cause. All 38 are in the table of §5,
marked **≠**.

### F1 — the int width (23 rows)

`Sys.int_size` is 63 natively (`mlvalues.h:77-80`: one tag bit in a 64-bit word) and 32 under
js_of_ocaml (`ints.js:90`, `generate.ml:326`: every integer result is `| 0`). This is ruling 6's
falsifier and it propagates: `max_int`, `min_int`, `add_2p31m1_1`, `add_max_1`, `sub_min_1`,
`mul_overflow`, `mul_big`, `neg_min`, `div_min_m1`, `abs_min`, `succ_max`, `int_size`,
`lsr_neg1_1`, `lsr_neg7_1`, `int_of_string_2p31`, `int64_of_int_max`, `int64_to_int_big`,
`float_of_int_max`, `float_of_int_max_bits`, `hash_int_max`, `nativeint_size`,
`nativeint_max`, `nativeint_max_succ`.

`Nativeint` is not a separate width under js_of_ocaml: `generate.ml:1981-1990` maps every
`Nativeint` primitive onto the `int` one, so `Nativeint.size` is 32 there and 64 natively.
`Int32` and `Int64` are the same width on both.

Modelled by `Backend.intBits`, `Backend.nativeintBits`, `wrap` and `Backend.arith`.

### F2 — the shift count is masked to 5 bits under js_of_ocaml (3 rows)

`generate.ml:925-927` emits the raw JS `<<`, `>>` and `>>>`, whose right operand is taken
modulo 32. So `1 lsl 32` is `1` and `1 lsl 62` is `1073741824` (`1 << 30`), where natively they
are `4294967296` and `min_int`. `lsl_1_31` differs for the width reason instead. Modelled by
`Backend.shiftBy` taking `n % k.width b`.

OCaml leaves a shift by more than the width unspecified, so this is conformant — but it is a
row a compiler-independent model would get wrong, and the profile has to carry it.

### F3 — js_of_ocaml's constant folder saturates `int_of_float`; its runtime truncates (2 rows)

| | `int_of_float 1e18` |
| --- | --- |
| native, both compilers | `1000000000000000000` |
| js_of_ocaml, argument known at compile time | `2147483647` |
| js_of_ocaml, argument written through a `ref` | `-1486618624` |

`generate.ml:326` defines `to_int cx = cx | 0` and `:947` uses it for `caml_int_of_float`, so
`-1486618624` = `wrap 32 (10^18)` is the compiled semantics. The folded `2147483647` is
`Backend.jsoo.maxInt`, i.e. a saturating conversion, and it is not what the emitted runtime
does. `Sys.opaque_identity` does not defeat the fold — the witness has to route the float
through a reference.

Modelled by two distinct expression forms, `Expr.intOfFloatE` (the runtime, `floatToInt` then
`wrapInt`) and `Expr.intOfFloatFoldE` (the folder, saturating). A model with only one of them
is wrong for half the programs.

### F4 — the NaN bit pattern (1 row)

`Int64.bits_of_float (0.0 /. 0.0)` is `7ff8000000000000` natively (the canonical quiet NaN the
hardware produces) and `7ff0000000000001` under js_of_ocaml, because `ieee_754.js:33-42` returns
the fixed triple `caml_int64_create_lo_mi_hi(1, 0, 0x7ff0)` for *any* NaN instead of reading the
host float's bits. Modelled by `Backend.floatBits`, which is the identity on native and the
constant on js_of_ocaml for NaN.

Every other float in the corpus — `0.1 +. 0.2`, `-0.0`, `sqrt 2.`, `max_float`, `min_float`,
`epsilon_float`, `±infinity`, `float_of_string "0.1"` — has identical bits and an identical
printed form on both hosts. `nan`, `inf` and `-inf` also *print* identically; it is only the bit
pattern that moves.

### F5 — js_of_ocaml cannot tell an integral float from an int (5 rows)

`float_tag` is 253 natively and 1000 (immediate) under js_of_ocaml; `boxed_float` shows as
`blk:253/1` natively and `imm:1.5` there — `Obj.is_int` answers `true` on a float. The same
collapse is what makes `hash_zero` and `hash_neg0` equal `hash_int_0` under js_of_ocaml and not
natively. `int32_tag` and `nativeint_tag` are 255 (`Custom_tag`) natively and 1000 there, for
the same reason.

`Int64` is the exception: it is a `Custom_tag` block natively *and* an object under
js_of_ocaml (`MlInt64{lo,mi,hi}`, three limbs of 24/24/16 bits), so `int64_tag` is 255 on both
and every `Int64` arithmetic row agrees.

Modelled by `Backend.objIsInt`, `Backend.objTag`, `Backend.objView`, `jsInt64`.

### F6 — a js_of_ocaml closure has no size (1 row)

`Obj.size` of a closure is 2 natively (`Closure_tag` 247 with the code pointer and the arity
word) and 0 under js_of_ocaml, where it is a JS function and `obj.js` has nothing to count. The
tag is 247 on both. Modelled by `Backend.closureSize`.

### F7 — `==` on an immutable value (2 rows, and the only intra-backend split)

| Fact | native | bytecode | jsoo | jsoo `--disable use-js-string` |
| --- | --- | --- | --- | --- |
| `phys_tuple`: two separately built `(1, 2)` | `true` | `false` | `false` | `false` |
| `string_phys_eq`: `"abc" == String.sub "xabcx" 1 3` | `false` | `false` | `true` | `false` |

`phys_tuple` is `ocamlopt` sharing a constant that `ocamlc` does not; the language leaves `==`
on immutable blocks unspecified, so the profile answers `PhysEq.unspecified` rather than a
Boolean. `string_phys_eq` is the one place the `use-js-string` flag is observable from OCaml:
with the flag on (`config.ml:93`, the default), an OCaml string *is* a JS primitive string
(`mlBytes.js:707-713`, `caml_string_of_jsbytes` is the identity), and `===` on primitive strings
is by value. `Host.physEqStrings` predicts all four cells.

### F8 — the rows that are *not* findings, and are worth saying so

Structural `compare` and `=` agree on all 31 rows, including the whole float order: `compare nan
nan = 0`, `compare nan 1.0 = -1`, `nan = nan` is `false`, `nan < 1.0` is `false`,
`compare (-0.0) 0.0 = 0` and `-0.0 = 0.0` is `true` on both. So does the physical-equality
short-circuit that makes `compare f f = 0` on a closure while `f = f` raises
`Invalid_argument "compare: functional value"` — `caml_compare` passes `total = true`
(`compare.js:239`, and the `!(total && a === b)` test at `:69`), `caml_equal` does not
(`:246`).

Strings are byte sequences on both: `String.length "héllo"` is 6, `s.[1]` is 195, `String.sub`,
`^`, `Bytes.set`, `Bytes.blit_string` and `String.uppercase_ascii` all agree byte for byte, with
`use-js-string` on or off. Blocks carry the same tags and sizes: constant constructors are
immediates numbered from 0, non-constant ones are blocks numbered from 0, records are tag 0,
all-float records and float arrays are tag 254, exception constructors are tag 248 with two
fields. Partial and over-application agree, including the effect count.

## 4. What the profile is

`workshop/OCaml5/Value.lean`, section by section.

### 4.1 Hosts and widths

`Backend` is `native | jsoo` (ruling 6). `Host` is a `Backend` plus a `StringRepr`
(`jsString | byteArray`), which is the `use-js-string` flag; `Host.native`, `Host.jsoo` and
`Host.jsooNoStr` are the three built configurations. `Backend.intBits` is 63/32,
`Backend.nativeintBits` 64/32. `wrap bits`, `unsigned bits`, `Backend.maxInt`, `minInt`.

### 4.2 `Ty`, `Val`, and the hand-written `DecidableEq`

`Val` covers `unit`, `bool`, `int`, `char`, `float`, `string`, `bytes`, `int32`, `int64`,
`nativeint` and `block (tag) (fields)`. Both `Ty` and `Val` are *nested* inductives (`List Ty`,
`List Val`), which the `DecidableEq` deriving handler does not cover, so `Ty.beq`/`Ty.beqList`
and `Val.beq`/`Val.beqList` are written out as mutual pairs and installed as `BEq`. `Float` has
no lawful `DecidableEq`, so the float payload is compared through `Float.toBits`; OCaml's own
float equality is `floatEqual` (IEEE) and its order is `floatCompare` (total, NaN least), kept
separate.

`Val.checks : Backend → Val → Ty → Bool` is the typing judgement, and it is backend-relative:
`Val.checks .jsoo (.int 2147483648) .int` is `false` while the native one is `true`.

Closures are deliberately *not* `Val`s. They are `EVal.clos`, so `Val` stays first-order and
`compare` can refuse them the way OCaml does.

### 4.3 The operations

`Backend.arith` (add, sub, mul, div, rem, and the three bitwise operations, on `int`, `int32`,
`int64`, `nativeint` and `float`), `Backend.shiftBy` (`lsl`, `asr`, `lsr`, with the count masked
to the width), `Backend.negate`, `absolute`, `bitnot`, `intOfString`, `floatBits`,
`floatToInt`/`intToFloat`, `Backend.objIsInt`/`objTag`/`objSize`/`objView`,
`Val.compareVal`/`equalVal`/`lessVal`, `cmpBytes`.

Division and remainder truncate toward zero on both hosts (`Int.tdiv`/`Int.tmod`), and the
result is wrapped: `min_int / (-1)` is `min_int` on both, at their respective widths.

### 4.4 The evaluator

`Expr` is a small language — literals, de Bruijn variables, `lam (id) (arity)`, `app` with an
argument *list*, `let`, `seq`, an observable `tick`, `countOf`, the arithmetic and comparison
forms, the `Obj` forms, the string and bytes forms, block construction and field access, the
integer conversions, and the two `int_of_float`s. `eval` is fuel-bounded and total; `run b e`
renders what the witness printed.

`applyMany` is `caml_call_gen` (`stdlib.js:23-70`) written out: with `d = arity - #args`,
`d = 0` runs the body, `d > 0` returns a closure remembering the arguments so far (which is
where the JS wrapper gets `g.l = d`), and `d < 0` runs the body on the first `arity` arguments
and applies the result to the rest. The same law is native OCaml's `caml_apply`, and that is
why every `w_closure.ml` row agrees on the two hosts.

`Expr.cmpE` carries the physical-equality short-circuit for closures; `Expr.eqE` does not, and
raises.

### 4.5 The hash claims

Nine `#guard`s over the transcribed hash table:

- `hash ()` = `hash None` = `hash 0` on both hosts (all three are the immediate 0);
- `hash true` = `hash 1` on both;
- `hash 0.0` = `hash (-0.0)` = `hash 0` **under js_of_ocaml**;
- `hash 0.0` ≠ `hash 0` **natively**;
- `hash (-0.0)` = `hash 0.0` on each host;
- `hash` of a non-integral float, a string, a UTF-8 string, a tuple, a list and an `Int64` is
  the same on both hosts;
- `hash max_int` under js_of_ocaml = `hash 2147483647` under js_of_ocaml;
- `hash 2147483647` is the same on both hosts;
- `hash max_int` differs between the hosts.

## 5. Every fact

Native sources are under
`~/.opam/default/.opam-switch/sources/ocaml-base-compiler.5.1.1/runtime/`; js_of_ocaml sources
under `~/.opam/4.14.2/.opam-switch/sources/js_of_ocaml-compiler.5.7.1/`, `runtime/` for the
`.js` files and `compiler/lib/` for the `.ml` ones. The `native` and `js_of_ocaml` columns are
the `ocamlopt` and default-`js_of_ocaml` columns of `values/out/all.tsv`; the `ocamlrun` column
equals `native` except at `phys_tuple`, and the `--disable use-js-string` column equals
`js_of_ocaml` except at `string_phys_eq`.

#### `w_block.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `ctor_A` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:0` | `imm:0` | `Backend.objView` |  |
| `ctor_B` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/1` | `blk:0/1` | `Backend.objView` |  |
| `ctor_C` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:1/2` | `blk:1/2` | `Backend.objView` |  |
| `ctor_D` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:2/1` | `blk:2/1` | `Backend.objView` |  |
| `field_B0` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `7` | `7` | `Expr.fieldE` |  |
| `field_C1` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `2` | `2` | `Expr.fieldE` |  |
| `record` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/2` | `blk:0/2` | `Backend.objView` |  |
| `float_record` | mlvalues.h:349 | generate.ml (Block, tag at index 0) | `blk:254/2` | `blk:254/2` | `Backend.objView` |  |
| `tuple2` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/2` | `blk:0/2` | `Backend.objView` |  |
| `tuple3` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/3` | `blk:0/3` | `Backend.objView` |  |
| `none` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:0` | `imm:0` | `Backend.objView` |  |
| `some` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/1` | `blk:0/1` | `Backend.objView` |  |
| `nil` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:0` | `imm:0` | `Backend.objView` |  |
| `cons` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/2` | `blk:0/2` | `Backend.objView` |  |
| `int_array` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/3` | `blk:0/3` | `Backend.objView` |  |
| `float_array` | mlvalues.h:349 | generate.ml (Block, tag at index 0) | `blk:254/3` | `blk:254/3` | `Backend.objView` |  |
| `string_array` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/1` | `blk:0/1` | `Backend.objView` |  |
| `unit` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:0` | `imm:0` | `Backend.objView` |  |
| `true` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:1` | `imm:1` | `Backend.objView` |  |
| `false` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:0` | `imm:0` | `Backend.objView` |  |
| `char` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `imm:97` | `imm:97` | `Backend.objView` |  |
| `boxed_float` | mlvalues.h:336 | obj.js (a JS number is an immediate) | `blk:253/1` | `imm:1.5` | `Backend.objView` | **≠** |
| `closure` | mlvalues.h (Closure_tag 247) | stdlib.js:23-70; obj.js | `blk:247/2` | `blk:247/0` | `Backend.objView` | **≠** |
| `exn_ctor` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:248/2` | `blk:248/2` | `Backend.objView` |  |
| `exn_arg` | mlvalues.h:72,328-401 | generate.ml (Block, tag at index 0) | `blk:0/2` | `blk:0/2` | `Backend.objView` |  |
| `double_field` | mlvalues.h:349 | generate.ml (Block, tag at index 0) | `2.5` | `2.5` | `Expr.fieldE` + `trimFloat` |  |
| `array_get_float` | mlvalues.h:349 | generate.ml (Block, tag at index 0) | `2.5` | `2.5` | `Expr.fieldE` + `trimFloat` |  |
| `array_len_float` | mlvalues.h:349 | generate.ml (Block, tag at index 0) | `2` | `2` | `Backend.objSize` |  |

#### `w_boxed.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `int32_size` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `32` | `32` | `IntKind.width` |  |
| `nativeint_size` | ints.c; mlvalues.h:401 | generate.ml:1981-1990 | `64` | `32` | `IntKind.width` | **≠** |
| `int32_max` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `2147483647` | `2147483647` | `Backend.kconst` |  |
| `int32_max_succ` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `-2147483648` | `-2147483648` | `Backend.arith` + `wrap` |  |
| `int32_mul_ovf` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `0` | `0` | `Backend.arith` + `wrap` |  |
| `int32_div_neg` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `-3` | `-3` | `Backend.arith` + `wrap` |  |
| `int32_lsr_neg` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `2147483647` | `2147483647` | `Backend.shiftBy` |  |
| `int32_min_div_m1` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `-2147483648` | `-2147483648` | `Backend.arith` + `wrap` |  |
| `nativeint_max` | ints.c; mlvalues.h:401 | generate.ml:1981-1990 | `9223372036854775807` | `2147483647` | `Backend.kconst` | **≠** |
| `nativeint_max_succ` | ints.c; mlvalues.h:401 | generate.ml:1981-1990 | `-9223372036854775808` | `-2147483648` | `Backend.arith` + `wrap` | **≠** |
| `int64_max` | ints.c; mlvalues.h:401 | int64.js | `9223372036854775807` | `9223372036854775807` | `Backend.kconst` |  |
| `int64_max_succ` | ints.c; mlvalues.h:401 | int64.js | `-9223372036854775808` | `-9223372036854775808` | `Backend.arith` + `wrap` |  |
| `int64_min` | ints.c; mlvalues.h:401 | int64.js | `-9223372036854775808` | `-9223372036854775808` | `Backend.kconst` |  |
| `int64_mul` | ints.c; mlvalues.h:401 | int64.js | `-9223372036709301616` | `-9223372036709301616` | `Backend.arith` + `wrap` |  |
| `int64_div_neg` | ints.c; mlvalues.h:401 | int64.js | `-3` | `-3` | `Backend.arith` + `wrap` |  |
| `int64_mod_neg` | ints.c; mlvalues.h:401 | int64.js | `-1` | `-1` | `Backend.arith` + `wrap` |  |
| `int64_lsr` | ints.c; mlvalues.h:401 | int64.js | `9223372036854775807` | `9223372036854775807` | `Backend.shiftBy` |  |
| `int64_asr` | ints.c; mlvalues.h:401 | int64.js | `-1` | `-1` | `Backend.shiftBy` |  |
| `int64_lsl` | ints.c; mlvalues.h:401 | int64.js | `4611686018427387904` | `4611686018427387904` | `Backend.shiftBy` |  |
| `int64_of_int_max` | ints.c; mlvalues.h:401 | int64.js | `4611686018427387903` | `2147483647` | `Backend.kconst` | **≠** |
| `int64_to_int_big` | ints.c; mlvalues.h:401 | int64.js | `4611686018427387903` | `-1` | `Expr.convE` + `IntKind.width` | **≠** |
| `int64_bits_of_01` | mlvalues.h:336 | ieee_754.js:31-60 | `3fb999999999999a` | `3fb999999999999a` | `Backend.floatBits` |  |
| `int64_compare` | ints.c; mlvalues.h:401 | int64.js | `-1` | `-1` | `Val.compareVal` |  |
| `int64_equal` | ints.c; mlvalues.h:401 | int64.js | `true` | `true` | `Val.equalVal` |  |
| `int64_tag` | mlvalues.h:401 | obj.js `caml_obj_tag` | `255` | `255` | `Backend.objTag` |  |
| `int32_tag` | ints.c; mlvalues.h:401 | generate.ml:1962-1972 | `255` | `1000` | `Backend.objTag` | **≠** |
| `nativeint_tag` | ints.c; mlvalues.h:401 | generate.ml:1981-1990 | `255` | `1000` | `Backend.objTag` | **≠** |

#### `w_closure.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `partial_2_1_1` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `1234` | `1234` | `applyMany` (caml_call_gen law) |  |
| `partial_1_3` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `1234` | `1234` | `applyMany` (caml_call_gen law) |  |
| `partial_1_1_1_1` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `1234` | `1234` | `applyMany` (caml_call_gen law) |  |
| `over_1_of_3` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `123` | `123` | `applyMany` (caml_call_gen law) |  |
| `over_2_of_3` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `123` | `123` | `applyMany` (caml_call_gen law) |  |
| `over_effect_result` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `31` | `31` | `applyMany` (caml_call_gen law) |  |
| `over_effect_count` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `1` | `1` | `applyMany` + `Expr.countOf` |  |
| `over_direct_result` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `15` | `15` | `applyMany` (caml_call_gen law) |  |
| `over_direct_count` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `1` | `1` | `applyMany` + `Expr.countOf` |  |
| `closure_is_int` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `false` | `false` | `Backend.objIsInt` |  |
| `closure_tag` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `247` | `247` | `Backend.closureTag` |  |
| `closure_compare` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `0` | `0` | `Expr.cmpE` (physical-equality short-circuit) |  |
| `closure_equal_self` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `Invalid_argument:compare: functional value` | `Invalid_argument:compare: functional value` | `Expr.eqE` raises `Invalid_argument` |  |
| `closure_phys_eq` | caml_apply / bytegen.ml | stdlib.js:23-70; generate.ml:760-832 | `true` | `true` | `physEqSameClosure` |  |

#### `w_compare.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `int_lt` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `int_gt` | compare.c | compare.js:66-238,239 | `1` | `1` | `Val.compareVal` |  |
| `int_eq` | compare.c | compare.js:66-238,239 | `0` | `0` | `Val.compareVal` |  |
| `int_min_max` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `bool` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `unit` | compare.c | compare.js:66-238,239 | `0` | `0` | `Val.compareVal` |  |
| `char` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `string` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `string_high` | compare.c | compare.js:66-238,239 | `1` | `1` | `Val.compareVal` |  |
| `float` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `float_neg0` | compare.c | compare.js:66-238,239 | `0` | `0` | `Val.compareVal` |  |
| `tuple` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `tuple_first` | compare.c | compare.js:66-238,239 | `1` | `1` | `Val.compareVal` |  |
| `list` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `list_len` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `option_none_some` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `option_some` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `ctor_imm_blk` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `ctor_blk_blk` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `ctor_same` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `int64` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `int32` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `nativeint` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `array` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `float_array` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `nested` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `eq_tuple` | compare.c | compare.js:246 | `true` | `true` | `Val.equalVal` |  |
| `phys_tuple` | pointer equality (unspecified) | pointer equality (unspecified) | `true` | `false` | `physEqBlocks = .unspecified` | **≠** |
| `eq_list` | compare.c | compare.js:246 | `true` | `true` | `Val.equalVal` |  |
| `eq_nested` | compare.c | compare.js:246 | `true` | `true` | `Val.equalVal` |  |
| `eq_int64` | compare.c | compare.js:246 | `true` | `true` | `Val.equalVal` |  |
| `eq_float_array` | compare.c | compare.js:246 | `true` | `true` | `Val.equalVal` |  |
| `cmp_int64_vs_int64_neg` | compare.c | compare.js:66-238,239 | `-1` | `-1` | `Val.compareVal` |  |
| `hash_int_0` | hash.c | hash.js | `129913994` | `129913994` | `hashes` relations (§13) |  |
| `hash_int_1` | hash.c | hash.js | `883721435` | `883721435` | `hashes` relations (§13) |  |
| `hash_int_max` | hash.c | hash.js | `952257787` | `911466517` | `hashes` relations (§13) | **≠** |
| `hash_int_2p31` | hash.c | hash.js | `911466517` | `911466517` | `hashes` relations (§13) |  |
| `hash_string` | hash.c | hash.js | `767105082` | `767105082` | `hashes` relations (§13) |  |
| `hash_string_utf8` | hash.c | hash.js | `179461141` | `179461141` | `hashes` relations (§13) |  |
| `hash_float` | hash.c | hash.js | `819188451` | `819188451` | `hashes` relations (§13) |  |
| `hash_neg0` | hash.c | hash.js | `256347020` | `129913994` | `hashes` relations (§13) | **≠** |
| `hash_zero` | hash.c | hash.js | `256347020` | `129913994` | `hashes` relations (§13) | **≠** |
| `hash_tuple` | hash.c | hash.js | `973911938` | `973911938` | `hashes` relations (§13) |  |
| `hash_list` | hash.c | hash.js | `794519639` | `794519639` | `hashes` relations (§13) |  |
| `hash_int64` | hash.c | hash.js | `883721435` | `883721435` | `hashes` relations (§13) |  |
| `hash_unit` | hash.c | hash.js | `129913994` | `129913994` | `hashes` relations (§13) |  |
| `hash_true` | hash.c | hash.js | `883721435` | `883721435` | `hashes` relations (§13) |  |
| `hash_none` | hash.c | hash.js | `129913994` | `129913994` | `hashes` relations (§13) |  |

#### `w_float.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `add_01_02` | caml_format_float | ieee_754.js:400-470 | `0.30000000000000004` | `0.30000000000000004` | `floatPrintingAgrees` |  |
| `add_01_02_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `3fd3333333333334` | `3fd3333333333334` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `add_01_02_eq_03` | compare.c | compare.js:246 | `false` | `false` | `floatEqual` |  |
| `string_of_float_01` | caml_format_float | ieee_754.js:400-470 | `0.1` | `0.1` | `floatPrintingAgrees` |  |
| `string_of_float_1` | caml_format_float | ieee_754.js:400-470 | `1.` | `1.` | `floatPrintingAgrees` |  |
| `string_of_float_neg0` | caml_format_float | ieee_754.js:400-470 | `-0.` | `-0.` | `floatPrintingAgrees` |  |
| `printf_g_neg0` | caml_format_float | ieee_754.js:400-470 | `-0` | `-0` | `floatPrintingAgrees` |  |
| `printf_f_neg0` | caml_format_float | ieee_754.js:400-470 | `-0.0` | `-0.0` | `floatPrintingAgrees` |  |
| `neg0_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `8000000000000000` | `8000000000000000` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `neg0_eq_0` | compare.c | compare.js:246 | `true` | `true` | `floatEqual` |  |
| `neg0_compare_0` | compare.c | compare.js:161-170 | `0` | `0` | `floatCompare` |  |
| `one_div_neg0` | caml_format_float | ieee_754.js:400-470 | `-inf` | `-inf` | `floatPrintingAgrees` |  |
| `nan_is_nan` | compare.c | compare.js:246 | `true` | `true` | `floatEqual` |  |
| `nan_eq_nan` | compare.c | compare.js:246 | `false` | `false` | `floatEqual` |  |
| `nan_compare_nan` | compare.c | compare.js:161-170 | `0` | `0` | `floatCompare` |  |
| `nan_compare_1` | compare.c | compare.js:161-170 | `-1` | `-1` | `floatCompare` |  |
| `one_compare_nan` | compare.c | compare.js:161-170 | `1` | `1` | `floatCompare` |  |
| `nan_lt_1` | compare.c | compare.js:161-170 (`total = false`) | `false` | `false` | `Val.lessVal` |  |
| `string_of_float_nan` | caml_format_float | ieee_754.js:400-470 | `nan` | `nan` | `floatPrintingAgrees` |  |
| `string_of_float_inf` | caml_format_float | ieee_754.js:400-470 | `inf` | `inf` | `floatPrintingAgrees` |  |
| `string_of_float_neginf` | caml_format_float | ieee_754.js:400-470 | `-inf` | `-inf` | `floatPrintingAgrees` |  |
| `max_float` | caml_format_float | ieee_754.js:400-470 | `1.7976931348623157e+308` | `1.7976931348623157e+308` | `floatPrintingAgrees` |  |
| `min_float` | caml_format_float | ieee_754.js:400-470 | `2.2250738585072014e-308` | `2.2250738585072014e-308` | `floatPrintingAgrees` |  |
| `epsilon` | caml_format_float | ieee_754.js:400-470 | `2.2204460492503131e-16` | `2.2204460492503131e-16` | `floatPrintingAgrees` |  |
| `float_of_string_rt` | caml_format_float | ieee_754.js:400-470 | `0.10000000000000001` | `0.10000000000000001` | `floatPrintingAgrees` |  |
| `int_of_float_big_fold` | ints.c | generate.ml:326,947 + the constant folder | `1000000000000000000` | `2147483647` | `Expr.intOfFloatFoldE` (saturating) | **≠** |
| `int_of_float_big_rt` | ints.c | generate.ml:326,947 + the constant folder | `1000000000000000000` | `-1486618624` | `Expr.intOfFloatE` (`floatToInt` + `wrapInt`) | **≠** |
| `int_of_float_small_rt` | ints.c | generate.ml:326,947 + the constant folder | `3` | `3` | `Expr.intOfFloatE` (`floatToInt` + `wrapInt`) |  |
| `int_of_float_trunc_neg` | ints.c | generate.ml:326,947 + the constant folder | `-2` | `-2` | `Expr.intOfFloatE` (`floatToInt` + `wrapInt`) |  |
| `float_of_int_max` | floats.c | generate.ml | `4.6116860184273879e+18` | `2147483647` | `toString Backend.jsoo.maxInt` (jsoo side) | **≠** |
| `float_of_int_max_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `43d0000000000000` | `41dfffffffc00000` | `Backend.floatBits` (Lean `Float.toBits`) | **≠** |
| `float_of_string_rt_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `3fb999999999999a` | `3fb999999999999a` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `max_float_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `7fefffffffffffff` | `7fefffffffffffff` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `min_float_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `10000000000000` | `10000000000000` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `epsilon_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `3cb0000000000000` | `3cb0000000000000` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `inf_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `7ff0000000000000` | `7ff0000000000000` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `neginf_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `fff0000000000000` | `fff0000000000000` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `nan_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `7ff8000000000000` | `7ff0000000000001` | `Backend.floatBits` (Lean `Float.toBits`) | **≠** |
| `sqrt2_bits` | mlvalues.h:336 | ieee_754.js:31-60 (:33-42 NaN) | `3ff6a09e667f3bcd` | `3ff6a09e667f3bcd` | `Backend.floatBits` (Lean `Float.toBits`) |  |
| `float_tag` | mlvalues.h:336,349 | obj.js `caml_obj_tag` | `253` | `1000` | `Backend.objTag` | **≠** |
| `float_array_tag` | mlvalues.h:336,349 | obj.js `caml_obj_tag` | `254` | `254` | `Backend.objTag` |  |

#### `w_int.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `int_size` | mlvalues.h:77-80 | ints.js:90; generate.ml:326 | `63` | `32` | `Backend.intBits` | **≠** |
| `max_int` | mlvalues.h:77-80 | ints.js:90; generate.ml:326 | `4611686018427387903` | `2147483647` | `Backend.maxInt` / `minInt` | **≠** |
| `min_int` | mlvalues.h:77-80 | ints.js:90; generate.ml:326 | `-4611686018427387904` | `-2147483648` | `Backend.maxInt` / `minInt` | **≠** |
| `add_2p31m1_1` | mlvalues.h:77-80 | generate.ml:326 (`| 0`) | `2147483648` | `-2147483648` | `Backend.arith` + `wrap` | **≠** |
| `add_max_1` | mlvalues.h:77-80 | generate.ml:326 (`| 0`) | `-4611686018427387904` | `-2147483648` | `Backend.arith` + `wrap` | **≠** |
| `sub_min_1` | mlvalues.h:77-80 | generate.ml:326 (`| 0`) | `4611686018427387903` | `2147483647` | `Backend.arith` + `wrap` | **≠** |
| `mul_overflow` | ints.c | ints.js:94-96 (`Math.imul`) | `4294967296` | `0` | `Backend.arith` + `wrap` | **≠** |
| `mul_big` | ints.c | ints.js:94-96 (`Math.imul`) | `121932631112635269` | `-67153019` | `Backend.arith` + `wrap` | **≠** |
| `neg_min` | mlvalues.h:77-80 | generate.ml:326 (`| 0`) | `-4611686018427387904` | `-2147483648` | `Backend.negate` | **≠** |
| `div_trunc_neg` | ints.c | ints.js:100-103 | `-3` | `-3` | `Backend.arith` + `wrap` |  |
| `mod_trunc_neg` | ints.c | ints.js:105-109 | `-1` | `-1` | `Backend.arith` + `wrap` |  |
| `div_neg_divisor` | ints.c | ints.js:100-103 | `-3` | `-3` | `Backend.arith` + `wrap` |  |
| `mod_neg_divisor` | ints.c | ints.js:105-109 | `1` | `1` | `Backend.arith` + `wrap` |  |
| `div_min_m1` | ints.c | ints.js:100-103 | `-4611686018427387904` | `-2147483648` | `Backend.arith` + `wrap` | **≠** |
| `asr_neg1_1` | hardware shift | generate.ml:925-927 | `-1` | `-1` | `Backend.shiftBy` |  |
| `asr_neg7_1` | hardware shift | generate.ml:925-927 | `-4` | `-4` | `Backend.shiftBy` |  |
| `lsr_neg1_1` | hardware shift | generate.ml:925-927 | `4611686018427387903` | `2147483647` | `Backend.shiftBy` | **≠** |
| `lsr_neg7_1` | hardware shift | generate.ml:925-927 | `4611686018427387900` | `2147483644` | `Backend.shiftBy` | **≠** |
| `lsl_1_30` | hardware shift | generate.ml:925-927 | `1073741824` | `1073741824` | `Backend.shiftBy` |  |
| `lsl_1_31` | hardware shift | generate.ml:925-927 | `2147483648` | `-2147483648` | `Backend.shiftBy` | **≠** |
| `lsl_1_32` | hardware shift | generate.ml:925-927 | `4294967296` | `1` | `Backend.shiftBy` | **≠** |
| `lsl_1_62` | hardware shift | generate.ml:925-927 | `-4611686018427387904` | `1073741824` | `Backend.shiftBy` | **≠** |
| `land_neg1_255` | ints.c | generate.ml:920-930 | `255` | `255` | `Backend.arith` + `wrap` |  |
| `lor_neg1_0` | ints.c | generate.ml:920-930 | `-1` | `-1` | `Backend.arith` + `wrap` |  |
| `lxor_neg1_neg1` | ints.c | generate.ml:920-930 | `0` | `0` | `Backend.arith` + `wrap` |  |
| `lnot_0` | ints.c | generate.ml:920-930 | `-1` | `-1` | `Backend.bitnot` |  |
| `abs_min` | mlvalues.h:77-80 | generate.ml:326 (`| 0`) | `-4611686018427387904` | `-2147483648` | `Backend.absolute` | **≠** |
| `int_of_string_2p31` | ints.c | ints.js:62-91 (:87) | `2147483648` | `Failure:int_of_string` | `Backend.intOfString` | **≠** |
| `succ_max` | mlvalues.h:77-80 | generate.ml:326 (`| 0`) | `-4611686018427387904` | `-2147483648` | `Backend.arith` + `wrap` | **≠** |

#### `w_string.ml`

| Fact | Native source | js_of_ocaml source | Native | js_of_ocaml | Lean prediction | |
| --- | --- | --- | --- | --- | --- | --- |
| `len_ascii` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `3` | `3` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `len_utf8` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `6` | `6` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `len_euro` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `3` | `3` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `codes_utf8` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `104,195,169,108,108,111` | `104,195,169,108,108,111` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `codes_euro` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `226,130,172` | `226,130,172` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `get_utf8_1` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `195` | `195` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `sub_utf8` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `195,169` | `195,169` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `char_code_a` | mlvalues.h:72 | immediates | `97` | `97` | `Val.asInt` on an immediate |  |
| `char_chr_255` | mlvalues.h:72 | immediates | `255` | `255` | `Val.asInt` on an immediate |  |
| `char_chr_0` | mlvalues.h:72 | immediates | `0` | `0` | `Val.asInt` on an immediate |  |
| `char_compare` | compare.c | compare.js:200-207 | `-1` | `-1` | `cmpBytes` |  |
| `str_len_with_nul` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `3` | `3` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `codes_with_nul` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `97,0,98` | `97,0,98` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `concat` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `97,98,99,226,130,172` | `97,98,99,226,130,172` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `string_compare_lt` | compare.c | compare.js:200-207 | `-1` | `-1` | `cmpBytes` |  |
| `string_compare_prefix` | compare.c | compare.js:200-207 | `-1` | `-1` | `cmpBytes` |  |
| `string_compare_high` | compare.c | compare.js:200-207 | `1` | `1` | `cmpBytes` |  |
| `string_equal` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `true` | `true` | `Val.equalVal` |  |
| `string_phys_eq` | pointer equality | mlBytes.js:707-713; config.ml:93 | `false` | `true` | `Host.physEqStrings` | **≠** |
| `bytes_mutated` | mlvalues.h:328 | mlBytes.js:410-414,483-520 | `aZc` | `aZc` | `setAt` / `blitAt` |  |
| `bytes_mutated_codes` | mlvalues.h:328 | mlBytes.js:410-414,483-520 | `97,90,99` | `97,90,99` | `setAt` / `blitAt` |  |
| `bytes_created_codes` | mlvalues.h:328 | mlBytes.js:410-414,483-520 | `255,0,0` | `255,0,0` | `setAt` / `blitAt` |  |
| `bytes_len` | mlvalues.h:328 | mlBytes.js:410-414,483-520 | `3` | `3` | `setAt` / `blitAt` |  |
| `bytes_blit` | mlvalues.h:328 | mlBytes.js:410-414,483-520 | `..xy.` | `..xy.` | `setAt` / `blitAt` |  |
| `string_tag` | mlvalues.h:328 | obj.js `caml_obj_tag` | `252` | `252` | `Backend.objTag` |  |
| `bytes_tag` | mlvalues.h:328 | obj.js `caml_obj_tag` | `252` | `252` | `Backend.objTag` |  |
| `string_uppercase_utf8` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `72,195,169,76,76,79` | `72,195,169,76,76,79` | `Expr.strLit` (Lean `String.toUTF8`) |  |
| `string_index_of_high` | mlvalues.h:328 | mlBytes.js:707-721; config.ml:93 | `1` | `1` | `Expr.strLit` (Lean `String.toUTF8`) |  |

### The js_of_ocaml representation probe rows

34 rows, js_of_ocaml only, from `values/p_jsrepr.ml` through the `caml_hash` override in
`values/p_jsrepr.js`. There is no native column: on that side the corresponding fact is the
`mlvalues.h` header layout, witnessed through `Obj` by `w_block.ml`. The 28 data rows are
predicted by `Host.jsRepr`, the 6 closure rows by `jsClosure`, and both predictions are
`#guard`ed in `Value.lean` §14.

| Value | `use-js-string` (default) | `--disable use-js-string` |
| --- | --- | --- |
| `int` | `number:42` | `number:42` |
| `int_neg` | `number:-42` | `number:-42` |
| `unit` | `number:0` | `number:0` |
| `bool_true` | `number:1` | `number:1` |
| `bool_false` | `number:0` | `number:0` |
| `char` | `number:97` | `number:97` |
| `float` | `number:1.5` | `number:1.5` |
| `float_neg0` | `number:-0` | `number:-0` |
| `float_integral` | `number:3` | `number:3` |
| `string_ascii` | `jsstring[3]:"abc"` | `MlBytes{t=0,l=3,c="abc"}` |
| `string_utf8` | `jsstring[6]:"hÃ©llo"` | `MlBytes{t=0,l=6,c="hÃ©llo"}` |
| `bytes` | `MlBytes{t=0,l=3,c="abc"}` | `MlBytes{t=0,l=3,c="abc"}` |
| `ctor_const` | `number:0` | `number:0` |
| `ctor_B` | `array[2]:{number:0,number:7}` | `array[2]:{number:0,number:7}` |
| `ctor_C` | `array[3]:{number:1,number:1,number:2}` | `array[3]:{number:1,number:1,number:2}` |
| `record` | `array[3]:{number:0,number:1,jsstring[1]:"s"}` | `array[3]:{number:0,number:1,MlBytes{t=0,l=1,c="s"}}` |
| `tuple` | `array[3]:{number:0,number:1,number:2}` | `array[3]:{number:0,number:1,number:2}` |
| `none` | `number:0` | `number:0` |
| `some` | `array[2]:{number:0,number:1}` | `array[2]:{number:0,number:1}` |
| `list` | `array[3]:{number:0,number:1,array[3]:{number:0,number:2,number:0}}` | `array[3]:{number:0,number:1,array[3]:{number:0,number:2,number:0}}` |
| `int_array` | `array[4]:{number:0,number:1,number:2,number:3}` | `array[4]:{number:0,number:1,number:2,number:3}` |
| `float_array` | `array[3]:{number:254,number:1,number:2}` | `array[3]:{number:254,number:1,number:2}` |
| `int64` | `MlInt64{lo=3,mi=0,hi=0}` | `MlInt64{lo=3,mi=0,hi=0}` |
| `int64_big` | `MlInt64{lo=16777215,mi=16777215,hi=16383}` | `MlInt64{lo=16777215,mi=16777215,hi=16383}` |
| `int32` | `number:3` | `number:3` |
| `nativeint` | `number:3` | `number:3` |
| `closure_4` | `function:l=undef,length=4` | `function:l=undef,length=4` |
| `closure_1` | `function:l=undef,length=3` | `function:l=undef,length=3` |
| `closure_partial` | `function:l=undef,length=2` | `function:l=undef,length=2` |
| `closure_table_before_call` | `function:l=undef,length=2` | `function:l=undef,length=2` |
| `closure_table_after_call` | `function:l=2,length=2` | `function:l=2,length=2` |
| `closure_call_gen_wrapper` | `function:l=1,length=1` | `function:l=1,length=1` |
| `exn_const` | `array[3]:{number:248,jsstring[9]:"Not_found",number:-7}` | `array[3]:{number:248,MlBytes{t=0,l=9,c="Not_found"},number:-7}` |
| `exn_arg` | `array[3]:{number:0,array[3]:{number:248,jsstring[16]:"Invalid_argument",number:-4},jsstring[1]:"z"}` | `array[3]:{number:0,array[3]:{number:248,MlBytes{t=0,l=16,c="Invalid_argument"},number:-4},MlBytes{t=0,l=1,c="z"}}` |

Read off the table: an OCaml block is a JS array with the tag at index 0, so its `length` is one
more than the OCaml size; `int`, `char`, `bool`, `unit`, `float`, `int32` and `nativeint` are all
plain JS numbers; `Int64` is `MlInt64{lo,mi,hi}`; `bytes` is always an `MlBytes{t,c,l}` and
`string` is one only when `use-js-string` is off; a closure is a JS function whose `.l` is
`undefined` until a generic call site fills it from `f.length` (`stdlib.js:24`), and the wrapper
`caml_call_gen` builds for a partial application carries `g.l = d` (`stdlib.js:66`).

The `closure_table_*` rows needed a closure the compiler could not track — one read out of an
array at a runtime index — because js_of_ocaml's flow analysis resolves an application whose
callee it can see, and `Sys.opaque_identity` does not hide it. In `w_closure.js` the generic
path is present (`caml_call1(a,b) = (a.l>=0?a.l:a.l=a.length)==1 ? a(b) : caml_call_gen(a,[b])`,
`generate.ml:760-832`); in the straight-line probe it was optimised away.

## 6. What the profile does not model

- **`caml_format_float` and `caml_hash`**, for the reasons of §1; their rows are agreement and
  relation claims, not computed values. Reimplementing `caml_hash` (`hash.c`, `hash.js`) would
  turn 15 relation claims into 15 computed ones and is the obvious next increment.
- **Physical equality on immutable values**, which the language leaves unspecified; the profile
  classifies rather than predicts, and records the `ocamlopt`/`ocamlrun` split as a finding.
- **Mutation.** `Bytes.set` is a functional update in the model, because every witness observes
  only the resulting value. A store would be needed to state aliasing.
- **Overflow of a shift by more than the width on native** (`1 lsl 63`). Unspecified in OCaml,
  not witnessed, and the uniform `n % width` the model uses is only claimed for `n < width`.
- **Non-ASCII in `Host.jsRepr`'s string rendering** beyond what `JSON.stringify` does for
  code units 0..255 without escapes; the two witnessed strings need no escaping.
- **`wasm_of_ocaml`, `--effects=double-translation`, and any other OCaml version.** As §5 of
  the plan says, the targets are OCaml 5.1.1 single-domain and js_of_ocaml 5.7.1.
- **The compilers are trust boundaries.** `ocamlc`, `ocamlopt`, `js_of_ocaml` and Node are
  named, not verified; every host row is evidence, and F3 is what it looks like when one of
  them is inconsistent with itself.

## 7. Reproduction

```
git rev-parse HEAD                      # b47c292
workshop/OCaml5/values/run-values.sh    # 215 rows, 38 differing, transcription check
lake env lean workshop/OCaml5/Value.lean
lake build OCaml5.Value
```

The runner writes build products to
`/private/tmp/claude-501/…/scratchpad/o3/build` (overridable with `BUILD=`) and never into the
repository or the opam switches. `run-values.sh` also honours `OCAMLC`, `OCAMLOPT`, `OCAMLRUN`,
`JSOO` and `NODE`.
