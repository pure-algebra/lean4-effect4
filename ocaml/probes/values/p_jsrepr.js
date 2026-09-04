// O3 probe runtime, js_of_ocaml only. Overrides `caml_hash` (hash.js) so that
// `Hashtbl.hash (key, v)` becomes a printed JS-level description of `v`.
// This is the only hook that reaches an arbitrary OCaml value from JS without
// linking js_of_ocaml's own library, which bytecode cannot link.
//Provides: caml_hash
//Requires: caml_o3_describe
//Weakdef
function caml_hash(count, limit, seed, a) {
  var k = a[1], v = a[2];
  var s = (typeof k === "string") ? k : k.c;
  globalThis.process.stdout.write(s + "\t" + caml_o3_describe(v, 0) + "\n");
  return 0;
}

//Provides: caml_o3_describe
function caml_o3_describe(v, depth) {
  if (depth > 3) return "...";
  var t = typeof v;
  if (t === "number") return "number:" + (Object.is(v, -0) ? "-0" : String(v));
  if (t === "string") return "jsstring[" + v.length + "]:" + JSON.stringify(v);
  if (t === "function") return "function:l=" + (v.l === undefined ? "undef" : v.l)
                              + ",length=" + v.length;
  if (Array.isArray(v)) {
    var parts = [];
    for (var i = 0; i < v.length; i++) parts.push(caml_o3_describe(v[i], depth + 1));
    return "array[" + v.length + "]:{" + parts.join(",") + "}";
  }
  if (v instanceof Float64Array) return "Float64Array[" + v.length + "]";
  // constructor names are minified, so recognise the runtime records by shape:
  // MlBytes is {t,c,l} (mlBytes.js:412) and MlInt64 is {lo,mi,hi} (int64.js).
  if (v && typeof v === "object" && "t" in v && "c" in v && "l" in v)
    return "MlBytes{t=" + v.t + ",l=" + v.l + ",c=" + JSON.stringify(v.c) + "}";
  if (v && typeof v === "object" && "lo" in v && "mi" in v && "hi" in v)
    return "MlInt64{lo=" + v.lo + ",mi=" + v.mi + ",hi=" + v.hi + "}";
  if (v && typeof v === "object")
    return "object{" + Object.keys(v).join(",") + "}";
  return t + ":" + String(v);
}
