// P6 witness B: the JS half of the OCaml `Await` bridge.
// Extra jsoo runtime, passed on the js_of_ocaml command line. Everything crossing the
// boundary is an int id or a string, so the OCaml side stays first-order (O3 value profile).

//Provides: p6_state
var p6_state = { log: [], cells: [], };

//Provides: p6_log
//Requires: p6_state, caml_jsstring_of_string
function p6_log(s) { p6_state.log.push(caml_jsstring_of_string(s)); return 0; }

//Provides: p6_new_promise
//Requires: p6_state
function p6_new_promise(unit) {
  var cell = {};
  cell.promise = new Promise(function (res, rej) { cell.resolve = res; cell.reject = rej; });
  p6_state.cells.push(cell);
  return p6_state.cells.length - 1;
}

//Provides: p6_settle
//Requires: p6_state, caml_jsstring_of_string
function p6_settle(id, ok, payload) {
  var cell = p6_state.cells[id];
  if (ok) cell.resolve(caml_jsstring_of_string(payload));
  else cell.reject(caml_jsstring_of_string(payload));
  return 0;
}

//Provides: p6_resolved
//Requires: p6_state, caml_jsstring_of_string
function p6_resolved(payload) {
  p6_state.cells.push({ promise: Promise.resolve(caml_jsstring_of_string(payload)) });
  return p6_state.cells.length - 1;
}

// The bridge. The OCaml handler hands us two OCaml closures; we wrap them with
// caml_js_wrap_callback (jslib.js:304) and attach them as the two arguments of a single
// `.then` -- exactly the shape Effect rc.112 uses at internal/effect.ts:1055.
//Provides: p6_then
//Requires: p6_state, caml_js_wrap_callback, caml_string_of_jsstring
function p6_then(id, onOk, onErr) {
  var ok = caml_js_wrap_callback(onOk);
  var err = caml_js_wrap_callback(onErr);
  p6_state.cells[id].promise.then(
    function (v) { p6_state.log.push("JS:then-entered(ok)"); ok(caml_string_of_jsstring(String(v)));
                   p6_state.log.push("JS:then-returned"); },
    function (e) { p6_state.log.push("JS:then-entered(err)"); err(caml_string_of_jsstring(String(e)));
                   p6_state.log.push("JS:then-returned"); });
  return 0;
}

// A pure-JS reaction on the same promise, for the registration-order witness.
//Provides: p6_js_then
//Requires: p6_state, caml_jsstring_of_string
function p6_js_then(id, label) {
  var tag = caml_jsstring_of_string(label);
  p6_state.cells[id].promise.then(function (v) { p6_state.log.push(tag + " " + v); },
                                  function (e) { p6_state.log.push(tag + "!" + e); });
  return 0;
}

//Provides: p6_dump
//Requires: p6_state
function p6_dump(unit) {
  console.log(JSON.stringify(p6_state.log).replace(/","/g, '",\n "'));
  return 0;
}

//Provides: p6_at_exit
//Requires: p6_dump
function p6_at_exit(unit) { process.on("exit", function () { p6_dump(0); }); return 0; }

// A foreign thenable whose `then` calls the fulfilment handler TWICE, synchronously --
// witness 3's shape. A native Promise would drop the second call (alreadyResolved);
// a raw caller does not. Used to probe OCaml's one-shot continuation guard.
//Provides: p6_call_twice
//Requires: p6_state, caml_js_wrap_callback, caml_string_of_jsstring
function p6_call_twice(onOk, payload) {
  var ok = caml_js_wrap_callback(onOk);
  var v = caml_string_of_jsstring(String(payload));
  p6_state.log.push("JS:foreign-then-entered");
  ok(v);
  p6_state.log.push("JS:foreign-second-call");
  try { ok(v); p6_state.log.push("JS:foreign-second-call-returned"); }
  catch (e) {
    var name = (e && e[1] && typeof e[1] === "object" && e[1][1]) ? e[1][1]
             : (e && e[1] && typeof e[1] === "string") ? e[1]
             : (e && e.constructor && e.constructor.name) || String(e);
    p6_state.log.push("JS:foreign-second-call-threw " + name);
  }
  p6_state.log.push("JS:foreign-then-returned");
  return 0;
}
