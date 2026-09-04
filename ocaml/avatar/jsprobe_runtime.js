// A0 deliverable 2: the JavaScript half of the closure-boundary probe.
// Extra jsoo runtime, passed on the js_of_ocaml command line.

//Provides: a0_state
var a0_state = { log: [], counter: 0 };

//Provides: a0_log
//Requires: a0_state, caml_jsstring_of_string
function a0_log(s) {
  var t = caml_jsstring_of_string(s);
  a0_state.log.push(t);
  console.log(t);
  return 0;
}

//Provides: a0_dump
//Requires: a0_state
function a0_dump(unit) { return 0; }

// A: wrap an OCaml closure with caml_js_wrap_callback (jslib.js:304-318) and call it from
// JavaScript with an int and a real JS function as arguments.
//Provides: a0_call_ocaml_from_js
//Requires: a0_state, caml_js_wrap_callback
function a0_call_ocaml_from_js(ocaml_fn) {
  var wrapped = caml_js_wrap_callback(ocaml_fn);
  a0_state.log.push("A:wrapped typeof=" + typeof wrapped + " l=" +
                    (ocaml_fn.l === undefined ? "-" : ocaml_fn.l) +
                    " length=" + ocaml_fn.length);
  var captured = 100;
  var jsClosure = function (x) { captured += x; return captured; };
  a0_state.log.push("A:js-calling-ocaml");
  var r = wrapped(7, jsClosure);
  a0_state.log.push("A:js-saw-return " + r + " captured=" + captured);
  return r;
}

// Call a JS closure the OCaml side is holding.
//Provides: a0_js_call1
function a0_js_call1(f, x) { return f(x); }

// B: a real JS function over a captured mutable variable.
//Provides: a0_make_js_closure
//Requires: a0_state
function a0_make_js_closure(unit) {
  return function (x) {
    a0_state.counter += x;
    a0_state.log.push("B:js-closure-body counter=" + a0_state.counter);
    return a0_state.counter;
  };
}

//Provides: a0_read_counter
//Requires: a0_state
function a0_read_counter(unit) { return a0_state.counter; }

// C: JavaScript invokes an OCaml thunk. This is the crux: under --enable effects,
// caml_js_wrap_callback's closure calls caml_callback (jslib.js:70-113), which SAVES AND
// REPLACES caml_fiber_stack with a fresh one-frame fiber whose only handler is
// uncaught_effect_handler, so an effect performed inside does not see handlers installed
// outside the JS call.
//Provides: a0_invoke_from_js
//Requires: a0_state, caml_js_wrap_callback
function a0_invoke_from_js(thunk) {
  var wrapped = caml_js_wrap_callback(thunk);
  a0_state.log.push("C:js-invoking-ocaml-thunk");
  try {
    var r = wrapped(0);
    a0_state.log.push("C:js-thunk-returned " + r);
    return r;
  } catch (e) {
    var tag = (e && e[1] && e[1][1]) ? e[1][1] : (e && e[1]) ? String(e[1]) : String(e);
    a0_state.log.push("C:js-thunk-threw " + tag);
    throw e;
  }
}

// D: the representation of a value at the boundary (O3 §7, the value profile).
//Provides: a0_probe_repr
//Requires: caml_string_of_jsstring
function a0_probe_repr(f) {
  return caml_string_of_jsstring(
    "typeof=" + typeof f +
    " l=" + (f && f.l !== undefined ? f.l : "-") +
    " length=" + (f && f.length !== undefined ? f.length : "-") +
    " name=" + (f && f.name ? f.name : "-"));
}

// caml_call_gen: partial and over-application of a two-argument OCaml closure.
//Provides: a0_apply_partial
//Requires: caml_string_of_jsstring, caml_call_gen, caml_js_wrap_callback
function a0_apply_partial(f) {
  var out = [];
  // Direct caml_call_gen on a closure the effects transform may have turned into a
  // CPS function: recorded, because it is the boundary the value profile has to describe.
  try { out.push("callgen-full=" + caml_call_gen(f, [3, 4])); }
  catch (e) { out.push("callgen-full-threw=" + (e && e.message ? e.message : String(e))); }
  try {
    var partial = caml_call_gen(f, [3]);
    out.push("callgen-partial.l=" + (partial && partial.l !== undefined ? partial.l : "-"));
    out.push("callgen-viaPartial=" + caml_call_gen(partial, [4]));
  } catch (e) { out.push("callgen-partial-threw=" + (e && e.message ? e.message : String(e))); }
  // The supported path: wrap it as a JS function first.
  try {
    var w = caml_js_wrap_callback(f);
    out.push("wrapped-full=" + w(3, 4));
    out.push("wrapped.length=" + w.length);
  } catch (e) { out.push("wrapped-threw=" + (e && e.message ? e.message : String(e))); }
  return caml_string_of_jsstring(out.join(" "));
}
