// The JavaScript half of the js_of_ocaml build of `effect4d`: four externals, passed to
// js_of_ocaml on the command line the way `ocaml/avatar/jsprobe_runtime.js` is.
//
// Everything crossing the boundary is a string, converted explicitly here rather than
// relying on how jsoo happens to represent an OCaml string in this version (spike O3 §7).

//Provides: e4d_exports
var e4d_exports = {};

// Register an OCaml `string -> string` as a JavaScript function, and publish the table as
// `module.exports` so `require("./effect4d.js")` returns it.
//
// `caml_js_wrap_callback` (jslib.js:304-318) is the supported way to call OCaml from JS.
// Under `--enable effects` it calls `caml_callback`, which replaces `caml_fiber_stack` with
// a fresh one-frame fiber, so a `perform` that escapes the callback is `Unhandled` -- spike
// A0 probe C. Nothing here escapes: the daemon installs its own handler inside the call.
//Provides: e4d_register
//Requires: e4d_exports, caml_js_wrap_callback, caml_jsstring_of_string, caml_string_of_jsstring
function e4d_register(name, fn) {
  var wrapped = caml_js_wrap_callback(fn);
  e4d_exports[caml_jsstring_of_string(name)] = function (argument) {
    var input = caml_string_of_jsstring(argument === undefined ? "" : String(argument));
    return caml_jsstring_of_string(wrapped(input));
  };
  if (typeof module !== "undefined" && module && module.exports) {
    for (var key in e4d_exports) module.exports[key] = e4d_exports[key];
  }
  if (typeof globalThis !== "undefined") globalThis.effect4d = e4d_exports;
  return 0;
}

// One line of stdin, synchronously, so the node host is a live newline-delimited JSON
// session and not a batch: `fs.readSync` on fd 0 blocks on a pipe until there is data and
// returns 0 at end of file. The answer is the line, or "\0" for end of file -- a sentinel
// rather than an option, because an OCaml `option` is a block and this boundary carries
// strings only (spike O3 §7, the value profile).
//
// EAGAIN is what a non-blocking descriptor gives (a terminal, or a parent that set O_NONBLOCK
// on the pipe); the loop retries, with a bounded spin so that a descriptor that never becomes
// readable ends the session instead of hanging the daemon.
//Provides: e4d_stdin_state
var e4d_stdin_state = { buffer: "", eof: false, spins: 0 };

//Provides: e4d_read_line
//Requires: e4d_stdin_state, caml_string_of_jsstring
function e4d_read_line(unit) {
  var fs = require("fs");
  var chunk = Buffer.alloc(65536);
  for (;;) {
    var cut = e4d_stdin_state.buffer.indexOf("\n");
    if (cut >= 0) {
      var line = e4d_stdin_state.buffer.slice(0, cut);
      e4d_stdin_state.buffer = e4d_stdin_state.buffer.slice(cut + 1);
      e4d_stdin_state.spins = 0;
      return caml_string_of_jsstring(line);
    }
    if (e4d_stdin_state.eof) {
      if (e4d_stdin_state.buffer.length > 0) {
        var rest = e4d_stdin_state.buffer;
        e4d_stdin_state.buffer = "";
        return caml_string_of_jsstring(rest);
      }
      return caml_string_of_jsstring("\0");
    }
    var read = 0;
    try {
      read = fs.readSync(0, chunk, 0, chunk.length, null);
    } catch (e) {
      if (e && (e.code === "EAGAIN" || e.code === "EWOULDBLOCK")) {
        if (++e4d_stdin_state.spins > 2000000) e4d_stdin_state.eof = true;
        continue;
      }
      if (e && (e.code === "EOF" || e.code === "EBADF")) read = 0;
      else throw e;
    }
    if (read === 0) e4d_stdin_state.eof = true;
    else e4d_stdin_state.buffer += chunk.toString("utf8", 0, read);
  }
}

//Provides: e4d_write_line
//Requires: caml_jsstring_of_string
function e4d_write_line(s) {
  var text = caml_jsstring_of_string(s);
  try {
    require("fs").writeSync(1, text + "\n");
  } catch (e) {
    console.log(text);
  }
  return 0;
}

// True when this file is the program node was asked to run, false when it was `require`d.
//Provides: e4d_is_main
function e4d_is_main(unit) {
  try {
    if (typeof require !== "undefined" && typeof module !== "undefined" && require.main) {
      return require.main === module ? 1 : 0;
    }
  } catch (e) {}
  return 1;
}
