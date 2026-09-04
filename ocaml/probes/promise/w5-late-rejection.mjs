// P6 witness 5: a rejection handled after the microtask checkpoint.
// Spec anchors: HostPromiseRejectionTracker ("reject" / "handle" operations),
// sec-rejectpromise step "Perform HostPromiseRejectionTracker(promise, ~reject~)",
// sec-performpromisethen step "Set promise.[[IsHandled]] to true".
// Node policy (--unhandled-rejections=throw is the default in 22; we install handlers
// so the process survives and we can see both hook calls).
const L = [];
const p = (s) => L.push(s);

process.on("unhandledRejection", (reason) => p("HOOK:unhandledRejection " + reason));
process.on("rejectionHandled", () => p("HOOK:rejectionHandled"));

const late = Promise.reject("boom");     // reject with no handler attached
p("S:rejected-with-no-handler");

// Handled inside the SAME turn: the tracker never reports it.
const early = Promise.reject("quiet");
early.catch((r) => p("EARLY:caught " + r));
p("S:early-handler-attached");

setTimeout(() => {
  p("MACRO:attaching-late-handler");
  late.catch((r) => p("LATE:caught " + r));
  setTimeout(() => {
    console.log(JSON.stringify(L).replace(/","/g, '",\n "'));
  }, 0);
}, 0);
