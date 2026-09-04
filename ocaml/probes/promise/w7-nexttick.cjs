// P6 witness 7b: NODE-SPECIFIC, CommonJS. process.nextTick is NOT a microtask; Node drains the
// entire nextTick queue before the promise/microtask queue, and again between microtasks.
// There is no ECMAScript anchor for this: HostEnqueuePromiseJob leaves the host free,
// and Node keeps a queue of higher priority. Do not model this as a spec fact.
const L = [];
const p = (s) => L.push(s);

process.nextTick(() => p("N:n1"));
Promise.resolve().then(() => { p("P:p1"); process.nextTick(() => p("N:n1-from-p1")); });
process.nextTick(() => { p("N:n2"); process.nextTick(() => p("N:n2-nested")); });
Promise.resolve().then(() => p("P:p2"));
queueMicrotask(() => p("Q:q1"));
setImmediate(() => p("I:immediate"));
setTimeout(() => p("T:timeout0"), 0);
p("S:sync-tail");

process.on("exit", () => console.log(JSON.stringify(L).replace(/","/g, '",\n "')));
