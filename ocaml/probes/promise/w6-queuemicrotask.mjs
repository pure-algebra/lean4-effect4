// P6 witness 6: queueMicrotask enqueues into the SAME job queue as promise reactions,
// in call order. Spec anchors: HostEnqueuePromiseJob (the "in FIFO order" requirement),
// HTML "queue a microtask" (queueMicrotask is defined against the same microtask queue).
const L = [];
const p = (s) => L.push(s);

queueMicrotask(() => p("Q:q1"));
Promise.resolve().then(() => p("P:p1"));
queueMicrotask(() => {
  p("Q:q2");
  queueMicrotask(() => p("Q:q2-nested"));      // appended to the tail of the running drain
  Promise.resolve().then(() => p("P:p2-from-q2"));
});
Promise.resolve().then(() => p("P:p3"));
p("S:sync-tail");

process.on("exit", () => console.log(JSON.stringify(L).replace(/","/g, '",\n "')));
