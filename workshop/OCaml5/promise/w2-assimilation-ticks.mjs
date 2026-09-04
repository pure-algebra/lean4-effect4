// P6 witness 2: what a resolution value costs in microtask ticks.
// Three chains started in the same synchronous turn, each numbering its own ticks.
// Spec anchors: sec-promise-resolve-functions (thenable branch),
// sec-newpromiseresolvethenablejob, sec-newpromisereactionjob.
const L = [];
const p = (s) => L.push(s);

// Ruler: a plain chain that fires one label per tick, 1..8.
let ruler = Promise.resolve();
for (let i = 1; i <= 8; i++) { const n = i; ruler = ruler.then(() => p("R:" + n)); }

// A: returns a plain value from the first handler.
Promise.resolve().then(() => { p("A:h"); return 0; })
  .then(() => p("A:resumed"));

// B: returns a NATIVE promise (assimilation: NewPromiseResolveThenableJob + its own then job).
Promise.resolve().then(() => { p("B:h"); return Promise.resolve(0); })
  .then(() => p("B:resumed"));

// C: returns a FOREIGN thenable (NewPromiseResolveThenableJob only).
Promise.resolve().then(() => { p("C:h"); return { then(r) { p("C:then-called"); r(0); } }; })
  .then(() => p("C:resumed"));

process.on("exit", () => console.log(JSON.stringify(L).replace(/","/g, '",\n "')));
