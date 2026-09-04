// P6 witness 3: a foreign thenable's `then` called DIRECTLY (the Effect rc.112 seam)
// vs the same thenable handed to the resolve function (assimilation).
// A well-typed foreign `then` may run its handler synchronously, twice, or throw.
// Spec anchors: sec-promise-resolve-functions step "Let thenAction be ? Get(resolution, "then")",
// sec-newpromiseresolvethenablejob.
const L = [];
const p = (s) => L.push(s);

const foreign = {
  then(onOk, onErr) {
    p("F:then-entered");
    onOk("first");            // synchronous, inside the caller's turn
    onOk("second");           // a second call: native Promise would ignore it; a raw caller may not
    p("F:then-returned");
  }
};

p("S:before-direct");
// Direct call: exactly what `Effect.promise`-style code does with a PromiseLike.
foreign.then((v) => p("D:onOk(" + v + ")"), (e) => p("D:onErr"));
p("S:after-direct");

// Assimilation: the same object through the resolve function.
p("S:before-assimilate");
Promise.resolve(foreign).then((v) => p("P:onOk(" + v + ")"));
p("S:after-assimilate");

// A thenable whose `then` throws after resolving: the throw is swallowed (already resolved).
const throwy = { then(r) { p("X:then-entered"); r("ok"); throw new Error("late"); } };
Promise.resolve(throwy).then((v) => p("X:onOk(" + v + ")"), () => p("X:onErr"));

process.on("exit", () => console.log(JSON.stringify(L).replace(/","/g, '",\n "')));
