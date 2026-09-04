// P6 witness 8: the reference order the OCaml+jsoo `Await` witness must match.
// A JS-side `then` is registered on the SAME promise BEFORE the "await" registers its own.
// The await here stands for what an OCaml effect handler does: attach a reaction whose
// job resumes a continuation. Spec anchors: sec-performpromisethen (reactions are appended
// to [[PromiseFulfillReactions]] in registration order), sec-triggerpromisereactions.
const L = [];
const p = (s) => L.push(s);

let go;
const gate = new Promise((r) => { go = r; });

gate.then((v) => p("JS:first-then " + v));      // registered first

async function ocamlish() {
  p("K:enter");
  const v = await gate;                          // registered second
  p("K:resumed-1 " + v);
  const w = await Promise.resolve(v + "!");      // a chained second await
  p("K:resumed-2 " + w);
  try {
    await Promise.reject("bad");                 // rejected await -> discontinue
    p("K:UNREACHABLE");
  } catch (e) {
    p("K:discontinued " + e);
  }
  p("K:done");
}

ocamlish();
gate.then((v) => p("JS:third-then " + v));      // registered third
p("S:settling");
go("v0");
p("S:sync-tail");

process.on("exit", () => console.log(JSON.stringify(L).replace(/","/g, '",\n "')));
