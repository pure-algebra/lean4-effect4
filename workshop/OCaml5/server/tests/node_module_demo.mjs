// Deliverable 4, the JavaScript half: the js_of_ocaml build of `effect4d` `require`d as a
// node module, not run as a program.
//
// The interesting part is that this works at all under `--enable effects`. Spike A0's probe C
// found that a `perform` inside an OCaml callback invoked from JavaScript is `Unhandled`,
// because `caml_callback` replaces `caml_fiber_stack` with a fresh one-frame fiber
// (`jslib.js:70-113`). The avatar performs constantly. It works because the handler is
// installed *inside* the callback: `run_under_handler`'s `match_with` runs on the fresh
// fiber, and every `perform` the fiber bodies make is under it. Nothing performs across the
// boundary.
//
// Usage: node tests/node_module_demo.mjs [path to effect4d.js]

import { createRequire } from "node:module";
import path from "node:path";
import process from "node:process";

const require = createRequire(import.meta.url);
const buildDefault =
  process.env.W2_BUILD ||
  "/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/" +
    "d87ba830-2e63-4750-815f-2679b36f870a/scratchpad/w2";
const target = process.argv[2] || path.join(buildDefault, "build", "effect4d.js");

const effect4d = require(target);

let failures = 0;
const check = (name, ok, detail) => {
  console.log(`${ok ? "PASS" : "FAIL"} ${name.padEnd(42)} ${detail}`);
  if (!ok) failures += 1;
};

check("module exports the request functions",
      typeof effect4d.request === "function" &&
      typeof effect4d.runProgram === "function" &&
      typeof effect4d.version === "function",
      Object.keys(effect4d).sort().join(","));

const version = JSON.parse(effect4d.version(""));
check("version answers from inside the module", version.ok === true,
      `${version.host} protocol ${version.protocol}`);
check("the host is js_of_ocaml", version.host === "js_of_ocaml", version.host);

// `run_program : program -> tape -> masks -> result`, over the boundary.
const run = JSON.parse(effect4d.runProgram(JSON.stringify({
  family: "ref", program: "makeGet", tape: "", masks: ["outcome", "m1", "m2"],
})));
check("runProgram over the JS boundary", run.ok === true, run.rows?.join(" | "));
check("runProgram rows are the golden's",
      JSON.stringify(run.rows) === JSON.stringify([
        "op\tmake\t7", "answer\tmake\t0", "op\tget\t0", "answer\tget\t7",
        'done\t{"success":7}',
      ]),
      JSON.stringify(run.rows));
check("runProgram projects under every mask",
      Object.keys(run.projections).length === 3 &&
      run.projections.outcome.length === 1,
      Object.entries(run.projections).map(([k, v]) => `${k}=${v.length}`).join(","));
check("runProgram carries the golden header",
      run.header.includes("face\tocaml") &&
      run.header.some((line) => line.startsWith("pin\teffects\t")),
      `${run.header.length} header lines`);

// A fiber program: forks, parks, races -- i.e. every `perform` the avatar makes, all of it
// under a handler installed inside this very JS call.
const raced = JSON.parse(effect4d.request(JSON.stringify({
  request: "run", source: "fixture", family: "fiber",
  program: "raceImmediateSuccessStopsLaunch", tape: "0:1,1:0",
})));
check("a forking, racing program runs under a JS caller", raced.ok === true,
      `${raced.rowCount} rows, outcome ${raced.outcome?.tag}`);
check("its RunEvent trace came back too", (raced.events?.length ?? 0) > 0,
      `${raced.events?.length} events`);

// The understanding APIs, from JavaScript.
const explained = JSON.parse(effect4d.request(JSON.stringify({
  request: "explain", source: "fixture", family: "scope", program: "lifo",
})));
const armed = explained.rows.filter((r) => r.kind === "op" && r.arms.length > 0);
check("explain names the avatar arm and the Lean site", armed.length > 0,
      armed.map((r) => `${r.name}->${r.arms.map((a) => a.arm).join("/")}`).join(" "));

const step = JSON.parse(effect4d.request(JSON.stringify({
  request: "step", source: "fixture", family: "fiber",
  program: "parentInterruptDuringChildWait", tape: "0:0,1:0", rounds: 1,
})));
check("step returns a RunMachine snapshot", step.ok === true && step.machine.fibers.length > 0,
      `${step.machine.fibers.length} fibers, ` +
      step.machine.fibers.map((f) => `${f.id}:${f.status}`).join(" "));

// Called repeatedly in one process: the avatar's global state is reset each time.
const first = JSON.parse(effect4d.request(JSON.stringify({
  request: "run", source: "fixture", family: "layer", program: "releaseOrder",
})));
const second = JSON.parse(effect4d.request(JSON.stringify({
  request: "run", source: "fixture", family: "layer", program: "releaseOrder",
})));
check("repeat calls are deterministic",
      JSON.stringify(first.rows) === JSON.stringify(second.rows),
      JSON.stringify(second.rows));

console.log(`${failures === 0 ? "PASS" : "FAIL"}: ${failures} failures`);
process.exit(failures === 0 ? 0 : 1);
