import {Effect} from "effect"; import {main} from "./candidate.ts"; console.log(JSON.stringify(await Effect.runPromise(main)));
