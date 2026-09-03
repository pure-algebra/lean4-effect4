# Standards survey sources, fetched 2026-09-02

Digest manifest for the primary sources the standards survey
(`docs/research/2026-09-02-standards-targets-survey.md`) read. The bytes were
fetched into a session scratchpad by five read-only sweeps on 2026-09-02 and
are **not vendored here**; this file records what was read so a later pin file
(`pins/standards.tsv`, survey §8) can be checked against it. Full digests are
in `SHA256SUMS`. Nothing in this directory is a contract, a corpus, or a pin.

`JSON-Schema-Test-Suite` was cloned at commit `55e23729473f4b629fd9266614280f355cd1b4fc` (committed 2026-09-01T12:53:04-07:00); the
`draft2020-12/` directory holds 47 test files. `json-patch-tests` was fetched
from `master` with no tag; its digests are the only pin available.

Not saved to the scratchpad (read through the fetch tool only, or written to
`/tmp`): the MCP `2026-07-28` `schema.json`, the AG-UI draft `schema.json`,
the A2A `a2a.proto` and generated `a2a.json`, the ACP `v1`/`v2` schemas, the
Standard Schema `index.ts`, the Vercel AI SDK stream-protocol page, the
OpenAPI 3.1/3.2 dated schemas. Those must be re-fetched and digested before
any row citing them is pinned.

| File | URL | SHA-256 | Bytes | What |
| --- | --- | --- | --- | --- |
| `oa.yaml` | https://raw.githubusercontent.com/openai/openai-openapi/master/openapi.yaml | `ca86486f9fefb2aa…` | 2976505 | OpenAI OpenAPI (master; byte-identical to main) |
| `so.md` | https://developers.openai.com/api/docs/guides/structured-outputs.md | `bbe9c469209404aa…` | 135215 | OpenAI structured outputs guide |
| `rs.md` | https://developers.openai.com/api/docs/api-reference/responses-streaming.md | `5df239de2f4eae5c…` | 307143 | OpenAI Responses streaming reference (markdown) |
| `rs.html` | https://platform.openai.com/docs/api-reference/responses-streaming | `63d468982550da78…` | 9824 | OpenAI Responses streaming reference (html) |
| `union.txt` | derived from oa.yaml | `54ec60e1de6260cd…` | 1956 | OpenAI response stream event union (58 variants), derived |
| `evt.txt` | derived from oa.yaml | `df65d7f5cdd87e9f…` | 2158 | OpenAI response stream event type strings, derived |
| `ant.yml` | https://storage.googleapis.com/stainless-sdk-openapi-specs/anthropic/anthropic-e50cf35b74cc0471a2b5af7ea03765aa81c035f82588e9a1ba1b29aeaa17d064.yml | `d1d189d791d1b551…` | 2463516 | Anthropic OpenAPI (content-hashed URL from anthropic-sdk .stats.yml) |
| `ant_so.md` | https://platform.claude.com/docs/en/build-with-claude/structured-outputs.md | `4e500fed30c75976…` | 110492 | Anthropic structured outputs |
| `ant_en_api_messages.md` | https://platform.claude.com/docs/en/api/messages.md | `8bf20e7b4ecfe6fb…` | 953017 | Anthropic Messages API |
| `ant_en_api_versioning.md` | https://platform.claude.com/docs/en/api/versioning.md | `45d247cdbfa26b28…` | 1806 | Anthropic versioning policy (enum-like values may grow) |
| `ant_en_api_beta-headers.md` | https://platform.claude.com/docs/en/api/beta-headers.md | `cfa06bd20fb1c32c…` | 7800 | Anthropic beta headers |
| `ant_en_docs_build-with-claude_streaming.md` | https://platform.claude.com/docs/en/docs/build-with-claude/streaming.md | `ad002d1a6e5aa3cb…` | 50803 | Anthropic streaming |
| `ant_en_docs_build-with-claude_tool-use_overview.md` | https://platform.claude.com/docs/en/docs/build-with-claude/tool-use/overview.md | `87e737a50fa73fe6…` | 38176 | Anthropic tool use |
| `gdisc.json` | https://generativelanguage.googleapis.com/$discovery/rest?version=v1beta | `af2272d9fbaecba0…` | 374694 | Gemini discovery document v1beta |
| `content.proto` | https://raw.githubusercontent.com/googleapis/googleapis/master/google/ai/generativelanguage/v1beta/content.proto | `8c01c50c6d6795bf…` | 29085 | Gemini content.proto (Schema message) |
| `rfc6901.txt` | https://www.rfc-editor.org/rfc/rfc6901.txt | `12f9f4fc13d686aa…` | 13037 | RFC 6901 JSON Pointer |
| `rfc6902.txt` | https://www.rfc-editor.org/rfc/rfc6902.txt | `ded8fa1754ab1566…` | 26405 | RFC 6902 JSON Patch |
| `rfc7807.txt` | https://www.rfc-editor.org/rfc/rfc7807.txt | `c6ee12b7109d42ed…` | 31210 | RFC 7807 Problem Details (obsoleted) |
| `rfc9457.txt` | https://www.rfc-editor.org/rfc/rfc9457.txt | `f2b3db92fb0bf348…` | 34106 | RFC 9457 Problem Details |
| `jp-tests.json` | https://raw.githubusercontent.com/json-patch/json-patch-tests/master/tests.json | `de3dce3d0d5029fe…` | 18707 | json-patch-tests corpus (Apache-2.0) |
| `jp-spec_tests.json` | https://raw.githubusercontent.com/json-patch/json-patch-tests/master/spec_tests.json | `a26b050292207033…` | 4031 | json-patch-tests RFC examples |
| `jp-README.md` | https://raw.githubusercontent.com/json-patch/json-patch-tests/master/README.md | `f995d6a6e1babf65…` | 2306 | json-patch-tests README |
| `jp-package.json` | https://raw.githubusercontent.com/json-patch/json-patch-tests/master/package.json | `7c808769bf7b0d72…` | 393 | json-patch-tests package.json |
| `jsts/test-schema.json` | https://github.com/json-schema-org/JSON-Schema-Test-Suite (clone) | `4727b2d096462b7f…` | 5725 | JSON-Schema-Test-Suite test-schema.json |
| `jsts/package.json` | https://github.com/json-schema-org/JSON-Schema-Test-Suite (clone) | `0eb192b04f96cb95…` | 322 | JSON-Schema-Test-Suite package.json |
| `spans.yaml` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/model/gen-ai/spans.yaml | `7bc1a3025319821c…` | 38428 | OTel GenAI spans model |
| `gen-ai-events.yaml` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/model/gen-ai/events.yaml | `55de2362957db452…` | 2707 | OTel GenAI events model |
| `gen-ai-metrics.yaml` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/model/gen-ai/metrics.yaml | `e490bcfc2d36696d…` | 11160 | OTel GenAI metrics model |
| `gen-ai-registry.yaml` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/model/gen-ai/registry.yaml | `8381a0cd47111869…` | 43067 | OTel GenAI attribute registry |
| `genai-README.md` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/README.md | `8ab882b40b743b34…` | 1232 | OTel GenAI semconv README |
| `genai-manifest.yaml` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/model/manifest.yaml | `53f3589761cd853c…` | 621 | OTel GenAI weaver manifest |
| `in-msgs.json` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions-genai/main/gen-ai-input-messages.json | `034fcd8c87f1e013…` | 20355 | OTel GenAI input-messages JSON Schema |
| `dep.yaml` | https://raw.githubusercontent.com/open-telemetry/semantic-conventions/main/model/gen-ai/deprecated/registry-deprecated.yaml | `4b489db09547f730…` | 55327 | OTel core semconv gen-ai deprecated registry (tombstones) |
| `weaver-semconv.schema.json` | https://raw.githubusercontent.com/open-telemetry/weaver/main/schemas/semconv.schema.json | `81d1252b46ae1aa8…` | 18360 | OTel weaver semconv JSON Schema |
| `span_data.py` | https://raw.githubusercontent.com/openai/openai-agents-python/main/src/agents/tracing/span_data.py | `f9d7e2fc19d2acff…` | 11024 | OpenAI Agents SDK tracing span data |
| `processors.py` | https://raw.githubusercontent.com/openai/openai-agents-python/main/src/agents/tracing/processors.py | `28accb52d1c1e20a…` | 29926 | OpenAI Agents SDK tracing processors (ingestion endpoint) |
| `traces_spans.py` | https://raw.githubusercontent.com/openai/openai-agents-python/main/src/agents/tracing/spans.py | `89ca21515427cb30…` | 12373 | OpenAI Agents SDK spans |
| `traces_traces.py` | https://raw.githubusercontent.com/openai/openai-agents-python/main/src/agents/tracing/traces.py | `ae5b5585a2c1c2a2…` | 19093 | OpenAI Agents SDK traces |
| `langfuse-openapi.yml` | https://cloud.langfuse.com/generated/api/openapi.yml | `2bb89352127497a6…` | 589554 | Langfuse OpenAPI |
| `langsmith-openapi.json` | https://api.smith.langchain.com/openapi.json | `befff16b1d3ca55b…` | 1132694 | LangSmith OpenAPI |
| `sse.html` | https://html.spec.whatwg.org/multipage/server-sent-events.html | `3bd9d721848d9adb…` | 76655 | WHATWG HTML server-sent events section |
