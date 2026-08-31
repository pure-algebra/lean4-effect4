/**
 * GENERATED — do not edit. THE MCP TOOL TABLE, as data: the rows
 * `Cas.Backend.Mcp.tools` carries — name, self-description, and the
 * canonical schema codes of params and result — emitted from
 * `library/cas/Cas/Backend/Mcp.lean` by `lake exe mcpspec`;
 * regeneration is byte-identity-gated (`--check`, wired into
 * `check:cas`). `mcp/cas-tools.json` is the same rows'
 * language-neutral rendering, from the same list in the same order.
 *
 * `bin/mcp/tools.ts` serves this table and `bin/mcp/manifest.ts`
 * gates it at boot against the emitted JSON. That gate now compares
 * two projections of ONE value, so it is trivially green and stays
 * as defence in depth: a red one means the two renderings in
 * `tools/EmitMcp.lean` have forked, never that a hand mirror drifted.
 *
 * emitted — schemaVersion 1, emitter `mcpspec`,
 * module `library/cas/tools/EmitMcp.lean`, toolchain Lean 4.33.1.
 */

/** A canonical schema code in the revision-0 tagged projection —
 * exactly the fragment the served codes inhabit. It is a TYPE, not
 * a decoder: the host's boot gate compares codes through the
 * canonical printer and never reads one, so a manifest carrying a
 * code outside this union still compares exactly. */
export type McpToolCode =
  | { readonly _tag: "Null" | "Boolean" | "Integer" | "String" }
  | { readonly _tag: "Literal"; readonly value: McpToolCodeLiteral }
  | { readonly _tag: "Array"; readonly item: McpToolCode }
  | { readonly _tag: "Struct"; readonly fields: McpToolCodeFields }
  | {
    readonly _tag: "Union"
    readonly members: ReadonlyArray<McpToolCode>
    readonly mode: "anyOf" | "oneOf"
  }

/** A literal code's value. `LitVal` is the four-row carrier, and
 * this is its projection: the discriminator of a derived union is
 * always a string, but the type says what the carrier says. */
export type McpToolCodeLiteral = null | boolean | number | string

/** A struct code's fields: the name-keyed record `fieldsToJson`
 * builds, each entry an optionality flag beside the field's own
 * code. */
export interface McpToolCodeFields {
  readonly [name: string]: McpToolCodeField
}

/** One entry of that record. */
export interface McpToolCodeField {
  readonly optional: boolean
  readonly schema: McpToolCode
}

/** One row of the tool table: a name, what the tool says about
 * itself, and the two canonical schema codes. */
export interface McpToolRow {
  readonly name: string
  readonly description: string
  readonly params: McpToolCode
  readonly result: McpToolCode
}

/** Every tool the estate serves, in the manifest's order —
 * which is part of what the boot gate compares. */
export const McpToolCodes: ReadonlyArray<McpToolRow> = [
  {
    name: "cas_put",
    description: "Admit one node; the reply is its content address. Admission is the only gate: well-formedness, reference presence, and kind agreement are checked, duplicates are inert, collisions refuse.",
    params: {
      _tag: "Struct",
      fields: {
        payload: { optional: false, schema: { _tag: "String" } },
        refs: {
          optional: false,
          schema: {
            _tag: "Array",
            item: {
              _tag: "Struct",
              fields: {
                expectedTag: { optional: false, schema: { _tag: "Integer" } },
                id: { optional: false, schema: { _tag: "String" } },
              },
            },
          },
        },
        tag: { optional: false, schema: { _tag: "Integer" } },
        version: { optional: false, schema: { _tag: "Integer" } },
      },
    },
    result: {
      _tag: "Struct",
      fields: {
        address: { optional: false, schema: { _tag: "String" } },
      },
    },
  },
  {
    name: "cas_load",
    description: "Load the node at an address, fail-closed: the frame is parsed exactly and the kind is answered as stored.",
    params: {
      _tag: "Struct",
      fields: {
        address: { optional: false, schema: { _tag: "String" } },
      },
    },
    result: {
      _tag: "Struct",
      fields: {
        payload: { optional: false, schema: { _tag: "String" } },
        refs: {
          optional: false,
          schema: {
            _tag: "Array",
            item: {
              _tag: "Struct",
              fields: {
                expectedTag: { optional: false, schema: { _tag: "Integer" } },
                id: { optional: false, schema: { _tag: "String" } },
              },
            },
          },
        },
        tag: { optional: false, schema: { _tag: "Integer" } },
        version: { optional: false, schema: { _tag: "Integer" } },
      },
    },
  },
  {
    name: "cas_run",
    description: "Run a straight-line program submitted inline: instructions in admission order, operands naming an earlier answer by index or a literal address, and loads requiring the address to be there. The reply is the word — the run's history, byte-decidable evidence.",
    params: {
      _tag: "Struct",
      fields: {
        instructions: {
          optional: false,
          schema: {
            _tag: "Array",
            item: {
              _tag: "Union",
              members: [
                {
                  _tag: "Struct",
                  fields: {
                    _tag: { optional: false, schema: { _tag: "Literal", value: "load" } },
                    source: {
                      optional: false,
                      schema: {
                        _tag: "Union",
                        members: [
                          {
                            _tag: "Struct",
                            fields: {
                              _tag: { optional: false, schema: { _tag: "Literal", value: "answer" } },
                              index: { optional: false, schema: { _tag: "Integer" } },
                            },
                          },
                          {
                            _tag: "Struct",
                            fields: {
                              _tag: { optional: false, schema: { _tag: "Literal", value: "literal" } },
                              addressHex: { optional: false, schema: { _tag: "String" } },
                            },
                          },
                        ],
                        mode: "oneOf",
                      },
                    },
                  },
                },
                {
                  _tag: "Struct",
                  fields: {
                    _tag: { optional: false, schema: { _tag: "Literal", value: "put" } },
                    payloadHex: { optional: false, schema: { _tag: "String" } },
                    refs: {
                      optional: false,
                      schema: {
                        _tag: "Array",
                        item: {
                          _tag: "Struct",
                          fields: {
                            expectedTag: { optional: false, schema: { _tag: "Integer" } },
                            source: {
                              optional: false,
                              schema: {
                                _tag: "Union",
                                members: [
                                  {
                                    _tag: "Struct",
                                    fields: {
                                      _tag: { optional: false, schema: { _tag: "Literal", value: "answer" } },
                                      index: { optional: false, schema: { _tag: "Integer" } },
                                    },
                                  },
                                  {
                                    _tag: "Struct",
                                    fields: {
                                      _tag: { optional: false, schema: { _tag: "Literal", value: "literal" } },
                                      addressHex: { optional: false, schema: { _tag: "String" } },
                                    },
                                  },
                                ],
                                mode: "oneOf",
                              },
                            },
                          },
                        },
                      },
                    },
                    tag: { optional: false, schema: { _tag: "Integer" } },
                    version: { optional: false, schema: { _tag: "Integer" } },
                  },
                },
              ],
              mode: "oneOf",
            },
          },
        },
      },
    },
    result: {
      _tag: "Struct",
      fields: {
        word: {
          optional: false,
          schema: {
            _tag: "Array",
            item: {
              _tag: "Struct",
              fields: {
                address: { optional: false, schema: { _tag: "String" } },
              },
            },
          },
        },
      },
    },
  },
  {
    name: "cas_run_ref",
    description: "Run the program stored at an address: load the cont node, recover its table from the step nodes it names, and run it through the same admission doors. The reply is the word. A program is content, so this names one the way everything else in the store is named.",
    params: {
      _tag: "Struct",
      fields: {
        root: { optional: false, schema: { _tag: "String" } },
      },
    },
    result: {
      _tag: "Struct",
      fields: {
        word: {
          optional: false,
          schema: {
            _tag: "Array",
            item: {
              _tag: "Struct",
              fields: {
                address: { optional: false, schema: { _tag: "String" } },
              },
            },
          },
        },
      },
    },
  },
  {
    name: "cas_publish_root",
    description: "Publish an address as a root.",
    params: {
      _tag: "Struct",
      fields: {
        address: { optional: false, schema: { _tag: "String" } },
      },
    },
    result: { _tag: "Struct", fields: {} },
  },
  {
    name: "cas_list_roots",
    description: "List the published roots.",
    params: { _tag: "Struct", fields: {} },
    result: {
      _tag: "Struct",
      fields: {
        roots: { optional: false, schema: { _tag: "Array", item: { _tag: "String" } } },
      },
    },
  },
]

/** What each tool says about itself, by tool name. A tool
 * teaches by use, and the sentence is the estate's, not the
 * host's. */
export const McpToolDescriptions = {
  cas_put: "Admit one node; the reply is its content address. Admission is the only gate: well-formedness, reference presence, and kind agreement are checked, duplicates are inert, collisions refuse.",
  cas_load: "Load the node at an address, fail-closed: the frame is parsed exactly and the kind is answered as stored.",
  cas_run: "Run a straight-line program submitted inline: instructions in admission order, operands naming an earlier answer by index or a literal address, and loads requiring the address to be there. The reply is the word — the run's history, byte-decidable evidence.",
  cas_run_ref: "Run the program stored at an address: load the cont node, recover its table from the step nodes it names, and run it through the same admission doors. The reply is the word. A program is content, so this names one the way everything else in the store is named.",
  cas_publish_root: "Publish an address as a root.",
  cas_list_roots: "List the published roots.",
}
