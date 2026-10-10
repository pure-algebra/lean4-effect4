#!/usr/bin/env python3
"""Read-only finite checks of the reviewed numeric and byte schema fragments."""
import importlib.metadata
import json
import sys
sys.path.insert(0, "/private/tmp/effect4-mcp-jsonschema")
import jsonschema
print("jsonschema", importlib.metadata.version("jsonschema"))
schema = {"type": "integer", "minimum": 0, "maximum": 9007199254740991}
for source in ["1", "1.0", "1e0", "0", "0.0", "-0", "-0.0"]:
    print(source, jsonschema.Draft202012Validator(schema).is_valid(json.loads(source)))
schema = {"type": "string", "pattern": "^([0-9a-f]{2})*$"}
for source in ["00", "00\n", "00\r", "00\r\n"]:
    print(repr(source), jsonschema.Draft202012Validator(schema).is_valid(source))
