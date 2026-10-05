from pathlib import Path
import sys,json
out=Path(sys.argv[1]); payload=json.loads(Path(sys.argv[2]).read_text())
for name,value in payload['files'].items():
 (out/name).write_text(json.dumps(value))
print('isolated producer diagnostic',file=sys.stderr)
sys.exit(payload['exit'])
