#!/usr/bin/env python3
"""Wrong pins must refuse before helper compilation or execution."""
import json, pathlib, subprocess, sys, tempfile
script = pathlib.Path(__file__).with_name("reproduce.py")
with tempfile.TemporaryDirectory(prefix="checked-product-version-controls-") as temp:
    root = pathlib.Path(temp)
    cases = [
        ("compiler-package", "7.0.0-dev.WRONG", "4.0.1", "7.0.0-dev.20260629.1", False, "Unsupported @typescript/native-preview version"),
        ("compiler-executable", "7.0.0-dev.20260629.1", "4.0.1", "7.0.0-dev.WRONG", False, "Unsupported tsgo executable version"),
        ("catalogue-effect", "7.0.0-dev.20260629.1", "4.0.0-rc.112", "7.0.0-dev.20260629.1", False, "Unsupported Effect version"),
        ("helpers-effect", "7.0.0-dev.20260629.1", "4.0.2", "7.0.0-dev.20260629.1", True, "Unsupported Effect version"),
    ]
    for name, compiler, effect, executable, helpers_only, refusal in cases:
        install = root / name / "install"
        for package, version in [("@typescript/native-preview", compiler), ("effect", effect)]:
            target = install / "node_modules" / package / "package.json"
            target.parent.mkdir(parents=True)
            target.write_text(json.dumps({"version": version}))
        binary = install / "node_modules/.bin/tsgo"
        binary.parent.mkdir(parents=True)
        binary.write_text(f"#!/usr/bin/env python3\nprint('Version {executable}')\n")
        binary.chmod(0o755)
        output = root / name / "output"
        command = [sys.executable, str(script), "--install", str(install), "--out", str(output)]
        if helpers_only:
            command.append("--helpers-only")
        result = subprocess.run(command, text=True, capture_output=True)
        if result.returncode == 0 or refusal not in result.stderr or (output / "helpers").exists():
            raise SystemExit(f"Control failed: {name}: {result.stdout}{result.stderr}")
        print(f"PASS {name}: {refusal}; no helper compilation or execution")
