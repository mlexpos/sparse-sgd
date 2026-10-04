"""Build every project module, audit Lean dependencies, and verify source provenance."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
manifest = json.loads((ROOT / "source/manifest.json").read_text())
# The manuscript text is not distributed with this repository; only its hashes
# are. Any copy of the frozen text placed under source/ is checked against them.
present = 0
for filename, expected in manifest["sha256"].items():
    path = ROOT / "source" / filename
    if not path.is_file():
        continue
    present += 1
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Frozen source changed: {filename}")

# The root target must reach every project module; a draft outside the import
# graph would otherwise escape both the build and the declaration audit.
seen = set()
def visit(module):
    if module in seen:
        return
    seen.add(module)
    path = ROOT / (module.replace(".", "/") + ".lean")
    if not path.is_file():
        raise SystemExit(f"Missing local import: {module}")
    for imported in re.findall(r"^import\s+(SparseSGD(?:\.[\w]+)*)\s*$", path.read_text(), re.M):
        visit(imported)

visit("SparseSGD")
all_modules = {str(p.relative_to(ROOT).with_suffix("")).replace("/", ".")
               for p in (ROOT / "SparseSGD").rglob("*.lean")}
missing = all_modules - seen
if missing:
    raise SystemExit(f"Modules outside the root import graph: {sorted(missing)}")

env = os.environ.copy()
local_elan = ROOT.parent / ".elan"
if local_elan.is_dir():
    env.setdefault("ELAN_HOME", str(local_elan))
lake = str(local_elan / "bin/lake") if (local_elan / "bin/lake").exists() else "lake"
# Ask Lean to resolve every declaration used to certify a source obligation.
# This is separate from the axiom audit: a stale coverage name must fail too.
obligations = json.loads((ROOT / "obligations.json").read_text())
required = sorted({name for entry in obligations for part in entry["subclaims"]
                   for name in part["declarations"]})
for name in required:
    if not re.fullmatch(r"SparseSGD(?:\.[A-Za-z_][A-Za-z_0-9']*)+", name):
        raise SystemExit(f"Invalid declaration name: {name}")
checks = "import SparseSGD\n" + "\n".join(f"#check {name}" for name in required) + "\n"
with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="obligation-check-",
                                 dir=ROOT / ".lake", delete=False) as declaration_file:
    declaration_file.write(checks)
    declaration_path = Path(declaration_file.name)
commands = [[lake, "build"], [lake, "env", "lean", "Audit.lean"],
            [lake, "env", "lean", str(declaration_path.relative_to(ROOT))],
            [sys.executable, "scripts/coverage.py"]]
try:
    with (ROOT / "verification.log").open("w") as log:
        for command in commands:
            result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                    stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            log.write("$ " + " ".join(command) + "\n" + result.stdout + "\n")
            log.flush()
            if result.returncode:
                print(result.stdout)
                raise SystemExit(result.returncode)
            if command == commands[0]:
                print("Lean build passed.")
            elif command == commands[2]:
                print(f"Verified {len(required)} source-obligation declaration references.")
            else:
                print(result.stdout, end="\n")
        summary = (f"Verified {len(all_modules)} imported modules and "
                   f"{present} of {len(manifest['sha256'])} frozen source hashes "
                   f"({len(manifest['sha256']) - present} source files not present).\n")
        log.write(summary)
        print(summary, end="")
finally:
    declaration_path.unlink(missing_ok=True)
