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
for filename, expected in manifest["sha256"].items():
    actual = hashlib.sha256((ROOT / "source" / filename).read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Frozen source changed: {filename}")
# The v2 (revised appendix) drafts are frozen separately, so the v1
# manifest above stays untouched.
v2_manifest_path = ROOT / "source/v2/manifest.json"
v2_manifest = json.loads(v2_manifest_path.read_text()) if v2_manifest_path.is_file() else {"sha256": {}}
# The live appendix chunks (beta in [0,1)) are snapshotted under source/v2/chunks/;
# every listed chunk must be hashed, so a dropped hash cannot silently disable the check.
for filename in v2_manifest.get("required_live_chunks", []):
    if filename not in v2_manifest["sha256"]:
        raise SystemExit(f"Live v2 chunk without a frozen hash: v2/{filename}")
for filename, expected in v2_manifest["sha256"].items():
    path = ROOT / "source/v2" / filename
    if not path.is_file():
        raise SystemExit(f"Missing frozen v2 source: v2/{filename}")
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected:
        raise SystemExit(f"Frozen v2 source changed: v2/{filename}")
v2_chunk_count = sum(name.startswith("chunks/") for name in v2_manifest["sha256"])

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
# Besides the certifying declarations, the beta-range bookkeeping names the old
# (1/2 <= beta) declarations ("v1_declarations") and the relaxed ones ("relaxed_by");
# these must resolve as well.
required = sorted({name for entry in obligations for part in entry["subclaims"]
                   for key in ("declarations", "relaxed_by", "v1_declarations")
                   for name in part.get(key, [])})
for name in required:
    if not re.fullmatch(r"SparseSGD(?:\.[A-Za-z_][A-Za-z_0-9']*)+", name):
        raise SystemExit(f"Invalid declaration name: {name}")
checks = "import SparseSGD\n" + "\n".join(f"#check {name}" for name in required) + "\n"
with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", prefix="obligation-check-",
                                 dir=ROOT / ".lake", delete=False) as declaration_file:
    declaration_file.write(checks)
    declaration_path = Path(declaration_file.name)
commands = [[lake, "build"], [lake, "env", "lean", "Audit.lean"],
            [lake, "env", "lean", str(declaration_path)],
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
                   f"{len(manifest['sha256'])} frozen v1 source hashes and "
                   f"{len(v2_manifest['sha256'])} frozen v2 source hashes "
                   f"({v2_chunk_count} of them live appendix chunks).\n")
        log.write(summary)
        print(summary, end="")
finally:
    declaration_path.unlink(missing_ok=True)
