"""Freeze active manuscript text and create an initial result inventory (run once)."""
from pathlib import Path
import hashlib
import json
import re
import shutil

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT.parent / "sparse-sgd-latex-source"
DEST = ROOT / "source"
if DEST.exists():
    raise SystemExit("Source snapshot already exists; refusing to overwrite provenance.")
paths = [SOURCE / "unified_scaling_limits.tex"]
for directory in ("chunks", "flow", "front", "refs"):
    paths.extend(sorted((SOURCE / directory).glob("*.tex")))
hashes = {}
claims = []
pattern = re.compile(r"\\begin\{(theorem|lemma|corollary|proposition|assumption|definition)\}(?:\[([^\]]*)\])?\s*\\label\{([^}]+)\}")
for path in paths:
    relative = path.relative_to(SOURCE)
    target = DEST / relative
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(path, target)
    hashes[str(relative)] = hashlib.sha256(target.read_bytes()).hexdigest()
    for match in pattern.finditer(target.read_text()):
        claims.append(dict(label=match[3], kind=match[1], title=match[2],
                           source=str(relative), status="pending", declarations=[]))
(DEST / "manifest.json").write_text(json.dumps(dict(source=str(SOURCE.resolve()),
    mathlib_revision="d13f23b723b8a846827a245b89c10fc7d3f11612", sha256=hashes), indent=2)+"\n")
for label, title in [("eq:LSoracle", "Sparse Gaussian minibatch oracle"),
                     ("phase-dictionary", "Scaling limits, rates, cells and boundaries")]:
    claims.append(dict(label=label, kind="unnumbered", title=title,
                       status="pending", declarations=[]))
(ROOT / "coverage.json").write_text(json.dumps(claims, indent=2)+"\n")
print(f"Snapshotted {len(paths)} source files; inventoried {len(claims)} entries.")
