#!/usr/bin/env python3
"""Run the toolchain's actual Comparator with both independent kernels.

Based on the PalomarTemplate verification script. Uses existing dependencies;
never runs a cache fetch or dependency update. This is not a substitute verifier.
"""
import json
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parent.parent
readiness = subprocess.run(["python3", "scripts/check_palomar.py"], cwd=ROOT)
if readiness.returncode:
    raise SystemExit(readiness.returncode)
for command in ("lake", "lean", "git", "env"):
    if not shutil.which(command):
        raise SystemExit(f"Required command missing: {command}")
if not shutil.which(os.environ.get("COMPARATOR_BWRAP", "bwrap")):
    raise SystemExit("Comparator sandbox command missing (COMPARATOR_BWRAP or bwrap)")
prefix = Path(subprocess.check_output(["lean", "--print-prefix"], cwd=ROOT, text=True).strip())
for command in ("lake", "leanexport", "leanchecker", "nanoda_bin", "con-ron"):
    if not (prefix / "bin" / command).is_file():
        raise SystemExit(f"Pinned toolchain does not bundle {command}; Palomar requires a supported toolchain.")
config = json.loads((ROOT / "comparator.json").read_text())
config.pop("enable_nanoda", None)
config.setdefault("external_kernels", {}).update({
    "nanoda": [str(prefix / "bin" / "nanoda_bin")],
    "con-ron": [str(prefix / "bin" / "con-ron")],
})
with tempfile.TemporaryDirectory(prefix="ginibre-palomar-") as directory:
    target = Path(directory) / "comparator.json"
    target.write_text(json.dumps(config, indent=2) + "\n")
    environment = os.environ.copy()
    environment["LEAN_NUM_THREADS"] = "1"
    if Path("/home").is_symlink() and "COMPARATOR_BWRAP" not in environment:
        environment["COMPARATOR_BWRAP"] = str(ROOT / "scripts" / "canonical_home_bwrap.py")
        print("Comparator sandbox: canonicalize symlink mount paths; hide canonical home; "
              "restore existing dependency store read-only.", flush=True)
    result = subprocess.run([str(prefix / "bin" / "lake"), "comparator", "--config", str(target)],
                            cwd=ROOT, env=environment)
    if result.returncode:
        raise SystemExit(result.returncode)
