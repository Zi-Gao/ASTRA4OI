"""Build the general Lean proof and audit its final theorems' trusted axioms.

Requires elan / Lake and the pinned dependencies in formal/.  Add --regression
to compile the optional finite executable model as well.
"""

import argparse
from pathlib import Path
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--regression", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    expected = re.findall(r"^#print axioms (\S+)$", (root / "Audit.lean").read_text(), re.MULTILINE)
    if not expected:
        raise RuntimeError("Audit.lean must name at least one theorem")
    allowed = {"propext", "Classical.choice", "Quot.sound"}
    try:
        subprocess.run([sys.executable, str(root / "sync_paper.py"), "--check"], check=True)
        subprocess.run(["lake", "build"], cwd=root, check=True)
        result = subprocess.run(["lake", "env", "lean", "Audit.lean"], cwd=root, text=True, capture_output=True, check=True)
        print(result.stdout, end="", flush=True)
        if result.stderr:
            print(result.stderr, file=sys.stderr, end="")
        found = re.findall(r"'([^']+)' (?:depends on axioms:\s*\[([^\]]*)\]|does not depend on any axioms)", result.stdout)
        if [name for name, _ in found] != expected:
            raise RuntimeError("Missing or unexpected theorem in axiom audit output")
        for name, axioms in found:
            used = {axiom.strip() for axiom in axioms.split(",") if axiom.strip()}
            if used - allowed:
                raise RuntimeError(f"{name}: unexpected axioms {sorted(used - allowed)}")
        if args.regression:
            subprocess.run(["lake", "build", "LeanRegression"], cwd=root, check=True)
    except FileNotFoundError:
        parser.exit(1, "Lake was not found; install elan and follow docs/zh/formalization.md.\n")
    except subprocess.CalledProcessError as error:
        if error.stdout:
            print(error.stdout, end="")
        if error.stderr:
            print(error.stderr, file=sys.stderr, end="")
        raise SystemExit(error.returncode) from error
    print(f"PASS core axiom audit: {len(expected)} declarations; only standard logical axioms")


if __name__ == "__main__":
    main()
