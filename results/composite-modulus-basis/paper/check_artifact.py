"""Check public artifact links, bilingual structure, paper labels, and examples."""

import ast
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent


def public_files():
    for directory, folders, files in os.walk(ROOT):
        folders[:] = [name for name in folders if not name.startswith(".") and name not in {"build", "tmp", "__pycache__"}]
        for name in files:
            yield Path(directory) / name


def main():
    for path in public_files():
        if path.suffix == ".py":
            ast.parse(path.read_text(), filename=str(path.relative_to(ROOT)), feature_version=(3, 10))
        if path.suffix != ".md":
            continue
        for href in re.findall(r"\[[^\]]*\]\(([^)]+)\)", path.read_text()):
            if "://" in href or href.startswith(("#", "mailto:")):
                continue
            target = (path.parent / href.split("#")[0]).resolve()
            if not target.exists():
                raise SystemExit(f"Broken link in {path.relative_to(ROOT)}: {href}")
    for chinese in (ROOT / "docs/zh").glob("*.md"):
        english = ROOT / "docs/en" / chinese.name
        if not english.exists():
            raise SystemExit(f"Missing translation: {english.relative_to(ROOT)}")
        headings = lambda p: re.findall(r"^(#+) ", p.read_text(), re.MULTILINE)
        if headings(chinese) != headings(english):
            raise SystemExit(f"Different heading structure: {chinese.name}")
    mapping = json.loads((ROOT / "paper/theorem-map.json").read_text())
    expected = [(claim["kind"], claim["id"]) for claim in mapping["claims"]]
    citations = set(re.findall(r"@\w+\{([^,]+),", (ROOT / "paper/references.bib").read_text()))
    for lang in ("zh", "en"):
        text = (ROOT / f"paper/main-{lang}.tex").read_text()
        statements = re.findall(r"\\begin\{(definition|lemma|theorem|corollary|proposition)\}(?:\[[^\]]*\])?\s*\\label\{([^}]+)\}", text)
        if statements != expected:
            raise SystemExit(f"Paper numbering differs from map: {lang}")
        all_text = text + (ROOT / f"paper/concordance-{lang}.tex").read_text()
        labels = set(re.findall(r"\\label\{([^}]+)\}", all_text))
        for ref in re.findall(r"\\ref\{([^}]+)\}", all_text):
            if ref not in labels:
                raise SystemExit(f"Unknown {lang} cross-reference: {ref}")
        for group in re.findall(r"\\cite\{([^}]+)\}", text):
            for key in group.split(","):
                if key not in citations:
                    raise SystemExit(f"Unknown {lang} citation: {key}")
        usage = (ROOT / f"docs/{lang}/usage.md").read_text()
        for code in re.findall(r"```python\n(.*?)\n```", usage, re.DOTALL):
            subprocess.run([sys.executable, "-c", code], cwd=ROOT / "implementation", check=True)
    print("PASS public links, translations, Python 3.10 grammar, paper numbering/citations, and API examples")


if __name__ == "__main__":
    main()
