#!/usr/bin/env python3
"""Refresh import closure and add public alternative-route declarations to the audit."""
from pathlib import Path
import re

root = Path(__file__).resolve().parent.parent
modules = sorted(root.glob("GinibrePoincare/**/*.lean"))
audit = root / "AllLocalAxiomAudit.lean"
tail = audit.read_text().split("meta import Lean.Util.CollectAxioms", 1)[1]
imports = ["GinibrePoincare"] + [
    str(p.relative_to(root).with_suffix("")).replace("/", ".") for p in modules
] + ["Solution"]
audit.write_text("module\n\n" + "".join(f"import all {m}\n" for m in imports)
                 + "meta import Lean.Util.CollectAxioms" + tail)

audit = root / "AxiomAudit.lean"
text = audit.read_text().rstrip()
existing = set(re.findall(r"^#print axioms (\S+)", text, re.M))
declarations = re.compile(
    r"^\s*(?:@\[[^\n]*\]\s*)?(?:public\s+)?(?:noncomputable\s+)?(?:theorem|lemma|def|abbrev)\s+(\w+)", re.M
)
added = []
for path in modules:
    if not path.stem.startswith(("Alternative", "BakryEmery", "Correspondence")):
        continue
    source = path.read_text()
    namespace = re.search(r"^namespace (GinibrePoincare(?:\.\w+)*)$", source, re.M)
    prefix = namespace[1] if namespace else "GinibrePoincare"
    for name in declarations.findall(source):
        qualified = f"{prefix}.{name}"
        if qualified not in existing:
            existing.add(qualified)
            added.append(f"#print axioms {qualified}")
audit.write_text(text + "\n" + "\n".join(added) + ("\n" if added else ""))
print(f"All-local imports: {len(imports)}; added public axiom queries: {len(added)}.")
