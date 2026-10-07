#!/usr/bin/env python3
"""Reject local proof placeholders and check the public import closure."""
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def code_only(source):
    result = []
    i = depth = 0
    in_string = False
    while i < len(source):
        pair = source[i:i + 2]
        if in_string:
            if source[i] == "\\":
                result.extend("  ")
                i += 2
                continue
            if source[i] == '"':
                in_string = False
            result.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif pair == "/-":
            depth += 1
            result.extend("  ")
            i += 2
        elif depth and pair == "-/":
            depth -= 1
            result.extend("  ")
            i += 2
        elif depth:
            result.append("\n" if source[i] == "\n" else " ")
            i += 1
        elif pair == "--":
            end = source.find("\n", i)
            if end < 0:
                end = len(source)
            result.extend(" " * (end - i))
            i = end
        elif source[i] == '"':
            in_string = True
            result.append(" ")
            i += 1
        else:
            result.append(source[i])
            i += 1
    if depth or in_string:
        raise ValueError("Unclosed comment or string")
    return "".join(result)


files = sorted((ROOT / "GinibrePoincare").rglob("*.lean"))
modules = {str(f.relative_to(ROOT).with_suffix("")).replace("/", "."): f for f in files}
root_files = sorted(ROOT.glob("*.lean"))
all_modules = dict(modules)
all_modules.update({f.stem: f for f in root_files})
clean = {f: code_only(f.read_text()) for f in files + root_files}
errors = []
for f, source in clean.items():
    allowed_sorry = None
    if f.name == "Challenge.lean" and f.parent == ROOT:
        target = re.search(
            r"\btheorem\s+theoremOneOne\s*:\s*∀ n : ℕ,[\s\S]*?\s*:=\s*by\s+(sorry)\s+end\s+PalomarGinibre\s*\Z",
            source,
        )
        namespaces = re.findall(r"^[ \t]*(namespace|end)[ \t]+(\S+)",
                                source[:target.start()] if target else source, re.M)
        stack = []
        for command, name in namespaces:
            if command == "namespace":
                stack.append(name)
            elif stack and stack[-1] == name:
                stack.pop()
        if target and stack == ["PalomarGinibre"]:
            allowed_sorry = target.start(1)
        else:
            errors.append("Challenge.lean: expected only the authorized PalomarGinibre.theoremOneOne statement hole")
    for match in re.finditer(r"\b(?:sorry|admit|axiom|opaque)\b", source):
        if match.group() == "sorry" and match.start() == allowed_sorry:
            continue
        line = source.count("\n", 0, match.start()) + 1
        errors.append(f"{f.relative_to(ROOT)}:{line}: forbidden token {match.group()}")


def imports(source):
    imported = []
    for line in source.splitlines():
        match = re.match(r"^[ \t]*(?:public[ \t]+)?(?:meta[ \t]+)?import[ \t]+"
                         r"(?:all[ \t]+)?(.+)$", line)
        if match:
            imported.extend(match.group(1).split())
    return imported


# Inspect every proof-library module, including modules outside the public closure,
# and the Solution's full local dependency closure. Challenge must never be imported.
proof_seen = set()
proof_todo = list(modules) + ["Solution"]
while proof_todo:
    module = proof_todo.pop()
    if module in proof_seen:
        continue
    proof_seen.add(module)
    if module == "Challenge":
        errors.append("Proof-library/Solution dependency closure imports Challenge")
    elif module in all_modules:
        proof_todo.extend(imports(clean[all_modules[module]]))

seen = set()
todo = imports(code_only((ROOT / "GinibrePoincare.lean").read_text()))
while todo:
    module = todo.pop()
    if module in seen:
        continue
    seen.add(module)
    if module in modules:
        todo.extend(imports(clean[modules[module]]))
for module in sorted(set(modules) - seen):
    errors.append(f"Local module outside public import closure: {module}")
if errors:
    raise SystemExit("\n".join(errors))
print(f"Local source audit passed: {len(files)} library modules; all publicly imported; "
      f"{len(root_files)} root Lean files scanned; only the authorized Challenge statement hole; "
      "proof-library/Solution closure excludes Challenge.")
