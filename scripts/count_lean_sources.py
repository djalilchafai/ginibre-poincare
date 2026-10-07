#!/usr/bin/env python3
"""Count physical Lean lines and the transitive Mathlib source import closure."""
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
MATHLIB = (ROOT / '.lake/packages/mathlib').resolve()


def imports(path):
    # Remove nested Lean block comments and line comments before reading imports.
    source = path.read_text()
    clean = []
    i = depth = 0
    while i < len(source):
        pair = source[i:i + 2]
        if pair == '/-':
            depth += 1
            i += 2
        elif depth and pair == '-/':
            depth -= 1
            i += 2
        elif depth:
            if source[i] == '\n':
                clean.append('\n')
            i += 1
        elif pair == '--':
            end = source.find('\n', i)
            i = len(source) if end < 0 else end
        else:
            clean.append(source[i])
            i += 1
    for match in re.finditer(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',
        ''.join(clean), re.MULTILINE
    ):
        for name in match.group(1).split():
            if name == "all":
                continue
            if re.fullmatch(r'[A-Za-z_][\w]*(?:\.[\w]+)*', name):
                yield name


def import_closure(seeds):
    pending = list(seeds)
    visited = set()
    used_mathlib = set()
    while pending:
        path = pending.pop().resolve()
        if path in visited:
            continue
        visited.add(path)
        if path.is_relative_to(MATHLIB) and path.relative_to(MATHLIB).parts[0] == 'Mathlib':
            used_mathlib.add(path)
        for name in imports(path):
            relative = Path(*name.split('.')).with_suffix('.lean')
            if name == 'Mathlib' or name.startswith('Mathlib.'):
                dependency = MATHLIB / relative
            elif name == 'GinibrePoincare' or name.startswith('GinibrePoincare.'):
                dependency = ROOT / relative
            else:
                continue  # Lean and other dependencies are outside this metric.
            if not dependency.is_file():
                raise FileNotFoundError(dependency)
            pending.append(dependency)
    return used_mathlib


def lines(paths):
    return sum(len(path.read_text().splitlines()) for path in paths)


project = sorted((ROOT / 'GinibrePoincare').rglob('*.lean')) + sorted(ROOT.glob('*.lean'))
used = import_closure(project)
verified_used = import_closure([ROOT / 'GinibrePoincare.lean'])
result = {
    'counting_rule': 'Physical .lean lines, including comments and blank lines. All active project sources including root files and excluded drafts; archives excluded. Used Mathlib is the transitive source-module import closure of those project files, each module counted once in full. Lean and non-Mathlib dependencies excluded. This is module-level usage, not declaration-level proof dependency usage.',
    'project_files': len(project),
    'project_lines': lines(project),
    'used_mathlib_files': len(used),
    'used_mathlib_lines': lines(used),
    'total_lines_with_used_mathlib': lines(project) + lines(used),
    'verified_entry_used_mathlib_files': len(verified_used),
    'verified_entry_used_mathlib_lines': lines(verified_used),
}
(ROOT / 'lean-source-counts.json').write_text(json.dumps(result, indent=2) + '\n')
(ROOT / 'used-mathlib-modules.txt').write_text(''.join(
    '.'.join(path.relative_to(MATHLIB).with_suffix('').parts) + '\n' for path in sorted(used)
))
print(json.dumps(result, indent=2))
