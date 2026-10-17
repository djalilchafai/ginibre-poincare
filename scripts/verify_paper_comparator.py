#!/usr/bin/env python3
"""Three-kernel Comparator recheck of selected paper-result endpoints.

This is an explicitly labelled self-comparison, not independent statement
certification. The independent Theorem 1.1 run remains verify_palomar.py.
No Challenge holes, dependencies, toolchains or registry records are changed.
"""
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def main():
    manifest = json.loads((ROOT / 'verification/paper-comparator-targets.json').read_text())
    names = sorted({name for result in manifest['results'] for name in result['theorem_names']})
    prefix = Path(subprocess.check_output(['lean', '--print-prefix'], cwd=ROOT, text=True).strip())
    config = {
        'challenge_module': 'GinibrePoincare',
        'solution_module': 'GinibrePoincare',
        'theorem_names': names,
        'definition_names': [],
        'permitted_axioms': ['propext', 'Quot.sound', 'Classical.choice'],
        'external_kernels': {name: [str(prefix / 'bin' / exe)]
                             for name, exe in [('nanoda', 'nanoda_bin'), ('con-ron', 'con-ron')]},
    }
    environment = dict(os.environ, LEAN_NUM_THREADS='1')
    home = Path('/home')
    packages = ROOT / '.lake/packages'
    if (home.is_symlink() or (packages.is_symlink() and
            packages.resolve().is_relative_to(home.resolve()))):
        environment.setdefault('COMPARATOR_BWRAP', str(ROOT / 'scripts/canonical_home_bwrap.py'))
    print(f'Paper-result endpoints: {len(names)}; internal helper targets excluded.', flush=True)
    print('SELF-COMPARISON: same library on both sides; no independent paper statement claim.', flush=True)
    with tempfile.TemporaryDirectory(prefix='ginibre-paper-comparator-') as directory:
        target = Path(directory) / 'comparator.json'
        target.write_text(json.dumps(config, indent=2) + '\n')
        return subprocess.run([str(prefix / 'bin/lake'), 'comparator', '--config', str(target)],
                              cwd=ROOT, env=environment).returncode


if __name__ == '__main__':
    raise SystemExit(main())
