#!/usr/bin/env python3
"""Keep Comparator's sandbox intact on hosts whose /home is a symlink.

Bubblewrap refuses mount destinations that are symlinks. Resolve only mount
path operands, including the home tmpfs cover, so the actual canonical home is
still hidden. Restore read-only access to this project's existing dependency
store when .lake/packages points into that hidden home. All isolation, network,
environment, command and writable-mount flags are passed through unchanged.
"""
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parent.parent
BWRAP = "/usr/bin/bwrap"


def sandbox_arguments(arguments):
    result = []
    i = 0
    while i < len(arguments) and arguments[i] != "--":
        flag = arguments[i]
        count = {"--tmpfs": 1, "--ro-bind": 2, "--bind": 2}.get(flag)
        if count is not None:
            if i + count >= len(arguments):
                raise ValueError(f"Missing mount operands for {flag}")
            result.append(flag)
            result.extend(str(Path(value).resolve()) for value in arguments[i + 1:i + 1 + count])
            i += count + 1
        else:
            result.append(flag)
            i += 1
    home = Path("/home")
    packages = ROOT / ".lake" / "packages"
    if home.is_symlink() and packages.is_symlink():
        canonical = packages.resolve(strict=True)
        if canonical.is_relative_to(home.resolve(strict=True)):
            if not canonical.is_dir():
                raise ValueError("The existing project dependency store is not a directory")
            result.extend(["--ro-bind", str(canonical), str(canonical)])
    result.extend(arguments[i:])
    return result


if __name__ == "__main__":
    os.execv(BWRAP, [BWRAP, *sandbox_arguments(sys.argv[1:])])
