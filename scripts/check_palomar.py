#!/usr/bin/env python3
"""Offline Palomar preflight; structural checks are not Comparator verification."""
from __future__ import annotations

import argparse
import json
import os
from pathlib import Path
import re
import sys
from urllib.parse import urlparse

ROOT = Path(__file__).resolve().parents[1]
MINIMUM = (4, 35, 0, 2)  # PalomarSubmission/toolchains.json, checked 2026-10-07
STANDARD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULE_NAME = re.compile(r"[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z")


def uncomment(source: str) -> str:
    """Remove nested Lean comments, preserving newlines and quoted strings."""
    out, i, depth = [], 0, 0
    while i < len(source):
        if depth:
            if source.startswith("/-", i):
                depth += 1
                i += 2
            elif source.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                out.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif source.startswith("/-", i):
            depth = 1
            out.append(" ")
            i += 2
        elif source.startswith("--", i):
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            out.append('"')
            i += 1
            while i < len(source):
                ch = source[i]
                out.append(ch)
                i += 1
                if ch == "\\" and i < len(source):
                    out.append(source[i])
                    i += 1
                elif ch == '"':
                    break
        else:
            out.append(source[i])
            i += 1
    return "".join(out)


def imports(source: str) -> list[str]:
    names = []
    for match in re.finditer(r"(?m)^\s*(?:(?:public|meta)\s+)*import\s+(?:all\s+)?([^\n]+)", uncomment(source)):
        names.extend(match[1].split())
    return names


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--structure-only", action="store_true",
                        help="skip toolchain gate; missing targets still fail")
    args = parser.parse_args()
    errors, warnings = [], []

    def require(condition: bool, message: str) -> None:
        if not condition:
            errors.append(message)

    sources = {}
    for directory, dirs, files in os.walk(ROOT, followlinks=False):
        dirs[:] = [d for d in dirs if d not in {".git", ".lake"}]
        for dirname in dirs:
            path = Path(directory) / dirname
            require(not path.is_symlink(), f"directory symlink refused: {path.relative_to(ROOT)}")
        for filename in files:
            if not filename.endswith(".lean"):
                continue
            path = Path(directory) / filename
            rel = path.relative_to(ROOT)
            if path.is_symlink():
                errors.append(f"Lean symlink refused: {rel}")
                continue
            source = path.read_text(encoding="utf-8")
            sources[rel] = source
            require(len(source.splitlines()) <= 10000, f"10,000-line cap exceeded: {rel}")
            if filename != "lakefile.lean":
                require(re.match(r"\s*module\b", uncomment(source)) is not None,
                        f"missing leading module header: {rel}")
    require(sum((ROOT / name).is_file() for name in ("lakefile.lean", "lakefile.toml")) == 1,
            "exactly one Lake configuration required")
    require((ROOT / "LICENSE").is_file(), "root LICENSE required")
    try:
        manifest = json.loads((ROOT / "lake-manifest.json").read_text())
        for package in manifest["packages"]:
            if package.get("type") == "git":
                require(re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")) is not None,
                        f"immutable manifest SHA required: {package.get('name')}")
                url = urlparse(package.get("url", ""))
                require(url.scheme == "https" and url.hostname == "github.com"
                        and url.username is None and url.password is None
                        and not url.query and not url.fragment
                        and re.fullmatch(r"/[^/]+/[^/]+/?", url.path) is not None,
                        f"public HTTPS GitHub dependency URL required: {package.get('name')}")
            elif package.get("type") == "path":
                target = (ROOT / package.get("dir", "")).resolve()
                require(target.is_relative_to(ROOT), "path dependency escapes repository")
            else:
                errors.append(f"unrecognized dependency type: {package.get('name')}")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors.append(f"invalid or missing lake-manifest.json: {exc}")
    try:
        import yaml
        metadata = yaml.safe_load((ROOT / "formalization.yaml").read_text())
        project = metadata["project"]
        for key in ("name", "license", "authors", "responsible_maintainers"):
            require(bool(project.get(key)), f"metadata project.{key} required")
        for key in ("authors", "responsible_maintainers"):
            values = project.get(key, [])
            require(isinstance(values, list), f"project.{key} must be a list")
            for person in values:
                name = person.get("name", "") if isinstance(person, dict) else person
                require(isinstance(name, str) and bool(name.strip()), f"invalid {key} name")
                require(not re.search(r"\b(?:AI|agents?|Codex|OpenAI|GPT|Claude)\b", str(name), re.I),
                        f"human-only {key}; move AI attribution to automation: {name}")
        require(bool(metadata.get("sources")), "metadata sources required")
        require(bool(metadata.get("automation", {}).get("methods")), "automation methods required")
        require(bool(metadata.get("review", {}).get("status")), "review status required")
        classes = metadata.get("classification", {})
        require(1 <= len(classes.get("arxiv", [])) <= 2, "1–2 arXiv categories required")
        require(1 <= len(classes.get("msc2020", [])) <= 8, "1–8 MSC2020 codes required")
    except (ImportError, OSError, ValueError, KeyError, TypeError) as exc:
        errors.append(f"metadata unavailable or invalid: {exc}")
    try:
        config = json.loads((ROOT / "comparator.json").read_text())
        require(isinstance(config, dict), "Comparator configuration must be an object")
        require(set(config) <= {"challenge_module", "solution_module", "theorem_names",
                                "definition_names", "permitted_axioms", "enable_nanoda",
                                "external_kernels"},
                "Comparator configuration has unsupported fields")
        require(all(key in config for key in ("challenge_module", "solution_module",
                    "theorem_names", "permitted_axioms")), "Comparator required fields missing")
        for field in ("challenge_module", "solution_module"):
            require(isinstance(config.get(field), str) and MODULE_NAME.fullmatch(config[field]) is not None,
                    f"safe dotted {field} required")
        require(set(config.get("permitted_axioms", [])) <= STANDARD_AXIOMS,
                "Comparator permits nonstandard axioms")
        require(bool(config.get("theorem_names")), "Comparator theorem_names required")
        # Lake 4.35 treats these as definition HOLES: their values are not
        # compared. This Challenge has concrete definitions, hence no holes.
        require(not config.get("definition_names"),
                "concrete Challenge requires empty definition_names; nonempty entries hide definition values")
        if "enable_nanoda" in config:
            require(isinstance(config["enable_nanoda"], bool), "enable_nanoda must be boolean")
        kernels = config.get("external_kernels", {})
        require(isinstance(kernels, dict), "external_kernels must be an object")
        require(not (config.get("enable_nanoda") and kernels),
                "enable_nanoda and external_kernels cannot both be enabled")
        if isinstance(kernels, dict):
            for name, command in kernels.items():
                require(isinstance(name, str) and bool(name) and isinstance(command, list)
                        and bool(command) and all(isinstance(arg, str) and bool(arg) for arg in command),
                        f"external kernel requires a nonempty command array: {name}")
        challenge_path = Path(config["challenge_module"].replace(".", "/") + ".lean")
        solution_path = Path(config["solution_module"].replace(".", "/") + ".lean")
        challenge, solution = sources[challenge_path], sources[solution_path]
        require(len(challenge.splitlines()) <= 1000, "Challenge exceeds 1,000 lines")
        require(len(challenge.encode("utf-8")) <= 100 * 1024, "Challenge exceeds 100 KiB")
        for imported in imports(challenge):
            require(imported.startswith(("Mathlib.", "Lean.", "Init.", "Std.", "TauCeti.", "CSLib."))
                    or imported in {"Mathlib", "Lean", "Init", "Std", "TauCeti", "CSLib"},
                    f"forbidden independent Challenge import: {imported}")
        # Direct imports have no local project imports; recursively inspect available
        # Mathlib source to ensure the Challenge closure cannot reach this project.
        pending, seen = list(imports(challenge)), set()
        while pending:
            name = pending.pop()
            if name in seen:
                continue
            seen.add(name)
            relative = Path(name.replace(".", "/") + ".lean")
            require(relative not in sources, f"Challenge closure reaches local module: {name}")
            for package_dir in (ROOT / ".lake/packages").glob("*"):
                candidate = package_dir / relative
                if candidate.is_file():
                    pending.extend(imports(candidate.read_text(encoding="utf-8")))
                    break
        for kind, names in (("theorem", config.get("theorem_names", [])),
                            ("definition", config.get("definition_names", []))):
            require(isinstance(names, list), f"{kind}_names must be a list")
            for name in names:
                require(isinstance(name, str) and MODULE_NAME.fullmatch(name) is not None,
                        f"invalid compared name: {name}")
                leaf = str(name).rsplit(".", 1)[-1]
                pattern = r"\b(?:theorem|lemma)\s+" if kind == "theorem" else r"\b(?:def|abbrev)\s+"
                require(re.search(pattern + re.escape(leaf) + r"\b", uncomment(challenge)) is not None,
                        f"Challenge missing compared {kind}: {name}")
                if kind == "theorem":
                    require(re.search(pattern + re.escape(leaf) + r"\b", uncomment(solution)) is not None,
                            f"Solution missing compared theorem: {name}")
    except (OSError, ValueError, KeyError, TypeError) as exc:
        errors.append(f"Comparator surface unavailable or invalid: {exc}")
    try:
        toolchain = (ROOT / "lean-toolchain").read_text().strip()
        mathlib_toolchain = ROOT / ".lake/packages/mathlib/lean-toolchain"
        if mathlib_toolchain.is_file():
            require(mathlib_toolchain.read_text().strip() == toolchain,
                    "project and resolved Mathlib toolchain pins must match exactly")
        match = re.fullmatch(r"leanprover/lean4:v(\d+)\.(\d+)\.(\d+)(?:-rc(\d+))?", toolchain)
        require(match is not None, "Lean toolchain must pin an official release or RC")
        if match:
            version = tuple(int(match[i]) for i in (1, 2, 3)) + (int(match[4]) if match[4] else 10**6,)
            if version < MINIMUM:
                message = f"unsupported toolchain {toolchain}; minimum v4.35.0-rc2"
                (warnings if args.structure_only else errors).append(message)
    except OSError as exc:
        errors.append(f"missing lean-toolchain: {exc}")
    for message in warnings:
        print(f"WARNING: {message}")
    for message in errors:
        print(f"BLOCKER: {message}")
    print(f"Scanned {len(sources)} Lean files; {len(errors)} blocker(s). "
          "Offline structure only; no Lean build, Comparator, or remote verification performed.")
    return bool(errors)


if __name__ == "__main__":
    sys.exit(main())
