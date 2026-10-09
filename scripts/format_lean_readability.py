#!/usr/bin/env python3
"""Conservative spacing for the project's Lean sources, without touching prose.

This is intentionally not a Lean pretty-printer. It spaces standalone commas and binder
colons in code. Arithmetic and comparison operators are deliberately untouched:
imported syntax can register compound tokens that a character regex cannot parse. Strings, character
literals, quoted identifiers, nested comments and registered type notations
are preserved. Run without arguments to check; use --write to apply. Generated
subproject facades and the independent registry Challenge are excluded.
"""

from collections import Counter
from pathlib import Path
import argparse
import re
import unicodedata

ROOT = Path(__file__).resolve().parent.parent


def segments(source):
    """Yield (is_code, text), protecting Lean literals and nested comments."""
    i = start = 0
    while i < len(source):
        end = None
        if source.startswith('--', i):
            end = source.find('\n', i)
            if end == -1:
                end = len(source)
        elif source.startswith('/-', i):
            depth, end = 1, i + 2
            while end < len(source) and depth:
                if source.startswith('/-', end):
                    depth += 1
                    end += 2
                elif source.startswith('-/', end):
                    depth -= 1
                    end += 2
                else:
                    end += 1
            if depth:
                raise ValueError('Unclosed Lean block comment')
        elif source[i] == '«':
            end = source.find('»', i + 1)
            if end == -1:
                raise ValueError('Unclosed quoted Lean identifier')
            end += 1
        elif source[i] == '"':
            end = i + 1
            while end < len(source):
                if source[end] == '\\':
                    end += 2
                elif source[end] == '"':
                    end += 1
                    break
                else:
                    end += 1
            else:
                raise ValueError('Unclosed Lean string')
        elif source[i] == "'" and (i == 0 or not (source[i - 1].isalnum() or source[i - 1] in "_'")):
            literal = re.match(r"'(?:\\(?:u[0-9a-fA-F]{4}|x[0-9a-fA-F]{2}|.)|[^'\\\n])'", source[i:])
            if literal:
                end = i + len(literal[0])
        # A registered custom syntax or raw literal may have spacing-sensitive
        # contents. Keep the entire source unchanged rather than guess its lexer.
        if end is not None:
            if start < i:
                yield True, source[start:i]
            yield False, source[i:end]
            start = i = end
        else:
            i += 1
    if start < len(source):
        yield True, source[start:]


def is_atom_start(char):
    """Recognize conservative punctuation neighbors, excluding notation suffixes.

    Lean notation uses modifier letters, subscripts, and superscripts as attached
    token characters. Python's regex word class includes many of these, so it is insufficient
    to distinguish an ordinary identifier from the suffix of a registered token.
    """
    return char in '([⟨‖' or char == '_' or (
        char.isalnum() and unicodedata.category(char) not in {'Lm', 'No', 'Mn', 'Me'}
    )


def format_code(code):
    # Do not split or re-space operators. Even apparently recognizable atoms can
    # be the suffix of imported tokens such as =ᵐ, =ᶠ, *ᵥ, ≤ᵐ, or +ᵥ. A full Lean
    # environment would be needed to obtain the registered token table.
    code = re.sub(r',(?=[^\s])',
                  lambda match: ', ' if is_atom_start(code[match.end()]) else ',', code)
    # Treat only a standalone colon with identifier-like neighbors as a binder
    # separator. In particular, preserve ::, :::, :=, and decorated colon tokens.
    def binder_colon(match):
        return ' : ' if is_atom_start(code[match.end()]) else match[0]
    code = re.sub(r'(?<=[\w)\]])[ \t]*:(?![:=])[ \t]*(?=[\w(])',
                  binder_colon, code)
    return code


def format_skip_reason(source, parts=None):
    """Explain conservative exclusions; skipped files are not fully formatted."""
    if re.search(r'(?m)^\s*(?:(?:local|scoped)\s+)?(?:syntax|declare_syntax_cat|macro|macro_rules|elab|elab_rules|notation3?|infix[lr]?|prefix|postfix)\b', source):
        return 'syntax declaration'
    if re.search(r'\br#*"', source):
        return 'raw string'
    if parts is None:
        parts = list(segments(source))
    if any(code and ('`' in text or '$' in text) for code, text in parts):
        return 'quotation or antiquotation'
    return None


def format_source(source):
    parts = list(segments(source))
    # Imported operators stay intact; source-defined grammar and embedded syntax
    # quotations need a real Lean lexer and are excluded from punctuation edits.
    if format_skip_reason(source, parts):
        return source
    result = ''.join(format_code(text) if code else text for code, text in parts)
    # This guards source preservation, not Lean token equivalence. The conservative
    # punctuation policy above and the subsequent Lean build supply separate checks.
    # Enforce an additional useful invariant: all
    # non-whitespace code characters, and all protected prose/literals, survive.
    before = [(code, re.sub(r'\s', '', text) if code else text) for code, text in segments(source)]
    after = [(code, re.sub(r'\s', '', text) if code else text) for code, text in segments(result)]
    if before != after:
        raise ValueError('Formatting changed non-whitespace content')
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--write', action='store_true', help='apply spacing changes')
    args = parser.parse_args()
    paths = sorted(p for p in (ROOT / 'GinibrePoincare').rglob('*.lean')
                   if 'Subprojects' not in p.parts)
    changed = []
    skipped = Counter()
    for path in paths:
        original = path.read_text()
        reason = format_skip_reason(original)
        if reason:
            skipped[reason] += 1
            continue
        formatted = format_source(original)
        if original != formatted:
            changed.append(path.relative_to(ROOT))
            if args.write:
                path.write_text(formatted)
    print(f'{len(paths)} library files inspected; {sum(skipped.values())} skipped; '
          f'{len(paths) - sum(skipped.values())} eligible for punctuation spacing; '
          f'{len(changed)} ' +
          ('formatted.' if args.write else 'need spacing changes.'))
    for reason, count in sorted(skipped.items()):
        print(f'Skipped {count}: {reason}.')
    if changed and not args.write:
        for path in changed[:20]:
            print(path)
        raise SystemExit(1)


if __name__ == '__main__':
    main()
