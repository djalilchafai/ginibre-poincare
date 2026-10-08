#!/usr/bin/env python3
"""Render exact compiled declaration references and local Lean source imports."""
import argparse
import base64
import gzip
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
OUT = ROOT / 'diagrams'
TARGETS = ['GinibrePoincare.fullMainAnalyticProof',
           'GinibrePoincare.fullMatrixLift_functional_inequalities',
           'GinibrePoincare.fullNonQuadraticPotentialTheorem',
           'GinibrePoincare.fullTheoremOneNine',
           'GinibrePoincare.fullTheoremOneTenSchwartz', 'PalomarGinibre.theoremOneOne']


def lean_imports(path):
    source = path.read_text()
    clean, i, depth = [], 0, 0
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
    return [name for match in re.finditer(
        r'^\s*(?:(?:public|private|meta)\s+)*import\s+([^\n]+)',
        ''.join(clean), re.MULTILINE) for name in match[1].split()
        if name != 'all' and re.fullmatch(r'[A-Za-z_]\w*(?:\.\w+)*', name)]


def module_graph():
    paths = sorted((ROOT / 'GinibrePoincare').rglob('*.lean')) + sorted(ROOT.glob('*.lean'))
    names = {'.'.join(p.relative_to(ROOT).with_suffix('').parts): p for p in paths}
    edges = sorted((dep, name) for name, p in names.items()
                   for dep in set(lean_imports(p)) if dep in names)
    # Kahn's algorithm independently verifies the source-module DAG.
    incoming = Counter(target for _, target in edges)
    children = {name: [] for name in names}
    for dep, target in edges:
        children[dep].append(target)
    queue = sorted(name for name in names if incoming[name] == 0)
    visited = 0
    while queue:
        name = queue.pop()
        visited += 1
        for child in children[name]:
            incoming[child] -= 1
            if incoming[child] == 0:
                queue.append(child)
    if visited != len(names):
        raise ValueError('Local source imports contain a cycle')
    return {'schema_version': 1, 'edge_direction': 'dependency -> importer',
            'nodes': [{'name': n, 'path': str(p.relative_to(ROOT))} for n, p in sorted(names.items())],
            'edges': [list(edge) for edge in edges]}


def graphviz(nodes, edges, title, target=None):
    lines = ['digraph formal_dependencies {', 'rankdir=BT;',
        'graph [bgcolor="white", pad="0.3", nodesep="0.25", ranksep="0.7", label=' + json.dumps(title) + ', labelloc=t, fontname="sans-serif"];',
        'node [shape=box, style="rounded,filled", fillcolor="#f8fafc", color="#64748b", fontname="sans-serif", fontsize=11];',
        'edge [arrowsize=0.7, fontname="sans-serif", fontsize=9];']
    for name in sorted(nodes):
        label = name.replace('GinibrePoincare.', '').replace('PalomarGinibre.', '')
        if len(label) > 80:
            label = label[:35] + '\n' + label[35:]
        attrs = ', fillcolor="#dbeafe", color="#2563eb", penwidth=2' if name == target else ''
        lines.append(json.dumps(name) + ' [label=' + json.dumps(label) + attrs + '];')
    for dependency, importer, kind in sorted(edges):
        color = {'type': '#b45309', 'value': '#2563eb', 'both': '#7e22ce', 'import': '#64748b'}[kind]
        lines.append(json.dumps(dependency) + ' -> ' + json.dumps(importer) +
                     ' [color=' + json.dumps(color) + ', tooltip=' + json.dumps(kind) + '];')
    return '\n'.join(lines) + '\n}\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--from-export', type=Path, help='use an existing Lean export')
    parser.add_argument('--check', action='store_true', help='check generated views from the saved export; does not rerun Lean')
    args = parser.parse_args()
    raw_path = OUT / 'formal-declarations.json'
    exporter = ROOT / 'scripts/ExportFormalDependencies.lean'
    expected_modules = sorted(['GinibrePoincare', 'Solution'] + [
        '.'.join(p.relative_to(ROOT).with_suffix('').parts)
        for p in (ROOT / 'GinibrePoincare').rglob('*.lean')])
    content = exporter.read_text()
    start_marker = '-- BEGIN GENERATED IMPORTS\n'
    end_marker = '-- END GENERATED IMPORTS'
    start = content.index(start_marker) + len(start_marker)
    end = content.index(end_marker, start)
    header = ''.join('import all ' + name + '\n' for name in expected_modules)
    if content[start:end] != header:
        if args.check or args.from_export:
            raise SystemExit('Exporter import list is stale; run the generator without --check/--from-export')
        exporter.write_text(content[:start] + header + content[end:])
    if args.from_export:
        raw = args.from_export.read_text()
    elif args.check:
        raw = raw_path.read_text()
    else:
        env = dict(os.environ, LEAN_NUM_THREADS='1', GINIBRE_DEPENDENCY_OUTPUT=str(raw_path))
        subprocess.run(['lake', 'env', 'lean', 'scripts/ExportFormalDependencies.lean'], cwd=ROOT, env=env, check=True)
        raw = raw_path.read_text()
    data = json.loads(raw)
    declarations = {node['name']: node for node in data['declarations']}
    if len(declarations) != len(data['declarations']):
        raise ValueError('Duplicate compiled declarations')
    external = {node['name'] for node in data['external_constants']}
    references = {dep for node in declarations.values() for key in ('type_dependencies', 'value_dependencies') for dep in node[key]}
    if references - declarations.keys() - external:
        raise ValueError('Missing dependency boundary declarations')
    for name in TARGETS:
        if name not in declarations:
            raise ValueError('Missing completion theorem: ' + name)
        if not declarations[name]['value_dependencies']:
            raise ValueError('Completion theorem proof body unavailable: ' + name)
    if 'PalomarGinibre.theoremOneOne' not in declarations or any(n['module'] == 'Challenge' for n in declarations.values()):
        raise ValueError('Solution inclusion / Challenge exclusion failed')
    modules = module_graph()
    files = {raw_path: json.dumps(data, sort_keys=True, separators=(',', ':')) + '\n',
             OUT / 'formal-module-imports.json': json.dumps(modules, indent=2) + '\n'}
    all_dot = graphviz([n['name'] for n in modules['nodes']],
                       [(a, b, 'import') for a, b in modules['edges']], 'Complete local Lean import DAG')
    files[OUT / 'formal-module-imports.dot'] = all_dot
    # The complete import graph is distributed as DOT/JSON, rather than a giant unreadable image.
    summaries = []
    for target in TARGETS:
        node = declarations[target]
        types, values = set(node['type_dependencies']), set(node['value_dependencies'])
        dependencies = (types | values) & declarations.keys()
        edges = [(dep, target, 'both' if dep in types and dep in values else 'type' if dep in types else 'value') for dep in dependencies]
        dot = graphviz(dependencies | {target}, edges, 'Exact direct local declaration references', target)
        stem = 'formal-' + target.split('.')[-1]
        files[OUT / (stem + '.dot')] = dot
        files[OUT / (stem + '.svg')] = subprocess.run(['dot', '-Tsvg'], input=dot, text=True, capture_output=True, check=True).stdout
        summaries.append({'target': target, 'direct_local_dependencies': len(dependencies),
                          'direct_external_dependencies': len((types | values) - declarations.keys())})
    template = (ROOT / 'scripts/formal_graph_template.html').read_text()
    payload = json.dumps(data, separators=(',', ':')).encode()
    embedded = base64.b64encode(gzip.compress(payload, compresslevel=9, mtime=0)).decode('ascii')
    files[ROOT / 'formal-dependencies.html'] = template.replace('__FORMAL_GRAPH_JSON__', embedded).replace(
        '__PAPER_OVERVIEW_SVG__', (OUT / 'Endgame.svg').read_text())
    summary = {'schema_version': 1, 'local_declarations': len(declarations),
               'local_theorems': sum(n['kind'] == 'theorem' for n in declarations.values()),
               'compiled_local_modules': len(data['modules']), 'external_boundary_constants': len(external),
               'direct_reference_pairs': sum(len(set(n['type_dependencies']) | set(n['value_dependencies'])) for n in declarations.values()),
               'source_modules': len(modules['nodes']), 'local_import_edges': len(modules['edges']),
               'export_sha256': hashlib.sha256(files[raw_path].encode()).hexdigest(), 'targets': summaries}
    files[OUT / 'formal-graph-summary.json'] = json.dumps(summary, indent=2) + '\n'
    if args.check:
        stale = [str(p.relative_to(ROOT)) for p, content in files.items() if not p.exists() or p.read_text() != content]
        if stale:
            raise SystemExit('Stale formal dependency views: ' + ', '.join(stale))
    else:
        for p, content in files.items():
            p.parent.mkdir(parents=True, exist_ok=True)
            p.write_text(content)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
