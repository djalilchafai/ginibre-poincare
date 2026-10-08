#!/usr/bin/env python3
"""Check compiled declaration independence of the new concrete proof endpoints.

This checks references, not correspondence to a paper proof. The latter is
recorded separately in REPORT.md. Run formal_dependency_graph.py first.
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[1]
TARGETS = {
    'GinibrePoincare.bochnerKodairaTheoremOneTen': {
        'GinibrePoincare.fullTheoremOneNine',
        'GinibrePoincare.fullTheoremOneTen',
        'GinibrePoincare.fullTheoremOneTenSchwartz',
        'GinibrePoincare.ginibreFullWeak_first_deficit_identity',
        'GinibrePoincare.gaussianInverseSquareRootSecondSynthesis_total_energy',
        'GinibrePoincare.finiteInverseSquareRoot_secondDbar_energy',
    },
    'GinibrePoincare.spectral_ginibre_symmetric_weak_poincare': {
        'GinibrePoincare.ginibre_symmetric_weak_poincare',
        'GinibrePoincare.ginibreFullWeak_first_deficit_identity',
        'GinibrePoincare.fullTheoremOneNine',
        'GinibrePoincare.fullMainAnalyticProof',
    },
    'GinibrePoincare.slater_ginibre_symmetric_weak_poincare': {
        'GinibrePoincare.ginibre_symmetric_weak_poincare',
        'GinibrePoincare.ginibreFullWeak_first_deficit_identity',
        'GinibrePoincare.fullTheoremOneNine',
        'GinibrePoincare.fullMainAnalyticProof',
        'GinibrePoincare.spectral_ginibre_symmetric_weak_poincare',
    },
    'GinibrePoincare.matrixSpectralLift_finite_overlap_gaussian_poincare': {
        'GinibrePoincare.ginibre_symmetric_weak_poincare',
        'GinibrePoincare.ginibre_C1_finite_energy_poincare',
        'GinibrePoincare.matrixSpectralLift_finite_overlap_poincare',
        'GinibrePoincare.matrixEigenvalueProjector_overlap_ge',
    },
}


def main():
    data = json.loads((ROOT / 'diagrams/formal-declarations.json').read_text())
    nodes = {d['name']: d for d in data['declarations']}
    for target, forbidden in TARGETS.items():
        if target not in nodes or not nodes[target]['value_dependencies']:
            raise SystemExit(f'Missing compiled proof body: {target}')
        visited, pending = set(), [target]
        while pending:
            name = pending.pop()
            if name in visited:
                continue
            visited.add(name)
            if name in nodes:
                node = nodes[name]
                if node['kind'] == 'theorem' and not node['value_dependencies']:
                    raise SystemExit(f'Unexpanded local theorem body: {name}; regenerate with all local imports')
                pending.extend(node['type_dependencies'])
                pending.extend(node['value_dependencies'])
        bad = visited & forbidden
        if bad:
            raise SystemExit(f'{target}: forbidden earlier endpoint dependencies: {sorted(bad)}')
        print(f'{target}: independence check passed ({len(visited & nodes.keys())} local declarations).')


if __name__ == '__main__':
    main()
