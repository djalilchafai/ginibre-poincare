#!/usr/bin/env python3
"""Generate exhaustive thematic import facades and source inventory; no source moves."""
from pathlib import Path
import argparse
import json
import re

ROOT = Path(__file__).resolve().parent.parent
GROUPS = {
 'ComplexGaussianHermite': ('Complex Gaussian and Hermite analysis', 'Gaussian laws, moments, complex Hermite basis, completeness, Parseval and Wirtinger calculus.'),
 'GaussianLSI': ('Gaussian log-Sobolev and entropy', 'Gaussian LSI via discrete approximation, entropy tensorization and analytic closure.'),
 'GinibreMeasureGeometry': ('Ginibre measure and holomorphic geometry', 'Concrete normalization, Vandermonde isometry, symmetry and holomorphic projection geometry.'),
 'WeakSobolev': ('Weak Sobolev domains and collision capacity', 'Weak gradients, mollification, core approximation, collision removal and capacity; Appendix A.'),
 'DeficitsEquality': ('Poincaré deficits and equality', 'Sharp symmetric inequality, Hermite deficits and affine equality; supports Theorems 1.1, 1.9 and 1.10.'),
 'PolynomialRadial': ('Polynomial, radial and equilibrium sectors', 'Equilibrium factorization, Hermite–Laguerre eigenfunctions, Kostlan laws and radial LSI; Theorems 1.2, 1.4, 1.12.'),
 'GeneratorSemigroup': ('Diffusion operators and analytic semigroups', 'Generator domains, Bochner identities, curvature, resolvents and transition identification.'),
 'StochasticCalculus': ('Stochastic calculus foundations', 'Brownian integration, quadratic variation, Girsanov changes of law and finite-dimensional Itô formulas.'),
 'StochasticDynamics': ('Ginibre stochastic dynamics', 'Singular stochastic equation, Hamiltonian noise constructions, independence, CIR factorization and stationarity; Theorem 1.3.'),
 'MatrixLift': ('Matrix lift and eigenvector overlaps', 'Schur and spectral charts, matrix Gaussian law and finite-energy overlap inequalities; Theorem 1.13.'),
 'NonQuadratic': ('Nonquadratic potentials', 'Weighted dbar, general-potential geometry, convex transports and radial LSI; Theorem 1.14.'),
 'Endgame': ('Paper assembly', 'Public completion endpoints and finite or abstract reduction assemblies.'),
}

def classify(p):
 n=p.stem
 if p.parent.name=='Endgame': return 'Endgame'
 if n.startswith(('Matrix',)): return 'MatrixLift'
 if n.startswith(('NonQuadratic','GeneralPotential','GeneralRadial','StrongConvex')): return 'NonQuadratic'
 if n.startswith(('Brownian','FiniteDimensionalIto','GinibreBrownianIntegral','GinibreBrownianPredictable','GinibreBrownianFiltration','GinibreStochasticBrownian','GinibreStochasticGaussian')): return 'StochasticCalculus'
 if n.startswith(('GinibreBrownian','GinibreStochastic','GinibreHamiltonian','GinibreDriven','GinibreNoise','GinibreOriginal','GinibreEquilibriumProcess','GinibreEquilibriumPositive','GinibreZeroPair','Dynamical','IndependentNoise','GinibreDynamics','GinibreZeroPair')): return 'StochasticDynamics'
 if n.startswith(('GinibreFull','GinibreTransitionAnalytic','GinibreOU')) or any(s in n for s in ('Semigroup','Generator','Pregenerator','Pointwise','Resolvent','Diffusion','Spectrum')): return 'GeneratorSemigroup'
 if n.startswith(('GinibreRadial','GinibreTwoRadiusEquilibrium','GinibrePairRadius','Polynomial','Radial','Radius','SumRadius','PairwiseRadius','PairRadius','Kostlan','Laguerre','GeneralizedLaguerre','Gamma','Equilibrium','CenterOfMassEigen','FullRadial','LogSobolev','BlockMagnitude','Magnitude','HomogeneousRadial')): return 'PolynomialRadial'
 if n.startswith(('Bernoulli','Entropy','FiniteEntropy','IntegralEntropy','TwoPoint','CompactLipschitz','LipschitzMollification')) or 'LSI' in n or 'LogSobolev' in n or n=='GinibreEntropy': return 'GaussianLSI'
 if n.startswith(('GinibreInteriorWeak','GinibreSmoothDistributional','GinibreWeak','GinibreArbitraryWeak','GinibreCollision','GinibreDistributional','GinibreWeightedInterior','GinibreValueTruncation','GinibreSpatial','GinibreLebesgue','Lebesgue','Weak','Sobolev','SmoothTest','TaylorDifference','L2Bounded','L2Representative','Collision')) or any(s in n for s in ('Sobolev','CoreClosure','GraphNorm','Mollification','CompactApproximation','GradientClosure')): return 'WeakSobolev'
 if n.startswith(('Hermite','Complex','NormalizedComplex','Multivariate','Gaussian','RealGaussian','PolarGaussian','FinitePi','AngularMoments','WeightedSeries')): return 'ComplexGaussianHermite'
 if n.startswith(('GinibreC1WeakPoincare','GinibreEquality','GinibreSymmetricWeak','GinibreSymmetricPoincare','FiniteHermite','GinibreNonsymmetric','GinibreLinearStatistic')) or 'Deficit' in n: return 'DeficitsEquality'
 return 'GinibreMeasureGeometry'

def imports(path):
 # Import statements in this project appear at top level before comment blocks.
 return re.findall(r'^(?:public\s+)?(?:meta\s+)?import\s+(?:all\s+)?([\w.]+)',path.read_text(),re.M)

def outputs():
 paths=sorted(p for p in (ROOT/'GinibrePoincare').rglob('*.lean') if 'Subprojects' not in p.parts)
 membership={'.'.join(p.relative_to(ROOT).with_suffix('').parts):classify(p) for p in paths}
 groups={k:[] for k in GROUPS}
 for p in paths: groups[classify(p)].append(p)
 result={'schema_version':1,'grouping':'Thematic import facades; existing source paths retained. Every original library module has exactly one primary group. Imports may cross groups.','library_module_count':len(paths),'groups':{}}
 files={}
 doc=['# Ginibre formalization subprojects','','Generated by `python3 scripts/group_subprojects.py`. Existing modules retain their paths. Each original library file belongs to exactly one primary subproject; root audit and compatibility files are separate infrastructure. Facades import original modules only, so grouping creates no import cycles. This is thematic organization inside one Lake package, not separate packages.','','Use `lake build GinibrePoincare.Subprojects.NAME` to build a group and its dependencies. Cross-group dependencies below describe direct source imports; mathematical workstreams can depend on one another in both directions without creating Lean import cycles.','','See [numbered report](FORMALIZATION_REPORT.md) for proof scope and open work.','','| Subproject / entry point | Modules | Lines | Scope |','| --- | ---: | ---: | --- |']
 for name,(title,scope) in GROUPS.items():
  ps=groups[name]; mods=['.'.join(p.relative_to(ROOT).with_suffix('').parts) for p in ps]
  deps=sorted({membership[m] for p in ps for m in imports(p) if m in membership and membership[m]!=name})
  count=sum(len(p.read_text().splitlines()) for p in ps)
  facade=ROOT/'GinibrePoincare/Subprojects'/f'{name}.lean'
  files[facade]='module\n\n'+''.join(f'public import {m}\n' for m in mods)+f'\n/-! # {title}\n\n{scope}\nGenerated by scripts/group_subprojects.py. Original modules retain their paths.\n-/\n'
  result['groups'][name]={'title':title,'scope':scope,'entrypoint':str(facade.relative_to(ROOT)),'modules':mods,'module_count':len(ps),'physical_lines':count,'direct_dependency_groups':deps}
  doc.append(f'| [{title}](GinibrePoincare/Subprojects/{name}.lean) | {len(ps)} | {count:,} | {scope} |')
 doc+=['','Counts include comments and blank lines, exclude generated facades and Mathlib. The full project/transitive Mathlib counts are refreshed separately with `python3 scripts/count_lean_sources.py`.','','## Exhaustive file inventory','']
 for name,(title,scope) in GROUPS.items():
  g=result['groups'][name]
  doc += [f'### {title}','',f'Entry point: `{name}`. Direct dependency groups: '+(', '.join(g['direct_dependency_groups']) or 'none')+'.','']
  doc += [f'- [{p.stem}]({p.relative_to(ROOT)})' for p in groups[name]]
  doc.append('')
 files[ROOT/'SUBPROJECTS.md']='\n'.join(doc)+'\n'
 files[ROOT/'subprojects.json']=json.dumps(result,indent=2)+'\n'
 return files,len(paths)

if __name__=='__main__':
 parser=argparse.ArgumentParser(); parser.add_argument('--check',action='store_true'); args=parser.parse_args()
 files,n=outputs()
 if args.check:
  stale=[str(p.relative_to(ROOT)) for p,s in files.items() if not p.exists() or p.read_text()!=s]
  if stale: raise SystemExit('Stale generated files: '+', '.join(stale))
 else:
  for p,s in files.items(): p.parent.mkdir(parents=True,exist_ok=True); p.write_text(s)
 print(f'{n} original library modules grouped exactly once into {len(GROUPS)} subprojects; '+('generated outputs current.' if args.check else 'outputs generated.'))
